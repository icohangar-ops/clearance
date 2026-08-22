/**
 * Clearance CHP adapter — domain policy + spend checks over `@cubiczan/chp`.
 *
 * Profile B (`evaluateGate` / `approveHuman`) owns capital thresholds and
 * content hashes. Clearance-specific adversarial checks (blocked vendors,
 * action catalog, prompt injection, zero-notional research) stay here.
 */
import {
  approveHuman,
  evaluateGate,
  type GatePolicy,
  type GateResult,
  type ProposedAction,
} from "@cubiczan/chp";
import type { ChpState, ClearanceStatus } from "./types";

export interface ChpInput {
  action: string;
  amountCents: number;
  vendor?: string;
  agentName: string;
  policyMaxAuto: number;
  blocked: boolean;
  actionAllowed: boolean;
  withinSpendCap: boolean;
  /** Remaining daily spend room in cents (agent cap − used). */
  spendRemainingCents?: number;
  memoryHints: string[];
}

export interface ChpResult {
  state: ChpState;
  status: ClearanceStatus;
  rationale: string;
  foundations: string[];
  attackFindings: string[];
  r0: {
    solvable: boolean;
    scoped: boolean;
    valid: boolean;
    worthIt: boolean;
  };
  /** Present when the published Profile B gate ran. */
  gate?: GateResult;
}

function dollars(cents: number): number {
  return Math.round(cents) / 100;
}

function policyFromInput(input: ChpInput): GatePolicy {
  const hitl = Math.max(dollars(input.policyMaxAuto), 0.01);
  const maxNotional = hitl * 10;
  const remaining =
    input.spendRemainingCents !== undefined
      ? dollars(input.spendRemainingCents)
      : maxNotional;
  return {
    max_notional: maxNotional,
    daily_cap: Math.max(remaining, hitl),
    hitl_threshold: hitl,
    min_confidence: 0.55,
    allowed_actions: input.actionAllowed ? [input.action] : [],
    per_asset_limits: {
      [input.vendor?.trim() || "USD"]: maxNotional,
    },
  };
}

function proposedFromInput(input: ChpInput): ProposedAction {
  return {
    action: input.action,
    asset: input.vendor?.trim() || "USD",
    notional: dollars(input.amountCents),
    confidence: 0.9,
    rationale: `clearance for ${input.agentName}`,
  };
}

function mapGateState(gate: GateResult): {
  state: ChpState;
  status: ClearanceStatus;
} {
  if (gate.state === "LOCKED") {
    return { state: "LOCKED", status: "approved" };
  }
  if (gate.state === "HITL_REQUIRED") {
    return { state: "PROVISIONAL", status: "pending_human" };
  }
  return { state: "REJECTED", status: "denied" };
}

/**
 * Consensus Hardening Protocol gate for Clearance.
 * Domain hard-fails first; capital path delegates to `@cubiczan/chp`.
 */
export function runChpGate(input: ChpInput): ChpResult {
  const foundations = [
    "Agent identity and API key are authentic for this org",
    "Policy pack is current and signed into org config",
    input.memoryHints[0] ?? "No prior memory — default enterprise thresholds apply",
  ].slice(0, 3);

  const attackFindings: string[] = [];

  if (!input.actionAllowed) {
    attackFindings.push("Adversarial: action is outside the allowed action catalog");
  }
  if (input.blocked) {
    attackFindings.push("Adversarial: vendor appears on the blocked list");
  }
  if (!input.withinSpendCap) {
    attackFindings.push("Adversarial: agent spend cap would be exceeded");
  }
  if (input.amountCents > input.policyMaxAuto * 4) {
    attackFindings.push(
      "Adversarial: amount is >4× auto-approve threshold — elevated fraud surface",
    );
  }
  if (/ignore|override|jailbreak/i.test(input.action)) {
    attackFindings.push("Adversarial: prompt-injection markers in action string");
  }

  const r0 = {
    solvable: input.actionAllowed && !input.blocked,
    scoped: Boolean(input.vendor || input.action.includes(".")),
    valid: input.withinSpendCap && input.amountCents >= 0,
    worthIt:
      input.amountCents === 0 ||
      input.amountCents <= input.policyMaxAuto * 10,
  };

  const hardFail =
    !r0.solvable ||
    !r0.valid ||
    attackFindings.some((f) => f.includes("blocked") || f.includes("injection"));

  if (hardFail) {
    return {
      state: "REJECTED",
      status: "denied",
      rationale: `CHP denied for ${input.agentName}: R0 or hard adversarial failure.`,
      foundations,
      attackFindings,
      r0,
    };
  }

  // Profile B is for capital-moving actions (notional > 0). Zero-amount
  // research / tool invokes stay domain-auto-lock when R0 is clean.
  if (input.amountCents === 0) {
    if (attackFindings.length > 0) {
      return {
        state: "PROVISIONAL_LOCK",
        status: "pending_human",
        rationale: "Soft adversarial findings present — human confirmation required.",
        foundations,
        attackFindings,
        r0,
      };
    }
    return {
      state: "LOCKED",
      status: "approved",
      rationale: `Auto-locked under policy for ${input.agentName}. Action is in-scope and under threshold.`,
      foundations,
      attackFindings: ["Devil's advocate: no material objections at routine tier"],
      r0,
    };
  }

  const policy = policyFromInput(input);
  const action = proposedFromInput(input);
  const gate = evaluateGate(action, policy);
  const mapped = mapGateState(gate);

  if (mapped.status === "denied") {
    return {
      state: mapped.state,
      status: mapped.status,
      rationale: `CHP blocked for ${input.agentName}: ${gate.reason}`,
      foundations,
      attackFindings: [
        ...attackFindings,
        ...gate.claims.filter((c) => !c.passed).map((c) => `CHP: ${c.rule} — ${c.detail}`),
      ],
      r0,
      gate,
    };
  }

  if (mapped.status === "pending_human" || attackFindings.length > 0) {
    const softOnly = mapped.status === "approved" && attackFindings.length > 0;
    return {
      state: softOnly ? "PROVISIONAL_LOCK" : mapped.state,
      status: "pending_human",
      rationale: softOnly
        ? "Soft adversarial findings present — human confirmation required."
        : gate.reason,
      foundations,
      attackFindings: softOnly
        ? attackFindings
        : [
            ...attackFindings,
            "Devil's advocate: large outbound value requires human lock before execution",
          ],
      r0,
      gate,
    };
  }

  return {
    state: "LOCKED",
    status: "approved",
    rationale: `Auto-locked under policy for ${input.agentName}. ${gate.reason}`,
    foundations,
    attackFindings: ["Devil's advocate: no material objections at routine tier"],
    r0,
    gate,
  };
}

export interface HumanDecisionContext {
  action: string;
  amountCents: number;
  vendor?: string;
  policyMaxAuto: number;
  /** Remaining spend room in cents after prior usage (optional). */
  spendRemainingCents?: number;
  approver?: string;
}

/**
 * Human HITL resolution. Approvals re-run `@cubiczan/chp` `approveHuman`
 * so hard rules cannot be waived; rejects stay domain-local.
 */
export function applyHumanDecision(
  decision: "approve" | "reject",
  notes?: string,
  ctx?: HumanDecisionContext,
): { state: ChpState; status: ClearanceStatus; rationale: string; gate?: GateResult } {
  if (decision === "reject") {
    return {
      state: "REJECTED",
      status: "denied",
      rationale: notes?.trim() || "Human validator rejected clearance.",
    };
  }

  if (ctx && ctx.amountCents > 0) {
    const input: ChpInput = {
      action: ctx.action,
      amountCents: ctx.amountCents,
      vendor: ctx.vendor,
      agentName: "human-review",
      policyMaxAuto: ctx.policyMaxAuto,
      blocked: false,
      actionAllowed: true,
      withinSpendCap: true,
      spendRemainingCents: ctx.spendRemainingCents,
      memoryHints: [],
    };
    const policy = policyFromInput(input);
    const action = proposedFromInput(input);
    const gate = approveHuman(
      action,
      policy,
      ctx.approver?.trim() || "human.operator",
    );
    if (gate.state === "BLOCKED") {
      return {
        state: "REJECTED",
        status: "denied",
        rationale: notes?.trim() || gate.reason,
        gate,
      };
    }
    return {
      state: "LOCKED",
      status: "approved",
      rationale:
        notes?.trim() ||
        gate.reason ||
        "Human validator locked clearance after CHP review.",
      gate,
    };
  }

  return {
    state: "LOCKED",
    status: "approved",
    rationale: notes?.trim() || "Human validator locked clearance after CHP review.",
  };
}
