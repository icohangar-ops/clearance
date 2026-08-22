import { applyHumanDecision, runChpGate } from "./chp";
import { rememberDecision, retrieveMemory } from "./memory";
import {
  appendAudit,
  mutateStore,
  newId,
  type Agent,
  type ClearanceRequest,
  type StoreShape,
} from "./store";

export interface ClearancePayload {
  action: string;
  amountCents?: number;
  currency?: string;
  vendor?: string;
  context?: Record<string, unknown>;
  agentId?: string;
}

export function evaluateClearance(
  agent: Agent,
  payload: ClearancePayload,
): ClearanceRequest {
  return mutateStore((store) => {
    const policy =
      store.policies.find((p) => p.orgId === agent.orgId) ?? store.policies[0];
    const amountCents = Math.max(0, Math.floor(payload.amountCents ?? 0));
    const action = payload.action?.trim() || "tool.invoke";
    const vendor = payload.vendor?.trim();

    const memoryHits = retrieveMemory(
      store.memory,
      agent.memoryNamespace,
      `${action} ${vendor ?? ""} ${amountCents}`,
    );

    const blocked = Boolean(
      vendor &&
        policy.blockedVendors.some((b) => b.toLowerCase() === vendor.toLowerCase()),
    );
    const actionAllowed = policy.allowedActions.includes(action);
    const withinSpendCap = agent.spendUsedCents + amountCents <= agent.spendCapCents;
    const spendRemainingCents = Math.max(0, agent.spendCapCents - agent.spendUsedCents);

    const chp = runChpGate({
      action,
      amountCents,
      vendor,
      agentName: agent.name,
      policyMaxAuto: policy.maxAutoApproveCents,
      blocked,
      actionAllowed,
      withinSpendCap,
      spendRemainingCents,
      memoryHints: memoryHits.map((m) => m.text),
    });

    const clearance: ClearanceRequest = {
      id: newId("clr"),
      orgId: agent.orgId,
      agentId: agent.id,
      action,
      amountCents,
      currency: payload.currency || "usd",
      vendor,
      context: payload.context ?? {},
      status: chp.status,
      chpState: chp.state,
      rationale: chp.rationale,
      foundations: chp.foundations,
      attackFindings: chp.attackFindings,
      memoryHits: memoryHits.map((m) => m.text),
      createdAt: new Date().toISOString(),
    };

    store.clearances.unshift(clearance);
    store.org.clearanceUsed += 1;

    if (chp.status === "pending_human") {
      store.approvals.unshift({
        id: newId("apr"),
        clearanceId: clearance.id,
        orgId: agent.orgId,
        agentId: agent.id,
        summary: `${agent.name}: ${action}${vendor ? ` → ${vendor}` : ""} ($${(amountCents / 100).toFixed(2)})`,
        amountCents,
        status: "open",
        createdAt: new Date().toISOString(),
      });
    }

    if (chp.status === "approved") {
      finalizeApproval(store, agent, clearance);
    }

    appendAudit(store, {
      orgId: agent.orgId,
      event: "clearance.evaluated",
      actor: agent.id,
      inputs: {
        action,
        amountCents,
        vendor,
        status: clearance.status,
        chpState: clearance.chpState,
      },
      sources: ["policy", "chp", "memory"],
      confidence: chp.status === "approved" ? "high" : "medium",
      rationale: clearance.rationale,
    });

    rememberDecision(
      store.memory,
      agent.memoryNamespace,
      `Clearance ${clearance.status} for ${action} $${(amountCents / 100).toFixed(2)} (${clearance.chpState})`,
      ["clearance", clearance.status, action],
    );

    return clearance;
  });
}

function finalizeApproval(
  store: StoreShape,
  agent: Agent,
  clearance: ClearanceRequest,
) {
  const target = store.agents.find((a) => a.id === agent.id);
  if (target) {
    target.spendUsedCents += clearance.amountCents;
  }
  store.usage.unshift({
    id: newId("use"),
    orgId: agent.orgId,
    agentId: agent.id,
    clearanceId: clearance.id,
    units: 1,
    amountCents: clearance.amountCents,
    ts: new Date().toISOString(),
  });
  clearance.decidedAt = new Date().toISOString();
  clearance.decidedBy = "chp-auto";
}

export function resolveApproval(
  approvalId: string,
  decision: "approve" | "reject",
  notes?: string,
  actor = "human.operator",
) {
  return mutateStore((store) => {
    const approval = store.approvals.find((a) => a.id === approvalId);
    if (!approval) throw new Error("Approval not found");
    if (approval.status !== "open") throw new Error("Approval already resolved");

    const clearance = store.clearances.find((c) => c.id === approval.clearanceId);
    if (!clearance) throw new Error("Clearance not found");

    const agent = store.agents.find((a) => a.id === clearance.agentId);
    if (!agent) throw new Error("Agent not found");

    const policy =
      store.policies.find((p) => p.orgId === agent.orgId) ?? store.policies[0];
    const outcome = applyHumanDecision(decision, notes, {
      action: clearance.action,
      amountCents: clearance.amountCents,
      vendor: clearance.vendor,
      policyMaxAuto: policy.maxAutoApproveCents,
      spendRemainingCents: Math.max(0, agent.spendCapCents - agent.spendUsedCents),
      approver: actor,
    });
    clearance.status = outcome.status;
    clearance.chpState = outcome.state;
    clearance.rationale = outcome.rationale;
    clearance.decidedAt = new Date().toISOString();
    clearance.decidedBy = actor;

    approval.status = decision === "approve" ? "approved" : "rejected";
    approval.notes = notes;
    approval.resolvedAt = clearance.decidedAt;
    approval.resolvedBy = actor;

    if (decision === "approve") {
      finalizeApproval(store, agent, clearance);
    }

    appendAudit(store, {
      orgId: clearance.orgId,
      event: decision === "approve" ? "clearance.locked" : "clearance.rejected",
      actor,
      inputs: { approvalId, clearanceId: clearance.id, decision },
      sources: ["human", "chp"],
      confidence: "high",
      rationale: outcome.rationale,
    });

    rememberDecision(
      store.memory,
      agent.memoryNamespace,
      `Human ${decision} on ${clearance.action} $${(clearance.amountCents / 100).toFixed(2)}`,
      ["human", decision],
    );

    return { approval, clearance };
  });
}

export function dashboardStats(store: StoreShape) {
  const openApprovals = store.approvals.filter((a) => a.status === "open").length;
  const approved = store.clearances.filter((c) => c.status === "approved").length;
  const denied = store.clearances.filter((c) => c.status === "denied").length;
  const pending = store.clearances.filter((c) => c.status === "pending_human").length;
  const spendCents = store.agents.reduce((acc, a) => acc + a.spendUsedCents, 0);
  return {
    agents: store.agents.length,
    openApprovals,
    approved,
    denied,
    pending,
    spendCents,
    clearanceUsed: store.org.clearanceUsed,
    clearanceQuota: store.org.clearanceQuota,
    plan: store.org.plan,
  };
}
