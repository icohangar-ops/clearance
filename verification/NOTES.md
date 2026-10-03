# Clearance — Lean 4 verification notes

Model: [`Clearance.lean`](./Clearance.lean) (Lean 4.34.1, **core library only**,
no Mathlib). No source files were modified; everything lives in `verification/`.

Verify:

```bash
cd verification
~/.elan/bin/lean Clearance.lean   # exit 0
grep -n "sorry\|admit" Clearance.lean   # no matches
```

Axiom audit (`#print axioms` on every headline theorem): only the standard
Lean core axioms `propext` / `Quot.sound` — no `sorryAx`, no custom axioms.
55 theorems, ~1,460 lines.

## The state machine the code actually has

There is no invoice/paid state for agent spend in this codebase. "Billing" of
agent spend is **metering**: `finalizeApproval` adds `clearance.amountCents` to
the agent's `spendUsedCents` and records a `UsageEvent`
(`src/lib/clearance.ts` ll. 124–144). Stripe bills only the org's subscription
plan (separate flow, §Risks 7–8). The clearance lifecycle is:

```text
POST /api/v1/clearance ─ evaluateClearance ─ runChpGate (src/lib/chp.ts)
        ├─ approved ──► finalizeApproval immediately (metered at creation)
        ├─ denied ────► terminal, never metered (unless a human later… no:
        │               denied-at-creation has no approval item, so it is final)
        └─ pending_human ──► ApprovalItem(open)
                                 └─ POST /api/approvals ─ resolveApproval
                                      ├─ reject ─► clearance denied, item rejected, no metering
                                      └─ approve ─► applyHumanDecision re-runs the CHP gate
                                                    ├─ gate BLOCKED ─► clearance DENIED,
                                                    │    item "approved", STILL METERED (§Finding 1)
                                                    └─ otherwise ─► clearance approved, metered
```

`escalated` (`src/lib/types.ts` ll. 3–7) is in the status type but **no code
path produces it** (proved: `no_escalated_reachable`).

## Model ↔ source mapping (definitions)

| Lean definition | Source |
|---|---|
| `GateState` (`locked`/`hitl`/`blocked`) | `mapGateState`, `src/lib/chp.ts` ll. 80–91 |
| `CStatus` | `ClearanceStatus`, `src/lib/types.ts` ll. 3–7 |
| `AStatus` | `ApprovalItem.status`, `src/lib/types.ts` l. 82 |
| `gateStatus` | `runChpGate` ladder, `src/lib/chp.ts` ll. 139–224 (hard fail ll. 135–149; zero-amount ll. 153–175; external gate ll. 177–193; HITL/soft ll. 195–212) |
| `humanStatus` | `applyHumanDecision`, `src/lib/chp.ts` ll. 237–294 (reject ll. 244–251; gate re-run ll. 253–288; zero-amount skip ll. 290–294) |
| `applyEval` | `evaluateClearance`, `src/lib/clearance.ts` ll. 21–122 (approval item ll. 80–91; auto-finalize ll. 93–95) |
| `applyResolve` | `resolveApproval` post-guard effect, `src/lib/clearance.ts` ll. 164–186 (item marked from decision l. 180; finalize iff decision = approve ll. 184–186) |
| `Step.resolve` guards | `resolveApproval` throws, `src/lib/clearance.ts` ll. 153–160; route `src/app/api/approvals/route.ts` ll. 19–37 |
| `Step.resolve`'s unused `actor` | route passes no actor (ll. 25–29); default `"human.operator"` (`clearance.ts` l. 150) is recorded, never checked |
| `Sys.spent` / `usage` / `base` | `Agent.spendUsedCents` + `UsageEvent`s (`types.ts` ll. 103–111) for one agent; `base` = seeded starting spend |

The external `@cubiczan/chp` package (`package.json` l. 17, `^0.1.1`) is not
vendored in this repo, so its verdicts enter the model abstractly:
`GateIn.gate` for `evaluateGate`, the `gateBlocked` boolean for `approveHuman`.
Everything else — the local ladder, both metering call sites, the resolve
guards — is modeled exactly.

## Theorem → source mapping

### Gate characterization (pure functions of `chp.ts`)

| Theorem | Property | Source |
|---|---|---|
| `gateStatus_hardFail` | hard fail ⇒ denied | chp.ts ll. 135–149 |
| `gateStatus_zero_clean` / `gateStatus_zero_soft` | zero amount: approved iff no findings, pending iff soft findings; external gate never consulted | chp.ts ll. 151–175 |
| `gateStatus_blocked` | gate BLOCKED ⇒ denied | chp.ts ll. 181–193 |
| `gateStatus_hitl` / `gateStatus_soft` | gate HITL or soft findings ⇒ pending | chp.ts ll. 195–212 |
| `gateStatus_locked_clean` | locked + clean + positive ⇒ approved | chp.ts ll. 214–224 |
| `gateStatus_ne_escalated`, `humanStatus_ne_escalated` | neither function can produce `escalated` | types.ts ll. 3–7 vs. chp.ts (no producer) |
| `humanStatus_reject` | reject ⇒ denied | chp.ts ll. 244–251 |
| `humanStatus_gate_veto` | approve + positive amount + gate BLOCKED ⇒ denied | chp.ts ll. 265–279 |
| `humanStatus_zero_no_veto` | zero-amount approve ⇒ approved (re-run skipped) | chp.ts ll. 290–294 |
| `humanStatus_approve_unblocked` | approve + gate not blocked ⇒ approved | chp.ts ll. 280–294 |

### Headline properties (over all reachable states, via invariant `Inv` +
`reach_inv`, preserved by `inv_eval` / `inv_resolve` / `inv_step`)

| Theorem | Property | Source basis |
|---|---|---|
| `metering_requires_approval` | Every usage event names a clearance, for exactly its amount, and that clearance is gate-approved **or** carries a human-approved approval item. Nothing is metered with no approval of either kind. | `finalizeApproval` call sites: clearance.ts ll. 93–95, 184–186 |
| `pending_never_metered` | A `pending_human` clearance has **zero** usage events — nothing is billed before the decision. | clearance.ts ll. 80–95 (item created, no finalize) |
| `denied_without_human_approval_never_metered` | A denied clearance with no human-approved item has zero usage events (gate-denied and human-rejected bill nothing). The human-approval hypothesis is necessary — see Finding 1. | chp.ts ll. 244–251; clearance.ts ll. 184–186 |
| `gate_veto_still_bills` | **Counterexample exhibit:** human approves, re-run gate blocks ⇒ clearance is `denied` and the full amount **is** metered. | clearance.ts ll. 176–186 |
| `no_double_billing` | `countId cid usage ≤ 1` for every clearance — no double-billing. | item resolves once (ll. 153–155); fresh ids at creation |
| `approved_metered_exactly_once` | An approved clearance has exactly one usage event. | ll. 93–95, 184–186 |
| `human_approved_metered_exactly_once` | A clearance whose item is human-approved has exactly one usage event (even when vetoed to `denied`). | ll. 180, 184–186 |
| `billed_never_exceeds_approved` | Metered amount **equals** the approved clearance amount (hence ≤). | `finalizeApproval` copies `clearance.amountCents`, ll. 131–141 |
| `total_spend_accounting` | `spent = seed + Σ usage amounts` — metering is the only way spend grows. | clearance.ts l. 131 |
| `terminal_absorbing`, `approved_absorbing`, `denied_absorbing` | Approved/denied clearances never change status again: evaluation writes only fresh ids; resolve writes only a pending clearance's record. | ll. 60–76 (fresh `newId`), 153–176 (guards) |
| `anyone_can_approve` | For **any** `actor : String` whatsoever, `Step.resolve` fires from an open approval — there is no authorization check to satisfy. | approvals/route.ts ll. 19–37; clearance.ts l. 150 |
| `resolve_outcome_independent_of_actor` | Two different actors resolve the same approval to the *identical* successor state (the actor is causally irrelevant; `applyResolve` has no actor parameter). | same |
| `arbitrary_actor_approval_meters` | End-to-end: an arbitrary actor string approves an open item and (gate not blocking) the clearance is approved and metered the exact amount. | same |
| `no_escalated_reachable` | No reachable clearance has status `escalated`. | types.ts ll. 3–7 vs. whole repo |

## Headline findings

1. **A gate-vetoed human approval still bills.** `resolveApproval` calls
   `finalizeApproval` under `if (decision === "approve")` only
   (`clearance.ts` ll. 184–186) — it never checks `outcome.status`. When
   `applyHumanDecision`'s re-run of `@cubiczan/chp` `approveHuman` returns
   BLOCKED, the clearance becomes `denied` (l. 176), the approval item reads
   `approved` (l. 180), the audit event is even emitted as
   `clearance.locked` (ll. 188–197) — and the agent is metered the full amount
   (ll. 124–144). "Denied" therefore does **not** imply "not billed" in this
   codebase; the naive property is false and the model proves the corrected
   one (`metering_requires_approval`, `gate_veto_still_bills`).
2. **Anyone can approve or reject anything.** `POST /api/approvals`
   (`src/app/api/approvals/route.ts` ll. 19–37) validates only
   `approvalId`/`decision`/`notes` — no authentication, no session, no role.
   `GET` on the same route (ll. 8–11) lists all approvals unauthenticated.
   `resolveApproval`'s `actor` defaults to the literal `"human.operator"`
   (l. 150), is written into `decidedBy`/`resolvedBy`/audit, and is checked
   nowhere. Exhibited formally: `anyone_can_approve`,
   `resolve_outcome_independent_of_actor`.
3. **The approval-time gate re-run quietly drops the local checks.**
   `applyHumanDecision` rebuilds its gate input with `blocked: false`,
   `actionAllowed: true`, `withinSpendCap: true` (`chp.ts` ll. 260–262) — the
   blocked-vendor list, action catalog, and spend cap enforced at evaluation
   are *not* re-checked when a human approves; only the external package's
   capital rules (over a policy rebuilt from `policyMaxAuto` and the agent's
   *current* remaining spend, `clearance.ts` l. 170) can veto.
4. **`escalated` is dead, and the plan quota is decorative.** No producer of
   `escalated` exists (`no_escalated_reachable`). `Org.clearanceQuota`
   (`types.ts` ll. 22–23) is never compared against usage anywhere:
   `evaluateClearance` increments `clearanceUsed` for *every* evaluation —
   including denials (l. 78) — and nothing stops evaluation at the quota.
   (The per-agent `spendCapCents` *is* wired in, but only indirectly: it
   feeds `withinSpendCap` → the gate's hard-fail rung, `chp.ts` ll. 113–115,
   129, 135–137.)
5. **What does hold** (proved): nothing meters before a decision
   (`pending_never_metered`); gate-denied and human-rejected clearances bill
   nothing (`denied_without_human_approval_never_metered`); no clearance is
   ever billed twice (`no_double_billing`, exactly-once theorems); billed
   amounts always equal the approved amount, never more
   (`billed_never_exceeds_approved`); terminal states are absorbing
   (`terminal_absorbing`).

## Discrepancies & risks

- **README vs. code.** README l. 32 says "Seats and clearances are billed
  through Stripe" — in code, Stripe bills only the subscription; per-clearance
  spend is internal metering never sent to Stripe. README ll. 38–47 diagrams
  "Approve | Deny | Escalate to human → Usage meter event": there is no
  escalate transition, and metering does not wait for the final CHP outcome
  (Finding 1). README l. 5's "must pass policy + CHP governance before spend
  executes" is violated by the veto path.
- **Demo fallbacks on the agent API.** `POST /api/v1/clearance`
  (`src/app/api/v1/clearance/route.ts` ll. 22–31): with no valid API key, a
  body-supplied `agentId` selects any active agent, and unless
  `CLEARANCE_ALLOW_DEMO=false` the request silently runs as the *first*
  agent. `GET` (ll. 51–58) returns recent clearances **and the demo API key**
  to anyone.
- **Unauthenticated plan control.** `POST /api/demo` (ll. 9–36) resets the
  whole store or sets any plan — including Enterprise (quota 1,000,000) — with
  no auth. `POST /api/stripe/checkout` (ll. 13–38) has no auth either, and if
  Stripe is unconfigured *or the plan is Enterprise* it activates the plan
  locally with `simulated: true` and no payment; the real-session path
  hardcodes `customer_email: "ops@acme.example"` (l. 45).
- **Webhook trust.** With no Stripe secret configured the webhook accepts any
  POST as "demo" (`src/app/api/stripe/webhook/route.ts` ll. 12–18). Configured
  correctly it verifies the signature (ll. 25–33), but on
  `checkout.session.completed` the plan comes from session metadata and
  **defaults to `"pro"` when the metadata is absent** (l. 37).
- **Float money at the gate boundary.** The adapter converts integer cents to
  float dollars (`dollars`, chp.ts ll. 47–49) and derives all thresholds in
  floats (`policyFromInput`, ll. 51–68): `max_notional = 10 × hitl`,
  `daily_cap = max(remaining, hitl)` — so a fully exhausted agent still gets
  `daily_cap = policyMaxAuto` in the external policy. Metering itself stays in
  exact integer cents; the model works in cents and abstracts the float policy
  arithmetic into the gate verdict. `proposedFromInput` also hardcodes
  `confidence: 0.9` (l. 75) against `min_confidence: 0.55` (l. 59), so that
  claim passes by construction.
- **Policy fallback crosses orgs.** Both `evaluateClearance` (l. 26) and
  `resolveApproval` (ll. 162–163) fall back to `store.policies[0]` when the
  agent's org has no policy — silent evaluation under another org's policy
  pack in a multi-policy store.
- **Approval-item amount is a display copy.** `ApprovalItem.amountCents`
  (`types.ts` l. 81) is written at creation (l. 88) but never read during
  resolution; metering uses `clearance.amountCents`. The model omits the copy;
  if the two diverged, billing would follow the clearance, not the amount the
  approver saw.
- **Model scope/assumptions.** Single agent (spend is per-agent in code; the
  shipped store seeds one org). Ids are modeled as fresh Nat counters —
  the code's `newId` is random-string based, so the model's freshness/
  injectivity facts (`aprInj`, `meterOnce`) assume no id collisions in
  `newId`. Audit/memory side effects (`appendAudit`, `rememberDecision`) and
  store persistence are not modeled — they do not touch clearance/approval/
  usage state. The amount is the post-normalization value
  (`Math.max(0, Math.floor(payload.amountCents ?? 0))`, l. 27), which is
  exactly what the gate sees.
