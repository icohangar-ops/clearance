/-!
# Clearance — Lean 4 model of the approval / spend-metering flow

Model of `~/workspace/cubiczan-repos/clearance` (TypeScript), following the
CODE, not the README.  Core library only; compiles with plain `lean`.

## What the code actually does

* `evaluateClearance` (`src/lib/clearance.ts` ll. 21–122) creates a clearance
  whose status is the CHP gate's verdict (`src/lib/chp.ts` `runChpGate`,
  ll. 97–232): `approved` | `denied` | `pending_human`.  The fourth status in
  the type, `escalated` (`src/lib/types.ts` ll. 3–7), is never produced anywhere.
* "Billing" of agent spend is `finalizeApproval` (`clearance.ts` ll. 124–144):
  it adds `clearance.amountCents` to the agent's `spendUsedCents` and unshifts
  a `UsageEvent { clearanceId, amountCents }`.  It has exactly two call sites:
  at creation when the gate auto-approved (ll. 93–95), and in `resolveApproval`
  whenever the human decision is "approve" (ll. 184–186) — crucially with NO
  check of `outcome.status`, so a human approval that the re-run gate vetoes
  (clearance left `denied`) is still metered in full.  The model follows the
  code here, not the intuitive reading; see `gate_veto_still_bills`.
* A pending clearance gets an `ApprovalItem` (`open`).  `resolveApproval`
  (ll. 146–208) throws unless the item is still `open`, so each item resolves
  at most once.  The HTTP route (`src/app/api/approvals/route.ts` ll. 19–37)
  performs NO authentication and never passes an actor: `resolveApproval`'s
  `actor` parameter defaults to the string `"human.operator"` and is only
  recorded, never checked.  The model therefore has an `actor` argument that
  is bound but never used — anyone can approve.
* Human "approve" re-runs the external `@cubiczan/chp` `approveHuman`
  (`chp.ts` ll. 253–288): if it returns BLOCKED the clearance is *denied*
  despite the human approval.  That package is an npm dependency (not in this
  repo), so its verdict enters the model as the abstract boolean
  `gateBlocked`, exactly like the local gate verdict enters as `GateIn.gate`.

Money is integer cents throughout the model, matching `amountCents` in the
code.  (The CHP adapter detours through float dollars — `chp.ts` ll. 47–68 —
see NOTES.md; the model works in exact cents.)

The store is modelled for a single agent/org (the shipped store is
single-org anyway): `spent` is that agent's `spendUsedCents`, plus a constant
`base` for the seeded starting balance.
-/

namespace Clearance

/-- Verdict of the external `@cubiczan/chp` Profile B gate (`evaluateGate`),
    as mapped by `mapGateState` (`chp.ts` ll. 80–91): LOCKED / HITL_REQUIRED /
    BLOCKED. -/
inductive GateState where
  | locked
  | hitl
  | blocked
deriving DecidableEq, Repr

/-- `ClearanceStatus` (`types.ts` ll. 3–7).  `escalated` exists in the type
    but no code path produces it — see `Inv.noEsc` below. -/
inductive CStatus where
  | approved
  | denied
  | pending
  | escalated
deriving DecidableEq, Repr

/-- `ApprovalItem.status` (`types.ts` l. 82). -/
inductive AStatus where
  | open
  | approved
  | rejected
deriving DecidableEq, Repr

/-- Inputs to the local gate ladder that the model keeps abstract:
    `hardFail` — the domain hard-fail disjunction (`chp.ts` ll. 124–137:
    action not allowed, blocked vendor, spend cap exceeded / R0 invalid,
    prompt-injection marker); `soft` — non-hard adversarial findings are
    present (`attackFindings.length > 0` without a hard trigger);
    `gate` — the external Profile B verdict for capital actions. -/
structure GateIn where
  amount : Int
  hardFail : Bool
  soft : Bool
  gate : GateState
deriving DecidableEq, Repr

/-- The status ladder of `runChpGate` (`chp.ts` ll. 139–224), in code order:
    hard fail → denied; zero amount (gate never consulted) → pending iff soft
    findings, else approved; gate BLOCKED → denied; gate HITL or soft
    findings → pending; otherwise approved. -/
def gateStatus (i : GateIn) : CStatus :=
  if i.hardFail then .denied
  else if i.amount = 0 then (if i.soft then .pending else .approved)
  else if i.gate = .blocked then .denied
  else if i.gate = .hitl || i.soft then .pending
  else .approved

/-- The outcome of `applyHumanDecision` (`chp.ts` ll. 237–294): reject →
    denied; approve of a positive amount that the re-run gate BLOCKs →
    denied; any other approve → approved.  Zero-amount approvals skip the
    gate entirely (ll. 290–294), hence the `amount > 0` guard. -/
def humanStatus (approve gateBlocked : Bool) (amount : Int) : CStatus :=
  if !approve then .denied
  else if amount > 0 && gateBlocked then .denied
  else .approved

/-! ## Gate characterisation lemmas -/

theorem gateStatus_hardFail {i : GateIn} (h : i.hardFail = true) :
    gateStatus i = .denied := by simp [gateStatus, h]

theorem gateStatus_zero_clean {i : GateIn} (h : i.hardFail = false)
    (ha : i.amount = 0) (hs : i.soft = false) :
    gateStatus i = .approved := by simp [gateStatus, h, ha, hs]

theorem gateStatus_zero_soft {i : GateIn} (h : i.hardFail = false)
    (ha : i.amount = 0) (hs : i.soft = true) :
    gateStatus i = .pending := by simp [gateStatus, h, ha, hs]

theorem gateStatus_blocked {i : GateIn} (h : i.hardFail = false)
    (ha : i.amount ≠ 0) (hg : i.gate = .blocked) :
    gateStatus i = .denied := by simp [gateStatus, h, ha, hg]

theorem gateStatus_hitl {i : GateIn} (h : i.hardFail = false)
    (ha : i.amount ≠ 0) (hg : i.gate = .hitl) :
    gateStatus i = .pending := by simp [gateStatus, h, ha, hg]

theorem gateStatus_soft {i : GateIn} (h : i.hardFail = false)
    (ha : i.amount ≠ 0) (hg : i.gate = .locked) (hs : i.soft = true) :
    gateStatus i = .pending := by simp [gateStatus, h, ha, hg, hs]

theorem gateStatus_locked_clean {i : GateIn} (h : i.hardFail = false)
    (ha : i.amount ≠ 0) (hg : i.gate = .locked) (hs : i.soft = false) :
    gateStatus i = .approved := by simp [gateStatus, h, ha, hg, hs]

/-- The gate never emits `escalated`. -/
theorem gateStatus_ne_escalated (i : GateIn) : gateStatus i ≠ .escalated := by
  unfold gateStatus
  split <;> (try split) <;> (try split) <;> (try split) <;> simp

/-- A human decision never emits `escalated` either. -/
theorem humanStatus_ne_escalated (a b : Bool) (m : Int) :
    humanStatus a b m ≠ .escalated := by
  unfold humanStatus
  split <;> (try split) <;> simp

/-- Human outcomes are only ever `approved` or `denied`. -/
theorem humanStatus_cases (a b : Bool) (m : Int) :
    humanStatus a b m = .approved ∨ humanStatus a b m = .denied := by
  unfold humanStatus
  split <;> (try split) <;> simp

/-- Reject always denies. -/
theorem humanStatus_reject (b : Bool) (m : Int) :
    humanStatus false b m = .denied := by simp [humanStatus]

/-- The re-run gate can veto a human approval of a positive amount:
    `applyHumanDecision` returns REJECTED when `approveHuman` says BLOCKED
    (`chp.ts` ll. 265–279). -/
theorem humanStatus_gate_veto (m : Int) (hm : m > 0) :
    humanStatus true true m = .denied := by simp [humanStatus, hm]

/-- …but a zero-amount approval skips the gate re-run entirely
    (`chp.ts` ll. 290–294), so the veto does not apply. -/
theorem humanStatus_zero_no_veto (m : Int) (hm : ¬ m > 0) :
    humanStatus true true m = .approved := by simp [humanStatus, hm]

/-! ## The store as a state machine -/

/-- A clearance record: the amount (integer cents, fixed at creation —
    `clearance.ts` l. 27 floors the payload once and nothing ever mutates
    `amountCents`) and its status. -/
structure Clr where
  amount : Int
  status : CStatus
deriving DecidableEq, Repr

/-- An approval item: which clearance it decides, and its status.  Its
    `amountCents` copy in the code is written once from the same variable as
    the clearance's (ll. 80–91) and never read for metering — metering uses
    `clearance.amountCents` — so the model omits it. -/
structure Apr where
  clrId : Nat
  status : AStatus
deriving DecidableEq, Repr

/-- Store state (single agent).  `usage` is the list of usage events
    `(clearanceId, amountCents)`; `spent` is the agent's `spendUsedCents`;
    `base` is its seeded starting value, which no step changes. -/
structure Sys where
  nextClr : Nat
  nextApr : Nat
  clrs : Nat → Option Clr
  aprs : Nat → Option Apr
  usage : List (Nat × Int)
  base : Int
  spent : Int

/-- `evaluateClearance` (`clearance.ts` ll. 21–122): a fresh clearance with
    id `nextClr` and the gate's status.  Pending ⇒ a fresh `open` approval
    item pointing at it (ll. 80–91).  Approved ⇒ `finalizeApproval` runs
    immediately (ll. 93–95): meter `(id, amount)` and add `amount` to `spent`.
    Denied ⇒ nothing else happens.  (Written as one flat record so every
    projection below is a definitional equation.) -/
def applyEval (s : Sys) (i : GateIn) : Sys where
  nextClr := s.nextClr + 1
  nextApr := if gateStatus i = .pending then s.nextApr + 1 else s.nextApr
  clrs := fun j => if j = s.nextClr then some ⟨i.amount, gateStatus i⟩ else s.clrs j
  aprs := fun j => if gateStatus i = .pending ∧ j = s.nextApr
    then some ⟨s.nextClr, .open⟩ else s.aprs j
  usage := if gateStatus i = .approved then (s.nextClr, i.amount) :: s.usage else s.usage
  base := s.base
  spent := if gateStatus i = .approved then s.spent + i.amount else s.spent

/-- The effect of `resolveApproval` (`clearance.ts` ll. 146–208) once its
    guards have passed (approval exists and is `open`, clearance exists and
    is `pending`): the approval item is marked from the *decision* (ll.
    176–180 — `approved` even when the gate veto turns the clearance into a
    denial), the clearance takes `humanStatus`, and `finalizeApproval` runs
    iff the decision was "approve" (ll. 184–186) — regardless of that veto —
    metering exactly the clearance's own `amountCents`. -/
def applyResolve (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (approve gateBlocked : Bool) : Sys where
  nextClr := s.nextClr
  nextApr := s.nextApr
  clrs := fun j => if j = ap.clrId
    then some ⟨cl.amount, humanStatus approve gateBlocked cl.amount⟩ else s.clrs j
  aprs := fun j => if j = aid
    then some ⟨ap.clrId, if approve then .approved else .rejected⟩ else s.aprs j
  usage := if approve then (ap.clrId, cl.amount) :: s.usage else s.usage
  base := s.base
  spent := if approve then s.spent + cl.amount else s.spent

@[simp] theorem applyEval_nextClr (s : Sys) (i : GateIn) :
    (applyEval s i).nextClr = s.nextClr + 1 := rfl

@[simp] theorem applyEval_nextApr_pending (s : Sys) (i : GateIn)
    (h : gateStatus i = .pending) :
    (applyEval s i).nextApr = s.nextApr + 1 := by simp [applyEval, h]

@[simp] theorem applyEval_nextApr_not_pending (s : Sys) (i : GateIn)
    (h : gateStatus i ≠ .pending) :
    (applyEval s i).nextApr = s.nextApr := by simp [applyEval, h]

@[simp] theorem applyEval_clrs (s : Sys) (i : GateIn) (j : Nat) :
    (applyEval s i).clrs j =
      if j = s.nextClr then some ⟨i.amount, gateStatus i⟩ else s.clrs j := rfl

@[simp] theorem applyEval_aprs (s : Sys) (i : GateIn) (j : Nat) :
    (applyEval s i).aprs j =
      if gateStatus i = .pending ∧ j = s.nextApr
        then some ⟨s.nextClr, .open⟩ else s.aprs j := rfl

@[simp] theorem applyEval_usage (s : Sys) (i : GateIn) :
    (applyEval s i).usage =
      if gateStatus i = .approved then (s.nextClr, i.amount) :: s.usage
        else s.usage := rfl

@[simp] theorem applyEval_base (s : Sys) (i : GateIn) :
    (applyEval s i).base = s.base := rfl

@[simp] theorem applyEval_spent (s : Sys) (i : GateIn) :
    (applyEval s i).spent =
      if gateStatus i = .approved then s.spent + i.amount else s.spent := rfl

@[simp] theorem applyResolve_nextClr (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) : (applyResolve s aid ap cl a b).nextClr = s.nextClr := rfl

@[simp] theorem applyResolve_nextApr (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) : (applyResolve s aid ap cl a b).nextApr = s.nextApr := rfl

@[simp] theorem applyResolve_clrs (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) (j : Nat) :
    (applyResolve s aid ap cl a b).clrs j =
      if j = ap.clrId
        then some ⟨cl.amount, humanStatus a b cl.amount⟩ else s.clrs j := rfl

@[simp] theorem applyResolve_aprs (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) (j : Nat) :
    (applyResolve s aid ap cl a b).aprs j =
      if j = aid
        then some ⟨ap.clrId, if a then .approved else .rejected⟩
        else s.aprs j := rfl

@[simp] theorem applyResolve_usage (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) :
    (applyResolve s aid ap cl a b).usage =
      if a then (ap.clrId, cl.amount) :: s.usage else s.usage := rfl

theorem applyResolve_usage_approve (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (b : Bool) :
    (applyResolve s aid ap cl true b).usage =
      (ap.clrId, cl.amount) :: s.usage := rfl

theorem applyResolve_usage_reject (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (b : Bool) :
    (applyResolve s aid ap cl false b).usage = s.usage := rfl

@[simp] theorem applyResolve_base (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) : (applyResolve s aid ap cl a b).base = s.base := rfl

@[simp] theorem applyResolve_spent (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) :
    (applyResolve s aid ap cl a b).spent =
      if a then s.spent + cl.amount else s.spent := rfl

theorem applyResolve_spent_approve (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (b : Bool) :
    (applyResolve s aid ap cl true b).spent = s.spent + cl.amount := rfl

theorem applyResolve_spent_reject (s : Sys) (aid : Nat) (ap : Apr) (cl : Clr)
    (b : Bool) :
    (applyResolve s aid ap cl false b).spent = s.spent := rfl

/-- One store transition.  `resolve` carries an `actor` — the HTTP route
    supplies none (`approvals/route.ts` ll. 25–29 calls `resolveApproval`
    with no actor, and the library default is the literal string
    `"human.operator"`), the code never authenticates or authorises it, and
    accordingly `actor` occurs in no guard and no effect. -/
inductive Step : Sys → Sys → Prop where
  | evaluate (s : Sys) (i : GateIn) : Step s (applyEval s i)
  | resolve (s : Sys) (aid : Nat) (approve gateBlocked : Bool) (actor : String)
      (ap : Apr) (cl : Clr)
      (ha : s.aprs aid = some ap) (ho : ap.status = .open)
      (hc : s.clrs ap.clrId = some cl) (hp : cl.status = .pending) :
      Step s (applyResolve s aid ap cl approve gateBlocked)

/-- Reflexive-transitive closure of `Step`. -/
inductive Reach : Sys → Sys → Prop where
  | refl (s : Sys) : Reach s s
  | step {s t u : Sys} : Step s t → Reach t u → Reach s u

/-- The seeded store: no clearances, no approvals, no usage events;
    `spent` starts at the seed balance `base`. -/
def init (base : Int) : Sys where
  nextClr := 0
  nextApr := 0
  clrs := fun _ => none
  aprs := fun _ => none
  usage := []
  base := base
  spent := base

/-! ## Counting usage events per clearance -/

/-- How many usage events in the list carry clearance id `cid`.  (A bespoke
    counter, rather than `List.filter`, to keep the arithmetic elementary.) -/
def countId (cid : Nat) : List (Nat × Int) → Nat
  | [] => 0
  | e :: l => (if e.1 = cid then 1 else 0) + countId cid l

@[simp] theorem countId_nil (cid : Nat) : countId cid [] = 0 := rfl

@[simp] theorem countId_cons (cid : Nat) (e : Nat × Int) (l : List (Nat × Int)) :
    countId cid (e :: l) = (if e.1 = cid then 1 else 0) + countId cid l := rfl

theorem countId_eq_zero_of_forall_ne {cid : Nat} :
    ∀ {l : List (Nat × Int)}, (∀ e ∈ l, e.1 ≠ cid) → countId cid l = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
      intro h
      have he : e.1 ≠ cid := h e List.mem_cons_self
      have ih' : countId cid l = 0 :=
        ih (fun x hx => h x (List.mem_cons_of_mem e hx))
      simp [countId_cons, he, ih']

theorem countId_pos_of_mem {cid : Nat} {e : Nat × Int} :
    ∀ {l : List (Nat × Int)}, e ∈ l → e.1 = cid → 0 < countId cid l := by
  intro l
  induction l with
  | nil => intro he; simp at he
  | cons x l ih =>
      intro he hf
      rw [countId_cons]
      cases List.mem_cons.mp he with
      | inl hxx => subst hxx; rw [if_pos hf]; omega
      | inr hxl =>
          have ih' : 0 < countId cid l := ih hxl hf
          by_cases hx : x.1 = cid
          · rw [if_pos hx]; omega
          · rw [if_neg hx]; omega

/-! ## The invariant -/

/-- Everything the two transitions jointly maintain.  Reading guide:

    * `freshClr`/`freshApr` — ids are issued in order, never reused
      (records are only ever written at `nextClr`/`nextApr` or at an
      existing id).
    * `aprClr`/`aprInj` — every approval item points at an existing
      clearance, and no two items point at the same clearance (each pending
      clearance gets exactly one item, at its creation).
    * `openPending`/`resolvedLink` — an item is `open` iff its clearance is
      still `pending`; once resolved, the clearance is decided, a rejection
      means the clearance is `denied`, and an "approved" item means the
      clearance is `approved` *or* `denied` (the gate-veto case: the item
      records the human's decision, `clearance.ts` ll. 176–180).
    * `approvedMetered`/`usageIds` — metering is exactly coextensive with
      approval: every approved clearance has its usage event (for exactly
      its amount), and every usage event belongs to an approved clearance
      (for exactly its amount).  Nothing is billed before — or without —
      approval.
    * `meterOnce` — no clearance is billed twice.
    * `noEsc` — the `escalated` status is unreachable.
    * `spentEq` — the agent's metered spend is the seed balance plus the
      sum of usage events. -/
structure Inv (s : Sys) : Prop where
  freshClr : ∀ cid cl, s.clrs cid = some cl → cid < s.nextClr
  freshApr : ∀ aid ap, s.aprs aid = some ap → aid < s.nextApr
  aprClr : ∀ aid ap, s.aprs aid = some ap → ∃ cl, s.clrs ap.clrId = some cl
  aprInj : ∀ aid₁ aid₂ ap₁ ap₂, s.aprs aid₁ = some ap₁ → s.aprs aid₂ = some ap₂ →
      ap₁.clrId = ap₂.clrId → aid₁ = aid₂
  openPending : ∀ aid ap, s.aprs aid = some ap → ap.status = .open →
      ∃ cl, s.clrs ap.clrId = some cl ∧ cl.status = .pending
  resolvedLink : ∀ aid ap, s.aprs aid = some ap → ap.status ≠ .open →
      ∃ cl, s.clrs ap.clrId = some cl ∧ cl.status ≠ .pending ∧
        (ap.status = .rejected → cl.status = .denied) ∧
        (ap.status = .approved → cl.status = .approved ∨ cl.status = .denied)
  approvedMetered : ∀ cid cl, s.clrs cid = some cl → cl.status = .approved →
      (cid, cl.amount) ∈ s.usage
  humanApprovedMetered : ∀ aid ap cl, s.aprs aid = some ap →
      ap.status = .approved → s.clrs ap.clrId = some cl →
      (ap.clrId, cl.amount) ∈ s.usage
  usageIds : ∀ e ∈ s.usage, ∃ cl, s.clrs e.1 = some cl ∧ e.2 = cl.amount ∧
      (cl.status = .approved ∨
        ∃ aid ap, s.aprs aid = some ap ∧ ap.clrId = e.1 ∧
          ap.status = .approved)
  meterOnce : ∀ cid, countId cid s.usage ≤ 1
  noEsc : ∀ cid cl, s.clrs cid = some cl → cl.status ≠ .escalated
  spentEq : s.spent = s.base + (s.usage.map Prod.snd).sum

theorem Inv.clr_fresh {s : Sys} (h : Inv s) : s.clrs s.nextClr = none := by
  cases hcl : s.clrs s.nextClr with
  | none => rfl
  | some cl => exact absurd (h.freshClr _ _ hcl) (Nat.lt_irrefl _)

theorem Inv.apr_fresh {s : Sys} (h : Inv s) : s.aprs s.nextApr = none := by
  cases hap : s.aprs s.nextApr with
  | none => rfl
  | some ap => exact absurd (h.freshApr _ _ hap) (Nat.lt_irrefl _)

/-- A still-pending clearance has no usage event: by `usageIds` a metered
    clearance is approved or carries a human-approved approval item, and
    both contradict pending (the second via `resolvedLink`). -/
theorem Inv.pending_unmetered {s : Sys} (h : Inv s) {cid : Nat} {cl : Clr}
    (hc : s.clrs cid = some cl) (hp : cl.status = .pending) :
    ∀ e ∈ s.usage, e.1 ≠ cid := by
  intro e he hfe
  obtain ⟨cl₂, hc₂, -, hdisj⟩ := h.usageIds e he
  rw [hfe] at hc₂
  rw [hc] at hc₂
  have hceq : cl = cl₂ := Option.some.inj hc₂
  rcases hdisj with happ | ⟨aid₂, ap₂, hap₂, hclr₂, happ₂⟩
  · have hst : cl.status = .approved := by rw [hceq]; exact happ
    rw [hp] at hst
    exact CStatus.noConfusion hst
  · have hne : ap₂.status ≠ .open := by
      rw [happ₂]; exact fun hh => AStatus.noConfusion hh
    obtain ⟨cl₃, hc₃, hnp, -, -⟩ := h.resolvedLink aid₂ ap₂ hap₂ hne
    rw [hclr₂, hfe] at hc₃
    rw [hc] at hc₃
    have hceq₃ : cl = cl₃ := Option.some.inj hc₃
    exact hnp (hceq₃ ▸ hp)

theorem Inv.countId_pending {s : Sys} (h : Inv s) {cid : Nat} {cl : Clr}
    (hc : s.clrs cid = some cl) (hp : cl.status = .pending) :
    countId cid s.usage = 0 :=
  countId_eq_zero_of_forall_ne (h.pending_unmetered hc hp)

theorem Inv.usage_fst_lt {s : Sys} (h : Inv s) {e : Nat × Int} (he : e ∈ s.usage) :
    e.1 < s.nextClr := by
  obtain ⟨cl, hc, -, -⟩ := h.usageIds e he
  exact h.freshClr _ _ hc

theorem inv_init (base : Int) : Inv (init base) where
  freshClr := by intro cid cl hcl; simp [init] at hcl
  freshApr := by intro aid ap hap; simp [init] at hap
  aprClr := by intro aid ap hap; simp [init] at hap
  aprInj := by intro a b x y hx; simp [init] at hx
  openPending := by intro aid ap hap; simp [init] at hap
  resolvedLink := by intro aid ap hap; simp [init] at hap
  approvedMetered := by intro cid cl hcl; simp [init] at hcl
  humanApprovedMetered := by intro aid ap cl hap; simp [init] at hap
  usageIds := by intro e he; simp [init] at he
  meterOnce := by intro cid; simp [init]
  noEsc := by intro cid cl hcl; simp [init] at hcl
  spentEq := by simp [init]

/-! ## Invariant preservation: `evaluate` -/

/-- In the pending branch, the approval map gains exactly one fresh `open`
    item, at `nextApr`, pointing at the fresh clearance. -/
theorem applyEval_aprs_pending (s : Sys) (i : GateIn) (hg : gateStatus i = .pending)
    (j : Nat) :
    (applyEval s i).aprs j =
      if j = s.nextApr then some ⟨s.nextClr, .open⟩ else s.aprs j := by
  simp only [applyEval_aprs]
  by_cases hj : j = s.nextApr
  · rw [if_pos ⟨hg, hj⟩, if_pos hj]
  · rw [if_neg (fun hc => hj hc.2), if_neg hj]

/-- In every non-pending branch, the approval map is untouched. -/
theorem applyEval_aprs_not_pending (s : Sys) (i : GateIn)
    (hg : gateStatus i ≠ .pending) (j : Nat) :
    (applyEval s i).aprs j = s.aprs j := by
  simp only [applyEval_aprs]
  exact if_neg (fun hc => hg hc.1)

theorem inv_eval_pending {s : Sys} (h : Inv s) (i : GateIn)
    (hg : gateStatus i = .pending) : Inv (applyEval s i) := by
  have hnotapp : gateStatus i ≠ .approved := by
    intro hh; rw [hg] at hh; exact CStatus.noConfusion hh
  have husage : (applyEval s i).usage = s.usage := by
    rw [applyEval_usage, if_neg hnotapp]
  have hspent : (applyEval s i).spent = s.spent := by
    rw [applyEval_spent, if_neg hnotapp]
  have hnapr : (applyEval s i).nextApr = s.nextApr + 1 :=
    applyEval_nextApr_pending s i hg
  -- Any old approval's clearance id differs from the fresh clearance id.
  have hne_of_apr : ∀ (aid : Nat) (ap : Apr), s.aprs aid = some ap →
      ap.clrId ≠ s.nextClr := by
    intro aid ap hap hcontra
    obtain ⟨cl, hcl⟩ := h.aprClr aid ap hap
    rw [hcontra] at hcl
    rw [h.clr_fresh] at hcl
    cases hcl
  refine Inv.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro cid cl hcl
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid; rw [applyEval_nextClr]; exact Nat.lt_succ_self _
    · rw [if_neg hcid] at hcl
      have hlt := h.freshClr cid cl hcl
      rw [applyEval_nextClr]; omega
  · intro aid ap hap
    rw [applyEval_aprs_pending s i hg] at hap
    by_cases haid : aid = s.nextApr
    · subst haid; rw [hnapr]; exact Nat.lt_succ_self _
    · rw [if_neg haid] at hap
      have hlt := h.freshApr aid ap hap
      rw [hnapr]; omega
  · intro aid ap hap
    rw [applyEval_aprs_pending s i hg] at hap
    by_cases haid : aid = s.nextApr
    · subst haid
      rw [if_pos rfl] at hap
      have hid : ap.clrId = s.nextClr := by
        have hrec := Option.some.inj hap
        rw [← hrec]
      refine ⟨⟨i.amount, gateStatus i⟩, ?_⟩
      rw [hid, applyEval_clrs, if_pos rfl]
    · rw [if_neg haid] at hap
      obtain ⟨cl, hcl⟩ := h.aprClr aid ap hap
      refine ⟨cl, ?_⟩
      simp only [applyEval_clrs]
      rw [if_neg (hne_of_apr aid ap hap)]
      exact hcl
  · intro a₁ a₂ x₁ x₂ h₁ h₂ hclr
    rw [applyEval_aprs_pending s i hg] at h₁ h₂
    by_cases ha₁ : a₁ = s.nextApr
    · subst ha₁
      rw [if_pos rfl] at h₁
      have hx₁ : x₁.clrId = s.nextClr := by
        have hrec := Option.some.inj h₁
        rw [← hrec]
      by_cases ha₂ : a₂ = s.nextApr
      · subst ha₂; rfl
      · rw [if_neg ha₂] at h₂
        exfalso
        exact hne_of_apr a₂ x₂ h₂ (by rw [← hclr, hx₁])
    · rw [if_neg ha₁] at h₁
      by_cases ha₂ : a₂ = s.nextApr
      · subst ha₂
        rw [if_pos rfl] at h₂
        have hx₂ : x₂.clrId = s.nextClr := by
          have hrec := Option.some.inj h₂
          rw [← hrec]
        exfalso
        exact hne_of_apr a₁ x₁ h₁ (by rw [hclr, hx₂])
      · rw [if_neg ha₂] at h₂
        exact h.aprInj a₁ a₂ x₁ x₂ h₁ h₂ hclr
  · intro aid ap hap hop
    rw [applyEval_aprs_pending s i hg] at hap
    by_cases haid : aid = s.nextApr
    · subst haid
      rw [if_pos rfl] at hap
      have hid : ap.clrId = s.nextClr := by
        have hrec := Option.some.inj hap
        rw [← hrec]
      refine ⟨⟨i.amount, gateStatus i⟩, ?_, hg⟩
      rw [hid, applyEval_clrs, if_pos rfl]
    · rw [if_neg haid] at hap
      obtain ⟨cl, hcl, hpend⟩ := h.openPending aid ap hap hop
      refine ⟨cl, ?_, hpend⟩
      simp only [applyEval_clrs]
      rw [if_neg (hne_of_apr aid ap hap)]
      exact hcl
  · intro aid ap hap hne
    rw [applyEval_aprs_pending s i hg] at hap
    by_cases haid : aid = s.nextApr
    · subst haid
      rw [if_pos rfl] at hap
      have hst : ap.status = .open := by
        have hrec := Option.some.inj hap
        rw [← hrec]
      exfalso; exact hne hst
    · rw [if_neg haid] at hap
      obtain ⟨cl, hcl, hnp, hrej, happ⟩ := h.resolvedLink aid ap hap hne
      refine ⟨cl, ?_, hnp, hrej, happ⟩
      simp only [applyEval_clrs]
      rw [if_neg (hne_of_apr aid ap hap)]
      exact hcl
  · intro cid cl hcl happ
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid
      rw [if_pos rfl] at hcl
      have hst : cl.status = gateStatus i := by
        have hrec := Option.some.inj hcl
        rw [← hrec]
      exfalso
      rw [hst, hg] at happ
      exact CStatus.noConfusion happ
    · rw [if_neg hcid] at hcl
      have hm := h.approvedMetered cid cl hcl happ
      rw [husage]; exact hm
  · intro aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
    have hne₂ : aid₂ ≠ s.nextApr := by
      intro hh
      rw [applyEval_aprs_pending s i hg aid₂, if_pos hh] at hap₂
      have hrec := Option.some.inj hap₂
      have hst : ap₂.status = .open := by rw [← hrec]
      rw [hst] at happ₂
      exact AStatus.noConfusion happ₂
    rw [applyEval_aprs_pending s i hg aid₂, if_neg hne₂] at hap₂
    simp only [applyEval_clrs] at hcl₂
    rw [if_neg (hne_of_apr aid₂ ap₂ hap₂)] at hcl₂
    have hm := h.humanApprovedMetered aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
    rw [husage]; exact hm
  · intro e he
    rw [husage] at he
    obtain ⟨cl, hcl, hamt, hdisj⟩ := h.usageIds e he
    refine ⟨cl, ?_, hamt, ?_⟩
    · simp only [applyEval_clrs]
      rw [if_neg]
      · exact hcl
      · have hlt := h.usage_fst_lt he
        omega
    · rcases hdisj with happ | ⟨aid₂, ap₂, hap₂, hclr₂, happ₂⟩
      · exact Or.inl happ
      · refine Or.inr ⟨aid₂, ap₂, ?_, hclr₂, happ₂⟩
        have hne₂ : aid₂ ≠ s.nextApr := by
          intro hh
          rw [hh] at hap₂
          rw [h.apr_fresh] at hap₂
          cases hap₂
        rw [applyEval_aprs_pending s i hg aid₂, if_neg hne₂]
        exact hap₂
  · intro cid
    rw [husage]
    exact h.meterOnce cid
  · intro cid cl hcl
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid
      rw [if_pos rfl] at hcl
      have hst : cl.status = gateStatus i := by
        have hrec := Option.some.inj hcl
        rw [← hrec]
      rw [hst]
      exact gateStatus_ne_escalated i
    · rw [if_neg hcid] at hcl
      exact h.noEsc cid cl hcl
  · rw [hspent, husage]
    exact h.spentEq

theorem inv_eval_approved {s : Sys} (h : Inv s) (i : GateIn)
    (hg : gateStatus i = .approved) : Inv (applyEval s i) := by
  have hnp : gateStatus i ≠ .pending := by
    intro hh; rw [hg] at hh; exact CStatus.noConfusion hh
  have husage : (applyEval s i).usage = (s.nextClr, i.amount) :: s.usage := by
    rw [applyEval_usage, if_pos hg]
  have hspent : (applyEval s i).spent = s.spent + i.amount := by
    rw [applyEval_spent, if_pos hg]
  have hnapr : (applyEval s i).nextApr = s.nextApr :=
    applyEval_nextApr_not_pending s i hnp
  have hne_of_apr : ∀ (aid : Nat) (ap : Apr), s.aprs aid = some ap →
      ap.clrId ≠ s.nextClr := by
    intro aid ap hap hcontra
    obtain ⟨cl, hcl⟩ := h.aprClr aid ap hap
    rw [hcontra] at hcl
    rw [h.clr_fresh] at hcl
    cases hcl
  refine Inv.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro cid cl hcl
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid; rw [applyEval_nextClr]; exact Nat.lt_succ_self _
    · rw [if_neg hcid] at hcl
      have hlt := h.freshClr cid cl hcl
      rw [applyEval_nextClr]; omega
  · intro aid ap hap
    rw [applyEval_aprs_not_pending s i hnp] at hap
    rw [hnapr]
    exact h.freshApr aid ap hap
  · intro aid ap hap
    rw [applyEval_aprs_not_pending s i hnp] at hap
    obtain ⟨cl, hcl⟩ := h.aprClr aid ap hap
    refine ⟨cl, ?_⟩
    simp only [applyEval_clrs]
    rw [if_neg (hne_of_apr aid ap hap)]
    exact hcl
  · intro a₁ a₂ x₁ x₂ h₁ h₂ hclr
    rw [applyEval_aprs_not_pending s i hnp] at h₁ h₂
    exact h.aprInj a₁ a₂ x₁ x₂ h₁ h₂ hclr
  · intro aid ap hap hop
    rw [applyEval_aprs_not_pending s i hnp] at hap
    obtain ⟨cl, hcl, hpend⟩ := h.openPending aid ap hap hop
    refine ⟨cl, ?_, hpend⟩
    simp only [applyEval_clrs]
    rw [if_neg (hne_of_apr aid ap hap)]
    exact hcl
  · intro aid ap hap hne
    rw [applyEval_aprs_not_pending s i hnp] at hap
    obtain ⟨cl, hcl, hnp', hrej, happ⟩ := h.resolvedLink aid ap hap hne
    refine ⟨cl, ?_, hnp', hrej, happ⟩
    simp only [applyEval_clrs]
    rw [if_neg (hne_of_apr aid ap hap)]
    exact hcl
  · intro cid cl hcl happ
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid
      rw [if_pos rfl] at hcl
      have hamt : cl.amount = i.amount := by
        have hrec := Option.some.inj hcl
        rw [← hrec]
      rw [hamt, husage]
      exact List.mem_cons_self
    · rw [if_neg hcid] at hcl
      have hm := h.approvedMetered cid cl hcl happ
      rw [husage]
      exact List.mem_cons_of_mem _ hm
  · intro aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
    rw [applyEval_aprs_not_pending s i hnp aid₂] at hap₂
    simp only [applyEval_clrs] at hcl₂
    rw [if_neg (hne_of_apr aid₂ ap₂ hap₂)] at hcl₂
    have hm := h.humanApprovedMetered aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
    rw [husage]
    exact List.mem_cons_of_mem _ hm
  · intro e he
    rw [husage] at he
    cases List.mem_cons.mp he with
    | inl hhead =>
        subst hhead
        exact ⟨⟨i.amount, gateStatus i⟩,
          by rw [applyEval_clrs, if_pos rfl], rfl, Or.inl hg⟩
    | inr htail =>
        obtain ⟨cl, hcl, hamt, hdisj⟩ := h.usageIds e htail
        refine ⟨cl, ?_, hamt, ?_⟩
        · simp only [applyEval_clrs]
          rw [if_neg]
          · exact hcl
          · have hlt := h.usage_fst_lt htail
            omega
        · rcases hdisj with happ | ⟨aid₂, ap₂, hap₂, hclr₂, happ₂⟩
          · exact Or.inl happ
          · refine Or.inr ⟨aid₂, ap₂, ?_, hclr₂, happ₂⟩
            rw [applyEval_aprs_not_pending s i hnp aid₂]
            exact hap₂
  · intro cid
    by_cases hcid : cid = s.nextClr
    · subst hcid
      rw [husage, countId_cons, if_pos rfl]
      have hz : countId s.nextClr s.usage = 0 :=
        countId_eq_zero_of_forall_ne (fun e he => by
          have hlt := h.usage_fst_lt he; omega)
      rw [hz]
      omega
    · rw [husage, countId_cons,
        if_neg (show (s.nextClr, i.amount).1 ≠ cid from fun hh => hcid hh.symm)]
      have hm := h.meterOnce cid
      omega
  · intro cid cl hcl
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid
      rw [if_pos rfl] at hcl
      have hst : cl.status = gateStatus i := by
        have hrec := Option.some.inj hcl
        rw [← hrec]
      rw [hst, hg]
      exact fun hh => CStatus.noConfusion hh
    · rw [if_neg hcid] at hcl
      exact h.noEsc cid cl hcl
  · rw [hspent, husage]
    show s.spent + i.amount =
      s.base + (((s.nextClr, i.amount) :: s.usage).map Prod.snd).sum
    simp only [List.map_cons, List.sum_cons]
    rw [h.spentEq]; omega

theorem inv_eval_other {s : Sys} (h : Inv s) (i : GateIn)
    (hg1 : gateStatus i ≠ .pending) (hg2 : gateStatus i ≠ .approved) :
    Inv (applyEval s i) := by
  have husage : (applyEval s i).usage = s.usage := by
    rw [applyEval_usage, if_neg hg2]
  have hspent : (applyEval s i).spent = s.spent := by
    rw [applyEval_spent, if_neg hg2]
  have hnapr : (applyEval s i).nextApr = s.nextApr :=
    applyEval_nextApr_not_pending s i hg1
  have hne_of_apr : ∀ (aid : Nat) (ap : Apr), s.aprs aid = some ap →
      ap.clrId ≠ s.nextClr := by
    intro aid ap hap hcontra
    obtain ⟨cl, hcl⟩ := h.aprClr aid ap hap
    rw [hcontra] at hcl
    rw [h.clr_fresh] at hcl
    cases hcl
  refine Inv.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro cid cl hcl
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid; rw [applyEval_nextClr]; exact Nat.lt_succ_self _
    · rw [if_neg hcid] at hcl
      have hlt := h.freshClr cid cl hcl
      rw [applyEval_nextClr]; omega
  · intro aid ap hap
    rw [applyEval_aprs_not_pending s i hg1] at hap
    rw [hnapr]
    exact h.freshApr aid ap hap
  · intro aid ap hap
    rw [applyEval_aprs_not_pending s i hg1] at hap
    obtain ⟨cl, hcl⟩ := h.aprClr aid ap hap
    refine ⟨cl, ?_⟩
    simp only [applyEval_clrs]
    rw [if_neg (hne_of_apr aid ap hap)]
    exact hcl
  · intro a₁ a₂ x₁ x₂ h₁ h₂ hclr
    rw [applyEval_aprs_not_pending s i hg1] at h₁ h₂
    exact h.aprInj a₁ a₂ x₁ x₂ h₁ h₂ hclr
  · intro aid ap hap hop
    rw [applyEval_aprs_not_pending s i hg1] at hap
    obtain ⟨cl, hcl, hpend⟩ := h.openPending aid ap hap hop
    refine ⟨cl, ?_, hpend⟩
    simp only [applyEval_clrs]
    rw [if_neg (hne_of_apr aid ap hap)]
    exact hcl
  · intro aid ap hap hne
    rw [applyEval_aprs_not_pending s i hg1] at hap
    obtain ⟨cl, hcl, hnp', hrej, happ⟩ := h.resolvedLink aid ap hap hne
    refine ⟨cl, ?_, hnp', hrej, happ⟩
    simp only [applyEval_clrs]
    rw [if_neg (hne_of_apr aid ap hap)]
    exact hcl
  · intro cid cl hcl happ
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid
      rw [if_pos rfl] at hcl
      have hst : cl.status = gateStatus i := by
        have hrec := Option.some.inj hcl
        rw [← hrec]
      exfalso
      rw [hst] at happ
      exact hg2 happ
    · rw [if_neg hcid] at hcl
      have hm := h.approvedMetered cid cl hcl happ
      rw [husage]; exact hm
  · intro aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
    rw [applyEval_aprs_not_pending s i hg1 aid₂] at hap₂
    simp only [applyEval_clrs] at hcl₂
    rw [if_neg (hne_of_apr aid₂ ap₂ hap₂)] at hcl₂
    have hm := h.humanApprovedMetered aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
    rw [husage]; exact hm
  · intro e he
    rw [husage] at he
    obtain ⟨cl, hcl, hamt, hdisj⟩ := h.usageIds e he
    refine ⟨cl, ?_, hamt, ?_⟩
    · simp only [applyEval_clrs]
      rw [if_neg]
      · exact hcl
      · have hlt := h.usage_fst_lt he
        omega
    · rcases hdisj with happ | ⟨aid₂, ap₂, hap₂, hclr₂, happ₂⟩
      · exact Or.inl happ
      · refine Or.inr ⟨aid₂, ap₂, ?_, hclr₂, happ₂⟩
        rw [applyEval_aprs_not_pending s i hg1 aid₂]
        exact hap₂
  · intro cid
    rw [husage]
    exact h.meterOnce cid
  · intro cid cl hcl
    simp only [applyEval_clrs] at hcl
    by_cases hcid : cid = s.nextClr
    · subst hcid
      rw [if_pos rfl] at hcl
      have hst : cl.status = gateStatus i := by
        have hrec := Option.some.inj hcl
        rw [← hrec]
      rw [hst]
      exact gateStatus_ne_escalated i
    · rw [if_neg hcid] at hcl
      exact h.noEsc cid cl hcl
  · rw [hspent, husage]
    exact h.spentEq

theorem inv_eval {s : Sys} (h : Inv s) (i : GateIn) : Inv (applyEval s i) := by
  by_cases hp : gateStatus i = .pending
  · exact inv_eval_pending h i hp
  · by_cases ha : gateStatus i = .approved
    · exact inv_eval_approved h i ha
    · exact inv_eval_other h i hp ha

/-! ## Invariant preservation: `resolve` -/

theorem inv_resolve {s : Sys} (h : Inv s) (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) (ha : s.aprs aid = some ap) (ho : ap.status = .open)
    (hc : s.clrs ap.clrId = some cl) (hp : cl.status = .pending) :
    Inv (applyResolve s aid ap cl a b) := by
  have hcidlt : ap.clrId < s.nextClr := h.freshClr _ _ hc
  have hcount0 : countId ap.clrId s.usage = 0 := h.countId_pending hc hp
  have hinj : ∀ aid₂ ap₂, s.aprs aid₂ = some ap₂ → ap₂.clrId = ap.clrId →
      aid₂ = aid :=
    fun aid₂ ap₂ h1 h2 => h.aprInj aid₂ aid ap₂ ap h1 ha h2
  have hne_of_usage : ∀ e ∈ s.usage, e.1 ≠ ap.clrId :=
    h.pending_unmetered hc hp
  refine Inv.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro cid cl₂ hcl
    simp only [applyResolve_clrs] at hcl
    rw [applyResolve_nextClr]
    by_cases hcid : cid = ap.clrId
    · subst hcid; exact hcidlt
    · rw [if_neg hcid] at hcl; exact h.freshClr cid cl₂ hcl
  · intro aid₂ ap₂ hap
    simp only [applyResolve_aprs] at hap
    rw [applyResolve_nextApr]
    by_cases haid : aid₂ = aid
    · subst haid; exact h.freshApr aid₂ ap ha
    · rw [if_neg haid] at hap; exact h.freshApr aid₂ ap₂ hap
  · intro aid₂ ap₂ hap
    simp only [applyResolve_aprs] at hap
    by_cases haid : aid₂ = aid
    · subst haid
      rw [if_pos rfl] at hap
      have hclr : ap₂.clrId = ap.clrId := by
        have hrec := Option.some.inj hap
        rw [← hrec]
      refine ⟨⟨cl.amount, humanStatus a b cl.amount⟩, ?_⟩
      rw [hclr, applyResolve_clrs, if_pos rfl]
    · rw [if_neg haid] at hap
      obtain ⟨cl₂, hcl₂⟩ := h.aprClr aid₂ ap₂ hap
      refine ⟨cl₂, ?_⟩
      simp only [applyResolve_clrs]
      rw [if_neg]
      · exact hcl₂
      · intro hcontra
        exact haid (hinj aid₂ ap₂ hap hcontra)
  · intro a₁ a₂ x₁ x₂ h₁ h₂ hclr
    simp only [applyResolve_aprs] at h₁ h₂
    by_cases ha₁ : a₁ = aid
    · subst ha₁
      rw [if_pos rfl] at h₁
      have hx₁ : x₁.clrId = ap.clrId := by
        have hrec := Option.some.inj h₁
        rw [← hrec]
      by_cases ha₂ : a₂ = a₁
      · subst ha₂; rfl
      · rw [if_neg ha₂] at h₂
        exfalso
        exact ha₂ (hinj a₂ x₂ h₂ (by rw [← hclr, hx₁]))
    · rw [if_neg ha₁] at h₁
      by_cases ha₂ : a₂ = aid
      · subst ha₂
        rw [if_pos rfl] at h₂
        have hx₂ : x₂.clrId = ap.clrId := by
          have hrec := Option.some.inj h₂
          rw [← hrec]
        exfalso
        exact ha₁ (hinj a₁ x₁ h₁ (by rw [hclr, hx₂]))
      · rw [if_neg ha₂] at h₂
        exact h.aprInj a₁ a₂ x₁ x₂ h₁ h₂ hclr
  · intro aid₂ ap₂ hap hop
    simp only [applyResolve_aprs] at hap
    by_cases haid : aid₂ = aid
    · subst haid
      rw [if_pos rfl] at hap
      have hrec := Option.some.inj hap
      rw [← hrec] at hop
      cases a <;> exact AStatus.noConfusion hop
    · rw [if_neg haid] at hap
      obtain ⟨cl₂, hcl₂, hpend⟩ := h.openPending aid₂ ap₂ hap hop
      refine ⟨cl₂, ?_, hpend⟩
      simp only [applyResolve_clrs]
      rw [if_neg]
      · exact hcl₂
      · intro hcontra
        exact haid (hinj aid₂ ap₂ hap hcontra)
  · intro aid₂ ap₂ hap hne
    simp only [applyResolve_aprs] at hap
    by_cases haid : aid₂ = aid
    · subst haid
      rw [if_pos rfl] at hap
      have hrec := Option.some.inj hap
      have hclr : ap₂.clrId = ap.clrId := by rw [← hrec]
      have hst : ap₂.status =
          (if a then AStatus.approved else AStatus.rejected) := by rw [← hrec]
      refine ⟨⟨cl.amount, humanStatus a b cl.amount⟩, ?_, ?_, ?_, ?_⟩
      · rw [hclr, applyResolve_clrs, if_pos rfl]
      · have hc2 := humanStatus_cases a b cl.amount
        rcases hc2 with hh | hh
        · rw [hh]; exact fun hcon => CStatus.noConfusion hcon
        · rw [hh]; exact fun hcon => CStatus.noConfusion hcon
      · intro hrej
        cases a with
        | false => exact humanStatus_reject b cl.amount
        | true =>
            exfalso
            rw [hst] at hrej
            simp at hrej
      · intro happ
        cases a with
        | true => exact humanStatus_cases true b cl.amount
        | false =>
            exfalso
            rw [hst] at happ
            simp at happ
    · rw [if_neg haid] at hap
      obtain ⟨cl₂, hcl₂, hnp, hrej, happ⟩ := h.resolvedLink aid₂ ap₂ hap hne
      refine ⟨cl₂, ?_, hnp, hrej, happ⟩
      simp only [applyResolve_clrs]
      rw [if_neg]
      · exact hcl₂
      · intro hcontra
        exact haid (hinj aid₂ ap₂ hap hcontra)
  · intro cid cl₂ hcl happ
    simp only [applyResolve_clrs] at hcl
    cases a with
    | true =>
        by_cases hcid : cid = ap.clrId
        · subst hcid
          rw [if_pos rfl] at hcl
          have hamt : cl₂.amount = cl.amount := by
            have hrec := Option.some.inj hcl
            rw [← hrec]
          rw [hamt, applyResolve_usage_approve]
          exact List.mem_cons_self
        · rw [if_neg hcid] at hcl
          have hm := h.approvedMetered cid cl₂ hcl happ
          rw [applyResolve_usage_approve]
          exact List.mem_cons_of_mem _ hm
    | false =>
        by_cases hcid : cid = ap.clrId
        · subst hcid
          rw [if_pos rfl] at hcl
          have hst2 : cl₂.status = humanStatus false b cl.amount := by
            have hrec := Option.some.inj hcl
            rw [← hrec]
          exfalso
          rw [humanStatus_reject] at hst2
          rw [hst2] at happ
          exact CStatus.noConfusion happ
        · rw [if_neg hcid] at hcl
          have hm := h.approvedMetered cid cl₂ hcl happ
          rw [applyResolve_usage_reject]
          exact hm
  · intro aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
    simp only [applyResolve_aprs] at hap₂
    simp only [applyResolve_clrs] at hcl₂
    by_cases haid : aid₂ = aid
    · subst haid
      rw [if_pos rfl] at hap₂
      have hrec := Option.some.inj hap₂
      have hclr₂ : ap₂.clrId = ap.clrId := by rw [← hrec]
      have hst₂ : ap₂.status =
          (if a then AStatus.approved else AStatus.rejected) := by rw [← hrec]
      cases a with
      | false =>
          rw [hst₂] at happ₂
          simp at happ₂
      | true =>
          rw [if_pos hclr₂] at hcl₂
          have hamt : cl₂.amount = cl.amount := by
            have hrec₂ := Option.some.inj hcl₂
            rw [← hrec₂]
          rw [hclr₂, hamt, applyResolve_usage_approve]
          exact List.mem_cons_self
    · rw [if_neg haid] at hap₂
      have hne₂ : ap₂.clrId ≠ ap.clrId := by
        intro hcontra
        exact haid (hinj aid₂ ap₂ hap₂ hcontra)
      rw [if_neg hne₂] at hcl₂
      have hm := h.humanApprovedMetered aid₂ ap₂ cl₂ hap₂ happ₂ hcl₂
      cases a with
      | true =>
          rw [applyResolve_usage_approve]
          exact List.mem_cons_of_mem _ hm
      | false =>
          rw [applyResolve_usage_reject]
          exact hm
  · intro e he
    cases a with
    | true =>
        rw [applyResolve_usage_approve] at he
        cases List.mem_cons.mp he with
        | inl hhead =>
            subst hhead
            exact ⟨⟨cl.amount, humanStatus true b cl.amount⟩,
              by rw [applyResolve_clrs, if_pos rfl], rfl,
              Or.inr ⟨aid,
                ⟨ap.clrId, if true then AStatus.approved else AStatus.rejected⟩,
                by rw [applyResolve_aprs, if_pos rfl], rfl, rfl⟩⟩
        | inr htail =>
            obtain ⟨cl₂, hcl₂, hamt, hdisj⟩ := h.usageIds e htail
            refine ⟨cl₂, ?_, hamt, ?_⟩
            · simp only [applyResolve_clrs]
              rw [if_neg (hne_of_usage e htail)]
              exact hcl₂
            · rcases hdisj with happ | ⟨aid₂, ap₂, hap₂, hclr₂, happ₂⟩
              · exact Or.inl happ
              · refine Or.inr ⟨aid₂, ap₂, ?_, hclr₂, happ₂⟩
                have hne₂ : aid₂ ≠ aid := by
                  intro hh
                  subst hh
                  rw [ha] at hap₂
                  have hrec := Option.some.inj hap₂
                  have h1 : ap₂.clrId = ap.clrId := by rw [← hrec]
                  rw [hclr₂] at h1
                  exact hne_of_usage e htail h1
                simp only [applyResolve_aprs]
                rw [if_neg hne₂]
                exact hap₂
    | false =>
        rw [applyResolve_usage_reject] at he
        obtain ⟨cl₂, hcl₂, hamt, hdisj⟩ := h.usageIds e he
        refine ⟨cl₂, ?_, hamt, ?_⟩
        · simp only [applyResolve_clrs]
          rw [if_neg (hne_of_usage e he)]
          exact hcl₂
        · rcases hdisj with happ | ⟨aid₂, ap₂, hap₂, hclr₂, happ₂⟩
          · exact Or.inl happ
          · refine Or.inr ⟨aid₂, ap₂, ?_, hclr₂, happ₂⟩
            have hne₂ : aid₂ ≠ aid := by
              intro hh
              subst hh
              rw [ha] at hap₂
              have hrec := Option.some.inj hap₂
              have h1 : ap₂.clrId = ap.clrId := by rw [← hrec]
              rw [hclr₂] at h1
              exact hne_of_usage e he h1
            simp only [applyResolve_aprs]
            rw [if_neg hne₂]
            exact hap₂
  · intro cid
    cases a with
    | true =>
        by_cases hcid : cid = ap.clrId
        · subst hcid
          rw [applyResolve_usage_approve, countId_cons, if_pos rfl, hcount0]
          omega
        · rw [applyResolve_usage_approve, countId_cons,
            if_neg (show (ap.clrId, cl.amount).1 ≠ cid from fun hh => hcid hh.symm)]
          have hm := h.meterOnce cid
          omega
    | false =>
        rw [applyResolve_usage_reject]
        exact h.meterOnce cid
  · intro cid cl₂ hcl
    simp only [applyResolve_clrs] at hcl
    by_cases hcid : cid = ap.clrId
    · subst hcid
      rw [if_pos rfl] at hcl
      have hst : cl₂.status = humanStatus a b cl.amount := by
        have hrec := Option.some.inj hcl
        rw [← hrec]
      rw [hst]
      exact humanStatus_ne_escalated a b cl.amount
    · rw [if_neg hcid] at hcl
      exact h.noEsc cid cl₂ hcl
  · cases a with
    | true =>
        rw [applyResolve_spent_approve, applyResolve_usage_approve]
        show s.spent + cl.amount =
          s.base + (((ap.clrId, cl.amount) :: s.usage).map Prod.snd).sum
        simp only [List.map_cons, List.sum_cons]
        rw [h.spentEq]; omega
    | false =>
        rw [applyResolve_spent_reject, applyResolve_usage_reject]
        exact h.spentEq

theorem inv_step {s t : Sys} (h : Inv s) (hst : Step s t) : Inv t := by
  cases hst with
  | evaluate i => exact inv_eval h i
  | resolve aid a b actor ap cl ha ho hc hp =>
      exact inv_resolve h aid ap cl a b ha ho hc hp

theorem reach_inv_from {s₀ s : Sys} (h0 : Inv s₀) (h : Reach s₀ s) : Inv s := by
  revert h0
  induction h with
  | refl => intro h0; exact h0
  | step hst _ ih => intro h0; exact ih (inv_step h0 hst)

theorem reach_inv {b : Int} {s : Sys} (h : Reach (init b) s) : Inv s :=
  reach_inv_from (inv_init b) h

/-! ## Headline theorems -/

/-- Metering requires an approval — but note *whose*: every usage event
    in a reachable state belongs to a clearance for the exact clearance
    amount, and that clearance is either gate-approved (`approved`) or
    carries a human-approved approval item.  The second disjunct is not
    redundant: when a human approves but the re-run CHP gate vetoes
    (clearance.ts ll. 184–186 calls `finalizeApproval` on
    `decision === "approve"` without checking `outcome.status`), the
    clearance is left `denied` yet still metered — see
    `gate_veto_still_bills`.  Nothing is ever metered with no approval
    of either kind behind it. -/
theorem metering_requires_approval {b : Int} {s : Sys}
    (hr : Reach (init b) s) {e : Nat × Int} (he : e ∈ s.usage) :
    ∃ cl : Clr, s.clrs e.1 = some cl ∧ e.2 = cl.amount ∧
      (cl.status = .approved ∨
        ∃ aid ap, s.aprs aid = some ap ∧ ap.clrId = e.1 ∧
          ap.status = .approved) :=
  (reach_inv hr).usageIds e he

/-- A pending clearance has no usage event: nothing is billed before the
    human decision lands. -/
theorem pending_never_metered {b : Int} {s : Sys} (hr : Reach (init b) s)
    {cid : Nat} {cl : Clr} (hcl : s.clrs cid = some cl)
    (hp : cl.status = .pending) : countId cid s.usage = 0 :=
  (reach_inv hr).countId_pending hcl hp

/-- A denied clearance with no human approval behind it is never
    metered: gate-denied and human-rejected clearances bill nothing.
    (The hypothesis cannot be dropped — a human-approved, gate-vetoed
    clearance is `denied` and *is* metered; see `gate_veto_still_bills`.) -/
theorem denied_without_human_approval_never_metered {b : Int} {s : Sys}
    (hr : Reach (init b) s) {cid : Nat} {cl : Clr}
    (hcl : s.clrs cid = some cl) (hd : cl.status = .denied)
    (hno : ∀ aid ap, s.aprs aid = some ap → ap.clrId = cid →
      ap.status ≠ .approved) :
    countId cid s.usage = 0 := by
  have hinv := reach_inv hr
  apply countId_eq_zero_of_forall_ne
  intro e he hcontra
  obtain ⟨cl₂, hcl₂, -, hdisj⟩ := hinv.usageIds e he
  rw [hcontra] at hcl₂
  rw [hcl] at hcl₂
  have hrec : cl = cl₂ := Option.some.inj hcl₂
  rcases hdisj with happ | ⟨aid₂, ap₂, hap₂, hclr₂, happ₂⟩
  · have hst : cl.status = .approved := by rw [hrec]; exact happ
    rw [hd] at hst
    exact CStatus.noConfusion hst
  · exact hno aid₂ ap₂ hap₂ (hclr₂.trans hcontra) happ₂

/-- COUNTEREXAMPLE to "denied ⇒ not billed", exhibited as a theorem: a
    human approves a positive-amount clearance (`approve = true`), the
    re-run external gate blocks it (`gateBlocked = true`), and the model
    — following clearance.ts ll. 176–186 exactly — leaves the clearance
    `denied` while still metering the full amount, because
    `finalizeApproval` is guarded only by the human decision. -/
theorem gate_veto_still_bills {s : Sys} (aid : Nat) (ap : Apr) (cl : Clr)
    (ha : s.aprs aid = some ap) (ho : ap.status = .open)
    (hc : s.clrs ap.clrId = some cl) (hp : cl.status = .pending)
    (hpos : 0 < cl.amount) :
    Step s (applyResolve s aid ap cl true true) ∧
    (applyResolve s aid ap cl true true).clrs ap.clrId =
      some ⟨cl.amount, .denied⟩ ∧
    (ap.clrId, cl.amount) ∈ (applyResolve s aid ap cl true true).usage := by
  refine ⟨Step.resolve s aid true true "anyone" ap cl ha ho hc hp, ?_, ?_⟩
  · rw [applyResolve_clrs, if_pos rfl, humanStatus_gate_veto cl.amount hpos]
  · rw [applyResolve_usage_approve]
    exact List.mem_cons_self

/-- No double billing: each clearance is metered at most once, in every
    reachable state.  (The approval item leaves `open` exactly once —
    `resolveApproval` throws on a non-open item — and auto-approved
    clearances are created already-metered under a fresh id.) -/
theorem no_double_billing {b : Int} {s : Sys} (hr : Reach (init b) s)
    (cid : Nat) : countId cid s.usage ≤ 1 :=
  (reach_inv hr).meterOnce cid

/-- An approved clearance in a reachable state is metered exactly once:
    metering is neither skipped nor duplicated for approved amounts. -/
theorem approved_metered_exactly_once {b : Int} {s : Sys}
    (hr : Reach (init b) s) {cid : Nat} {cl : Clr}
    (hcl : s.clrs cid = some cl) (happ : cl.status = .approved) :
    countId cid s.usage = 1 := by
  have hinv := reach_inv hr
  have hle := hinv.meterOnce cid
  have hmem := hinv.approvedMetered cid cl hcl happ
  have hpos : 0 < countId cid s.usage := countId_pos_of_mem hmem rfl
  omega

/-- A human-approved clearance (its approval item is `approved`) is
    metered exactly once — including the gate-veto case, where the
    clearance itself ends `denied`. -/
theorem human_approved_metered_exactly_once {b : Int} {s : Sys}
    (hr : Reach (init b) s) {aid : Nat} {ap : Apr} {cl : Clr}
    (hap : s.aprs aid = some ap) (happ : ap.status = .approved)
    (hcl : s.clrs ap.clrId = some cl) : countId ap.clrId s.usage = 1 := by
  have hinv := reach_inv hr
  have hle := hinv.meterOnce ap.clrId
  have hmem := hinv.humanApprovedMetered aid ap cl hap happ hcl
  have hpos : 0 < countId ap.clrId s.usage := countId_pos_of_mem hmem rfl
  omega

/-- Amounts billed never exceed the (gate- or human-) approved amount:
    in fact the metered amount always *equals* the clearance amount that
    was approved, so in particular `e.2 ≤ cl.amount`. -/
theorem billed_never_exceeds_approved {b : Int} {s : Sys}
    (hr : Reach (init b) s) {e : Nat × Int} (he : e ∈ s.usage) :
    ∃ cl : Clr, s.clrs e.1 = some cl ∧ e.2 ≤ cl.amount ∧
      (cl.status = .approved ∨
        ∃ aid ap, s.aprs aid = some ap ∧ ap.clrId = e.1 ∧
          ap.status = .approved) := by
  obtain ⟨cl, h1, h2, h3⟩ := metering_requires_approval hr he
  exact ⟨cl, h1, by omega, h3⟩

theorem reach_base_from {s₀ s : Sys} {b : Int} (h0 : s₀.base = b)
    (h : Reach s₀ s) : s.base = b := by
  revert h0
  induction h with
  | refl => intro h0; exact h0
  | step hst _ ih =>
      intro h0
      cases hst with
      | evaluate i =>
          apply ih
          show (applyEval _ i).base = b
          rw [applyEval_base]
          exact h0
      | resolve aid a bb actor ap cl ha ho hc hp =>
          apply ih
          show (applyResolve _ aid ap cl a bb).base = b
          rw [applyResolve_base]
          exact h0

/-- Total spend accounting: cumulative metered spend equals the seed
    balance plus the sum of all usage-event amounts — metering is the only
    way `spendUsedCents` grows, and it grows by exactly the billed events. -/
theorem total_spend_accounting {b : Int} {s : Sys} (hr : Reach (init b) s) :
    s.spent = b + (s.usage.map Prod.snd).sum := by
  have h1 := (reach_inv hr).spentEq
  have h2 : s.base = b := reach_base_from rfl hr
  rwa [h2] at h1

/-- One step never changes a clearance that is already in a terminal
    (`approved`/`denied`) state: evaluation writes only a fresh id, and
    `resolve` writes only the clearance of an `open` approval, which the
    invariant ties to a `pending` clearance. -/
theorem step_clrs_of_terminal {s t : Sys} (hinv : Inv s) (hst : Step s t)
    {cid : Nat} {cl : Clr} (hcl : s.clrs cid = some cl)
    (hterm : cl.status = .approved ∨ cl.status = .denied) :
    t.clrs cid = some cl := by
  cases hst with
  | evaluate i =>
      have hne : cid ≠ s.nextClr := by
        have hlt := hinv.freshClr cid cl hcl
        omega
      show (applyEval s i).clrs cid = some cl
      rw [applyEval_clrs, if_neg hne]
      exact hcl
  | resolve aid a b actor ap cl' ha ho hc hp =>
      have hne : cid ≠ ap.clrId := by
        intro hcontra
        rw [← hcontra] at hc
        have hrec : cl = cl' := Option.some.inj (hcl.symm.trans hc)
        have hst' : cl.status = cl'.status := by rw [hrec]
        rw [hp] at hst'
        rcases hterm with hh | hh <;> rw [hh] at hst' <;>
          exact CStatus.noConfusion hst'
      show (applyResolve s aid ap cl' a b).clrs cid = some cl
      rw [applyResolve_clrs, if_neg hne]
      exact hcl

/-- Terminal states are absorbing over any number of steps. -/
theorem reach_preserves_terminal_from {s t : Sys} (hinv : Inv s)
    (hrt : Reach s t) {cid : Nat} {cl : Clr} (hcl : s.clrs cid = some cl)
    (hterm : cl.status = .approved ∨ cl.status = .denied) :
    t.clrs cid = some cl := by
  revert hinv hcl
  induction hrt with
  | refl => intro _ hcl; exact hcl
  | step hst _ ih =>
      intro hinv hcl
      exact ih (inv_step hinv hst)
        (step_clrs_of_terminal hinv hst hcl hterm)

theorem terminal_absorbing {b : Int} {s t : Sys} (hr : Reach (init b) s)
    (hrt : Reach s t) {cid : Nat} {cl : Clr} (hcl : s.clrs cid = some cl)
    (hterm : cl.status = .approved ∨ cl.status = .denied) :
    t.clrs cid = some cl :=
  reach_preserves_terminal_from (reach_inv hr) hrt hcl hterm

/-- Corollary: an approved clearance stays approved forever. -/
theorem approved_absorbing {b : Int} {s t : Sys} (hr : Reach (init b) s)
    (hrt : Reach s t) {cid : Nat} {cl : Clr} (hcl : s.clrs cid = some cl)
    (happ : cl.status = .approved) : t.clrs cid = some cl :=
  terminal_absorbing hr hrt hcl (Or.inl happ)

/-- Corollary: a denied clearance stays denied forever. -/
theorem denied_absorbing {b : Int} {s t : Sys} (hr : Reach (init b) s)
    (hrt : Reach s t) {cid : Nat} {cl : Clr} (hcl : s.clrs cid = some cl)
    (hd : cl.status = .denied) : t.clrs cid = some cl :=
  terminal_absorbing hr hrt hcl (Or.inr hd)

/-- ANYONE CAN APPROVE.  The approvals API route performs no
    authentication or authorization (approvals/route.ts), and
    `resolveApproval`'s actor defaults to the literal string
    `"human.operator"` and is never checked.  In the model this is exact:
    the `Step.resolve` constructor takes an arbitrary `actor : String`
    that appears in no guard and does not affect the successor state
    (`applyResolve` has no actor parameter at all).  Hence for every
    string `actor` whatsoever, an open approval can be resolved from a
    reachable state. -/
theorem anyone_can_approve {s : Sys} (aid : Nat) (ap : Apr) (cl : Clr)
    (a b : Bool) (actor : String)
    (ha : s.aprs aid = some ap) (ho : ap.status = .open)
    (hc : s.clrs ap.clrId = some cl) (hp : cl.status = .pending) :
    Step s (applyResolve s aid ap cl a b) :=
  Step.resolve s aid a b actor ap cl ha ho hc hp

/-- Two different actors — say the empty string and an arbitrary
    attacker-chosen string — resolve the same approval to the *identical*
    successor state.  Authorization is not merely weak; the actor is
    causally irrelevant to the transition. -/
theorem resolve_outcome_independent_of_actor {s : Sys}
    (aid : Nat) (ap : Apr) (cl : Clr) (a b : Bool)
    (actor₁ actor₂ : String)
    (ha : s.aprs aid = some ap) (ho : ap.status = .open)
    (hc : s.clrs ap.clrId = some cl) (hp : cl.status = .pending) :
    Step s (applyResolve s aid ap cl a b) ∧
      Step s (applyResolve s aid ap cl a b) :=
  ⟨Step.resolve s aid a b actor₁ ap cl ha ho hc hp,
   Step.resolve s aid a b actor₂ ap cl ha ho hc hp⟩

/-- With the external gate not blocking (`blocked = false`), a human
    "approve" always yields an approved clearance — no veto. -/
theorem humanStatus_approve_unblocked (m : Int) :
    humanStatus true false m = .approved := by
  by_cases hm : m > 0 <;> simp [humanStatus, hm]

/-- End-to-end exhibit: from any state satisfying the invariant in which
    an approval is open on a pending clearance, an *arbitrary* actor
    string can approve it, and (when the external gate does not block)
    the clearance is approved and metered exactly the approved amount. -/
theorem arbitrary_actor_approval_meters {s : Sys} (hinv : Inv s)
    (aid : Nat) (ap : Apr) (cl : Clr)
    (ha : s.aprs aid = some ap) (ho : ap.status = .open)
    (hc : s.clrs ap.clrId = some cl) (hp : cl.status = .pending)
    (actor : String) :
    Step s (applyResolve s aid ap cl true false) ∧
      (ap.clrId, cl.amount) ∈ (applyResolve s aid ap cl true false).usage := by
  refine ⟨Step.resolve s aid true false actor ap cl ha ho hc hp, ?_⟩
  have hinv' := inv_resolve hinv aid ap cl true false ha ho hc hp
  have hcl' : (applyResolve s aid ap cl true false).clrs ap.clrId =
      some ⟨cl.amount, .approved⟩ := by
    rw [applyResolve_clrs, if_pos rfl, humanStatus_approve_unblocked]
  exact hinv'.approvedMetered ap.clrId ⟨cl.amount, .approved⟩ hcl' rfl

/-- The `escalated` status exists in the TypeScript union type
    (types.ts) but no code path produces it: it is unreachable. -/
theorem no_escalated_reachable {b : Int} {s : Sys} (hr : Reach (init b) s)
    (cid : Nat) (cl : Clr) (hcl : s.clrs cid = some cl) :
    cl.status ≠ .escalated :=
  (reach_inv hr).noEsc cid cl hcl
