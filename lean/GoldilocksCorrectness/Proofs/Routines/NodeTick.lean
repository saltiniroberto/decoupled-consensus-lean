module
public import GoldilocksCorrectness.Proofs.Routines.ACInterfaceTick
public import GoldilocksCorrectness.Proofs.Routines.Attestation
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.Interface
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The tick's duties: their cases, and no error raised

`tick_cases`, `tick_latest_cases`, `tick_period_cases`, `tick_attest_input`, `tick_attest_awake`:
what the tick does in each of its duties; `attest_ok`, `propose_block_ok`, `tick_ok`: the duties and
the tick raise no error from a node state satisfying the node invariant.

They read the node routines and node states alone: no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact, the duty's input.** At the action time of the round of its slot, when the node
passes the duty test, every answer of the tick has `ac_to_fg` answering on its final AC state over
the frame of the node's FG state.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_attest_input (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBRel (fun n' _ => t = C.a_ (C.round (C.slot t)) →
        (record_awake n t).awake_since (duty_window_start C (C.slot t)) = true →
        ∃ fi : FGInput V, ac_to_fg C n'.A (fg_to_ac n.S) t = .ok fi)
      (tick C P X n t) := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBRel.bind (DREBRel.of_emits (ac_on_tick_sends C P _ _ t _ _ _))
    (fun A₁ l₁ _ => ?_)
  refine DREBRel.ite (fun hc₁ => ?_) (fun hc₁ => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₁
    have hstart : t = C.t_ (C.slot t) := hc₁.1.1.2
    refine DREBRel.bind (DREBRel.of_emits (propose_block_sends C P X _)) (fun n₄ l₂ _ => ?_)
    refine DREBRel.ite (fun hc₂ => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      exact absurd (hstart.symm.trans hc₂.1) (slotStart_ne_actionTime C _)
    · exact DREBRel.pure (fun ht _ => absurd (hstart.symm.trans ht) (slotStart_ne_actionTime C _))
  · refine DREBRel.ite (fun _ => ?_) (fun hc₂ => ?_)
    · refine DREBRel.bind (attest_rel C _) (fun n₅ l₂ hl₂ => ?_)
      refine DREBRel.pure ?_
      obtain ⟨hA, fi, hfi, -, -⟩ := hl₂
      dsimp only at hA hfi
      rw [hS] at hfi
      exact fun _ _ => ⟨fi, by rw [hA]; exact hfi⟩
    · refine DREBRel.pure (fun ht hawake => ?_)
      exfalso
      apply hc₂
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ht, hawake⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact, a tick that sends an attestation passed the duty test.** Every attestation a tick
at `t` sends was sent with the duty test of the slot of `t` passing on the state the tick's first
step leaves.

Why: the attestation duty runs only inside its `if`, whose condition includes the duty test; the
tick of the available chain sends Goldfish votes only, and the proposal a block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_attest_awake (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBRel (fun _ l => ∀ a : Attestation V, NamedObject.attest a ∈ l →
        (record_awake n t).awake_since (duty_window_start C (C.slot t)) = true)
      (tick C P X n t) := by
  simp only [tick]
  refine DREBRel.bind (DREBRel.of_emits (ac_on_tick_sends C P _ _ t _ _ _))
    (fun A₁ l₁ hl₁ => ?_)
  have hl₁' : NoAttest l₁ := noAttest_of_ac_on_tick hl₁
  refine DREBRel.ite (fun hc₁ => ?_) (fun hc₁ => ?_)
  · -- the proposal ran, at the start of the slot: the attestation duty does not run
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₁
    have hstart : t = C.t_ (C.slot t) := hc₁.1.1.2
    refine DREBRel.bind (DREBRel.of_emits (propose_block_sends C P X _)) (fun n₄ l₂ hl₂ => ?_)
    refine DREBRel.ite (fun hc₂ => ?_) (fun hc₂ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      exact absurd (hstart.symm.trans hc₂.1) (slotStart_ne_actionTime C _)
    · refine DREBRel.pure (fun a ha => ?_)
      obtain ⟨B, rfl⟩ := hl₂
      simp only [List.append_nil, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · exact absurd ha (hl₁' a)
      · cases ha
  · refine DREBRel.ite (fun hc₂ => ?_) (fun hc₂ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      refine DREBRel.bind (attest_rel C _) (fun n₅ l₂ _ => ?_)
      exact DREBRel.pure (fun _ _ => hc₂.2)
    · refine DREBRel.pure (fun a ha => ?_)
      rw [List.append_nil] at ha
      exact absurd ha (hl₁' a)

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What a successful tick does to the record of the confirmed tip: it keeps it; or `t` is the
support cutoff of its slot, the node's stored `awakeSince` is some time at most the duty window's
start of that slot, and the tick leaves the saved confirmations and the record of the
confirmation update of that slot on `expireLocks n.A t`, over the frame `fg_to_ac n.S`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent. -/
theorem tick_latest_cases (C : Config) (P : Provisional V) (X : External V) (n n' : NodeState V)
    (t : Time) (sent : List (NamedObject V))
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes) :
    n'.A.latest_confirmed = n.A.latest_confirmed ∨
    (t = C.t_ (C.slot t) + 2 * C.Δ ∧
      (∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t)) ∧
      ∃ A'' : ACState V,
        update_confirmation C P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A'' ∧
        n'.A.saved_confirmation = A''.saved_confirmation ∧
        n'.A.latest_confirmed = A''.latest_confirmed) := by
  obtain ⟨A₁, out, out', hrun, hk⟩ := tick_ac_on_tick C P X n n' t sent hRun
  have hc := ac_on_tick_latest_cases C P n.A (fg_to_ac n.S) t n.v _ _ out A₁ out' hrun
  rw [hk.2.2.2]
  rcases hc with h | ⟨h1, h2, A'', hA'', hEq⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, awakeSince_of_record_awake h2 ?_, A'', hA'', hEq ▸ hk.2.1, hEq ▸ rfl⟩
    have hΔ := C.Δ_pos
    have hk0 : (0 : Int) ≤ 4 * C.Δ * (C.k : Int) := by positivity
    have e1 : @Eq Int (duty_window_start C (C.slot t))
        (C.t_ (C.slot t) + C.Δ - 4 * C.Δ * (C.k : Int)) := rfl
    have e2 : @Eq Int t (C.t_ (C.slot t) + 2 * C.Δ) := h1
    have hΔ' : @LT.lt Int _ 0 C.Δ := hΔ
    have hk0' : @LE.le Int _ 0 (4 * C.Δ * (C.k : Int)) := hk0
    show @LT.lt Int _ (duty_window_start C (C.slot t)) t
    omega

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- What a successful tick does to the saved confirmations and the lock entries, in three cases:
it keeps the saved confirmations and keeps a subset of the lock entries; or `t` is the vote time
of its slot, and the tick keeps the saved confirmations and leaves the lock entries of the
revocation of that slot on `expireLocks n.A t`, over the frame `fg_to_ac n.S`; or `t` is the
support cutoff of its slot, the node's stored `awakeSince` is some time at most the duty window's
start of that slot, and the tick leaves the saved confirmations and the lock entries of the
confirmation update of that slot on `expireLocks n.A t`.

Why: the tick's AC fields are its tick of the available chain's (`tick_ac_on_tick`), whose two
tests are the duty test; at the support cutoff the duty window's start is before the tick, so the
test reads a present `awakeSince` (`awakeSince_of_record_awake`).

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent. -/
theorem tick_cases (C : Config) (P : Provisional V) (X : External V) (n n' : NodeState V)
    (t : Time) (sent : List (NamedObject V))
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes) :
    (n'.A.saved_confirmation = n.A.saved_confirmation ∧ n'.A.lock_entries ⊆ n.A.lock_entries) ∨
    (t = C.t_ (C.slot t) + C.Δ ∧ ∃ A' : ACState V,
      revoke_locks P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A' ∧
      n'.A.saved_confirmation = n.A.saved_confirmation ∧ n'.A.lock_entries = A'.lock_entries) ∨
    (t = C.t_ (C.slot t) + 2 * C.Δ ∧
      (∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t)) ∧
      ∃ A'' : ACState V,
        update_confirmation C P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A'' ∧
        n'.A.saved_confirmation = A''.saved_confirmation ∧
        n'.A.lock_entries = A''.lock_entries) := by
  obtain ⟨A₁, out, out', hrun, hk⟩ := tick_ac_on_tick C P X n n' t sent hRun
  have hc := ac_on_tick_cases C P n.A (fg_to_ac n.S) t n.v _ _ out A₁ out' hrun
  rw [hk.1, hk.2.1]
  rcases hc with h | ⟨h1, -, A', hA', h2, h3⟩ | ⟨h1, h2, A'', hA'', h3, h4⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, A', hA', h2, h3⟩)
  · refine Or.inr (Or.inr ⟨h1, awakeSince_of_record_awake h2 ?_, A'', hA'', h3, h4⟩)
    have hΔ := C.Δ_pos
    have hk0 : (0 : Int) ≤ 4 * C.Δ * (C.k : Int) := by positivity
    have e1 : @Eq Int (duty_window_start C (C.slot t))
        (C.t_ (C.slot t) + C.Δ - 4 * C.Δ * (C.k : Int)) := rfl
    have e2 : @Eq Int t (C.t_ (C.slot t) + 2 * C.Δ) := h1
    have hΔ' : @LT.lt Int _ 0 C.Δ := hΔ
    have hk0' : @LE.le Int _ 0 (4 * C.Δ * (C.k : Int)) := hk0
    show @LT.lt Int _ (duty_window_start C (C.slot t)) t
    omega

end

end

section

open GoldilocksCorrectness.Statements.Routines (NodeInv PoolAttestationsWellFormed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The proposal answers on a node state satisfying `NodeInv`.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `X`: the digest; `n`: the node
  state. -/
theorem propose_block_ok (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (h : NodeInv C P X n) : DREBOk (propose_block C P X n) := by
  simp only [propose_block]
  refine DREBOk.bind_any (DREBOk.liftM
    (ac_proposal_ok C n.A (nodeInv_frameRoots h) n.t (nodeInv_poolStamped h)
      (nodeInv_frameStamped h))) (fun _ => ?_)
  exact DREBOk.bind_any (DREBOk.broadcast _) (fun _ => DREBOk.pure _)

/-- The attestation duty answers on a node state satisfying `NodeInv`.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `X`: the digest; `n`: the node
  state. -/
theorem attest_ok (C : Config) {P : Provisional V} {X : External V} (n : NodeState V)
    (h : NodeInv C P X n) : DREBOk (attest C n) := by
  simp only [attest]
  refine DREBOk.bind_any (DREBOk.liftM
    (ac_to_fg_ok C n.A (nodeInv_frameRoots h) n.t (nodeInv_poolStamped h)
      (nodeInv_frameStamped h))) (fun _ => ?_)
  repeat' first
    | refine DREBOk.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBOk.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBOk.bind_any (DREBOk.broadcast _) (fun _ => ?_)
    | exact DREBOk.pure _

/-- **The node's tick answers** on a node state satisfying `NodeInv`, at a time no earlier than
the node's clock, whatever was sent before it.

Why: the raise sites read only the three clauses of `NodeInv` on the roots and the stamps, and the
proposal and the attestation duty run on node states that satisfy `NodeInv` too
(`nodeInv_of_frame`, `propose_block_nodeInv`); the clock condition is what `nodeInv_of_frame`
needs to carry `NodeInv` across the tick of the available chain.

Read aloud: a node whose state satisfies the node invariant never fails a tick at a time no
earlier than its clock.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `X`: the digest; `n`: the node state;
  `t`: the time of the tick. -/
theorem tick_ok (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (t : Time)
    (h : NodeInv C P X n) (ht : n.t ≤ t) : DREBOk (tick C P X n t) := by
  obtain ⟨hS, hA, -, -⟩ := record_awake_frame n t
  have hV : VotesInv P (record_awake n t).A t := by
    rw [hA]
    exact VotesInv.mono ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.1.2⟩ ht
  have h2 : NodeInv C P X { record_awake n t with t := t } :=
    nodeInv_of_frame h (n' := { record_awake n t with t := t }) (by show _ = _; rw [hS])
      (by show _ = _; rw [hS]) (by show _ = _; rw [hS]) (by show _ = _; rw [hS])
      (by show _ = _; rw [hS]) (by show _ = _; rw [hS]) (record_awake_keeps_record n t)
      (by show _ = _; rw [hA]) ht hV
      (by show PoolAttestationsWellFormed (record_awake n t).S; rw [hS]
          exact h.2.2.2.2.2.2.2.2.2.2)
  simp only [tick]
  refine DREBOk.bind
    (P := fun A' => VotesInv P A' t ∧ A'.timestamp_block = (record_awake n t).A.timestamp_block)
    (ac_on_tick_ok C P _ (nodeInv_frameRoots h2) t _ _ _ hV (nodeInv_frameStamped h2))
    (ac_on_tick_votesInv C P _ _ t t _ _ _ hV le_rfl) (fun A' hA' => ?_)
  have hq : NodeInv C P X { { record_awake n t with t := t } with A := A' } :=
    nodeInv_of_frame h2 rfl rfl rfl rfl rfl rfl rfl hA'.2 le_rfl hA'.1 h2.2.2.2.2.2.2.2.2.2.2
  refine DREBOk.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBOk.bind (propose_block_ok C P X _ hq) (propose_block_nodeInv C P X _ hq)
      (fun n₄ h₄ => ?_)
    refine DREBOk.ite (fun _ => ?_) (fun _ => DREBOk.pure _)
    exact DREBOk.bind_any (attest_ok C _ h₄.1) (fun _ => DREBOk.pure _)
  · refine DREBOk.ite (fun _ => ?_) (fun _ => DREBOk.pure _)
    exact DREBOk.bind_any (attest_ok C _ hq) (fun _ => DREBOk.pure _)

end

end

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What a successful tick does to the lock entries, the record of the confirmed tip and the fast
blocks: the three cases of `ac_on_tick_period_cases`, over the node's AC state and the frame
`fg_to_ac n.S`.

Why: the tick's AC fields are its tick of the available chain's (`tick_ac_on_tick`).

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent;
- `hRun`: the tick at `t` answers `n'` and sends `sent`. -/
theorem tick_period_cases (C : Config) (P : Provisional V) (X : External V) (n n' : NodeState V)
    (t : Time) (sent : List (NamedObject V))
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes) :
    (n'.A.lock_entries = (expireLocks n.A t).lock_entries ∧
      n'.A.latest_confirmed = n.A.latest_confirmed ∧ n'.A.fast_blocks = n.A.fast_blocks) ∨
    (t = C.t_ (C.slot t) + C.Δ ∧ ∃ A' : ACState V,
      revoke_locks P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A' ∧
      n'.A.lock_entries = A'.lock_entries ∧
      n'.A.latest_confirmed = n.A.latest_confirmed ∧ n'.A.fast_blocks = n.A.fast_blocks) ∨
    (t = C.t_ (C.slot t) + 2 * C.Δ ∧ ∃ A'' : ACState V,
      update_confirmation C P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A'' ∧
      n'.A.lock_entries = A''.lock_entries ∧
      n'.A.latest_confirmed = A''.latest_confirmed ∧ n'.A.fast_blocks = A''.fast_blocks) := by
  obtain ⟨A₁, out, out', hrun, hk⟩ := tick_ac_on_tick C P X n n' t sent hRun
  have hc := ac_on_tick_period_cases C P n.A (fg_to_ac n.S) t n.v _ _ out A₁ out' hrun
  rw [hk.1, hk.2.2.1, hk.2.2.2]
  exact hc

end

end GoldilocksCorrectness.Proofs.Routines
