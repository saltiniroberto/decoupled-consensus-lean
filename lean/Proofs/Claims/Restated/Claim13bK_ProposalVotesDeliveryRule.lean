import Proofs.Claims.Restated.Claim13bW_ScheduleRule

/-!
# A proposer's awake window read off the grade-1 test its proposal tick passed

A validator's tick at slot `s`'s proposal instant sends a block only when its node state passes the
grade-1 awake test of `s`'s round. `NodeWakeFacts` reads the passed test back: the validator was
awake at every time from that round's grade-1 window start to the proposal instant, which contains
the two delays before the proposal instant. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Round `r`'s grade-1 window start is at least two delays before the proposal instant of every
    slot of round `r` or later. -/
theorem early_g1_sub_delta_le_proposal_sub_two (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ ≤ M.proposal_time S.E s - 2 * S.E.Δ := by
  have h1 := facts.gr.q10_early_g1_le_domain_g2 S (M.round_of S.hc s)
  have h2 := facts.gr.domain_g2_add_delta_le_domain_g1 S (M.round_of S.hc s)
  have h3 := facts.gr.Sts_domain_g1_eq_opening S (M.round_of S.hc s)
  have h4 := facts.gr.opening_eq_proposal_time S.E S.hc (M.round_of S.hc s)
  have h5 := facts.sch.proposal_time_mono S.E (facts.gr.opening_slot_round_of_le_slot S.hc s)
  linarith

/-- If, at the tick step `k` at slot `s`'s proposal instant, the node state of a validator `v`,
    awake there and not held by the adversary up to there, passes the grade-1 awake test of `s`'s
    round, and that round's grade-1 window start is at or after time `0`, then `v` was awake at every
    time from two delays before the proposal instant to it.

    Variables: `s` the slot, `k` the tick step, `τ` its time, `v` the validator. -/
theorem awakeThroughout_before_proposal_of_g1 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {s : Slot} {k τ : Nat} {v : V} (hl : x.lbl k = AtomicAction.tickAllAwake τ)
    (hτ : (τ : Int) = M.proposal_time S.E s)
    -- `v` is not held by the adversary at any time up to `τ`
    (hhon : ∀ t ≤ (τ : Int), v ∉ Sched.adv t)
    (haw : v ∈ Sched.awake (τ : Int))
    -- the grade-1 window start of `s`'s round is at or after time `0`
    (hr : 0 ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ)
    (hrun : M.awake_for_grade1 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (τ : Int) x[k] v) (M.round_of S.hc s)) :
    v ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ) (M.proposal_time S.E s) := by
  have hwin := facts.ndWake.run_fact_g1_sound_at S Sched x k τ (M.round_of S.hc s) v hl hr hhon haw hrun
  rw [hτ] at hwin
  exact awakeThroughout_mono Sched hwin
    (Restated.early_g1_sub_delta_le_proposal_sub_two facts S s) le_rfl

/-- If an outcome of the tick of a validator `v` at the tick step `k`, at slot `s`'s proposal
    instant, sends a block, `v` is awake there and not held by the adversary up to there, and the
    grade-1 window start of `s`'s round is at or after time `0`, then `v` was awake at every time
    from two delays before the proposal instant to it.

    Variables: `s` the slot, `k` the tick step, `τ` its time, `v` the proposer, `out` the tick's
    outcome, `B` the block. -/
theorem awakeThroughout_before_proposal_rule (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {s : Slot} {k τ : Nat} {v : V} (hl : x.lbl k = AtomicAction.tickAllAwake τ)
    (hτ : (τ : Int) = M.proposal_time S.E s)
    -- `v` is not held by the adversary at any time up to `τ`
    (hhon : ∀ t ≤ (τ : Int), v ∉ Sched.adv t)
    (haw : v ∈ Sched.awake (τ : Int))
    -- the grade-1 window start of `s`'s round is at or after time `0`
    (hr : 0 ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ)
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (τ : Int) x[k] v) (τ : Int) ⇢ out)
    {B : NamedBlock V} (hemit : NamedObject.block B ∈ out.2) :
    v ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ) (M.proposal_time S.E s) := by
  have hrun : M.awake_for_grade1 (Setup.alwaysAwake S) v (Record.wakeStage M Sched (τ : Int) x[k] v)
      (M.round_of S.hc (S.E.slotOf (τ : Int))) :=
    facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) v _ _ out hout hemit
  have hslot : S.E.slotOf (τ : Int) = s := by rw [hτ]; exact facts.sch.slotOf_proposal_time S.E s
  rw [hslot] at hrun
  exact Restated.awakeThroughout_before_proposal_of_g1 facts S Sched x hl hτ hhon haw hr hrun

end

end DecoupledConsensusModel.Sts.Restated
