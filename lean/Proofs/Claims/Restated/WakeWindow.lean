import Model.Record.Model
import Model.Record.Facts

/-!
# An awake window from the wake-ups at action instants

A validator awake through the window before a round's action instant, or before a slot's proposal or
vote instant, passes the grade-2 or grade-1 awake test there.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Restated

open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At a tick step `k` whose instant `τ` is round `r`'s action instant, a validator awake at every
    instant from one delay before round `r`'s grade-2 cutoff to `τ`, and not held by the adversary
    at any instant up to `τ`, passes the grade-2 test on the node state its tick at `τ` reads. -/
theorem run_fact_g2 {M : Record.Model V} (facts : Record.Facts M) :
    ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (Record.protocolOf M S) Sched) (k τ : Nat) (r : Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ → (τ : Int) = M.a S.hc S.E.Δ r →
    v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) (M.a S.hc S.E.Δ r) →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    M.awake_for_grade2 (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.a S.hc S.E.Δ r) x[k] v) r := by
  intro S Sched x k τ r v hlbl hτ hv hhon
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  rw [← hτ] at hv ⊢
  refine facts.ndRun.run_fact_g2_at S Sched x k τ r v hlbl ?_ hv hhon
  rw [facts.gr.early_g2_eq S r, hτ]
  linarith

/-- At a tick step `k` whose instant `τ` is slot `s`'s proposal instant or its Goldfish vote
    instant, a validator awake at every instant from one delay before the grade-1 cutoff of `s`'s
    round to `τ`, and not held by the adversary at any instant up to `τ`, passes the grade-1 test of
    `s`'s round on the node state its tick at `τ` reads. -/
theorem run_fact_g1 {M : Record.Model V} (facts : Record.Facts M) :
    ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (Record.protocolOf M S) Sched) (k τ : Nat) (s : Slot) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    ((τ : Int) = M.proposal_time S.E s ∨ (τ : Int) = M.vote_time S.E s) →
    v ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ) (τ : Int) →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    M.awake_for_grade1 (Setup.alwaysAwake S) v (Record.wakeStage M Sched (τ : Int) x[k] v)
      (M.round_of S.hc s) := by
  intro S Sched x k τ s v hlbl hτ hv hhon
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  refine facts.ndRun.run_fact_g1_at S Sched x k τ (M.round_of S.hc s) v hlbl ?_ hv hhon
  have h1 := facts.gr.early_g1_le_domain_g1 S (M.round_of S.hc s)
  have h2 := facts.gr.Sts_domain_g1_eq_opening S (M.round_of S.hc s)
  have h3 := facts.gr.opening_eq_proposal_time S.E S.hc (M.round_of S.hc s)
  have h4 := facts.sch.proposal_time_mono S.E (facts.gr.opening_slot_round_of_le_slot S.hc s)
  have h5 := facts.sch.proposal_time_lt_vote_time S.E s
  rcases hτ with hτ | hτ <;> rw [hτ] <;> linarith

/-- `Setup.alwaysAwake (Setup.alwaysAwake S)` is `Setup.alwaysAwake S`. -/
theorem alwaysAwake_alwaysAwake (S : Setup V) :
    Setup.alwaysAwake (Setup.alwaysAwake S) = Setup.alwaysAwake S :=
  rfl

end DecoupledConsensusModel.Sts.Restated

