import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bInvariantActive

/-!
# Honest active attesters of a round

Over a model `M : Record.Model V`: a member of `HonRound` for round `r` is honest through the
round's action instant, and awake throughout the window of the round's opening-slot confirmation.
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

/-- Under monotone corruption, every validator awake throughout round `r`'s attester window and not
    held by the adversary at `S.a r` is held by the adversary at no instant at or before `S.a r`. -/
theorem honRound_subset_honestThroughSet (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (r : Round)
    (hmono : Sched.MonotoneCorruption) :
    Restated.HonRound M S Sched r ⊆ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
  intro v hv
  have hadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := (Finset.mem_sdiff.1 hv).2
  exact mem_honestThroughSet.2 (fun t' ht' hmem => hadv (hmono t' ((Restated.Vocabulary.Execution.Setup.a M S r)) ht' hmem))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `HonRound` for round `r` is awake at every instant from one delay before the round's
    opening slot starts through that slot's confirmation instant. -/
theorem honRound_awakeThroughout_confirmation (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (r : Round)
    {v : V} (hv : v ∈ Restated.HonRound M S Sched r) :
    v ∈ Sched.awakeThroughout
      (slotStart S.E.Δ ((M.opening_slot S.hc r)) - S.E.Δ)
      (M.confirmation_time S.E ((M.opening_slot S.hc r))) := by
  have hact : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - 12 * S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
    have he := facts.gr.early_g2_eq S r
    refine awakeThroughout_mono Sched (Finset.mem_sdiff.1 hv).1 ?_ le_rfl
    show M.a S.hc S.E.Δ r - 12 * S.E.Δ ≥ M.early S.E S.hc r .g2 - S.E.Δ
    linarith
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hw : 12 * S.E.Δ ≤ wAttest S := twelve_delta_le_wAttest S
  have hconf : M.confirmation_time S.E ((M.opening_slot S.hc r)) = (Restated.Vocabulary.Execution.Setup.a M S r) :=
    Restated.confirmation_time_opening_slot facts S r
  have hconf' : M.confirmation_time S.E ((M.opening_slot S.hc r))
      = slotStart S.E.Δ ((M.opening_slot S.hc r)) + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hstart : slotStart S.E.Δ ((M.opening_slot S.hc r)) = (Restated.Vocabulary.Execution.Setup.a M S r) - 6 * S.E.Δ := by
    rw [hconf'] at hconf
    linarith
  rw [hconf, hstart]
  exact awakeThroughout_mono Sched hact (by linarith) le_rfl

end

end DecoupledConsensusModel.Sts.Restated
