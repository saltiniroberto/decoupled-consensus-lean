import Proofs.Vocabulary.Execution.RecoveryFilterSchedule
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# An action time before a vote time

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a round's action
time that is before a slot's vote time is at least one delay `S.E.Δ` before it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- If round `r`'s action time is before the vote time `M.vote_time S.E s` of slot `s`, that action
    time plus `S.E.Δ` is at most `M.vote_time S.E s`. -/
theorem Vocabulary.Proofs.HealingSurface.action_add_delta_le_vote_of_lt (facts : Record.Facts M)
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : (Restated.Vocabulary.Execution.Setup.a M S r) < M.vote_time S.E s) :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.vote_time S.E s := by
  have hproposal : (Restated.Vocabulary.Execution.Setup.a M S r) < M.proposal_time S.E s := by
    rw [Restated.Vocabulary.Execution.Setup.a,
      Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts S.hc S.E r] at hlt ⊢
    exact facts.sch.support_cutoff_lt_vote_time_imp_lt_proposal_time S.E hlt
  have hstep : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E s := by
    have hx : S.E.Δ ∣ (Restated.Vocabulary.Execution.Setup.a M S r) := by
      rw [Restated.Vocabulary.Execution.Setup.a,
        Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts]
      exact Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S _)
    have hy : S.E.Δ ∣ M.proposal_time S.E s :=
      Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E _)
    obtain ⟨x, hx⟩ := hx
    obtain ⟨y, hy⟩ := hy
    rw [hx, hy] at hproposal ⊢
    have hd := S.E.Δ_pos
    have hxy : x < y := lt_of_mul_lt_mul_left hproposal hd.le
    nlinarith
  exact le_trans hstep (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s))

end

end DecoupledConsensusModel.Sts.Restated
