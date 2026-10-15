import Proofs.Vocabulary.Protocol.Grades.SafetyCompatibilityJoin
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# An earlier round's action precedes a later vote

The action time of a round is before the vote time of every slot of a later round, stated over a
model `M : Record.Model V`.
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
open Protocol
open Proofs.Optimistic

/-- If round `r` is before the round `M.round_of S.hc d` of slot `d`, then round `r`'s action time
    is before slot `d`'s vote time `M.vote_time S.E d`. -/
theorem Vocabulary.Proofs.HealingSurface.action_before_vote_of_round_lt (facts : Record.Facts M)
    (S : Setup V) {r : Round} {d : Slot} (hr : r < (M.round_of S.hc d)) :
    (Restated.Vocabulary.Execution.Setup.a M S r) < M.vote_time S.E d := by
  have hfirst := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hr
  have hslots : (M.opening_slot S.hc ((M.round_of S.hc d))) ≤ d :=
    facts.gr.opening_slot_round_of_le_slot S.hc d
  have hproposal := hfirst.trans (facts.sch.proposal_time_mono S.E hslots)
  exact (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
    (hproposal.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d)))

end

end DecoupledConsensusModel.Sts.Restated
