import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Record.Wiring

/-!
# Vote times and a round's opening

Every vote time of a slot in round `r` is at least round `r`'s opening time `Γ_0`, stated over a
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
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- If slot `s` is in round `r`, then round `r`'s opening time `Γ_0` is at most slot `s`'s vote
    time. -/
theorem Vocabulary.Proofs.HealingSurface.Γ_0_le_vote_time_of_round_eq (facts : Record.Facts M)
    (S : Setup V) {r : Round} {s : Slot}
    (hround : (M.round_of S.hc s) = r) :
    Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ r ≤ M.vote_time S.E s := by
  have hopen : (M.opening_slot S.hc r) ≤ s := by
    rw [← hround]
    exact facts.gr.opening_slot_round_of_le_slot S.hc s
  unfold Restated.Vocabulary.Protocol.HealConfig.Γ_0
  rw [facts.sch.Γ_0_eq_proposal_time]
  exact (facts.sch.proposal_time_mono S.E hopen).trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s))

end

end DecoupledConsensusModel.Sts.Restated
