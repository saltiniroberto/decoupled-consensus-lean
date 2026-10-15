import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The delivery horizon at the first interior duty

The vote time of the slot after a round's opening slot, plus one delay, is within the run's horizon,
stated over a model `M : Record.Model V`.
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
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas DecoupledConsensusModel.Protocol

/-- If round `c + 1`'s action time is within the horizon of `rho`, then the vote time of the slot
    after round `c + 1`'s opening slot, plus `Δ`, is within that horizon. -/
theorem Vocabulary.Proofs.HealingSurface.firstInterior_vote_add_delta_le_horizon (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {c : Round}
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon) :
    M.vote_time S.E ((M.opening_slot S.hc (c + 1)) + 1) + S.E.Δ ≤
      rho.horizon := by
  calc M.vote_time S.E ((M.opening_slot S.hc (c + 1)) + 1) + S.E.Δ
      ≤ M.confirmation_time S.E (M.opening_slot S.hc (c + 1)) :=
        facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E _
    _ = Restated.Vocabulary.Execution.Setup.a M S (c + 1) :=
        Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (c + 1)
    _ ≤ rho.horizon := hhor

end

end DecoupledConsensusModel.Sts.Restated
