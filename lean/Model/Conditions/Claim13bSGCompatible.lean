import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bSGCompatible

/-!
# The switch round and the bound on the cut

The round `switchRound` at which the phase ends and the round `cutBoundW`, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The switch round: the largest round `r` (at most `tE.toNat`) for which the confirmation time of
    the slot two after `r`'s opening slot is at most `tE`. -/
noncomputable def switchRound (M : Record.Model V) (S : Setup V) (tE : Int) : Round :=
  Nat.findGreatest
    (fun r => M.confirmation_time S.E ((M.opening_slot S.hc r) + 2) ≤ tE) tE.toNat

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The round after the one at `tGAT`, plus two rounds, plus one progress window per `D + K + 5`
    heights, plus two more progress windows, plus one round, plus the SG expiry window. -/
noncomputable def cutBoundW (M : Record.Model V) (S : Setup V) (tGAT : Int) (gap : Nat) : Round :=
  Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1 + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * (7 * gap + 22 + 4 * S.extraRounds)) +
    2 * (7 * gap + 22 + 4 * S.extraRounds) + 1 + S.hc.η_SG

end

end DecoupledConsensusModel.Sts.Restated
