import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_OutageWindow
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring

/-!
# The timing constants

The timing constants of the end results for a setup, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel
open DecoupledConsensusModel.Execution DecoupledConsensusModel.Protocol

/-- The timing constants for the setup `S`: the period is one round's action period `S.a 1 − S.a 0`,
    the participation window is `η_SG` periods and the participation lag one period, and the prefix
    and recovery ends are read at `recoveryRound`. -/
noncomputable def Vocabulary.Statements.Instantiation.constants (M : Record.Model V) (S : Setup V) : Generic.Constants where
  period := (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)
  participationWindow := (S.hc.η_SG : Time) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0))
  participationLag := (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)
  proposerSlots := 3
  prefixEnd := fun t₀ gap => (Restated.Vocabulary.Execution.Setup.a M S)
    (Restated.Vocabulary.Statements.Instantiation.recoveryRound M S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  recoveryEnd := fun t₀ gap =>
    Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime M S
      (Restated.Vocabulary.Statements.Instantiation.recoveryRound M S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  maxGap := S.cfg.K
  confirmationDelay := 6 * S.E.Δ
  growthDelay := fun gap =>
    (gap : Time) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + 6 * S.E.Δ
  stableGrowthDelay := fun gap =>
    (gap + S.hc.η_SG : Nat) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + 2 * S.E.Δ
  stableInclusionDelay := fun gap =>
    6 * S.E.Δ + ((gap + S.hc.η_SG : Nat) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + 2 * S.E.Δ)
  finalityStartup := fun gap =>
    Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime M S
        (DecoupledConsensusModel.Statements.Instantiation.finalityStartup S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)
  finalityDeadline := fun gap =>
    Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime M S
        (DecoupledConsensusModel.Statements.Instantiation.finalityDeadline S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) +
      3 * S.E.Δ
  outageStart := fun T =>
    Restated.Vocabulary.Statements.Instantiation.nextAction M S T + ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + S.E.Δ
  expiry := fun T =>
    M.early S.E S.hc
      ((M.round_of S.hc (S.E.slotOf (Restated.Vocabulary.Statements.Instantiation.nextAction M S T))) +
        S.hc.η_SG + 1) .g2

end

end DecoupledConsensusModel.Sts.Restated
