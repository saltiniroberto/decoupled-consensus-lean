import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Round times

The round period, the round at or after a time, the recovery round and the healing boundary time,
stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The round action period `S.a 1 − S.a 0`, as a `Nat`. -/
def Vocabulary.Statements.Instantiation.roundPeriod (M : Record.Model V) (S : Setup V) : Nat := Int.toNat ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0))

end

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The first round whose action time is at or after `t`: `⌈(t − a₀) / period⌉`, clamped at zero. -/
def Vocabulary.Statements.Instantiation.nextRound (M : Record.Model V) (S : Setup V) (t : Time) : Round :=
  Int.toNat (t - (Restated.Vocabulary.Execution.Setup.a M S 0)) ⌈/⌉ Restated.Vocabulary.Statements.Instantiation.roundPeriod M S

end

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Equal to `nextRound`. -/
def Vocabulary.Statements.Instantiation.roundAt (M : Record.Model V) (S : Setup V) (t : Time) : Round :=
  Restated.Vocabulary.Statements.Instantiation.nextRound M S t

end

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The recovery round for the reference time `t₀`: the round after `roundAt M S t₀`, offset by lags
    built from `boundedPhaseStartLag gap extra`, by `max (1 + S.hc.η_SG) (gap + 3)` and by `gap`. -/
noncomputable def Vocabulary.Statements.Instantiation.recoveryRound (M : Record.Model V) (S : Setup V) (t₀ : Time) (gap extra : Nat) : Round :=
  Restated.Vocabulary.Statements.Instantiation.roundAt M S t₀ + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * boundedPhaseStartLag gap extra) +
    2 * boundedPhaseStartLag gap extra +
    max (1 + S.hc.η_SG) (gap + 3) + gap

end

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open Execution

/-- The vote time of slot `opening_slot q + 2`, two slots after round `q`'s opening slot. -/
def Vocabulary.Statements.Instantiation.healingBoundaryTime (M : Record.Model V) (S : Setup V) (q : Round) : Time :=
  M.vote_time S.E ((M.opening_slot S.hc q) + 2)

end

end DecoupledConsensusModel.Sts.Restated
