import Model.Sts.Constants
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Round arithmetic and the protocol constants

The round period, the round of an instant, the recovery round, the healing boundary, the next action
instant and the protocol constants, stated over a model `M : Record.Model V`. The last section
equates each with the definition of the same name in `DecoupledConsensusModel.Sts` at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The number of time units between two consecutive round action instants, clamped at zero. -/
def roundPeriod (M : Record.Model V) (S : Setup V) : Nat := Int.toNat ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The first round whose action instant is at or after `t`: the number of action periods from the
    round-zero action instant to `t`, rounded up, and never negative. -/
def nextRound (M : Record.Model V) (S : Setup V) (t : Time) : Round :=
  Int.toNat (t - (Restated.Vocabulary.Execution.Setup.a M S 0)) ⌈/⌉ Restated.roundPeriod M S

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The round of the instant `t`, which is `nextRound`. -/
def roundAt (M : Record.Model V) (S : Setup V) (t : Time) : Round :=
  Restated.nextRound M S t

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The recovery round: the round of `t₀` plus the bounded phase-start lag, the two progress lags,
    the SG lookback and the recurrence gap. -/
noncomputable def recoveryRound (M : Record.Model V) (S : Setup V) (t₀ : Time) (gap extra : Nat) : Round :=
  Restated.roundAt M S t₀ + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * boundedPhaseStartLag gap extra) +
    2 * boundedPhaseStartLag gap extra +
    max (1 + S.hc.η_SG) (gap + 3) + gap

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The Goldfish vote instant of the slot two after round `q`'s opening slot. -/
def healingBoundaryTime (M : Record.Model V) (S : Setup V) (q : Round) : Time :=
  M.vote_time S.E ((M.opening_slot S.hc q) + 2)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The action instant of the first round whose action is not before `T`. -/
def nextAction (M : Record.Model V) (S : Setup V) (T : Time) : Time := (Restated.Vocabulary.Execution.Setup.a M S (roundAfter S T))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The protocol constants, each computed from `S`; `period` is one round, `S.a 1 − S.a 0`. -/
noncomputable def constants (M : Record.Model V) (S : Setup V) : Constants where
  period := (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)
  participationWindow := (S.hc.η_SG : Time) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0))
  participationLag := (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)
  proposerSlots := 3
  prefixEnd := fun t₀ gap => (Restated.Vocabulary.Execution.Setup.a M S)
    (Restated.recoveryRound M S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  recoveryEnd := fun t₀ gap =>
    Restated.healingBoundaryTime M S
      (Restated.recoveryRound M S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  maxGap := S.cfg.K
  confirmationDelay := 6 * S.E.Δ
  growthDelay := fun gap =>
    (gap : Time) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + 6 * S.E.Δ
  stableGrowthDelay := fun gap =>
    (gap + S.hc.η_SG : Nat) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + 2 * S.E.Δ
  stableInclusionDelay := fun gap =>
    6 * S.E.Δ + ((gap + S.hc.η_SG : Nat) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + 2 * S.E.Δ)
  finalityStartup := fun gap =>
    Restated.healingBoundaryTime M S
        (DecoupledConsensusModel.Sts.finalityStartup S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)
  finalityDeadline := fun gap =>
    Restated.healingBoundaryTime M S
        (DecoupledConsensusModel.Sts.finalityDeadline S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) +
      3 * S.E.Δ
  outageStart := fun T =>
    Restated.nextAction M S T + ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + S.E.Δ
  expiry := fun T =>
    M.early S.E S.hc
      ((M.round_of S.hc (S.E.slotOf (Restated.nextAction M S T))) + S.hc.η_SG + 1) .g2

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Execution

/-- At `Record.Model.vocabulary`, `Restated.roundPeriod` is `Sts.roundPeriod`. -/
@[record_vocabulary]
theorem roundPeriod_vocabulary_eq (S : Setup V) :
    _root_.DecoupledConsensusModel.Sts.roundPeriod (V := V) S = Restated.roundPeriod (V := V) Record.Model.vocabulary S :=
  rfl

/-- At `Record.Model.vocabulary`, `Restated.nextRound` is `Sts.nextRound`. -/
@[record_vocabulary]
theorem nextRound_vocabulary_eq (S : Setup V) (t : Time) :
    _root_.DecoupledConsensusModel.Sts.nextRound (V := V) S t = Restated.nextRound (V := V) Record.Model.vocabulary S t :=
  rfl

/-- At `Record.Model.vocabulary`, `Restated.roundAt` is `Sts.roundAt`. -/
@[record_vocabulary]
theorem roundAt_vocabulary_eq (S : Setup V) (t : Time) :
    _root_.DecoupledConsensusModel.Sts.roundAt (V := V) S t = Restated.roundAt (V := V) Record.Model.vocabulary S t :=
  rfl

/-- At `Record.Model.vocabulary`, `Restated.recoveryRound` is `Sts.recoveryRound`. -/
@[record_vocabulary]
theorem recoveryRound_vocabulary_eq (S : Setup V) (t₀ : Time) (gap extra : Nat) :
    _root_.DecoupledConsensusModel.Sts.recoveryRound (V := V) S t₀ gap extra = Restated.recoveryRound (V := V) Record.Model.vocabulary S t₀ gap extra :=
  rfl

/-- At `Record.Model.vocabulary`, `Restated.healingBoundaryTime` is `Sts.healingBoundaryTime`. -/
@[record_vocabulary]
theorem healingBoundaryTime_vocabulary_eq (S : Setup V) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.healingBoundaryTime (V := V) S q = Restated.healingBoundaryTime (V := V) Record.Model.vocabulary S q :=
  rfl

/-- At `Record.Model.vocabulary`, `Restated.nextAction` is `Sts.nextAction`. -/
@[record_vocabulary]
theorem nextAction_vocabulary_eq (S : Setup V) (T : Time) :
    _root_.DecoupledConsensusModel.Sts.nextAction (V := V) S T = Restated.nextAction (V := V) Record.Model.vocabulary S T :=
  rfl

/-- At `Record.Model.vocabulary`, `Restated.constants` is `Sts.constants`. -/
@[record_vocabulary]
theorem constants_vocabulary_eq (S : Setup V) :
    _root_.DecoupledConsensusModel.Sts.constants (V := V) S = Restated.constants (V := V) Record.Model.vocabulary S :=
  rfl

end

end DecoupledConsensusModel.Sts.Restated
