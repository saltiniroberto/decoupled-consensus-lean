module
public import Mathlib.Algebra.Order.Floor.Div
public import Model.Vocabulary.Execution.Setup
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The timing constants

The round-schedule arithmetic, the finality deadlines, and the record `Constants` of timing numbers
with its instance `constants S`, all computed from `S : Setup V`. The file does not open the sts
framework, so `Time` here is `Int`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The round schedule -/

/-- The number of time units between two consecutive round action instants, clamped at zero. -/
def roundPeriod (S : Setup V) : Nat := Int.toNat (S.a 1 - S.a 0)

/-- The first round whose action instant is at or after `t`: the number of action periods from the
    round-zero action instant to `t`, rounded up and never negative. -/
def nextRound (S : Setup V) (t : Time) : Round :=
  Int.toNat (t - S.a 0) ⌈/⌉ roundPeriod S

/-- Another name for `nextRound`. -/
def roundAt (S : Setup V) (t : Time) : Round :=
  nextRound S t

/-- The bounded phase-start lag, in rounds, computed from the recurrence gap and an extra allowance. -/
def boundedPhaseStartLag (gap extra : Nat) : Nat :=
  (4 * gap + 12 + 2 * extra) + 3 * gap + 10 + 2 * extra

/-- The recovery round: the round of `t₀` plus allowances for the bounded phase-start lag, the two
    progress lags, the SG lookback and the recurrence gap. -/
noncomputable def recoveryRound (S : Setup V) (t₀ : Time) (gap extra : Nat) : Round :=
  roundAt S t₀ + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * boundedPhaseStartLag gap extra) +
    2 * boundedPhaseStartLag gap extra +
    max (1 + S.hc.η_SG) (gap + 3) + gap

/-- The Goldfish vote instant of the slot two after round `q`'s opening slot. -/
def healingBoundaryTime (S : Setup V) (q : Round) : Time :=
  Protocol.vote_time S.E (S.hc.opening_slot q + 2)

/-! ## Finality deadlines -/

/-- The startup lag for finality liveness, in rounds, built from the height parameters `D` and `K`,
    the recurrence gap and the extra allowance. -/
def finalityStartup (S : Setup V) (gap : Round) (extra : Nat) : Round :=
  1 + (S.cfg.D + S.cfg.K + 5) * (7 * gap + 22 + 4 * extra) +
    3 * (7 * gap + 22 + 4 * extra) + gap + 5

/-- The finality deadline, in rounds, built from the height parameters `D` and `K`, the recurrence
    gap and the extra allowance. -/
def finalityDeadline (S : Setup V) (gap : Round) (extra : Nat) : Round :=
  (S.cfg.D + S.cfg.K + 2) *
    (4 * (7 * gap + 22 + 4 * extra) + 4 * gap + 7 +
      (S.cfg.D + S.cfg.K + 5) * (gap + 1))

/-! ## Round length and next action -/

/-- The round length `4 · S.E.Δ · S.hc.R`, the time between two consecutive round action instants. -/
def roundLength (S : Setup V) : Time := 4 * S.E.Δ * (S.hc.R : Time)

/-- The first round whose action instant is at or after `T`, computed from
    `S.a r = 6Δ + r · roundLength S`. -/
def roundAfter (S : Setup V) (T : Time) : Round :=
  (Int.ediv (T - 6 * S.E.Δ + roundLength S - 1) (roundLength S)).toNat

/-- The action instant of the first round whose action instant is at or after `T`. -/
def nextAction (S : Setup V) (T : Time) : Time := S.a (roundAfter S T)

/-! ## The constants -/

/-- The protocol's timing constants: a period length, a participation window and lag, the number of
    proposer slots, the recovery boundary functions, and an inclusion delay and a growth delay per
    output. -/
structure Constants where
  /-- Duration of one recurrence period, in `Time`; expected to be positive. -/
  period : Time
  /-- Width of the awake-history window, in `Time`. -/
  participationWindow : Time
  /-- Time offset used to form the participation reference sample. -/
  participationLag : Time
  /-- Number of consecutive proposer slots, including the opening slot. -/
  proposerSlots : Nat
  /-- End time of the source prefix at reference time `t₀` and recurrence gap
  `gap`. -/
  prefixEnd : Time → Nat → Time
  /-- Time at which the continuation counts as recovered, from reference time
  `t₀` and recurrence gap `gap`. -/
  recoveryEnd : Time → Nat → Time
  /-- Maximum recurrence gap, measured in periods. -/
  maxGap : Nat
  /-- Delay from a proposal at its proposal time to confirmed inclusion, in
  `Time`; the confirmed inclusion delay. -/
  confirmationDelay : Time
  /-- The confirmed growth delay for recurrence gap `gap`, in `Time`. -/
  growthDelay : Nat → Time
  /-- Stable-output growth delay for recurrence gap `gap`, in `Time`. -/
  stableGrowthDelay : Nat → Time
  /-- Inclusion delay of the stable output when honest multi-proposer windows recur within
  `gap` periods, in `Time`. -/
  stableInclusionDelay : Nat → Time
  /-- Protocol-specific finality startup delay for recurrence gap `gap`, in
  `Time`; the finalized startup delay. -/
  finalityStartup : Nat → Time
  /-- Protocol-specific finality inclusion deadline after startup for
  recurrence gap `gap`, in `Time`; the finalized inclusion delay. -/
  finalityDeadline : Nat → Time
  /-- Earliest permitted outage start for the stable output read at time `T`,
  in `Time`. -/
  outageStart : Time → Time
  /-- The time after which votes formed for the stable output read at `T` may
  expire, in `Time`. -/
  expiry : Time → Time

/-- The constants are well formed: the period is positive, the window and the lag are not negative,
    there is at least one proposer slot, the maximum gap is at least two, every delay is not
    negative, the prefix ends no later than the recovery, and `C.outageStart T < C.expiry T` for
    every `T`. -/
structure Constants.Valid (C : Constants) : Prop where
  period_pos : 0 < C.period
  participationWindow_nonneg : 0 ≤ C.participationWindow
  participationLag_nonneg : 0 ≤ C.participationLag
  proposerSlots_pos : 0 < C.proposerSlots
  maxGap_ge_two : 2 ≤ C.maxGap
  delays_nonneg : ∀ gap,
    0 ≤ C.confirmationDelay ∧
    0 ≤ C.growthDelay gap ∧
    0 ≤ C.stableGrowthDelay gap ∧
    0 ≤ C.stableInclusionDelay gap ∧
    0 ≤ C.finalityStartup gap ∧
    0 ≤ C.finalityDeadline gap
  prefixEnd_le_recoveryEnd : ∀ t₀ gap, C.prefixEnd t₀ gap ≤ C.recoveryEnd t₀ gap
  outage_window_nonempty : ∀ T, C.outageStart T < C.expiry T

/-- The constants of the wired protocol, each read off `S`'s environment, healing schedule and
    height configuration: `period` is one round `S.a 1 − S.a 0`, `participationLag` is one round,
    and `participationWindow` is `η_SG` rounds. -/
noncomputable def constants (S : Setup V) : Constants where
  period := S.a 1 - S.a 0
  participationWindow := (S.hc.η_SG : Time) * (S.a 1 - S.a 0)
  participationLag := S.a 1 - S.a 0
  proposerSlots := 3
  prefixEnd := fun t₀ gap => S.a
    (recoveryRound S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  recoveryEnd := fun t₀ gap =>
    healingBoundaryTime S
      (recoveryRound S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  maxGap := S.cfg.K
  confirmationDelay := 6 * S.E.Δ
  growthDelay := fun gap =>
    (gap : Time) * (S.a 1 - S.a 0) + 6 * S.E.Δ
  stableGrowthDelay := fun gap =>
    (gap + S.hc.η_SG : Nat) * (S.a 1 - S.a 0) + 2 * S.E.Δ
  stableInclusionDelay := fun gap =>
    6 * S.E.Δ + ((gap + S.hc.η_SG : Nat) * (S.a 1 - S.a 0) + 2 * S.E.Δ)
  finalityStartup := fun gap =>
    healingBoundaryTime S
        (DecoupledConsensusModel.Sts.finalityStartup S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - S.a 0
  finalityDeadline := fun gap =>
    healingBoundaryTime S
        (DecoupledConsensusModel.Sts.finalityDeadline S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - S.a 0 +
      3 * S.E.Δ
  outageStart := fun T =>
    nextAction S T + (S.a 1 - S.a 0) + S.E.Δ
  expiry := fun T =>
    Protocol.early S.E S.hc
      (S.hc.round_of (S.E.slotOf (nextAction S T)) + S.hc.η_SG + 1) .g2

end DecoupledConsensusModel.Sts
