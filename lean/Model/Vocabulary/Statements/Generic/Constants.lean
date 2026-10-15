module
public import Model.Vocabulary.Objects.Time

@[expose] public section

/-!
# Generic constants

The timing and bound constants used by the generic claims.
-/

namespace DecoupledConsensusModel.Statements.Generic

open DecoupledConsensusModel

/-- Timing and bound constants for the generic claims: the recurrence period, the participation
    window, and the inclusion and growth delays of the confirmed, stable and finalized outputs. -/
structure Constants where
  /-- Duration of one recurrence period. -/
  period : Time
  /-- Width of the awake-history window. -/
  participationWindow : Time
  /-- The time offset of the reference sample used by the participation conditions. -/
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
  /-- The confirmed inclusion delay: from a proposal at its proposal time to its confirmed
      inclusion. -/
  confirmationDelay : Time
  /-- The confirmed growth delay for a recurrence gap. -/
  growthDelay : Nat → Time
  /-- Stable-output growth delay for recurrence gap `gap`, in `Time`. -/
  stableGrowthDelay : Nat → Time
  /-- The stable inclusion delay when honest multi-proposer windows recur within the given number of
      periods. -/
  stableInclusionDelay : Nat → Time
  /-- The finality startup delay for a recurrence gap. -/
  finalityStartup : Nat → Time
  /-- The finality inclusion deadline after startup, for a recurrence gap. -/
  finalityDeadline : Nat → Time
  /-- The earliest permitted start of the asynchronous period, for the stable output read at time
      `T`. -/
  outageStart : Time → Time
  /-- The time after which votes formed for the stable output read at `T` may
  expire, in `Time`. -/
  expiry : Time → Time

/-- The constants are well formed. -/
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

end DecoupledConsensusModel.Statements.Generic

end
