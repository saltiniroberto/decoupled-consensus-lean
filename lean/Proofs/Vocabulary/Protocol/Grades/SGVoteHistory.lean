module
public import Proofs.Vocabulary.Protocol.Grades.JointHistoryGaps
public import Proofs.Vocabulary.Protocol.Grades.GuardedGradeHelpers
public import Proofs.Vocabulary.Internal.Definitions.NamedOutageEntry
import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
import Proofs.Vocabulary.Protocol.Store.JointHistoryB4B5
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.SGVoteOnHistoryTime
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time JointHistoryGapsTime
variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## G1-phase schedule arithmetic -/

/-- When `3 ≤ R`, the action of an earlier round `k < r` plus one delay is at or before round `r`'s
    G1 early cutoff. -/
theorem action_delta_le_early_g1 (S : Setup V) {k r : Round} (hkr : k < r)
    (hR : 3 ≤ S.hc.R) : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 := by
  rw [← GuardedHelpers.early_g2_add_delta S r]
  exact (action_delta_le_early_g2 S hkr hR).trans (le_add_of_nonneg_right S.E.Δ_pos.le)


end DecoupledConsensusModel.Proofs.NamedOutageHistory.SGVoteOnHistoryTime

end
