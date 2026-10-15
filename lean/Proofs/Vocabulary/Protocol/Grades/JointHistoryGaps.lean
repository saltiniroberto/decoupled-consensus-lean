module
public import Proofs.Vocabulary.Protocol.Store.JointHistoryB4B5
public import Model.Vocabulary.Execution.Setup
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Execution.PrefixThroughHistory
public import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
public import Proofs.Vocabulary.Internal.Definitions.NamedJointOutage

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryGapsTime
open Execution Internal.NamedOutageEntry Internal.NamedJointOutage Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time
variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## `Setup.a` is strictly monotone in the round -/

theorem setup_a_strictMono (S : Setup V) : StrictMono S.a := by
  intro r1 r2 hr
  show S.hc.a S.E.Δ r1 < S.hc.a S.E.Δ r2
  have hR : 0 < S.hc.R := lt_of_lt_of_le (by norm_num) S.hc.R_ge_two
  have hnat : r1 * S.hc.R < r2 * S.hc.R := (Nat.mul_lt_mul_right hR).mpr hr
  have hcast : ((r1 * S.hc.R : Nat) : Time) < ((r2 * S.hc.R : Nat) : Time) := by
    exact_mod_cast hnat
  have heq : S.hc.a S.E.Δ r2 - S.hc.a S.E.Δ r1 =
      4 * S.E.Δ * (((r2 * S.hc.R : Nat) : Time) - ((r1 * S.hc.R : Nat) : Time)) := by
    unfold Protocol.HealConfig.a Protocol.HealConfig.opening_slot
      DecoupledConsensusModel.slotStart
    push_cast
    ring
  have hpos : (0 : Time) < 4 * S.E.Δ *
      (((r2 * S.hc.R : Nat) : Time) - ((r1 * S.hc.R : Nat) : Time)) :=
    Int.mul_pos (Int.mul_pos (by norm_num) S.E.Δ_pos) (sub_pos.mpr hcast)
  have hdiff : (0 : Time) < S.hc.a S.E.Δ r2 - S.hc.a S.E.Δ r1 := by rw [heq]; exact hpos
  exact sub_pos.mp hdiff

theorem setup_a_injective (S : Setup V) {r1 r2 : Round} (h : S.a r1 = S.a r2) : r1 = r2 :=
  (setup_a_strictMono S).injective h


end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryGapsTime

end
