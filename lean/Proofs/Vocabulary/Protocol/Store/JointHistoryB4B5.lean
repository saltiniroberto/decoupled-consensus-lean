module
public import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
public import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
public import Proofs.Vocabulary.Execution.OutageActionInputs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Execution.PrefixThroughHistory

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5Time
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule arithmetic -/

theorem action_delta_le_early_g2 (S : Setup V) {k r : Round} (hkr : k < r)
    (hR : 3 ≤ S.hc.R) : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 := by
  have hnat : k * S.hc.R + 3 ≤ r * S.hc.R := by
    have h1 : (k + 1) * S.hc.R ≤ r * S.hc.R := Nat.mul_le_mul_right _ hkr
    have h2 : (k + 1) * S.hc.R = k * S.hc.R + S.hc.R := by ring
    rw [h2] at h1
    exact le_trans (Nat.add_le_add_left hR _) h1
  have hcast : ((k * S.hc.R : Nat) : Time) + 3 ≤ ((r * S.hc.R : Nat) : Time) := by
    exact_mod_cast hnat
  have heq : early S.E S.hc r .g2 - (S.a k + S.E.Δ) =
      4 * S.E.Δ * (((r * S.hc.R : Nat) : Time) - (((k * S.hc.R : Nat) : Time) + 3)) := by
    unfold DecoupledConsensusModel.Protocol.early DecoupledConsensusModel.Protocol.opening DecoupledConsensusModel.Protocol.Phase.earlyOffset
      Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a
      Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  have hnonneg : (0 : Time) ≤ 4 * S.E.Δ *
      (((r * S.hc.R : Nat) : Time) - (((k * S.hc.R : Nat) : Time) + 3)) :=
    Int.mul_nonneg (Int.mul_nonneg (by norm_num) S.E.Δ_pos.le) (sub_nonneg.mpr hcast)
  exact sub_nonneg.mp (by rw [heq]; exact hnonneg)

theorem early_g2_lt_domain_g2 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 < domain S.E S.hc r .g2 := by
  change DecoupledConsensusModel.Protocol.opening S.E S.hc r + (-5) * S.E.Δ <
    DecoupledConsensusModel.Protocol.opening S.E S.hc r + (-1) * S.E.Δ
  refine Int.add_lt_add_left ?_ _
  calc (-5 : Time) * S.E.Δ = (-1 : Time) * S.E.Δ - 4 * S.E.Δ := by ring
    _ < (-1 : Time) * S.E.Δ := sub_lt_self _ (Int.mul_pos (by norm_num) S.E.Δ_pos)


#print axioms action_delta_le_early_g2
end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5Time

end
