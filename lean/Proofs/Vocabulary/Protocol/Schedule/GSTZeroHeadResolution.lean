module
public import Proofs.Vocabulary.Objects.BlockVisibilityCore
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Honest heads resolved at later stores

When every honest head of slot `s` is available to an honest node before the slot-`s` support
cutoff, every such head resolves in that node's store at any later time.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Every honest head of slot `s` is genesis or was admitted by `v` before `Gamma`. -/
def HonestHeadsAvailableBefore (S : Setup V) (rho : Run V) (s : Slot)
    (v : V) (Gamma : Time) : Prop :=
  ∀ X : Block V, Proofs.Optimistic.HonestHead S rho s X →
    X = Block.genesis ∨ AdmittedBefore S rho v X Gamma


/-- If every honest head of slot `s` is available to an honest `v` before the slot-`s` support
    cutoff, the heads resolve in `v`'s store before any `Gamma` at or after that cutoff. -/
theorem headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) (s : Slot) {Gamma : Time}
    (hcut : Protocol.support_cutoff S.E s ≤ Gamma)
    (havailable : HonestHeadsAvailableBefore S rho s v
      (Protocol.support_cutoff S.E s)) :
    Proofs.Optimistic.HeadsResolveIn S rho s
      (rho.storeBeforeTime S v Gamma).T
      (rho.storeBeforeTime S v Gamma).timestamp_block := by
  let cutoff := Protocol.support_cutoff S.E s
  have htransport : ∀ X : Block V, Proofs.Optimistic.HonestHead S rho s X →
      X ∈ (rho.storeBeforeTime S v Gamma).T ∧
        stampedBefore (rho.storeBeforeTime S v Gamma).timestamp_block cutoff X = true := by
    intro X hX
    rcases havailable X hX with rfl | hadmit
    · exact genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedScheduleWellFormed v Gamma cutoff
    · exact admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
        hadmit hcut
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hstore : rho.storeBeforeTime S v Gamma = (rho.stateBefore S n v).st :=
    congrArg NamedNodeState.st (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take
      S adm.toNamedScheduleWellFormed Gamma) v)
  have hrun : ∀ X : Block V, X ∈ (rho.storeBeforeTime S v Gamma).T →
      ∃ C : NamedBlock V, C.erase = X ∧ RunBlock S rho C := by
    intro X hX
    have hXT : X ∈ (rho.stateBefore S n v).st.core.T := by
      rw [← hstore]; exact hX
    obtain ⟨D, hDbodies, hDerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hXT
    exact ⟨D, hDerase, D, Or.inr ⟨v, hv, n, hDbodies⟩, Proofs.NamedAncestry.named_self D⟩
  apply Proofs.Optimistic.headsResolveIn_of S rho s
  · intro X hX
    exact (htransport X hX).1
  · intro X Y hX hY hroot
    obtain ⟨CX, hCX, hCXrun⟩ := hrun X hX
    obtain ⟨CY, hCY, hCYrun⟩ := hrun Y hY
    have hrootNamed : CX.root = CY.root := by
      rw [← Proofs.NamedWire.erase_root CX, ← Proofs.NamedWire.erase_root CY, hCX, hCY]
      exact hroot
    have hCXY : CX = CY :=
      adm.toNamedRootCollisionFree.root_injective CX CY hCXrun hCYrun CX CY
        (Or.inl (Proofs.NamedAncestry.named_self CX)) (Or.inr (Proofs.NamedAncestry.named_self CY)) hrootNamed
    rw [← hCX, ← hCY, hCXY]
  · intro X hX
    exact (htransport X hX).2

theorem headsResolveIn_storeBeforeTime_of_availableBefore_at
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (s : Slot) {Gamma : Time}
    (hcut : Protocol.support_cutoff S.E s ≤ Gamma)
    (havailable : HonestHeadsAvailableBefore S rho s v
      (Protocol.support_cutoff S.E s)) :
    Proofs.Optimistic.HeadsResolveIn S rho s
      (rho.storeBeforeTime S v Gamma).T
      (rho.storeBeforeTime S v Gamma).timestamp_block :=
  headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    S adm.toNamedAdmissibleCore hv s hcut havailable


end Protocol
end DecoupledConsensusModel

end
