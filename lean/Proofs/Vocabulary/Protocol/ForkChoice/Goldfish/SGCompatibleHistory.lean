module
public import Proofs.Vocabulary.Protocol.Store.HonestPoolActionBridge
import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# SG compatibility from honest emissions

The condition that every honest SG emission of a round is compatible with a block `B`, and what it
gives for the honest SG votes in a store.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every honest validator that emits its round-`r` attestation at `S.a r` chooses an SG block
    compatible with `B`. -/
def HonestSGEmissionsCompatibleAtRound
    (S : Setup V) (rho : Run V) (r : Round) (B : Block V) : Prop :=
  ∀ v ∈ rho.honest,
    rho.emits S v (Object.attest (actionAttestationAt S rho v r)) (S.a r) →
      Block.compatible (actionSGBlockAt S rho v r) B = true

/-- Under `HonestSGEmissionsCompatibleAtRound S rho r B`, the confirmed root of every honest
    round-`r` SG vote in `w`'s store before time `time` is compatible with `B` in that store's tree. -/
theorem rootCompatible_of_emittedSGHistory_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {time : Time} {r : Round} {B : Block V}
    (hhistory : HonestSGEmissionsCompatibleAtRound S rho r B)
    {u : Protocol.SGVote V}
    (hu : u ∈ (rho.storeBeforeTime S w time).toHealing.sg_votes r)
    (huh : u.val_index ∈ rho.honest) :
    rootCompatible (rho.storeBeforeTime S w time).T B u.confirmed = true := by
  obtain ⟨huEq, hemit⟩ :=
    honestSGVote_actionEmission_of_mem_storeBeforeTime S adm huh hu rfl
  have hcompat := hhistory u.val_index huh hemit
  let C := actionSGBlockAt S rho u.val_index r
  have hconfirmed : u.confirmed = some C.root := by
    rw [huEq]
    rfl
  rw [hconfirmed]
  cases hfind : Block.find? (rho.storeBeforeTime S w time).T C.root with
  | none => simp only [rootCompatible, hfind]
  | some X =>
      have hXmem := find?_mem hfind
      obtain ⟨Xn, hXerase, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw time hXmem
      have hCmem : C ∈ (rho.storeBeforeTime S u.val_index (S.a r)).T :=
        actionSGBlockAt_mem_storeBeforeTime S rho u.val_index r
      obtain ⟨Cn, hCerase, hCrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed huh (S.a r) hCmem
      have hroot : Xn.root = Cn.root := by
        rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
          hXerase, hCerase]
        exact find?_root hfind
      have hnamed := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
        Xn Cn hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self Cn)) hroot
      have hXC : X = C := hXerase.symm.trans
        ((congrArg NamedBlock.erase hnamed).trans hCerase)
      simpa only [rootCompatible, hfind, hXC] using hcompat


#print axioms rootCompatible_of_emittedSGHistory_at_read

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
