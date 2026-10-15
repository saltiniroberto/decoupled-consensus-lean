module
public import Proofs.Vocabulary.Objects.AdmissibleCore
import Proofs.Vocabulary.Execution.Runtime
import Proofs.Vocabulary.Execution.Wire
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Vote-duty heads in the voter's tree

The run block an honest Goldfish vote names as its head is in the tree of the voter's vote-duty
read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Internal
open Execution
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


theorem voteDutyHead_mem_of_emission_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} {C : NamedBlock V}
    (hCrun : NamedRun.blockInRun S rho C) {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho x (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (hroot : u.head = C.erase.root) :
    C.erase ∈ (voteDutyRead S rho x s).st.core.T := by
  obtain ⟨i, hi, ho⟩ := hemit
  let t := Protocol.vote_time S.E s
  let before := NamedRun.stateBefore S rho i x
  let read := NamedActionReads.confirmationReadFrom S before t
  let st := read.st.core
  let tree := Protocol.voter_filtered_block_tree S.E st st.s
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let H := Protocol.get_head_in_tree_with_layer
    (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
    tree votes support (st.s - 1)
  obtain ⟨-, -, hduty, -, -⟩ :=
    Proofs.Optimistic.gfVote_emitted_shape S x before t ho
  have hrootMem : Protocol.get_fg_root st.toHealing.toFG ∈ st.T := by
    have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st :=
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg before.st t
        (Proofs.NamedRuntime.stateBefore_invariants S rho i x).1
    exact Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have htree : tree ⊆ st.T := by
    dsimp only [tree]
    rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
    intro D hD
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.voter_processed_block_tree, Finset.mem_filter] at hD
    exact hD.1.1.1.1
  have hanchor : Protocol.get_sg_root_with
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      (S.hc.round_of st.s) ∈ st.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hrootMem
  have hHmem : H ∈ st.T := by
    dsimp only [H]
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hhead : u.head = H.root := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with] at hduty
    split_ifs at hduty
    · exact Option.some.inj hduty |>.symm ▸ rfl
  have hCroot : C.erase.root = H.root := by
    rw [← hroot, hhead]
  obtain ⟨D, hDerase, hDrun⟩ := Proofs.NamedStoreBridge.runBlock_of_mem_core_T
    S rho hx i
    (by simpa only [st, read, before, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHmem)
  have hDroot : D.root = C.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root C, hDerase]
    exact hCroot.symm
  have hDC : D = C :=
    adm.toNamedRootCollisionFree.root_injective D C hDrun hCrun
      D C (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hDroot
  have hCmem : C.erase ∈ before.st.core.T := by
    rw [← hDC, hDerase]
    exact hHmem
  have hstate : before = NamedRun.stateBeforeTime S rho t x :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
      S adm.toNamedScheduleWellFormed hi
  simpa only [hstate, t, voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hCmem


end Optimistic
end Proofs
end DecoupledConsensusModel

end
