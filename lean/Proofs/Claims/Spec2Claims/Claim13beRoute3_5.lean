import Proofs.Claims.Spec2Claims.Claim13beRoute3_4
import Proofs.Vocabulary.Execution.NamedAncestry
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Vocabulary.Protocol.Handlers.Receipt
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_commitBlock
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with
import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
import Proofs.Vocabulary.ModelProperties.on_block_checked_using
import Proofs.Vocabulary.ModelProperties.NamedStore_commitBlock
import Proofs.Vocabulary.ModelProperties.NamedNode_process
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Claims.Spec2Claims.Claim13bModel_on_block_using_s2

/-!
# The shape of a tree's blocks

The invariant `TreeBlockShaped`: every block of a store's tree, genesis apart, names its slot's
proposer, has a parent of a strictly earlier slot, and carries only attestations of its own slot's
round or an earlier one. Every handler, the tick and the receipt of an object keep it.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every block a store's tree holds, genesis apart, names its slot's proposer, has a parent of a
    strictly earlier slot, and carries only attestations of its own slot's round or an earlier one. -/
def TreeBlockShaped (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) : Prop :=
  ∀ B : Block V, B ∈ st.T → B ≠ Block.genesis →
    B.proposer? = some (E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
      Protocol.carried_attestations_admissible hc B = true

/-- If the store `st` satisfies `TreeBlockShaped`, so does the store `st'`. -/
def TreeBlockShapedStep (E : Env V) (hc : Protocol.HealConfig) (st st' : Protocol.Store V) :
    Prop :=
  TreeBlockShaped E hc st → TreeBlockShaped E hc st'

namespace TreeBlockShapedStep

variable {E : Env V} {hc : Protocol.HealConfig} {st st' st'' : Protocol.Store V}

/-- Leaving the store alone keeps the invariant. -/
theorem refl' (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) :
    TreeBlockShapedStep E hc st st := fun h => h

/-- Two transitions that each keep the invariant keep it composed. -/
theorem trans' (h₁ : TreeBlockShapedStep E hc st st') (h₂ : TreeBlockShapedStep E hc st' st'') :
    TreeBlockShapedStep E hc st st'' := fun h => h₂ (h₁ h)

/-- A transition whose tree is a subset of the tree before it keeps the invariant. -/
theorem of_subset (hT : st'.T ⊆ st.T) : TreeBlockShapedStep E hc st st' :=
  fun h B hB => h B (hT hB)

/-- A transition that leaves `Σ.T` as it was keeps the invariant. -/
theorem of_eq (hT : st'.T = st.T) : TreeBlockShapedStep E hc st st' :=
  of_subset (fun _ hx => by rw [hT] at hx; exact hx)

end TreeBlockShapedStep

/-- Stamping a store's clock keeps the invariant. -/
theorem treeBlockShapedStep_setClock (E : Env V) (hc : Protocol.HealConfig)
    (stn : Protocol.NamedStore V) (t : Int) :
    TreeBlockShapedStep E hc stn.core (Protocol.NamedStore.setClock E stn t).core :=
  TreeBlockShapedStep.of_subset (fun _ hx => by rw [Proofs.ModelProperties.setClock_core_T] at hx; exact hx)

/-- The shared block-processing body keeps the invariant, given that the block's carried
    attestations are admissible. -/
theorem treeBlockShapedStep_on_block_using (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (build : Protocol.ChainState V → Protocol.ChainState V)
    (hadm : Protocol.carried_attestations_admissible hc B = true) :
    TreeBlockShapedStep E hc st (Protocol.on_block_using E st B build) := by
  intro h
  by_cases h1 : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B build (Or.inl h1)]
    exact h
  by_cases h2 : (!Block.preceq st.F B) = true
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B build (Or.inr (Or.inl h2))]
    exact h
  by_cases h3 : B.proposer? ≠ some (E.proposer B.slot)
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B build (Or.inr (Or.inr (Or.inl h3)))]
    exact h
  by_cases h4 : ¬ (B.parent.slot < B.slot)
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B build (Or.inr (Or.inr (Or.inr h4)))]
    exact h
  intro C hC hCne
  rcases on_block_using_tree_cases E st B build with hT | hT
  · rw [hT] at hC
    exact h C hC hCne
  · rw [hT] at hC
    rcases Finset.mem_insert.mp hC with rfl | hC'
    · exact ⟨not_not.mp h3, not_not.mp h4, hadm⟩
    · exact h C hC' hCne

/-- The carried-round wrapper keeps the invariant. -/
theorem treeBlockShapedStep_on_block_checked_using (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (build : Protocol.ChainState V → Protocol.ChainState V) :
    TreeBlockShapedStep E hc st
      (Protocol.on_block_checked_using
        (fun current => Protocol.on_block_using E current B build) hc st B) := by
  by_cases hvalid : Protocol.carried_attestations_admissible hc B = true
  · rw [on_block_checked_using_eq_handle _ hc st hvalid]
    exact treeBlockShapedStep_on_block_using E hc st B build hvalid
  · have hfalse : Protocol.carried_attestations_admissible hc B = false :=
      Bool.eq_false_of_not_eq_true hvalid
    rw [on_block_checked_using_eq_self _ hc st hvalid]
    exact TreeBlockShapedStep.refl' E hc st

/-- Receiving a named block keeps the invariant. -/
theorem treeBlockShapedStep_process_block_core (S : Setup V) (stn : Protocol.NamedStore V)
    (B : NamedBlock V) :
    TreeBlockShapedStep S.E S.hc stn.core
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg stn B).core := by
  by_cases hp : B.parent ∉ stn.bodies
  · rw [Proofs.ModelProperties.process_block_core_of_parent_not_mem S.E S.hc S.cfg hp]
    exact TreeBlockShapedStep.refl' S.E S.hc stn.core
  · rw [Proofs.ModelProperties.process_block_core_of_parent_mem S.E S.hc S.cfg (not_not.mp hp)]
    rw [commitBlock_core]
    exact treeBlockShapedStep_on_block_checked_using S.E S.hc stn.core B.erase _

/-- Admitting an attestation keeps the invariant. -/
theorem treeBlockShapedStep_admit_row (E : Env V) (hc : Protocol.HealConfig)
    (stn : Protocol.NamedStore V) (a : NamedAttestation V) :
    TreeBlockShapedStep E hc stn.core (Protocol.NamedAdmission.admit_row hc stn a).core :=
  TreeBlockShapedStep.of_eq (Protocol.admit_row_core_T hc stn a)

/-- Admitting a list of attestations keeps the invariant. -/
theorem treeBlockShapedStep_admit_rows (E : Env V) (hc : Protocol.HealConfig)
    (stn : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    TreeBlockShapedStep E hc stn.core (Protocol.NamedAdmission.admit_rows hc stn rows).core :=
  TreeBlockShapedStep.of_eq (Protocol.admit_rows_bodies_and_core_T hc rows stn).2

/-- Receiving a named block and admitting the attestations it carries keeps the invariant. -/
theorem treeBlockShapedStep_on_block_with (adm : Protocol.CarriedAdmission) (S : Setup V)
    (stn : Protocol.NamedStore V) (B : NamedBlock V) :
    TreeBlockShapedStep S.E S.hc stn.core
      (Protocol.NamedAdmission.on_block_with adm S.E S.hc S.cfg stn B).core := by
  rcases on_block_with_cases adm S.E S.hc S.cfg stn B with h | h <;> rw [h]
  · exact TreeBlockShapedStep.trans' (treeBlockShapedStep_process_block_core S stn B)
      (treeBlockShapedStep_admit_rows S.E S.hc _ B.attestations)
  · exact treeBlockShapedStep_process_block_core S stn B

/-- The proposal duty keeps the invariant. -/
theorem treeBlockShapedStep_named_propose_block_with (contract : Protocol.GradeContract V)
    (S : Setup V) (nd : Protocol.Node V) (stn : Protocol.NamedStore V) :
    TreeBlockShapedStep S.E S.hc stn.core
      (Protocol.NamedDuties.propose_block_with contract S.E S.hc S.cfg nd stn).1.core := by
  cases hp : Protocol.NamedActions.proposal_with contract .poolAndCarried S.E S.hc nd stn with
  | none =>
      rw [Proofs.ModelProperties.propose_block_with_fst_of_none _ _ _ _ _ _ hp]
      exact TreeBlockShapedStep.refl' S.E S.hc stn.core
  | some B =>
      rw [Proofs.ModelProperties.propose_block_with_fst_of_some _ _ _ _ _ _ hp]
      exact treeBlockShapedStep_on_block_with .alsoCarried S stn _

/-- The Goldfish vote duty keeps the invariant. -/
theorem treeBlockShapedStep_named_goldfish_vote_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (stn : Protocol.NamedStore V) :
    TreeBlockShapedStep E hc stn.core
      (Protocol.NamedDuties.goldfish_vote_with contract E hc nd stn).1.core :=
  TreeBlockShapedStep.of_eq (by
    rw [namedDuties_goldfish_vote_with_fst_core]
    exact Protocol.goldfish_vote_with_T contract E hc nd stn.core)

/-- The confirmation duty keeps the invariant. -/
theorem treeBlockShapedStep_named_update_confirmation_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (stn : Protocol.NamedStore V) (s : Slot) :
    TreeBlockShapedStep E hc stn.core
      (Protocol.NamedDuties.update_confirmation_with contract E hc stn s).core :=
  TreeBlockShapedStep.of_eq
    (by rw [namedDuties_update_confirmation_with_core, update_confirmation_with_T])

/-- The attestation duty keeps the invariant. -/
theorem treeBlockShapedStep_named_attest_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (stn : Protocol.NamedStore V) (record : Protocol.NamedRecord) :
    TreeBlockShapedStep E hc stn.core
      (Protocol.NamedDuties.attest_with contract E hc nd stn record).1.core :=
  by rw [namedDuties_attest_with_fst]; exact treeBlockShapedStep_admit_row E hc stn _

/-- A complete named tick keeps the invariant, at any instant. -/
theorem treeBlockShapedStep_named_tick (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (stn : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Int) :
    TreeBlockShapedStep S.E S.hc stn.core
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd stn record t).1.core := by
  have h0 : TreeBlockShapedStep S.E S.hc stn.core
      (Protocol.NamedStore.setClock S.E stn t).core :=
    treeBlockShapedStep_setClock S.E S.hc stn t
  exact named_tick_preserves (fun st' => TreeBlockShapedStep S.E S.hc stn.core st'.core)
    gc S.E S.hc S.cfg nd
    (fun st' h => TreeBlockShapedStep.trans' h
      (treeBlockShapedStep_named_propose_block_with gc S nd st'))
    (fun st' h => TreeBlockShapedStep.trans' h
      (treeBlockShapedStep_named_goldfish_vote_with gc S.E S.hc nd st'))
    (fun st' s h => TreeBlockShapedStep.trans' h
      (treeBlockShapedStep_named_update_confirmation_with gc S.E S.hc st' s))
    (fun st' record' h => TreeBlockShapedStep.trans' h
      (treeBlockShapedStep_named_attest_with gc S.E S.hc nd st' record'))
    stn record t h0

/-- The node-level tick keeps the invariant. -/
theorem treeBlockShapedStep_node_tick (S' : Setup V) (v : V) (n : NamedNodeState V) (t : Int) :
    TreeBlockShapedStep S'.E S'.hc n.st.core (NamedNode.tick S' v n t).1.st.core := by
  obtain ⟨gc, hgc⟩ : ∃ gc : Protocol.GradeContract V,
      (NamedNode.tick S' v n t).1.st
        = (Protocol.NamedTick.tick gc S'.E S'.hc S'.cfg (S'.node v) n.st n.record t).1 :=
    ⟨_, namedNode_tick_st S' v n t⟩
  rw [hgc]
  exact treeBlockShapedStep_named_tick gc S' (S'.node v) n.st n.record t

/-- The receipt of any object keeps the invariant. -/
theorem treeBlockShapedStep_node_process (S' : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) :
    TreeBlockShapedStep S'.E S'.hc n.st.core (NamedNode.process S' n o).st.core := by
  cases o with
  | block B =>
      rw [Proofs.ModelProperties.process_st, Proofs.ModelProperties.process_block]
      exact treeBlockShapedStep_on_block_with .alsoCarried S' n.st B
  | gfVote u =>
      rw [Proofs.ModelProperties.process_st, Proofs.ModelProperties.process_gfVote]
      exact TreeBlockShapedStep.of_eq (Proofs.on_goldfish_vote_checked_T S'.E n.st.core u)
  | attest a =>
      rw [Proofs.ModelProperties.process_st, Proofs.ModelProperties.process_attest]
      exact treeBlockShapedStep_admit_row S'.E S'.hc n.st a

end DecoupledConsensusModel.Sts
