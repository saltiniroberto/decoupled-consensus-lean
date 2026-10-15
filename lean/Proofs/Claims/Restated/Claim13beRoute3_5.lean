import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Redelivery
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_5

/-!
# The block-shape invariant and block admission

Every store of an execution satisfies `TreeBlockShaped`, and a delivered block meeting the slot,
finalization and shape conditions is among the receiver's bodies at the next step, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Sts.TreeBlockShapedStep
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Leaving the store alone keeps the invariant. -/
theorem TreeBlockShapedStep.refl' (facts : Record.Facts M) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) :
    Restated.TreeBlockShapedStep M E hc st st := fun h => h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The initial store satisfies `TreeBlockShaped`. -/
theorem treeBlockShaped_init (facts : Record.Facts M) (E : Env V) (hc : Protocol.HealConfig) :
    Restated.TreeBlockShaped M E hc (M.ns_initial : M.NS).core := by
  intro B hB hne
  rw [facts.hd.initial_core_T, Finset.mem_singleton] at hB
  exact absurd hB hne

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- One step of an execution keeps `TreeBlockShaped` at every validator's store. -/
theorem treeBlockShapedStep_sts_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) :
    Restated.TreeBlockShapedStep M S.E S.hc (x[i][w].st).st.core (x[i + 1][w].st).st.core := by
  rcases Record.st_succ_cases M S Sched x w i with hst | hst | ⟨t, out, hout | hout, hst⟩ | ⟨o, ho⟩
  · rw [hst]; exact Restated.TreeBlockShapedStep.refl' facts _ _ _
  · rw [hst, (facts.nd.wake_st_record _).1]; exact Restated.TreeBlockShapedStep.refl' facts _ _ _
  · rw [hst]
    exact facts.nd.treeBlockShapedStep_node_tick (Setup.alwaysAwake S) w (x[i][w].st) t out hout
  · rw [hst]
    have h := facts.nd.treeBlockShapedStep_node_tick (Setup.alwaysAwake S) w (M.wake (x[i][w].st))
      t out hout
    rwa [(facts.nd.wake_st_record _).1] at h
  · exact facts.nd.treeBlockShapedStep_node_process (Setup.alwaysAwake S) (x[i][w].st) o _ ho

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every block other than genesis in any validator's tree names its
    slot's proposer, has a parent of a strictly earlier slot, and includes only attestations of its
    own slot's round or an earlier one. -/
theorem treeBlockShaped_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) :
    Restated.TreeBlockShaped M S.E S.hc (x[m][w].st).st.core := by
  induction m with
  | zero =>
      rw [Record.st_zero M S Sched x w, facts.nd.initial_st_inclG2]
      exact Restated.treeBlockShaped_init facts S.E S.hc
  | succ i ih => exact Restated.treeBlockShapedStep_sts_succ facts S Sched x i w ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A block some step delivers to some validator is a block in play in the execution. -/
theorem blockInLog_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {d : Nat} {w u : V} {B : NamedBlock V}
    (hlbl : x.lbl d
      = AtomicAction.deliver w (⟨u, NamedObject.block B⟩ : SignedMsg V (NamedObject V))) :
    Restated.blockInLog M S Sched x B :=
  ⟨B, Or.inl ⟨d, ⟨u, NamedObject.block B⟩, (Restated.sent_of_deliver facts S Sched x hlbl).1, rfl⟩,
    namedBlock_Preceq_self B⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the erasure of a named block in play is in the tree of a validator honest up to the reading
    step, then that named block is among the validator's bodies. -/
theorem mem_bodies_of_mem_T_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {n : Nat} {w : V} (hwh : Restated.HonestThrough M Sched x n w) {B : NamedBlock V}
    (hlog : Restated.blockInLog M S Sched x B) (hmem : B.erase ∈ (x[n][w].st).st.core.T) :
    B ∈ (x[n][w].st).st.bodies := by
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x n w hmem
  have hroot : Restated.RootCollisionFreeInLog M S Sched x := hexec.idealization
  have hself : ∀ C : NamedBlock V, NamedBlock.Preceq C C := Proofs.NamedAncestry.named_self
  have hDB : D = B :=
    hroot.root_injective D B (Restated.blockInLog_of_mem_bodies facts S Sched hwh hD) hlog D B
      (Or.inl (hself D)) (Or.inr (hself B))
      (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDe])
  rw [← hDB]
  exact hD

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a step delivers the named block `B` to a validator honest up to that step, `B`'s slot is at
    or before the slot of the receiver's store, the receiver's finalized block is an ancestor of
    `B`, `B` names its slot's proposer, `B`'s parent is of a strictly earlier slot, and every
    attestation `B` includes is of its own slot's round or an earlier one, then `B` is among the
    receiver's bodies at the next step. -/
theorem block_admitted_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {d : Nat} {w u : V} {B : NamedBlock V}
    (hlbl : x.lbl d
      = AtomicAction.deliver w (⟨u, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hwh : Restated.HonestThrough M Sched x d w)
    (hslot : B.erase.slot ≤ (x[d][w].st).st.core.s)
    (hfin : Block.preceq (x[d][w].st).st.core.F B.erase = true)
    (hprop : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hpslot : B.erase.parent.slot < B.erase.slot)
    (hadm : M.carried_attestations_admissible S.hc B.erase = true) :
    B ∈ (x[d + 1][w].st).st.bodies := by
  have _hr_0 : M.reachedNode (x[d][w].st) := Record.reachedNode_sts facts S Sched x d w
  classical
  have hparent : B.parent ∈ (x[d][w].st).st.bodies := hexec.deps d w _ hlbl B rfl
  have hcore : B ∈ (M.ns_process_block_core S.E S.hc S.cfg
      (x[d][w].st).st B).bodies := by
    rw [facts.hd.process_block_core_bodies_eq_commit S.E S.hc S.cfg hparent]
    by_cases hmemT : B.erase ∈ (x[d][w].st).st.core.T
    · have hB : B ∈ (x[d][w].st).st.bodies :=
        Restated.mem_bodies_of_mem_T_honest facts S Sched x hexec hwh (Restated.blockInLog_of_deliver facts S Sched x hlbl)
          hmemT
      exact facts.hd.mem_commitBlock_bodies_of_mem S.E S.hc S.cfg rfl hB
    · have hparT : B.erase.parent ∈ (x[d][w].st).st.core.T := by
        rw [Proofs.NamedWire.erase_parent, Restated.bodies_image_eq_T facts S Sched x d w]
        exact Finset.mem_image_of_mem NamedBlock.erase hparent
      have hadmT : B.erase ∈ (M.on_block_checked_using
          (fun current => M.on_block_using S.E current B.erase
            (fun parentState => M.named_transition S.E S.cfg parentState B))
          S.hc (x[d][w].st).st.core B.erase).T := by
        rw [facts.hd.on_block_checked_using_eq_handle _ S.hc _ hadm]
        exact facts.hd.mem_T_on_block_using S.E (x[d][w].st).st.core B.erase _ hslot hmemT hparT hfin
          hprop hpslot (facts.sto.rootFresh_of_distinct _ _ (fun C hC hr => by
            obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x d w hC
            have hDB : D = B :=
              hexec.idealization.root_injective D B
                (Restated.blockInLog_of_mem_bodies facts S Sched hwh hD)
                (Restated.blockInLog_of_deliver facts S Sched x hlbl) D B
                (Or.inl (Proofs.NamedAncestry.named_self D))
                (Or.inr (Proofs.NamedAncestry.named_self B))
                (by rw [← Proofs.NamedWire.erase_root D, hDe, hr, Proofs.NamedWire.erase_root B])
            rw [← hDe, hDB]))
      refine facts.hd.mem_commitBlock_bodies_of_fresh S.E S.hc S.cfg rfl ⟨hmemT, ?_⟩
      have _hr_s1 := facts.nd.reachedStore_of_node _ (Record.reachedNode_sts facts S Sched x (d) w)
      rw [facts.hd.sameCore_T (facts.hd.process_block_core_of_parent_mem S.E S.hc S.cfg hparent),
        facts.hd.commit_core _ _ B
          (facts.hd.on_block_checked_using_store_part S.E S.hc S.cfg (x[d][w].st).st B)]
      exact hadmT
  rcases Restated.st_succ_of_deliver facts S Sched x hlbl with hout | ⟨hnone, -⟩
  · rw [facts.nd.process_st _ _ _ _ hout, facts.nd.make_grades_compatible_with_finalized_bodies]
    show B ∈ (M.receipt_process (Setup.alwaysAwake S) (x[d][w].st).st (NamedObject.block B)).bodies
    rw [facts.nd.process_block]
    exact facts.hd.mem_on_block_with_bodies_of_mem_core .alsoCarried S.E S.hc S.cfg _ B hcore
  ·
    obtain ⟨n', hn'⟩ := Restated.receipt_outcome_of_deliver_honest facts S Sched x hexec.idealization hlbl hwh
    exact absurd hn' (hnone n')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If some validator's tree, at some step, holds the erasure of a named block other than genesis,
    and that block is delivered to a validator honest up to the delivery whose store is at a slot at
    or after the block's and whose finalized block is an ancestor of the block, then the block is
    among the receiver's bodies at the next step. -/
theorem block_admitted_of_deliver_of_tree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {d n : Nat} {w u q : V} {B : NamedBlock V}
    (hlbl : x.lbl d
      = AtomicAction.deliver w (⟨u, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hwh : Restated.HonestThrough M Sched x d w)
    (hmem : B.erase ∈ (x[n][q].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hslot : B.erase.slot ≤ (x[d][w].st).st.core.s)
    (hfin : Block.preceq (x[d][w].st).st.core.F B.erase = true) :
    B ∈ (x[d + 1][w].st).st.bodies := by
  have hne : B.erase ≠ Block.genesis := fun h => hgen (eq_named_genesis_of_erase_eq_genesis h)
  obtain ⟨hprop, hpslot, hadm⟩ := Restated.treeBlockShaped_sts facts S Sched x n q B.erase hmem hne
  exact Restated.block_admitted_of_deliver facts S Sched x hexec hlbl hwh hslot hfin hprop hpslot hadm

end

end DecoupledConsensusModel.Sts.Restated
