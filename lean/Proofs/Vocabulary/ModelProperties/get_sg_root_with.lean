module
public import Model.Vocabulary.Protocol.ForkChoice.Head
public import Model.Vocabulary.Execution.Node
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.anchor

@[expose] public section

/-!
# Facts about `Protocol.get_sg_root_with`

The SG root under a grade contract.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The SG root under `contract` at `st` and `r` is the anchor of the contract's grade read at `st`
    and `r`. -/
theorem get_sg_root_with_eq_read_anchor (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    Protocol.get_sg_root_with contract E hc st r = (contract.read E hc st r).anchor := rfl

/-- Under the grade contract of a cache, the SG root is in the filtered tree when the FG root is. -/
theorem get_sg_root_with_gradeContract_mem_filtered
    (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round)
    (hroot : Protocol.get_fg_root st.toFG ∈ Protocol.get_filtered_block_tree st.toFG) :
    Protocol.get_sg_root_with (NamedProfile.gradeContract c) E hc st r ∈
      Protocol.get_filtered_block_tree st.toFG := by
  show DecoupledConsensusModel.Protocol.anchor E hc st r
      (DecoupledConsensusModel.Protocol.readFrame c st r).g1 ∈ _
  rcases anchor_cases E hc st r (DecoupledConsensusModel.Protocol.readFrame c st r).g1 with
    h | ⟨root, A, _, ha, h⟩
  · rw [h]
    exact hroot
  · rw [h]
    unfold DecoupledConsensusModel.Protocol.activePrefix at ha
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem ha)).1

/-- Under the grade contract of a cache, the FG root is an ancestor of the SG root. -/
theorem fg_root_Preceq_get_sg_root_with_gradeContract
    (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (Protocol.get_sg_root_with (NamedProfile.gradeContract c) E hc st r) := by
  show Block.Preceq _ (DecoupledConsensusModel.Protocol.anchor E hc st r
      (DecoupledConsensusModel.Protocol.readFrame c st r).g1)
  rcases anchor_cases E hc st r (DecoupledConsensusModel.Protocol.readFrame c st r).g1 with
    h | ⟨root, A, _, ha, h⟩
  · rw [h]
    exact Preceq_self _
  · rw [h]
    unfold DecoupledConsensusModel.Protocol.activePrefix at ha
    exact preceq_eq_true_iff_Preceq.mp (Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem ha)).1)

end DecoupledConsensusModel.Proofs.ModelProperties

end
