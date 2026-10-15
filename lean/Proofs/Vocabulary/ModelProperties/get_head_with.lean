module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-!
# Facts about `Protocol.get_head_with`

The composed head over the full tree under a grade contract.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the SG root under `contract` at `st`'s own round is in `st`'s filtered tree, so is the
    composed head under `contract` at `st`. -/
theorem get_head_with_mem_filtered (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (votes support : Finset (GoldfishVote V)) (k : Slot)
    (hanchor : Protocol.get_sg_root_with contract E hc st (hc.round_of st.s) ∈
      Protocol.get_filtered_block_tree st.toFG) :
    Protocol.get_head_with contract E hc st votes support k ∈
      Protocol.get_filtered_block_tree st.toFG := by
  unfold Protocol.get_head_with Protocol.get_head_in_tree_with_layer
  exact Proofs.Records.ghost_mem_of _ _ hanchor (Finset.Subset.refl _)

end DecoupledConsensusModel.Proofs.ModelProperties

end
