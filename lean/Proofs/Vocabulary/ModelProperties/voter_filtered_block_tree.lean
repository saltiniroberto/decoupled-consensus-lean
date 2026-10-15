module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-!
# Facts about the voter's candidate tree

Facts about `Protocol.voter_filtered_block_tree`, the filtered tree drawn from the blocks the voter
has processed.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The voter's candidate tree at the store `st` and slot `s` is a subset of `st`'s block tree. -/
theorem voter_filtered_block_tree_subset (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Protocol.voter_filtered_block_tree E st s ⊆ st.T := by
  intro D hD
  unfold Protocol.voter_filtered_block_tree at hD
  have hp := Proofs.Records.get_filtered_block_tree_from_subset _ _ hD
  unfold Protocol.voter_processed_block_tree at hp
  exact (Finset.mem_filter.mp hp).1

end DecoupledConsensusModel.Proofs.ModelProperties

end
