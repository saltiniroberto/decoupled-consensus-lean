import Model.Vocabulary.Protocol.ForkChoice.Views
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Objects.Ancestry

/-!
# Facts on `Protocol.voter_processed_block_tree`

The blocks of a Goldfish store's tree that the vote duty of a slot may descend through.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.voter_processed_block_tree

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every block of the voter's processed tree of the Goldfish store `gs` at slot `s` is in `gs.T`. -/
theorem mem_T_of_mem_voter_processed_block_tree (E : Env V) (gs : Protocol.GoldfishStore V)
    (s : Slot) {B : Block V} (h : B ∈ Protocol.voter_processed_block_tree E gs s) :
    B ∈ gs.T := by
  unfold Protocol.voter_processed_block_tree at h
  exact (Finset.mem_filter.mp h).1

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block of `gs.T` that `gs` stamped before the view freeze of slot `s − 1` is in the voter's
    processed tree of `gs` at slot `s`. -/
theorem mem_voter_processed_block_tree_of_stamped (E : Env V) (gs : Protocol.GoldfishStore V)
    (s : Slot) {B : Block V} (hT : B ∈ gs.T)
    (hst : stampedBefore gs.timestamp_block (Protocol.view_freeze E (s - 1)) B = true) :
    B ∈ Protocol.voter_processed_block_tree E gs s := by
  unfold Protocol.voter_processed_block_tree
  exact Finset.mem_filter.mpr ⟨hT, Or.inl hst⟩


/-- A block `B` of the voter's processed tree of `gs` at slot `s` is in `gs.T`, and either `gs`
    stamped `B` before the view freeze of slot `s − 1`, or `B` is an ancestor of, or equal to, some
    block of `gs.T` of slot `s`. -/
theorem voter_processed_block_tree_cases (E : Env V) (gs : Protocol.GoldfishStore V) (s : Slot)
    {B : Block V} (h : B ∈ Protocol.voter_processed_block_tree E gs s) :
    B ∈ gs.T ∧
      (stampedBefore gs.timestamp_block (Protocol.view_freeze E (s - 1)) B = true ∨
        ∃ P ∈ gs.T, P.slot = s ∧ Block.Preceq B P) := by
  unfold Protocol.voter_processed_block_tree at h
  obtain ⟨hT, hcase⟩ := Finset.mem_filter.mp h
  refine ⟨hT, ?_⟩
  rcases hcase with hst | ⟨P, hP, hBP⟩
  · exact Or.inl hst
  · exact Or.inr ⟨P, (Finset.mem_filter.mp hP).1, (Finset.mem_filter.mp hP).2, hBP⟩

/-- If `B` and `P` are in `gs.T`, `P` has slot `s`, and `B` is an ancestor of `P` or `P` itself,
    then `B` is in the voter's processed tree of `gs` at slot `s`. -/
theorem mem_voter_processed_block_tree_of_proposal (E : Env V) (gs : Protocol.GoldfishStore V)
    (s : Slot) {B P : Block V} (hT : B ∈ gs.T) (hP : P ∈ gs.T) (hPs : P.slot = s)
    (hBP : Block.Preceq B P) :
    B ∈ Protocol.voter_processed_block_tree E gs s := by
  unfold Protocol.voter_processed_block_tree
  exact Finset.mem_filter.mpr ⟨hT, Or.inr ⟨P, Finset.mem_filter.mpr ⟨hP, hPs⟩, hBP⟩⟩

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block of `gs.T` whose slot is `s` is in the voter's processed tree of `gs` at slot `s`. -/
theorem mem_voter_processed_block_tree_of_slot (E : Env V) (gs : Protocol.GoldfishStore V)
    (s : Slot) {B : Block V} (hB : B ∈ gs.T) (hs : B.slot = s) :
    B ∈ Protocol.voter_processed_block_tree E gs s := by
  unfold Protocol.voter_processed_block_tree
  exact Finset.mem_filter.mpr
    ⟨hB, Or.inr ⟨B, Finset.mem_filter.mpr ⟨hB, hs⟩, Block.preceq_self B⟩⟩


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts
