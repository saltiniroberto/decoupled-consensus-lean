import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.on_block_using`

The raw block handler's effect on the tree: it leaves the tree alone or inserts exactly its own
block, and it inserts the block once none of its refusal conditions holds.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_block_using

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- After `Protocol.on_block_using`, the tree is either the tree it started with or that tree with
    the incoming block added. -/
theorem on_block_using_tree_cases (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : Protocol.ChainState V → Protocol.ChainState V) :
    (Protocol.on_block_using E st B build).T = st.T ∨
      (Protocol.on_block_using E st B build).T = insert B st.T := by
  simp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact Or.inl rfl
    | exact Or.inr (by rw [Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T E])

/-- If the incoming block's slot is at most the store's, the block is not already in the tree, its
    parent is, the store's finalized block is an ancestor of it, its `proposer?` field is its slot's
    proposer and its parent is of a strictly earlier slot, then the block is in the tree
    `Protocol.on_block_using` returns. -/
theorem mem_T_on_block_using (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : Protocol.ChainState V → Protocol.ChainState V)
    (hslot : B.slot ≤ st.s) (hnew : B ∉ st.T) (hpar : B.parent ∈ st.T)
    (hfin : Block.preceq st.F B = true)
    (hprop : B.proposer? = some (E.proposer B.slot))
    (hpslot : B.parent.slot < B.slot) :
    B ∈ (Protocol.on_block_using E st B build).T := by
  have h1 : ¬ (st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T) := by
    rintro (h | h | h)
    · exact absurd h (Nat.not_lt.mpr hslot)
    · exact hnew h
    · exact h hpar
  have h2 : ¬ ((!Block.preceq st.F B) = true) := by rw [hfin]; simp
  have h3 : ¬ (B.proposer? ≠ some (E.proposer B.slot)) := not_not_intro hprop
  have h4 : ¬ ¬ (B.parent.slot < B.slot) := not_not_intro hpslot
  simp only [Protocol.on_block_using]
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, Proofs.update_finality_T,
    Proofs.foldl_on_goldfish_vote_checked_T]
  exact Finset.mem_insert_self _ _

end DecoupledConsensusModel.Sts
