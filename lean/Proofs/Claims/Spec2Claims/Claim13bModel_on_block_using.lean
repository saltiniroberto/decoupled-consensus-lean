module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_goldfish_vote_checked
public import Proofs.Claims.Spec2Claims.Claim13bModel_update_finality

@[expose] public section

/-!
# Facts about `Protocol.on_block_using`

Lemmas that unfold the raw block handler on the core store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_block_using

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Processing a block the store's tree already holds returns the store unchanged. -/
theorem on_block_using_eq_of_mem_T (E : Env V) (st : Store V) (B : Block V)
    (bs : ChainState V → ChainState V) (hB : B ∈ st.T) :
    on_block_using E st B bs = st := by
  rw [on_block_using, if_pos (Or.inr (Or.inl hB))]

/-- The block core either returns the store, or puts the block in the erased tree. -/
theorem on_block_using_noop_or_mem_T (E : Env V) (st : Store V) (B : Block V)
    (bs : ChainState V → ChainState V) :
    on_block_using E st B bs = st ∨ B ∈ (on_block_using E st B bs).T := by
  simp only [on_block_using]
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [update_finality_T, foldl_on_goldfish_vote_checked_T]
    exact Finset.mem_insert_self _ _

/-- The block core only adds to the slot vote lists. -/
theorem on_block_using_gf_votes_subset (E : Env V) (st : Store V) (B : Block V)
    (bs : ChainState V → ChainState V) (k : Slot) :
    st.gf_votes k ⊆ (on_block_using E st B bs).gf_votes k := by
  simp only [on_block_using]
  split
  · exact fun _ h => h
  split
  · exact fun _ h => h
  split
  · exact fun _ h => h
  split
  · exact fun _ h => h
  · intro y hy
    rw [update_finality_gf_votes]
    exact foldl_on_goldfish_vote_checked_gf_votes_subset E k B.gf_votes _ hy

/-- The raw block core either returns its store, or puts the block in the erased tree and adds
    nothing to the slot vote lists but the Goldfish votes the block includes. -/
theorem on_block_using_dichotomy (E : Env V) (st : Store V) (B : Block V)
    (bs : ChainState V → ChainState V) :
    on_block_using E st B bs = st ∨
      (B ∉ st.T ∧ B ∈ (on_block_using E st B bs).T ∧
        ∀ (k : Slot) (y : GoldfishVote V), y ∈ (on_block_using E st B bs).gf_votes k →
          y ∈ st.gf_votes k ∨ y ∈ B.gf_votes) := by
  simp only [on_block_using]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · rename_i hfirst _ _ _
          refine Or.inr ⟨fun hm => hfirst (Or.inr (Or.inl hm)), ?_, ?_⟩
          · rw [update_finality_T, foldl_on_goldfish_vote_checked_T]
            exact Finset.mem_insert_self _ _
          · intro k y hyy
            rw [update_finality_gf_votes] at hyy
            exact (mem_gf_votes_foldl_on_goldfish_vote_checked E k B.gf_votes _ hyy).imp
              id id

/-- Processing a block the store's erased tree already holds returns the core store unchanged. -/
theorem on_block_using_of_mem_T (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) (h : B ∈ st.T) :
    Protocol.on_block_using E st B buildState = st := by
  unfold Protocol.on_block_using
  exact if_pos (Or.inr (Or.inl h))

end DecoupledConsensusModel.Sts
