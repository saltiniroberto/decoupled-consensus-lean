module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_block_using

@[expose] public section

/-!
# Facts about `Protocol.on_block_checked_using`

Lemmas that unfold the receiver-side block wrapper that tests the attestations a block includes.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_block_checked_using

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The checked block core either returns the store, or puts the block in the erased tree. -/
theorem on_block_checked_using_noop_or_mem_T (hc : Protocol.HealConfig) (E : Env V)
    (st : Store V) (B : Block V) (bs : ChainState V → ChainState V) :
    on_block_checked_using (fun current => on_block_using E current B bs) hc st B = st ∨
      B ∈ (on_block_checked_using (fun current => on_block_using E current B bs)
        hc st B).T := by
  simp only [on_block_checked_using]
  split
  · exact on_block_using_noop_or_mem_T E st B bs
  · exact Or.inl rfl

/-- The checked block core only adds to the slot vote lists. -/
theorem on_block_checked_using_gf_votes_subset (hc : Protocol.HealConfig) (E : Env V)
    (st : Store V) (B : Block V) (bs : ChainState V → ChainState V) (k : Slot) :
    st.gf_votes k ⊆
      (on_block_checked_using (fun current => on_block_using E current B bs)
        hc st B).gf_votes k := by
  simp only [on_block_checked_using]
  split
  · exact on_block_using_gf_votes_subset E st B bs k
  · exact fun _ h => h

/-- The checked block core either returns its store, or puts the block in the erased tree and adds
    nothing to the slot vote lists but the votes the block includes. -/
theorem on_block_checked_using_dichotomy (hc : HealConfig) (E : Env V) (st : Store V)
    (B : Block V) (bs : ChainState V → ChainState V) :
    on_block_checked_using (fun current => on_block_using E current B bs) hc st B = st ∨
      (B ∉ st.T ∧
        B ∈ (on_block_checked_using (fun current => on_block_using E current B bs)
          hc st B).T ∧
        ∀ (k : Slot) (y : GoldfishVote V),
          y ∈ (on_block_checked_using (fun current => on_block_using E current B bs)
            hc st B).gf_votes k → y ∈ st.gf_votes k ∨ y ∈ B.gf_votes) := by
  simp only [on_block_checked_using]
  split
  · exact on_block_using_dichotomy E st B bs
  · exact Or.inl rfl

omit [DecidableEq V] [Fintype V] in
/-- The receiver-side block wrapper returns the store unchanged whenever the handler it wraps does. -/
theorem on_block_checked_using_of_id (handle : Protocol.Store V → Protocol.Store V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (B : Block V)
    (h : handle st = st) :
    Protocol.on_block_checked_using handle hc st B = st := by
  unfold Protocol.on_block_checked_using
  split_ifs with hadm
  · exact h
  · rfl

end DecoupledConsensusModel.Sts
