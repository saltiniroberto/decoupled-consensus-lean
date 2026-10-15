module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_block_checked_using
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_commitBlock_mk

@[expose] public section

/-!
# Facts about `NamedStore.process_block_core`

What the named block core writes and keeps.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.process_block_core

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named block core either returns the store unchanged, or puts the named body in `bodies`. -/
theorem process_block_core_noop_or_mem (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) :
    NamedStore.process_block_core E hc cfg st B = st ∨
      B ∈ (NamedStore.process_block_core E hc cfg st B).bodies := by
  rw [NamedStore.process_block_core]
  split
  · exact Or.inl rfl
  · rename_i hparent
    set after := on_block_checked_using
      (fun current => on_block_using E current B.erase
        (fun parentState => Protocol.named_transition E cfg parentState B)) hc st.core B.erase
      with hafterdef
    by_cases hcond : B.erase ∉ st.core.T ∧ B.erase ∈ after.T
    · refine Or.inr ?_
      rw [NamedStore.commitBlock, if_pos hcond]
      exact Finset.mem_insert_self _ _
    · refine Or.inl ?_
      refine commitBlock_eq_of_core_eq st after B ?_
      by_cases hmem : B.erase ∈ st.core.T
      · rw [hafterdef, on_block_checked_using]
        split
        · exact on_block_using_eq_of_mem_T E st.core B.erase _ hmem
        · rfl
      · rcases on_block_checked_using_noop_or_mem_T hc E st.core B.erase
          (fun parentState => Protocol.named_transition E cfg parentState B) with h | h
        · exact h
        · exact absurd ⟨hmem, h⟩ hcond

/-- The named block core keeps the named row lists. -/
theorem process_block_core_sg_rows (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) :
    (NamedStore.process_block_core E hc cfg st B).sg_rows = st.sg_rows := by
  rw [NamedStore.process_block_core]
  split
  · rfl
  · exact commitBlock_sg_rows st _ B

/-- The named block core only adds to the named bodies. -/
theorem process_block_core_bodies_subset (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) :
    st.bodies ⊆ (NamedStore.process_block_core E hc cfg st B).bodies := by
  rw [NamedStore.process_block_core]
  split
  · exact Finset.Subset.refl _
  · exact commitBlock_bodies_subset st _ B

/-- The named block core only adds to the slot vote lists. -/
theorem process_block_core_gf_votes_subset (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) (k : Slot) :
    st.core.gf_votes k ⊆ (NamedStore.process_block_core E hc cfg st B).core.gf_votes k := by
  rw [NamedStore.process_block_core]
  split
  · exact fun _ h => h
  · rw [commitBlock_core]
    exact on_block_checked_using_gf_votes_subset hc E st.core B.erase _ k

/-- A Goldfish vote the named block core adds to a slot vote list is one the block includes, and the
    block was absent from the erased tree before and is present after. -/
theorem process_block_core_gf_votes_upper (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : NamedStore V) (B : NamedBlock V) (k : Slot)
    (y : GoldfishVote V) :
    y ∈ (NamedStore.process_block_core E hc cfg st B).core.gf_votes k →
      y ∈ st.core.gf_votes k ∨
        (y ∈ B.gf_votes ∧ B.erase ∉ st.core.T ∧
          B.erase ∈ (NamedStore.process_block_core E hc cfg st B).core.T) := by
  rw [NamedStore.process_block_core]
  split
  · exact fun h => Or.inl h
  · rw [commitBlock_core]
    rcases on_block_checked_using_dichotomy hc E st.core B.erase
      (fun parentState => Protocol.named_transition E cfg parentState B) with h | ⟨h1, h2, h3⟩
    · rw [h]; exact fun hh => Or.inl hh
    · intro hh
      rcases h3 k y hh with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨by rwa [Proofs.NamedWire.erase_goldfish_votes] at h', h1, h2⟩

/-- The named block core adds to the named bodies no block other than the one it is given. -/
theorem process_block_core_bodies_upper (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : NamedStore V) (B C : NamedBlock V) :
    C ∈ (NamedStore.process_block_core E hc cfg st B).bodies → C ∈ st.bodies ∨ C = B := by
  rw [NamedStore.process_block_core]
  split
  · exact fun h => Or.inl h
  · exact fun h => mem_bodies_commitBlock st _ B h

/-- Running the named block core on a block the store already holds among its named bodies returns
    the store unchanged. -/
theorem process_block_core_of_mem_bodies (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hT : st.core.T = st.bodies.image NamedBlock.erase) (hB : B ∈ st.bodies) :
    Protocol.NamedStore.process_block_core E hc cfg st B = st := by
  have hBT : B.erase ∈ st.core.T := by
    rw [hT]; exact Finset.mem_image_of_mem _ hB
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · rw [on_block_checked_using_of_id _ hc st.core B.erase
      (on_block_using_of_mem_T E st.core B.erase _ hBT)]
    unfold Protocol.NamedStore.commitBlock
    rw [if_neg (fun h => h.1 hBT)]
  · rfl

end DecoupledConsensusModel.Sts
