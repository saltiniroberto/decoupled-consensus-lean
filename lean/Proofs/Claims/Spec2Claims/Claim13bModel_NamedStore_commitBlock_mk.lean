module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# More facts about `NamedStore.commitBlock`

What committing a named body onto a named store writes and keeps.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.commitBlock

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Committing a body with the core store unchanged returns the named store unchanged. -/
theorem commitBlock_eq_of_core_eq (st : NamedStore V) (after : Store V)
    (B : NamedBlock V) (h : after = st.core) :
    NamedStore.commitBlock st after B = st := by
  subst h
  rw [NamedStore.commitBlock, if_neg (fun hh => hh.1 hh.2)]

omit [Fintype V] in
/-- Committing a body keeps the named row lists. -/
theorem commitBlock_sg_rows (st : NamedStore V) (after : Store V) (B : NamedBlock V) :
    (NamedStore.commitBlock st after B).sg_rows = st.sg_rows := by
  simp only [NamedStore.commitBlock]; split <;> rfl

omit [Fintype V] in
/-- Committing a body only adds to the named bodies. -/
theorem commitBlock_bodies_subset (st : NamedStore V) (after : Store V)
    (B : NamedBlock V) :
    st.bodies ⊆ (NamedStore.commitBlock st after B).bodies := by
  simp only [NamedStore.commitBlock]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

omit [Fintype V] in
/-- Committing a body writes the core store `after` it is given. -/
theorem commitBlock_core (st : NamedStore V) (after : Store V) (B : NamedBlock V) :
    (NamedStore.commitBlock st after B).core = after := by
  simp only [NamedStore.commitBlock]; split <;> rfl

omit [Fintype V] in
/-- Committing the body `B` adds no body other than `B`. -/
theorem mem_bodies_commitBlock (st : NamedStore V) (after : Store V) (B : NamedBlock V)
    {C : NamedBlock V} (h : C ∈ (NamedStore.commitBlock st after B).bodies) :
    C ∈ st.bodies ∨ C = B := by
  simp only [NamedStore.commitBlock] at h
  split at h
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  · exact Or.inl h

end DecoupledConsensusModel.Sts
