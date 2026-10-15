module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.commitBlock`

The commit of a named body after the block handler, read through the bodies.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- If the erasure of `B` is not in the tree of `before`'s core store and is in the tree of `after`,
    then `B` is among the bodies of the commit of `B` over `after`. -/
theorem mem_commitBlock_bodies_of_fresh {before : Protocol.NamedStore V} {after : Protocol.Store V}
    {B : NamedBlock V} (h : B.erase ∉ before.core.T ∧ B.erase ∈ after.T) :
    B ∈ (Protocol.NamedStore.commitBlock before after B).bodies := by
  unfold Protocol.NamedStore.commitBlock
  rw [if_pos h]
  exact Finset.mem_insert_self _ _

/-- A body of the commit of `B` over `after` is `B` itself, freshly inserted, or a body of `before`. -/
theorem mem_commitBlock_bodies {before : Protocol.NamedStore V} {after : Protocol.Store V}
    {B D : NamedBlock V} (hD : D ∈ (Protocol.NamedStore.commitBlock before after B).bodies) :
    ((B.erase ∉ before.core.T ∧ B.erase ∈ after.T) ∧ D = B) ∨ D ∈ before.bodies := by
  unfold Protocol.NamedStore.commitBlock at hD
  split_ifs at hD with hgrow
  · rcases Finset.mem_insert.mp hD with hDB | hDold
    · exact Or.inl ⟨hgrow, hDB⟩
    · exact Or.inr hDold
  · exact Or.inr hD

end DecoupledConsensusModel.Proofs.ModelProperties

end
