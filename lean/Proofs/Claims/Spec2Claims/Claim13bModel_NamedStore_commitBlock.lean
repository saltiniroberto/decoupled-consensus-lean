import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedStore.commitBlock`

`commitBlock` installs the core store a block handler returns into a named store, and adds the named
block to the bodies when its erased form is new to the tree and in the returned tree.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.commitBlock

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- A named block `D` among the bodies of `before` is among the bodies of the store `commitBlock`
    returns, whatever the core store `after` and the block `B`. -/
theorem mem_commitBlock_bodies_of_mem {before : Protocol.NamedStore V} {after : Protocol.Store V}
    {B D : NamedBlock V} (hD : D ∈ before.bodies) :
    D ∈ (Protocol.NamedStore.commitBlock before after B).bodies := by
  unfold Protocol.NamedStore.commitBlock
  split
  · exact Finset.mem_insert_of_mem hD
  · exact hD

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts
