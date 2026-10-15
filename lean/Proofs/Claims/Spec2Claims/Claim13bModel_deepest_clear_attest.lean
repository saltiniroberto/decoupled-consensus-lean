import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Proofs.Claims.ModelIrreducible

/-!
# The floor of `Protocol.deepest_clear`

The floor of a clear walk is an ancestor of its answer.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.deepest? DecoupledConsensusModel.Protocol.deepest_clear

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `deepest_clear` with the floor `A` returns `D`, then `A ⪯ D`. -/
theorem floor_preceq_deepest_clear {A C D : Block V} {test : Block V → Bool}
    (h : Protocol.deepest_clear (some A) C test = some D) : Block.Preceq A D := by
  unfold Protocol.deepest_clear at h
  have hmem := (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).2
  exact hmem.1

end DecoupledConsensusModel.Sts
