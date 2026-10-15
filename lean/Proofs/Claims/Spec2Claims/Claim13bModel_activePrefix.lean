import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# Facts about `Protocol.activePrefix`

The active prefix of a root in a tree: the deepest block of the tree that is an ancestor of the root
or the root itself.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.activePrefix

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the active prefix of `root` in `tree` is `L`, then `L ⪯ root`. -/
theorem preceq_of_activePrefix_eq_some {tree : Finset (Block V)} {root L : Block V}
    (h : Protocol.activePrefix tree root = some L) : Block.Preceq L root := by
  unfold Protocol.activePrefix at h
  exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.1
    (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).2

/-- If the active prefix of `root` in `tree` is `L`, then `L` is in `tree`. -/
theorem mem_of_activePrefix_eq_some {tree : Finset (Block V)} {root L : Block V}
    (h : Protocol.activePrefix tree root = some L) : L ∈ tree := by
  unfold Protocol.activePrefix at h
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).1

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


end DecoupledConsensusModel.Sts
