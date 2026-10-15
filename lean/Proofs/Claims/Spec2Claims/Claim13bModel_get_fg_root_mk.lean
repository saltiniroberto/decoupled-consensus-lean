module
public import Model.Vocabulary.Protocol.Store
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Claims.Spec2Claims.Claim13bModel_compatible

@[expose] public section

/-!
# `Protocol.get_fg_root` at a healing store

When the root `Protocol.get_fg_root` of a healing store is compatible with, or an ancestor of, a
given block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.get_fg_root

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The store's `get_fg_root` is compatible with `T` when `stH.F ⪯ T` and, if `h_max = h_j + 1`, its
    justified block is compatible with `T`. -/
theorem fgRoot_compatible_ofJustifiedBranch {stH : Protocol.HealingStore V} {T : Block V}
    (hF : Block.Preceq stH.F T)
    (hJ : stH.h_max = stH.h_j + 1 → Block.compatible stH.J T = true) :
    Block.compatible (Protocol.get_fg_root stH.toFG) T = true := by
  unfold Protocol.get_fg_root
  split
  · exact hJ ‹_›
  · exact compatible_of_preceq_common_Preceq hF (Proofs.ModelProperties.Preceq_self T)

/-- The store's `get_fg_root` is an ancestor of `T` when its finalized block and its justified block
    both are. -/
theorem fgRoot_preceq {stH : Protocol.HealingStore V} {T : Block V}
    (hF : Block.Preceq stH.F T) (hJ : Block.Preceq stH.J T) :
    Block.Preceq (Protocol.get_fg_root stH.toFG) T := by
  unfold Protocol.get_fg_root
  split
  · exact hJ
  · exact hF

/-- The store's `get_fg_root` is an ancestor of `T` when `stH.F ⪯ T` and, if `h_max = h_j + 1`,
    `stH.J ⪯ T`. -/
theorem fgRoot_preceq_ofJustifiedBranch {stH : Protocol.HealingStore V} {T : Block V}
    (hF : Block.Preceq stH.F T) (hJ : stH.h_max = stH.h_j + 1 → Block.Preceq stH.J T) :
    Block.Preceq (Protocol.get_fg_root stH.toFG) T := by
  unfold Protocol.get_fg_root
  split
  · exact hJ ‹_›
  · exact hF

end DecoupledConsensusModel.Sts
