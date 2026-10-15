import Model.Vocabulary.Protocol.Store
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.ModelProperties.Block_Preceq

/-!
# Facts about `Protocol.get_fg_root`

The fork-choice root of a store: its justified block `J` when its height maximum `h_max` is
`h_j + 1`, and its finalized block `F` otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.get_fg_root

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The root `Protocol.get_fg_root` of a store is its justified block `J` or its finalized block
    `F`. -/
theorem get_fg_root_eq_J_or_F (st : Protocol.Store V) :
    Protocol.get_fg_root st.toHealing.toFG = st.J ∨
      Protocol.get_fg_root st.toHealing.toFG = st.F := by
  unfold Protocol.get_fg_root
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Setting a store's clock and slot leaves its `get_fg_root` unchanged. -/
theorem get_fg_root_set_clock_slot (st : Protocol.Store V) (t : Int) (s : Slot) :
    Protocol.get_fg_root ({ st with t := t, s := s } : Protocol.Store V).toHealing.toFG
      = Protocol.get_fg_root st.toHealing.toFG := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `st.F ⪯ st.J`, then `st.F` is an ancestor of the store's `get_fg_root`. -/
theorem finalized_preceq_get_fg_root (st : Protocol.Store V) (hFJ : Block.Preceq st.F st.J) :
    Block.Preceq st.F (Protocol.get_fg_root st.toHealing.toFG) := by
  rcases get_fg_root_eq_J_or_F st with h | h
  · rw [h]
    exact hFJ
  · rw [h]
    exact Proofs.ModelProperties.Preceq_self _

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The store's `get_fg_root` is compatible with `B` when its finalized block is, and its justified
    block is too whenever `h_max = h_j + 1`. -/
theorem fgRoot_compatible_of_compatible {stH : Protocol.HealingStore V} {B : Block V}
    (hF : Block.compatible stH.F B = true)
    (hJ : stH.h_max = stH.h_j + 1 → Block.compatible stH.J B = true) :
    Block.compatible (Protocol.get_fg_root stH.toFG) B = true := by
  unfold Protocol.get_fg_root
  split
  · exact hJ ‹_›
  · exact hF

end DecoupledConsensusModel.Sts
