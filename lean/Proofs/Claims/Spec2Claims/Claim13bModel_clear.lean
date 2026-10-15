import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.clear`

The test a frame applies to a block: compatibility with the frame's completed grade-0 root when
there is one, and `true` otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.clear

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `B` passes the test of `frame` and `frame`'s grade-0 entry is the completed root `root`, then
    `B` and `root` are compatible. -/
theorem compatible_of_clear {frame : Protocol.Frame V} {B root : Block V}
    (hclear : Protocol.clear frame B = true) (hg0 : frame.g0 = some (some root)) :
    Block.compatible B root = true := by
  unfold Protocol.clear at hclear
  rw [hg0] at hclear
  exact hclear

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


/-- If the frame's grade-0 entry is a completed phase with no root, every block passes the frame's
    test. -/
theorem clear_of_g0_some_none {frame : Protocol.Frame V}
    (h : frame.g0 = some none) (B : Block V) :
    Protocol.clear frame B = true := by
  unfold Protocol.clear
  rw [h]

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the grade-0 entry of `frame` is the root `root`, the test of `frame` at `B` is
    `Block.compatible B root`. -/
theorem clear_of_g0 {frame : Protocol.Frame V} {root : Block V}
    (h : frame.g0 = some (some root)) (B : Block V) :
    Protocol.clear frame B = Block.compatible B root := by
  unfold Protocol.clear
  rw [h]

/-- If the grade-0 entry of `frame` is no completed root, the test of `frame` passes every block. -/
theorem clear_of_g0_ne {frame : Protocol.Frame V}
    (h : ∀ root : Block V, frame.g0 ≠ some (some root)) (B : Block V) :
    Protocol.clear frame B = true := by
  unfold Protocol.clear
  split
  · rename_i root hroot
    exact absurd hroot (h root)
  · rfl

end DecoupledConsensusModel.Sts
