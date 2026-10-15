import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.positive`

The Boolean test that a sender supports a block in a grade view, read as the proposition
`Protocol.Supports` it decides.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.positive

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the sender `u` is positive for `B` in the grade view `gv`, then `u`'s ready tokens at
    `early`, its ready tokens at `late` and its raw tokens at `late` satisfy `Protocol.Supports` for
    `B`, with covering in `gv` as the cover test. -/
theorem supports_of_positive {gv : Protocol.GradeView V} {F : Block V} {η r : Round}
    {early late : Time} {u : V} {B : Block V}
    (h : Protocol.positive gv F η r early late u B = true) :
    Protocol.Supports (fun k b => Protocol.localCovers gv k b = true)
      (Protocol.readyView gv F η r early u) (Protocol.readyView gv F η r late u)
      (Protocol.rawView gv η r late u) B := by
  unfold Protocol.positive at h
  exact of_decide_eq_true h


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts
