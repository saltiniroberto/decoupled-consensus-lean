import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.opposing`

The Boolean test that a sender opposes a block in a grade view, read as the proposition
`Protocol.Opposes` it decides.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.opposing

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the sender `u` opposes `B` in the grade view `gv`, then `u`'s ready tokens at `early`, its
    ready tokens at `late` and its raw tokens at `late` satisfy `Protocol.Opposes` for `B`, with
    covering in `gv` as the cover test. -/
theorem opposes_of_opposing {gv : Protocol.GradeView V} {F : Block V} {η r : Round}
    {early late : Time} {u : V} {B : Block V}
    (h : Protocol.opposing gv F η r early late u B = true) :
    Protocol.Opposes (fun k b => Protocol.localCovers gv k b = true)
      (Protocol.readyView gv F η r early u) (Protocol.readyView gv F η r late u)
      (Protocol.rawView gv η r late u) B := by
  unfold Protocol.opposing at h
  exact of_decide_eq_true h


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts
