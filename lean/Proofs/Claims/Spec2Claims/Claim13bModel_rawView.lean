import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.rawView`

A lemma that unfolds the tokens of a sender's raw inputs to a round's grade at a cutoff.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.rawView

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A token is in `v`'s raw view of the grade view `gv` for round `r` at the cutoff `c` exactly when
    it is the token of an attestation among `v`'s raw inputs to that grade at that cutoff. -/
theorem mem_rawView_iff (gv : Protocol.GradeView V) (η r : Round) (c : Time) (v : V)
    (tok : Protocol.Token (Option BlockId)) :
    tok ∈ Protocol.rawView gv η r c v ↔
      ∃ y ∈ Protocol.rawInputs gv η r c v, Protocol.token y = tok := by
  unfold Protocol.rawView
  exact Finset.mem_image

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
