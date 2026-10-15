import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.currentSGVote`

The block a round's attestation names as confirmed: the deepest block between the grade read's
anchor and the store's `live_confirmed` that passes the read's test, with three fallbacks when there
is none.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.currentSGVote

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `Protocol.deepest_clear` from the grade read's anchor to the store's `live_confirmed`, under
    the read's test, returns `D`, then `currentSGVote` returns `D`. -/
theorem currentSGVote_of_deepest_clear {st : Protocol.HealingStore V}
    {grades : Protocol.GradeRead V} {D : Block V}
    (h : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear = some D) :
    Protocol.currentSGVote st grades = D := by
  unfold Protocol.currentSGVote
  rw [h]

end DecoupledConsensusModel.Sts
