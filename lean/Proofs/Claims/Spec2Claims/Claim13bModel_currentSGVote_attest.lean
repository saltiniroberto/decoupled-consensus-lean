import Proofs.Claims.Spec2Claims.Claim13bModel_deepest_clear_attest

/-!
# `Protocol.currentSGVote` against one ancestor

A block that is an ancestor of every block `currentSGVote` can return is an ancestor of its output.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.currentSGVote

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `P` is an ancestor of the read's anchor, of the read's grade-2 block when there is one, and
    of the store's `get_fg_root` when there is none, then `P ⪯ currentSGVote st grades`. -/
theorem preceq_currentSGVote_of_cases {st : Protocol.HealingStore V}
    {grades : Protocol.GradeRead V} {P : Block V}
    (hA : Block.Preceq P grades.anchor)
    (hQ : ∀ q : Block V, grades.Q2 = some q → Block.Preceq P q)
    (hR : grades.Q2 = none → Block.Preceq P (Protocol.get_fg_root st.toFG)) :
    Block.Preceq P (Protocol.currentSGVote st grades) := by
  unfold Protocol.currentSGVote
  split
  · rename_i D hD
    exact Block.preceq_trans hA (floor_preceq_deepest_clear hD)
  · split
    · rename_i q hq
      exact hQ q hq
    · rename_i hq
      split
      · exact hR hq
      · exact hA

end DecoupledConsensusModel.Sts
