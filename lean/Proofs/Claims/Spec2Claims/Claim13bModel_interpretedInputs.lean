module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.interpretedInputs`

A lemma that unfolds a sender's interpreted inputs to a round's grade, the raw inputs that pass the
body condition.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.interpretedInputs

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- An attestation is among `v`'s interpreted inputs of the round-`r` grade of `gv` at the cutoff
    `c` exactly when it is among `v`'s raw inputs there and passes the body condition at `gv`, `F`
    and `c`. -/
theorem mem_interpretedInputs_iff {gv : Protocol.GradeView V} {F : Block V} {η r : Round}
    {c : Time} {v : V} {y : Protocol.SGVote V} :
    y ∈ Protocol.interpretedInputs gv F η r c v ↔
      y ∈ Protocol.rawInputs gv η r c v ∧ Protocol.bodyReady gv F c y = true := by
  unfold Protocol.interpretedInputs
  exact Finset.mem_filter

end DecoupledConsensusModel.Sts
