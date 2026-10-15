module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.rawView`, as a module file

The tokens of a sender's raw inputs to a round's grade at a cutoff.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.rawView

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the token `tok` is in `v`'s raw view of the round-`r` grade of `gv` at the cutoff `c`, then
    `tok` is the token of some attestation among `v`'s raw inputs to that grade at that cutoff. -/
theorem exists_rawInputs_of_mem_rawView {gv : Protocol.GradeView V} {η r : Round} {c : Time}
    {v : V} {tok : Protocol.Token (Option BlockId)} (h : tok ∈ Protocol.rawView gv η r c v) :
    ∃ y ∈ Protocol.rawInputs gv η r c v, Protocol.token y = tok := by
  unfold Protocol.rawView at h
  exact Finset.mem_image.mp h

end DecoupledConsensusModel.Sts
