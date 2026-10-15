module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.readyView`

Lemmas that unfold the tokens of a sender's raw inputs whose named block passes the body condition
`Protocol.bodyReady`, and `Protocol.interpretedInputs`, which `readyView` reads.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.interpretedInputs
  DecoupledConsensusModel.Protocol.rawInputs DecoupledConsensusModel.Protocol.readyView

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If the attestation `y` is among `v`'s raw inputs to the round-`r` grade of `gv` at the cutoff
    `c` and passes the body condition at `gv`, `F` and `c`, then the token of `y` is in `v`'s ready
    view at that cutoff. -/
theorem token_mem_readyView (gv : Protocol.GradeView V) (F : Block V) (η r : Round) (c : Time)
    (v : V) {y : Protocol.SGVote V} (hraw : y ∈ Protocol.rawInputs gv η r c v)
    (hready : Protocol.bodyReady gv F c y = true) :
    Protocol.token y ∈ Protocol.readyView gv F η r c v := by
  unfold Protocol.readyView Protocol.interpretedInputs
  exact Finset.mem_image_of_mem Protocol.token (Finset.mem_filter.mpr ⟨hraw, hready⟩)

omit [Fintype V] in
/-- A token is in `v`'s ready view of the round-`r` grade of `gv` at the cutoff `c` exactly when it
    is the token of some attestation among `v`'s interpreted inputs there. -/
theorem mem_readyView_iff {gv : Protocol.GradeView V} {F : Block V} {η r : Round} {c : Time}
    {v : V} {tok : Protocol.Token (Option BlockId)} :
    tok ∈ Protocol.readyView gv F η r c v ↔
      ∃ y ∈ Protocol.interpretedInputs gv F η r c v, Protocol.token y = tok := by
  unfold Protocol.readyView
  exact Finset.mem_image

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
