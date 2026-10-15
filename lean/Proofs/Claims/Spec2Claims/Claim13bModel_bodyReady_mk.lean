module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# More facts about `Protocol.bodyReady`

The two cases in which an SG vote passes the body condition.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.bodyReady

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- An SG vote whose `confirmed` field is empty passes the body condition of every grade view at
    every cutoff. -/
theorem bodyReady_of_no_head (gv : Protocol.GradeView V) (F : Block V) (cutoff : Int)
    (u : Protocol.SGVote V) (hu : u.confirmed = none) :
    Protocol.bodyReady gv F cutoff u = true := by
  simp only [Protocol.bodyReady, hu]

/-- An SG vote whose confirmed root resolves in the view's tree to a block stamped before the cutoff
    and compatible with `F` passes the body condition. -/
theorem bodyReady_of_head (gv : Protocol.GradeView V) (F : Block V) (cutoff : Int)
    (u : Protocol.SGVote V) {root : BlockId} {H : Block V}
    (hu : u.confirmed = some root) (hfind : Block.find? gv.T root = some H)
    (hstamp : stampedBefore gv.timestamp_block cutoff H = true)
    (hcompat : Block.compatible H F = true) :
    Protocol.bodyReady gv F cutoff u = true := by
  simp only [Protocol.bodyReady, hu, hfind, hstamp, hcompat, Bool.and_self]

end DecoupledConsensusModel.Sts
