import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.bodyReady`

The body condition a grade applies to an SG vote: a vote with no confirmed root passes; a vote whose
confirmed root names a block `H` of the view's tree passes when `H` is stamped strictly before the
cutoff and compatible with the finalized block; any other vote fails.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.bodyReady

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the SG vote `u` confirms `root`, `root` resolves in the tree of `gv` to `H`, `gv` stamps `H`
    before `cutoff`, and `H` is compatible with `F`, then `u` passes the body condition. -/
theorem bodyReady_of_find {gv : Protocol.GradeView V} {F : Block V} {cutoff : Time}
    {u : Protocol.SGVote V} {root : BlockId} {H : Block V}
    (hconf : u.confirmed = some root) (hfind : Block.find? gv.T root = some H)
    (hstamp : stampedBefore gv.timestamp_block cutoff H = true)
    (hcomp : Block.compatible H F = true) :
    Protocol.bodyReady gv F cutoff u = true := by
  unfold Protocol.bodyReady
  rw [hconf]
  simp only [hfind, hstamp, hcomp, Bool.and_self]

/-- If the SG vote `u` confirms `root` and passes the body condition of `gv` at `cutoff` against
    `F`, then `root` resolves in the tree of `gv` to a block `H` that `gv` stamps before `cutoff`
    and that is compatible with `F`. -/
theorem exists_find_of_bodyReady {gv : Protocol.GradeView V} {F : Block V} {cutoff : Time}
    {u : Protocol.SGVote V} {root : BlockId} (hconf : u.confirmed = some root)
    (h : Protocol.bodyReady gv F cutoff u = true) :
    ∃ H : Block V, Block.find? gv.T root = some H ∧
      stampedBefore gv.timestamp_block cutoff H = true ∧ Block.compatible H F = true := by
  unfold Protocol.bodyReady at h
  rw [hconf] at h
  dsimp only at h
  cases hf : Block.find? gv.T root with
  | none =>
      rw [hf] at h
      cases h
  | some H =>
      rw [hf, Bool.and_eq_true] at h
      exact ⟨H, rfl, h.1, h.2⟩

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- An SG vote that confirms no root passes the body condition. -/
theorem bodyReady_of_confirmed_none {gv : Protocol.GradeView V} {F : Block V} {cutoff : Time}
    {u : Protocol.SGVote V} (h : u.confirmed = none) :
    Protocol.bodyReady gv F cutoff u = true := by
  unfold Protocol.bodyReady
  simp only [h]

/-- If the SG vote `u` passes the body condition and confirms `root`, then `gv`'s tree finds a block
    `H` at `root`, `gv` stamped `H` before `cutoff`, and `H` is compatible with `F`. -/
theorem bodyReady_parts {gv : Protocol.GradeView V} {F : Block V} {cutoff : Time}
    {u : Protocol.SGVote V} {root : BlockId} (h : Protocol.bodyReady gv F cutoff u = true)
    (hconf : u.confirmed = some root) :
    ∃ H : Block V, Block.find? gv.T root = some H ∧
      stampedBefore gv.timestamp_block cutoff H = true ∧ Block.compatible H F = true := by
  unfold Protocol.bodyReady at h
  simp only [hconf] at h
  cases hfind : Block.find? gv.T root with
  | none => simp only [hfind] at h; exact absurd h Bool.false_ne_true
  | some H =>
    simp only [hfind, Bool.and_eq_true] at h
    exact ⟨H, rfl, h.1, h.2⟩


end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the SG vote `u` confirms `root` and the tree of `gv` has no block with that root, then `u`
    fails the body condition at every `F` and `cutoff`. -/
theorem bodyReady_eq_false_of_find_none (gv : Protocol.GradeView V) (F : Block V)
    (cutoff : Time) (u : Protocol.SGVote V) {root : BlockId}
    (hu : u.confirmed = some root) (hfind : Block.find? gv.T root = none) :
    Protocol.bodyReady gv F cutoff u = false := by
  unfold Protocol.bodyReady
  rw [hu]
  simp only [hfind]


end DecoupledConsensusModel.Sts
