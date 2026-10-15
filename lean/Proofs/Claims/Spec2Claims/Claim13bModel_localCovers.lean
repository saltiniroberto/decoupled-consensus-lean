module

public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_head_covers

@[expose] public section

/-!
# Facts about `Protocol.localCovers`

Lemmas that unfold `Protocol.localCovers`, the cover test a grade view applies to a key and a block:
whether the key resolves in the view's tree to a descendant of the block or to the block itself.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.find? DecoupledConsensusModel.Protocol.head_covers
  DecoupledConsensusModel.Protocol.localCovers

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the key `some root` covers `B` in the grade view `gv` and `root` resolves in `gv`'s tree to
    the block `H`, then `B ⪯ H`. -/
theorem preceq_of_localCovers_of_find {gv : Protocol.GradeView V} {root : BlockId}
    {B H : Block V} (hcov : Protocol.localCovers gv (some root) B = true)
    (hfind : Block.find? gv.T root = some H) : Block.Preceq B H := by
  unfold Protocol.localCovers Protocol.head_covers at hcov
  simp only [hfind] at hcov
  exact hcov

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the root `root` resolves in the tree of the grade view `gv` to the block `H` and `B ⪯ H`,
    then the key `some root` covers `B` in `gv`. -/
theorem localCovers_of_find {gv : Protocol.GradeView V} {root : BlockId} {B H : Block V}
    (hfind : Block.find? gv.T root = some H) (hBH : Block.Preceq B H) :
    Protocol.localCovers gv (some root) B = true := by
  unfold Protocol.localCovers Protocol.head_covers
  simp only [hfind]
  exact hBH

/-- If the key `some root` covers `B` in the grade view `gv`, then `root` resolves in `gv`'s tree to
    some block `H` with `B ⪯ H`. -/
theorem exists_find_of_localCovers {gv : Protocol.GradeView V} {root : BlockId} {B : Block V}
    (hcov : Protocol.localCovers gv (some root) B = true) :
    ∃ H : Block V, Block.find? gv.T root = some H ∧ Block.Preceq B H := by
  unfold Protocol.localCovers Protocol.head_covers at hcov
  dsimp only at hcov
  cases hf : Block.find? gv.T root with
  | none =>
      rw [hf] at hcov
      cases hcov
  | some H =>
      rw [hf] at hcov
      exact ⟨H, rfl, hcov⟩


end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The key `k` covers `B` in the grade view `gv` exactly when `Protocol.head_covers gv.T B k`
    holds. -/
theorem localCovers_eq_true_iff (gv : Protocol.GradeView V) (k : Option BlockId) (B : Block V) :
    Protocol.localCovers gv k B = true ↔ Protocol.head_covers gv.T B k = true := Iff.rfl

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


/-- In any grade view, the empty key covers no block. -/
theorem localCovers_none (gv : Protocol.GradeView V) (B : Block V) :
    Protocol.localCovers gv none B = false := by
  unfold Protocol.localCovers
  exact head_covers_none _ _

/-- If the key `key` resolves in the tree of the grade view `gv` to the block `H`, then `key` covers
    `B` in `gv` exactly when `B ⪯ H`. -/
theorem localCovers_some_iff_of_find {gv : Protocol.GradeView V} {key : BlockId}
    {B H : Block V} (hfind : Block.find? gv.T key = some H) :
    Protocol.localCovers gv (some key) B = true ↔ Block.Preceq B H := by
  unfold Protocol.localCovers
  exact ⟨fun h => preceq_of_head_covers_of_find h hfind, fun h => head_covers_of_find hfind h⟩

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


end DecoupledConsensusModel.Sts
