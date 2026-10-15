module

public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.head_covers`

Lemmas that unfold `Protocol.head_covers`, whether a named root resolves in a tree to a descendant
of a block or to the block itself.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.find? DecoupledConsensusModel.Protocol.head_covers

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the root `root` resolves in the tree `T` to the block `H` and `X ⪯ H`, then `root` covers `X`
    in `T`. -/
theorem head_covers_of_find {T : Finset (Block V)} {X H : Block V} {root : BlockId}
    (hfind : Block.find? T root = some H) (hXH : Block.Preceq X H) :
    Protocol.head_covers T X (some root) = true := by
  unfold Protocol.head_covers
  simp only [hfind]
  exact hXH

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the root `root` covers `X` in the tree `T`, then `root` resolves in `T` to some block `H`
    with `X ⪯ H`. The converse of `head_covers_of_find`. -/
theorem exists_find_of_head_covers {T : Finset (Block V)} {X : Block V} {root : BlockId}
    (h : Protocol.head_covers T X (some root) = true) :
    ∃ H : Block V, Block.find? T root = some H ∧ Block.Preceq X H := by
  unfold Protocol.head_covers at h
  dsimp only at h
  cases hf : Block.find? T root with
  | none =>
      rw [hf] at h
      cases h
  | some H =>
      rw [hf] at h
      exact ⟨H, rfl, h⟩


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `root` covers `X` in the tree `T` and resolves in `T` to the block `H`, then `X ⪯ H`. -/
theorem preceq_of_head_covers_of_find {T : Finset (Block V)} {X H : Block V} {root : BlockId}
    (h : Protocol.head_covers T X (some root) = true) (hfind : Block.find? T root = some H) :
    Block.Preceq X H := by
  unfold Protocol.head_covers at h
  simp only [hfind] at h
  exact h


/-- When no root is named, the cover test over the tree `T` fails for every block `X`. -/
theorem head_covers_none (T : Finset (Block V)) (X : Block V) :
    Protocol.head_covers T X none = false := by
  unfold Protocol.head_covers
  rfl


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


end DecoupledConsensusModel.Sts
