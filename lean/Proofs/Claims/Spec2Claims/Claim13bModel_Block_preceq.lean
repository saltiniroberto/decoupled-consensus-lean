import Model.Vocabulary.Objects.Blocks
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Proofs.Claims.ModelIrreducible

/-!
# Slots along ancestry

On a parent-closed set of blocks whose parents are of strictly smaller slots, an ancestor of a
member is of a slot at most the member's.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.parent DecoupledConsensusModel.Block.parent?
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.Block.slot

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Let `T` be a set of blocks such that every member with a parent has its parent in `T`, and every
    member other than genesis has its parent at a strictly smaller slot. Then for every member `C`
    of `T` and every block `X` with `X ⪯ C`, the slot of `X` is at most the slot of `C`. -/
theorem preceq_slot_le_of_parentClosed {T : Finset (Block V)}
    (hcl : ∀ B ∈ T, B.parent? = none ∨ B.parent ∈ T)
    (hslot : ∀ C ∈ T, C ≠ Block.genesis → C.parent.slot < C.slot) :
    ∀ C : Block V, C ∈ T → ∀ X : Block V, Block.Preceq X C → X.slot ≤ C.slot := by
  intro C
  induction C with
  | genesis =>
      intro _ X hX
      simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at hX
      exact hX ▸ Nat.le_refl _
  | node p s r gv support ats i ih =>
      intro hC X hX
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hX
      rcases hX with rfl | hXp
      · exact Nat.le_refl _
      · have hpmem : p ∈ T := by
          rcases hcl _ hC with h | h
          · simp [Block.parent?] at h
          · simpa only [Block.parent] using h
        have hlt := hslot _ hC (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
        simp only [Block.parent, Block.slot] at hlt
        exact (ih hpmem X hXp).trans (Nat.le_of_lt hlt)

end DecoupledConsensusModel.Sts
