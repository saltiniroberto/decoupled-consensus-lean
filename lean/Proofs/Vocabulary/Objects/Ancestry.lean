module
public import Model.Vocabulary.Objects.Blocks
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# Ancestry lemmas

The order properties of the ancestry test `⪯`, a structural walk over its second argument:
reflexivity, transitivity, antisymmetry, and comparability of two ancestors of one block, with the
depth bound the proofs use.
-/


namespace DecoupledConsensusModel
namespace Block

variable {V : Type} [DecidableEq V]

/-- `B ⪯ B`. -/
theorem preceq_self (B : Block V) : Block.preceq B B = true := by
  cases B <;> simp [Block.preceq]

/-- `B ≺ C` implies `B ⪯ C`. -/
theorem preceq_of_prec {B C : Block V} (h : Block.prec B C = true) :
    Block.preceq B C = true := by
  rw [Block.prec, Bool.and_eq_true] at h
  exact h.2

/-- `⪯` is transitive. -/
theorem preceq_trans {A B C : Block V} (h₁ : Block.preceq A B = true)
    (h₂ : Block.preceq B C = true) : Block.preceq A C = true := by
  induction C with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at h₂
      subst h₂
      exact h₁
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h₂
      rcases h₂ with h | h
      · subst h
        exact h₁
      · simp only [Block.preceq, Bool.or_eq_true]
        exact Or.inr (ih h)

/-- An ancestor's depth is at most its descendant's. -/
theorem preceq_depth_le {B C : Block V} (h : Block.preceq B C = true) :
    B.depth ≤ C.depth := by
  induction C with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at h
      subst h
      exact Nat.le_refl _
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · subst h
        exact Nat.le_refl _
      · exact Nat.le_succ_of_le (ih h)

/-- An ancestor of `C` whose depth is at least `C`'s is `C` itself. -/
theorem preceq_eq_of_depth_le {B C : Block V} (h : Block.preceq B C = true)
    (hd : C.depth ≤ B.depth) : B = C := by
  induction C with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at h
      exact h
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact h
      · exact absurd (preceq_depth_le h) (by simp only [Block.depth] at hd; omega)

/-- `⪯` is antisymmetric. -/
theorem preceq_antisymm {B C : Block V} (h₁ : Block.preceq B C = true)
    (h₂ : Block.preceq C B = true) : B = C :=
  preceq_eq_of_depth_le h₁ (preceq_depth_le h₂)

/-- Two ancestors of a common block are comparable. -/
theorem preceq_linear {X Y Z : Block V} (hX : Block.preceq X Z = true)
    (hY : Block.preceq Y Z = true) :
    Block.preceq X Y = true ∨ Block.preceq Y X = true := by
  induction Z with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at hX hY
      subst hX
      subst hY
      exact Or.inl (preceq_self _)
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hX hY
      rcases hX with hX | hX
      · rcases hY with hY | hY
        · subst hX
          subst hY
          exact Or.inl (preceq_self _)
        · subst hX
          refine Or.inr ?_
          simp only [Block.preceq, Bool.or_eq_true]
          exact Or.inr hY
      · rcases hY with hY | hY
        · subst hY
          refine Or.inl ?_
          simp only [Block.preceq, Bool.or_eq_true]
          exact Or.inr hX
        · exact ih hX hY

/-- Two ancestors of a common block are compatible. -/
theorem compatible_of_preceq_common {X Y Z : Block V}
    (hX : Block.preceq X Z = true) (hY : Block.preceq Y Z = true) :
    Block.compatible X Y = true := by
  simp only [Block.compatible, Bool.or_eq_true]
  exact preceq_linear hX hY

end Block
end DecoupledConsensusModel

end
