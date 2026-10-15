import Model.Vocabulary.Protocol.Grades
import Mathlib.Data.Rat.Floor
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Protocol.ChainState.Chain

/-!
# Facts about `Protocol.clipGrade`

The clip of a grade root against a finalized block: `Protocol.clipGrade g F` walks from `g` towards
genesis and stops at the first block compatible with `F`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.compatible DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Protocol.clipGrade

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `X ⪯ g` and `X` is compatible with `F`, then `X ⪯ Protocol.clipGrade g F`. -/
theorem preceq_clipGrade {X F : Block V} (hXF : Block.compatible X F = true) :
    ∀ g : Block V, Block.Preceq X g → Block.Preceq X (Protocol.clipGrade g F) := by
  intro g
  induction g with
  | genesis =>
      intro hXg
      simp only [Protocol.clipGrade]
      exact hXg
  | node p s root gv gsv ats v ih =>
      intro hXg
      simp only [Protocol.clipGrade]
      split
      · exact hXg
      · rename_i hnc
        have h' : decide (X = Block.node p s root gv gsv ats v) = true ∨
            Block.preceq X p = true := by
          simpa only [Block.Preceq, Block.preceq, Bool.or_eq_true] using hXg
        rcases h' with heq | hp
        · have hX : X = Block.node p s root gv gsv ats v := of_decide_eq_true heq
          subst hX
          exact absurd hXF hnc
        · exact ih hp

/-- `Protocol.clipGrade g F ⪯ g`. -/
theorem clipGrade_Preceq (g F : Block V) : Block.Preceq (Protocol.clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
      simp only [Protocol.clipGrade]
      split
      · exact Block.preceq_self _
      · exact Block.preceq_trans ih (by
          simp only [Block.preceq, Bool.or_eq_true]
          exact Or.inr (Block.preceq_self _))

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Clipping a grade twice at `F` is clipping it once. -/
theorem clipGrade_clipGrade (g F : Block V) :
    Protocol.clipGrade (Protocol.clipGrade g F) F = Protocol.clipGrade g F := by
  have hc : Block.compatible (Protocol.clipGrade g F) F = true := by
    induction g with
    | genesis => simp [Protocol.clipGrade, Block.compatible, Protocol.preceq_genesis]
    | node p s root gv gsv ats v ih =>
        simp only [Protocol.clipGrade]
        split
        · assumption
        · exact ih
  cases h : Protocol.clipGrade g F with
  | genesis => rw [Protocol.clipGrade]
  | node p s root gv gsv ats v =>
      rw [h] at hc
      rw [Protocol.clipGrade, if_pos hc]

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- `Protocol.clipGrade g F ⪯ g`. -/
theorem clipGrade_preceq_self (g F : Block V) [DecidableEq V] :
    Block.Preceq (Protocol.clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
      simp only [Protocol.clipGrade]
      split
      · exact Block.preceq_self _
      · exact Block.preceq_trans ih (by
          simp only [Block.preceq, Bool.or_eq_true]
          exact Or.inr (Block.preceq_self _))

end DecoupledConsensusModel.Sts
