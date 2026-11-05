module
public import GoldilocksCorrectness.Proofs.Executions.FinalizedFromChain
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements

@[expose] public section

/-!
# Accountable safety over executions

Lemma 73: two node states of an execution, read at any two steps, whose finalized blocks
conflict, each hold a block such that `SlashableBetween` holds of the two blocks, or two different
blocks of the two trees taken together share a root. Each finalized block is the finalized block
of the chain state of a block of its tree (`finalizedFromChain_of_exec`), so Lemma 70 applies to
those two blocks; a root shared on their two chains is shared in the two trees, which hold every
ancestor of their blocks.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (SlashableBetween RootCollisionIn
  lem70_accountable_safety_chain)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 73, accountable safety over executions.** When the finalized blocks of `p₁`'s node
state after `i` steps and of `p₂`'s after `j` steps conflict, the first tree holds a block `b₁` and
the second a block `b₂` with `SlashableBetween b₁ b₂`, or two different blocks of the two trees
taken together share a root.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`, `j`: the two steps; `p₁`, `p₂`:
  the two validators. -/
theorem lem73_accountable_safety (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i j : ℕ) (p₁ p₂ : V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (x[i][p₁].st).S.F.compatible (x[j][p₂].st).S.F = false) :
    (∃ b₁ ∈ (x[i][p₁].st).S.T, ∃ b₂ ∈ (x[j][p₂].st).S.T, SlashableBetween b₁ b₂) ∨
      RootCollisionIn ((x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) := by
  obtain ⟨b₁, hb₁, hF₁⟩ := finalizedFromChain_of_exec S Sched x i p₁
  obtain ⟨b₂, hb₂, hF₂⟩ := finalizedFromChain_of_exec S Sched x j p₂
  rw [hF₁, hF₂] at hConflict
  rcases lem70_accountable_safety_chain S.C b₁ b₂ hConflict with hs | ⟨X, Y, hX, hY, hr, hne⟩
  · exact Or.inl ⟨b₁, hb₁, b₂, hb₂, hs⟩
  · have hmem : ∀ Z : Block V, (Z.AncestorEq b₁ ∨ Z.AncestorEq b₂) →
        Z ∈ (x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T := by
      rintro Z (hZ | hZ)
      · exact Finset.mem_union_left _ (ancestors_mem_T_of_exec S Sched x i p₁ b₁ Z hb₁ hZ)
      · exact Finset.mem_union_right _ (ancestors_mem_T_of_exec S Sched x j p₂ b₂ Z hb₂ hZ)
    exact Or.inr ⟨X, hmem X hX, Y, hmem Y hY, hr, hne⟩

end GoldilocksCorrectness.Proofs.Executions
