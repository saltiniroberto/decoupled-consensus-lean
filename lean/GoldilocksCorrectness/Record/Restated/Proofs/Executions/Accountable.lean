module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalizedFromChain
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableStatementsChains
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements

@[expose] public section

/-!
# Accountable, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Accountable.lean` over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 73, accountable safety over
executions, from each finalized block being the finalized block of the chain state of a block of its
tree and the record's Lemma 70.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (SlashableBetween)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 73, accountable safety over a trace of the model, from the run's facts alone.** When
the finalized blocks of `p₁`'s node state after `i` steps and of `p₂`'s after `j` steps conflict,
the first tree holds a block `b₁` and the second a block `b₂` with `SlashableBetween M b₁ b₂`, or
two different blocks of the two trees taken together share a root.

Why: each finalized block is the finalized block of the chain state of a block of its tree, and
Lemma 70 applies to those two blocks; the trees hold every ancestor of their blocks.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`: the setup; `x`: the trace; `R`: the run's facts; `i`, `j`: the two steps; `p₁`, `p₂`: the two
  validators.

Read aloud: conflicting finalized blocks give two blocks of the two trees between which enough
validators are slashable, or a shared root. -/
theorem lem73_accountable_safety_of_run (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (i j : ℕ) (p₁ p₂ : V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (x.st i p₁).finalized.compatible (x.st j p₂).finalized = false) :
    (∃ b₁ ∈ (x.st i p₁).tree, ∃ b₂ ∈ (x.st j p₂).tree, SlashableBetween M b₁ b₂) ∨
      RootCollisionIn ((x.st i p₁).tree ∪ (x.st j p₂).tree) := by
  obtain ⟨b₁, hb₁, hF₁⟩ := (finalizedFromChain_of_run M F) S x R i p₁
  obtain ⟨b₂, hb₂, hF₂⟩ := (finalizedFromChain_of_run M F) S x R j p₂
  rw [hF₁, hF₂] at hConflict
  rcases (GoldilocksCorrectness.Record.Statements.Routines.lem70_accountable_safety_chain M F Fx) S.C b₁ b₂ hConflict with hs | ⟨X, Y, hX, hY, hr, hne⟩
  · exact Or.inl ⟨b₁, hb₁, b₂, hb₂, hs⟩
  · have hmem : ∀ Z : Block V, (Z.AncestorEq b₁ ∨ Z.AncestorEq b₂) →
        Z ∈ (x.st i p₁).tree ∪ (x.st j p₂).tree := by
      rintro Z (hZ | hZ)
      · exact Finset.mem_union_left _ ((ancestors_mem_T_of_run M F) S x R i p₁ b₁ Z hb₁ hZ)
      · exact Finset.mem_union_right _ ((ancestors_mem_T_of_run M F) S x R j p₂ b₂ Z hb₂ hZ)
    exact Or.inr ⟨X, hmem X hX, Y, hmem Y hY, hr, hne⟩

/-- **Lemma 73, accountable safety over executions.** When the finalized blocks of `p₁`'s node
state after `i` steps and of `p₂`'s after `j` steps conflict, the first tree holds a block `b₁` and
the second a block `b₂` with `SlashableBetween M b₁ b₂`, or two different blocks of the two trees
taken together share a root.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`, `j`: the two steps; `p₁`, `p₂`:
  the two validators.

Read aloud: conflicting finalized blocks give two blocks of the two trees between which enough
validators are slashable, or a shared root. -/
theorem lem73_accountable_safety (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i j : ℕ) (p₁ p₂ : V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (x.st i p₁).finalized.compatible (x.st j p₂).finalized = false) :
    (∃ b₁ ∈ (x.st i p₁).tree, ∃ b₂ ∈ (x.st j p₂).tree, SlashableBetween M b₁ b₂) ∨
      RootCollisionIn ((x.st i p₁).tree ∪ (x.st j p₂).tree) := by
  obtain ⟨b₁, hb₁, hF₁⟩ := (finalizedFromChain_of_exec M F) S A x R E i p₁
  obtain ⟨b₂, hb₂, hF₂⟩ := (finalizedFromChain_of_exec M F) S A x R E j p₂
  rw [hF₁, hF₂] at hConflict
  rcases (GoldilocksCorrectness.Record.Statements.Routines.lem70_accountable_safety_chain M F Fx) S.C b₁ b₂ hConflict with hs | ⟨X, Y, hX, hY, hr, hne⟩
  · exact Or.inl ⟨b₁, hb₁, b₂, hb₂, hs⟩
  · have hmem : ∀ Z : Block V, (Z.AncestorEq b₁ ∨ Z.AncestorEq b₂) →
        Z ∈ (x.st i p₁).tree ∪ (x.st j p₂).tree := by
      rintro Z (hZ | hZ)
      · exact Finset.mem_union_left _
          ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E
            i p₁ b₁ Z hb₁ hZ)
      · exact Finset.mem_union_right _
          ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E
            j p₂ b₂ Z hb₂ hZ)
    exact Or.inr ⟨X, hmem X hX, Y, hmem Y hY, hr, hne⟩

end GoldilocksCorrectness.Record.Proofs.Executions

