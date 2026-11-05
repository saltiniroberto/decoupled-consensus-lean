module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# Roots, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Roots.lean` over a model `M`, for an
execution `x` of `protocolOf M S`: how `RootsNameBlocksUntil M S Sched x t` relates to
`RootsNameBlocks M S Sched x` and to `RootCollisionHeldBy M S Sched x t`. None reads a fact of the
model.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

variable {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

/-- Being held by a time is monotone in the time. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `M`: the model;
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`; `B`: the block.

Read aloud: a block held by `t` is held by every later time. -/
theorem inHonestTreeBy_mono {t t' : ℝ} (h : t ≤ t') {B : Block V} (hB : inHonestTreeBy M A x t B) :
    inHonestTreeBy M A x t' B := by
  obtain ⟨i, v, hv, hi, hB⟩ := hB
  exact ⟨i, v, hv, le_trans hi h, hB⟩

/-- A larger bound gives the smaller one. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `M`: the model;
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`.

Read aloud: uniqueness among what is held by `t'` is uniqueness among what is held by `t ≤ t'`. -/
theorem RootsNameBlocksUntil.mono {x : Trace V (NamedObject V) M.N} {t t' : ℝ} (h : t ≤ t')
    (hR : RootsNameBlocksUntil M A x t') : RootsNameBlocksUntil M A x t :=
  fun B B' hB hB' hr => hR B B' ((inHonestTreeBy_mono M) x h hB) ((inHonestTreeBy_mono M) x h hB') hr

/-- A block held at some step is held by some time. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`, `E`: the run's facts and the condition on executions; `B`: the block.

Read aloud: an honest validator holds `B` at some step exactly when it does so by some time. -/
theorem inHonestTree_iff_exists_by (F : Facts M) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (B : Block V) :
    inHonestTree M A x B ↔ ∃ t : ℕ, inHonestTreeBy M A x t B := by
  constructor
  · rintro ⟨i, v, hv, hB⟩
    obtain ⟨t, ht⟩ := exists_nat_ge (x.time i)
    exact ⟨t, (inHonestTreeBy_of_st M F) x R E hv ht hB⟩
  · rintro ⟨t, hB⟩
    exact (inHonestTree_of_inHonestTreeBy M F) x R E hB

/-- The landed premise is the bounded one at every bound. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`, `E`: the run's facts and the condition on executions.

Read aloud: roots name blocks among everything honest validators ever hold exactly when they do so
among what is held by every time `t`. -/
theorem rootsNameBlocks_iff_forall_until (F : Facts M) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) :
    RootsNameBlocks M A x ↔ ∀ t : ℕ, RootsNameBlocksUntil M A x t := by
  constructor
  · intro hR t B B' hB hB' hr
    exact hR B B' (((inHonestTree_iff_exists_by M) x F R E B).2 ⟨t, hB⟩)
      (((inHonestTree_iff_exists_by M) x F R E B').2 ⟨t, hB'⟩) hr
  · intro hR B B' hB hB' hr
    obtain ⟨t, hBt⟩ := ((inHonestTree_iff_exists_by M) x F R E B).1 hB
    obtain ⟨t', hBt'⟩ := ((inHonestTree_iff_exists_by M) x F R E B').1 hB'
    exact hR (max t t') B B' ((inHonestTreeBy_mono M) x (by exact_mod_cast le_max_left _ _) hBt)
      ((inHonestTreeBy_mono M) x (by exact_mod_cast le_max_right _ _) hBt') hr

/-- The landed premise gives the bounded one at any bound. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`, `E`: the run's facts and the condition on executions; `t`: the bound.

Read aloud: if roots name blocks among everything honest validators ever hold, they do among what is
held by `t`. -/
theorem rootsNameBlocksUntil_of_rootsNameBlocks (F : Facts M) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ)
    (hR : RootsNameBlocks M A x) : RootsNameBlocksUntil M A x t :=
  ((rootsNameBlocks_iff_forall_until M) x F R E).1 hR t

/-- Either roots name blocks among what is held by `t`, or a collision has hit by `t`. The proof;
the audited statement is in `Statements/Executions/RootsStatements.lean`.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound.

Read aloud: the bounded premise fails only through a collision by `t`. -/
theorem rootsNameBlocksUntil_or_collision (t : ℕ) :
    RootsNameBlocksUntil M A x t ∨ RootCollisionHeldBy M S A x t := by
  by_cases h : RootsNameBlocksUntil M A x t
  · exact Or.inl h
  · right
    by_contra hno
    apply h
    intro B B' hB hB' hr
    by_contra hne
    exact hno ⟨B, B', hB, hB', hr, hne⟩

/-- The bounded premise fails exactly through a collision. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound.

Read aloud: roots fail to name blocks among what is held by `t` exactly when a collision has hit two
blocks held by `t`. -/
theorem not_rootsNameBlocksUntil_iff_collision (t : ℕ) :
    ¬ RootsNameBlocksUntil M A x t ↔ RootCollisionHeldBy M S A x t := by
  constructor
  · intro h
    rcases (rootsNameBlocksUntil_or_collision M) x t with h' | h'
    · exact absurd h' h
    · exact h'
  · rintro ⟨B, B', hB, hB', hr, hne⟩ hR
    exact hne (hR B B' hB hB' hr)

end GoldilocksCorrectness.Record.Proofs.Executions

