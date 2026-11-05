module
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# The bounded roots premise and the landed one

The proofs of the statements of `GoldilocksCorrectness/Statements/Executions/RootsStatements.lean`:
how `RootsNameBlocksUntil S Sched x t` (within the blocks honest validators hold by the time `t`, a
root names one block) relates to the landed `RootsNameBlocks S Sched x` (within the blocks honest
validators ever hold, a root names one block), and to `RootCollisionHeldBy S Sched x t` (two
distinct blocks held by `t` share a root).

The route: a block held at a step is held by that step's time (`inHonestTree_iff_exists_by`), and
being held by `t` is monotone in `t` (`inHonestTreeBy_mono`); so the unbounded premise is the
bounded one at every bound, the bound at `max t t'` covering two blocks held by `t` and by `t'`.
The bounded premise fails only through a collision, classically.


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

variable {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- Being held by a time is monotone in the time. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`; `B`: the block. -/
theorem inHonestTreeBy_mono {t t' : ℕ} (h : t ≤ t') {B : Block V} (hB : inHonestTreeBy x t B) :
    inHonestTreeBy x t' B := by
  obtain ⟨i, v, hv, hi, hB⟩ := hB
  exact ⟨i, v, hv, le_trans hi h, hB⟩

/-- A larger bound gives the smaller one. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`. -/
theorem RootsNameBlocksUntil.mono {x : AtomicExec (protocol S) Sched} {t t' : ℕ} (h : t ≤ t')
    (hR : RootsNameBlocksUntil S Sched x t') : RootsNameBlocksUntil S Sched x t :=
  fun B B' hB hB' hr => hR B B' (inHonestTreeBy_mono x h hB) (inHonestTreeBy_mono x h hB') hr

/-- A block held at some step is held by some time. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `x`: the execution; `B`: the block. -/
theorem inHonestTree_iff_exists_by (B : Block V) :
    inHonestTree x B ↔ ∃ t : ℕ, inHonestTreeBy x t B := by
  constructor
  · rintro ⟨i, v, hv, hB⟩
    exact ⟨x[i].time, i, v, hv, le_rfl, hB⟩
  · rintro ⟨t, i, v, hv, -, hB⟩
    exact ⟨i, v, hv, hB⟩

/-- The landed premise is the bounded one at every bound. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `x`: the execution. -/
theorem rootsNameBlocks_iff_forall_until :
    RootsNameBlocks S Sched x ↔ ∀ t : ℕ, RootsNameBlocksUntil S Sched x t := by
  constructor
  · intro hR t B B' hB hB' hr
    exact hR B B' ((inHonestTree_iff_exists_by x B).2 ⟨t, hB⟩)
      ((inHonestTree_iff_exists_by x B').2 ⟨t, hB'⟩) hr
  · intro hR B B' hB hB' hr
    obtain ⟨t, hBt⟩ := (inHonestTree_iff_exists_by x B).1 hB
    obtain ⟨t', hBt'⟩ := (inHonestTree_iff_exists_by x B').1 hB'
    exact hR (max t t') B B' (inHonestTreeBy_mono x (le_max_left _ _) hBt)
      (inHonestTreeBy_mono x (le_max_right _ _) hBt') hr

/-- The landed premise gives the bounded one at any bound. The proof; the audited statement is in
`Statements/Executions/RootsStatements.lean`.

The variables:
- `x`: the execution; `t`: the bound. -/
theorem rootsNameBlocksUntil_of_rootsNameBlocks (t : ℕ) (hR : RootsNameBlocks S Sched x) :
    RootsNameBlocksUntil S Sched x t :=
  (rootsNameBlocks_iff_forall_until x).1 hR t

/-- Either roots name blocks among what is held by `t`, or a collision has hit by `t`. The proof;
the audited statement is in `Statements/Executions/RootsStatements.lean`.

The variables:
- `x`: the execution; `t`: the bound. -/
theorem rootsNameBlocksUntil_or_collision (t : ℕ) :
    RootsNameBlocksUntil S Sched x t ∨ RootCollisionHeldBy S Sched x t := by
  by_cases h : RootsNameBlocksUntil S Sched x t
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
- `x`: the execution; `t`: the bound. -/
theorem not_rootsNameBlocksUntil_iff_collision (t : ℕ) :
    ¬ RootsNameBlocksUntil S Sched x t ↔ RootCollisionHeldBy S Sched x t := by
  constructor
  · intro h
    rcases rootsNameBlocksUntil_or_collision x t with h' | h'
    · exact absurd h' h
    · exact h'
  · rintro ⟨B, B', hB, hB', hr, hne⟩ hR
    exact hne (hR B B' hB hB' hr)

end GoldilocksCorrectness.Proofs.Executions
