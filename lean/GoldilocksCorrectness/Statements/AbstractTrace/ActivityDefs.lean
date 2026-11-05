module
public import StsMultisetLog
public import Mathlib.Data.Fintype.Lattice

@[expose] public section

/-!
# Activity

`Activity V`: who is awake and who is in the adversary set, after each step of a run. It is the one
notion of who counts that the facts over a trace are stated on.

Its readings here: the active validators after a step (awake and outside the adversary set), honesty
up to a step and its opposite (in the adversary set after some step up to a step). The readings at a
time and over an interval of times read the trace too, and are on
`GoldilocksCorrectness/Statements/AbstractTrace/TraceDefs.lean`.

This page imports only the sts framework, so that it reads no protocol.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Statements.AbstractTrace

/-- Who is awake and who is in the adversary set, after each step. -/
structure Activity (V : Type) where
  /-- `awake i`: the validators awake after `i` steps. -/
  awake : (i : ℕ) → Finset V
  /-- `corrupted i`: the validators in the adversary set after `i` steps. -/
  corrupted : (i : ℕ) → Finset V

namespace Activity

variable {V : Type} [DecidableEq V] (A : Activity V)

/-- `A.active i`: the validators awake after `i` steps and outside the adversary set then.

The variables:
- `A`: the activity; `i`: the step.

Read aloud: the validators active after `i` steps. -/
def active (i : ℕ) : Finset V := A.awake i \ A.corrupted i

/-- `A.HonestThroughStep i v`: `v` is outside the adversary set after every step up to `i`.

The variables:
- `A`: the activity; `i`: the step; `v`: the validator.

Read aloud: `v` has not been in the adversary set up to step `i`. -/
def HonestThroughStep (i : ℕ) (v : V) : Prop := ∀ i' : ℕ, i' ≤ i → v ∉ A.corrupted i'

/-- `A.EverCorruptedBy i v`: `v` is in the adversary set after some step up to `i`.

The variables:
- `A`: the activity; `i`: the step; `v`: the validator.

Read aloud: `v` has been in the adversary set at some step up to `i`. -/
def EverCorruptedBy (i : ℕ) (v : V) : Prop := ∃ i' : ℕ, i' ≤ i ∧ v ∈ A.corrupted i'

/-! ## Short facts -/

variable {A}

/-- A validator is active after `i` steps exactly when it is awake then and outside the adversary
set then.

The variables:
- `A`: the activity; `i`: the step; `v`: the validator.

Read aloud: active means awake and honest. -/
@[simp]
theorem mem_active {i : ℕ} {v : V} : v ∈ A.active i ↔ v ∈ A.awake i ∧ v ∉ A.corrupted i :=
  Finset.mem_sdiff

/-- A validator active after `i` steps is outside the adversary set then.

The variables:
- `A`: the activity; `i`: the step; `v`: the validator.

Read aloud: an active validator is honest. -/
theorem not_mem_corrupted_of_mem_active {i : ℕ} {v : V} (h : v ∈ A.active i) :
    v ∉ A.corrupted i :=
  (mem_active.1 h).2

/-- A validator active after `i` steps is awake then.

The variables:
- `A`: the activity; `i`: the step; `v`: the validator.

Read aloud: an active validator is awake. -/
theorem mem_awake_of_mem_active {i : ℕ} {v : V} (h : v ∈ A.active i) : v ∈ A.awake i :=
  (mem_active.1 h).1

/-- A validator has been in the adversary set by step `i` exactly when it is in it after some step
up to `i`.

The variables:
- `A`: the activity; `i`: the step; `v`: the validator.

Read aloud: ever in the adversary set by `i` means in it at some step up to `i`. -/
theorem everCorruptedBy_iff {i : ℕ} {v : V} :
    A.EverCorruptedBy i v ↔ ∃ i' : ℕ, i' ≤ i ∧ v ∈ A.corrupted i' :=
  Iff.rfl

/-- Honesty up to a step gives honesty up to every earlier step.

The variables:
- `A`: the activity; `i`, `i'`: the two steps; `v`: the validator.

Read aloud: a validator honest up to step `i` is honest up to any step `i' ≤ i`. -/
theorem HonestThroughStep.mono {i i' : ℕ} {v : V} (hle : i' ≤ i)
    (h : A.HonestThroughStep i v) : A.HonestThroughStep i' v :=
  fun i'' hi'' => h i'' (le_trans hi'' hle)

end Activity

end GoldilocksCorrectness.Statements.AbstractTrace
