module
public import Goldilocks.AC.ForkChoice
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# The walk as a predicate: where a walk with a tie-break function ends

The Goldfish walk descends from a start block through a tree of blocks, at each step to an
eligible child of the highest score, and stops where no child is eligible. This page states that
behaviour as a predicate over the tree, the score and the eligibility test, without the spec's
computation of it:

- `TieBreak V`: a function that picks one block of a finite set of blocks, with two laws: it picks
  a member of a nonempty set (`tieBreak_mem`), and it keeps its pick when blocks it did not pick
  are removed from the set (`tieBreak_subset`);
- `highestEligibleChildren tree score eligible H`: the children of `H` in `tree` that pass the
  test and whose score is the highest among those that pass it;
- `WalkStep tree score eligible H C`: the walk may step from `H` to `C`;
- `WalkEnd tree score eligible anchor H`: the walk from `anchor` ends at `H`.

The tie-break is a class, as the spec's `RootOrder` is: a statement over the walk then reads
`WalkEnd tree score eligible anchor H`, and a model supplies its own tie-break as an instance.

This file holds definitions only.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

/-- `TieBreak V`: a function `tieBreak` that picks one block of each finite set of blocks, such
that

1. `tieBreak_mem`: the pick from a nonempty set `S` is a member of `S`;
2. `tieBreak_subset`: when `T` is a subset of `S` and the pick from `S` is in `T`, the pick from
   `T` is the pick from `S`.

Read aloud: it picks a member, and it keeps its pick when unchosen candidates are removed. -/
class TieBreak (V : Type) where
  /-- `tieBreak S`: the block picked from the set `S`. -/
  tieBreak : Finset (Block V) → Block V
  /-- The pick from a nonempty set is a member of it. -/
  tieBreak_mem : ∀ S : Finset (Block V), S.Nonempty → tieBreak S ∈ S
  /-- Removing blocks other than the pick keeps the pick. -/
  tieBreak_subset : ∀ S T : Finset (Block V), T ⊆ S → tieBreak S ∈ T → tieBreak T = tieBreak S

variable {V : Type}

open Classical in
/-- `highestEligibleChildren tree score eligible H`: the blocks `D` of `tree` whose parent is `H`,
on which the test `eligible` answers `true`, on which the score answers some `k`, and such that
the score answers at most `k` on every other block of `tree` whose parent is `H` and on which the
test answers `true`.

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the eligibility test;
- `H`: the block whose children are compared.

Read aloud: the eligible children of `H` in `tree` with the highest score. -/
noncomputable def highestEligibleChildren (tree : Finset (Block V)) (score : Block V → DRE ℕ)
    (eligible : Block V → DRE Bool) (H : Block V) : Finset (Block V) :=
  tree.filter fun D => D.parent? = some H ∧ eligible D = .ok true ∧
    ∃ k : ℕ, score D = .ok k ∧
      ∀ D' ∈ tree, D'.parent? = some H → eligible D' = .ok true →
        ∀ k' : ℕ, score D' = .ok k' → k' ≤ k

/-- `WalkStep tree score eligible H C`: the walk may step from `H` to `C`:

1. `C` is a block of `tree` whose parent is `H`, and the test `eligible` answers `true` on `C`;
2. the test answers on every block of `tree` whose parent is `H`;
3. the score answers on every block of `tree` whose parent is `H` and on which the test answers
   `true`;
4. `C` is the block `tieBreak` picks from the eligible children of `H` in `tree` with the highest
   score (`highestEligibleChildren`).

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the eligibility test;
- `H`: the block the step starts from; `C`: the block it goes to.

Read aloud: `C` is the eligible child of `H` the walk steps to. -/
def WalkStep [TieBreak V] (tree : Finset (Block V)) (score : Block V → DRE ℕ)
    (eligible : Block V → DRE Bool) (H C : Block V) : Prop :=
  C ∈ tree ∧ C.parent? = some H ∧ eligible C = .ok true ∧
    (∀ D ∈ tree, D.parent? = some H → ∃ b : Bool, eligible D = .ok b) ∧
    (∀ D ∈ tree, D.parent? = some H → eligible D = .ok true → ∃ k : ℕ, score D = .ok k) ∧
    C = TieBreak.tieBreak (highestEligibleChildren tree score eligible H)

/-- `WalkEnd tree score eligible anchor H`: `H` is reached from `anchor` by walk steps
(`WalkStep`, none or more), and no walk step leaves `H`: the test `eligible` answers `false` on
every block of `tree` whose parent is `H`.

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the eligibility test;
- `anchor`: the block the walk starts from; `H`: the block it ends at.

Read aloud: the walk from `anchor` ends at `H`. -/
def WalkEnd [TieBreak V] (tree : Finset (Block V)) (score : Block V → DRE ℕ)
    (eligible : Block V → DRE Bool) (anchor H : Block V) : Prop :=
  Relation.ReflTransGen (WalkStep tree score eligible) anchor H ∧
    ∀ D ∈ tree, D.parent? = some H → eligible D = .ok false

end GoldilocksCorrectness.Statements.Routines
