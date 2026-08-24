import Mathlib.Data.Set.Functor
import Spec.Defs.Raise

/-!
# Nondeterminism: the two stacks, the pick, and the loop over a set

**This file is not a specification.** It holds no protocol content — nothing here renders a
definition or a figure of the draft. It is the nondeterminism vocabulary the rendering is
adopting (Roberto, 2026-08-23), measured first in `scratch/SetMonadProbe.lean` and
`scratch/SetExceptProbe.lean`; `CONTEXT.md`'s for-all entry carries the decision trail.

## The two stacks

* `NDR α := Set α` — picks only. A value is the **set of outcomes**, one per combination of
  picks; Mathlib's `Set.monad` (opt-in, activated scoped here) makes `do` its language.
* `NDRE α := ExceptT Error Set α` — picks and raising reads. Under `.run` it is
  definitionally `Set (DRE α)`: each outcome an answer or the failure, an error
  path cut short exactly as `DRE` alone would cut it.

A routine that raises but never picks keeps plain `DRE`; one that does neither
stays pure. The lifts below let the four kinds compose in one `do` with no visible plumbing:
core lifts `Set` into `NDRE`, and this file adds the bare `Except` value.

## The pick, `let x ←ᵖ s`

The nondeterministic bind wears its own arrow — a pick never looks like an ordinary bind,
`←` staying for raising reads and callee composition. `Pickable` says what may stand on the
right: a `Set`, or a `Finset` read as its members, so set-builders, bracket reads and whole
store fields pick directly. A pick from the empty set has **no outcomes** — the empty set of
results, not a raise.

## `listings`, and the loop that moved out

`listings s` is the set of duplicate-free orderings of `s` — a predicate, not an
enumeration: no list is ever built, so none is ever chosen. `propose_block` picks one for
the block's carried votes. The `ForIn` over `Finset` it once powered — pick a listing, loop
the list, every visitation order among the outcomes — lost its last consumer in the
2026-08-23 migration and is parked in `OldDefs.lean`.

## Consuming a stack

Inside a stack, compose by `←`. At the boundary, a stack is consumed as a **relation** —
`res ∈ (f …).run` — the lean-sts step shape; there is deliberately no computable exit, every
exit being a choice this vocabulary exists to avoid. Statements about all outcomes — the
failure is never among them, the outcome set is a singleton — are `Analysis/` matter over
`.run`.

## Measured traps, from the probes

* A `do` block's **result type must name the stack** (`NDR`/`NDRE`, reducible `abbrev`s):
  declared as bare `Set (DRE …)`, the elaborator picks the `Set` monad and every
  bind means the wrong thing.
* Membership proofs through several binds normalize with `ExceptT.run_bind` before the
  `Set` reasoning; the smallest cases are `Set.mem_singleton`/`Set.mem_biUnion`.
-/

set_option autoImplicit false

namespace Consensus1

attribute [scoped instance] Set.monad

/-- Nondeterminism alone: the value is the set of outcomes, one per combination of picks. -/
abbrev NDR (α : Type) := Set α

/-- Nondeterminism and raising: definitionally `Set (DRE α)` under `.run` — each
    outcome an answer or the failure. -/
abbrev NDRE (α : Type) := ExceptT Error Set α

/-- The lift core does not ship: a bare `Except` value into `ExceptT ε m`, so a raising
    read — `let σB ← S.σ[B]` — binds in `NDRE` with the same spelling `DRE`
    routines use. -/
scoped instance {ε : Type} {m : Type → Type} [Monad m] :
    MonadLift (Except ε) (ExceptT ε m) := ⟨fun e => ExceptT.mk (pure e)⟩

/-- What a pick may pick from: a `Set`, or a `Finset` read as its members. -/
class Pickable (σ : Type → Type) where
  /-- The set a pick ranges over. -/
  toSet : {α : Type} → σ α → Set α

instance : Pickable Set := ⟨id⟩
instance : Pickable Finset := ⟨fun s => ↑s⟩

/-- Pick one element, in any monad `Set` lifts into — `NDR` by reflexivity, `NDRE` by the
    transformer's own lift. On the empty set: no outcomes. -/
def pickFrom {σ : Type → Type} [Pickable σ] {α : Type} {m : Type → Type} [Monad m]
    [MonadLiftT Set m] (c : σ α) : m α :=
  liftM (Pickable.toSet c)

/-- `let x ←ᵖ s`, the nondeterministic pick; see the module header. -/
scoped syntax (name := pickBind) "let " ident " ←ᵖ " term : doElem

macro_rules
  | `(doElem| let $x:ident ←ᵖ $e) => `(doElem| let $x:ident ← pickFrom $e)

/-- Every duplicate-free listing of `s` — a predicate, never an enumeration. -/
def listings {α : Type} [DecidableEq α] (s : Finset α) : Set (List α) :=
  { l | l.Nodup ∧ l.toFinset = s }

end Consensus1
