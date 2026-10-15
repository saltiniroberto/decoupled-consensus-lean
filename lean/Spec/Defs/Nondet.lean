import Mathlib.Data.Set.Functor
import Spec.Defs.Raise

/-!
# Nondeterminism: the two stacks

**This file is not a specification.** It holds no protocol content — nothing here renders a
routine of the protocol. It is a nondeterminism vocabulary. No routine of `Spec` uses it: the
routines of `Spec` are deterministic. The record `Model` of `lean/Model/Record/Model.lean` uses `NDR` and
`NDRE`.

## The two stacks

* `NDR α := Set α` — picks only. A value is the **set of outcomes**, one per combination of
  picks; Mathlib's `Set.monad` (opt-in, activated scoped here) makes `do` its language.
* `NDRE α := ExceptT Error Set α` — picks and raising reads. Under `.run` it is
  definitionally `Set (DRE α)`: each outcome an answer or the failure, an error
  path cut short exactly as `DRE` alone would cut it.

A routine that raises but never picks keeps plain `DRE`; one that does neither
stays pure. Core lifts `Set` into `NDRE`.

## Consuming a stack

Inside a stack, compose by `←`. At the boundary, a stack is consumed as a **relation** —
`res ∈ (f …).run` — the lean-sts step shape; there is deliberately no computable exit, every
exit being a choice this vocabulary exists to avoid. Statements about all outcomes — the failure is
never among them, the outcome set is a singleton — are stated outside the spec, over `.run`.

## Measured traps, from the probes

* A `do` block's **result type must name the stack** (`NDR`/`NDRE`, reducible `abbrev`s):
  declared as bare `Set (DRE …)`, the elaborator picks the `Set` monad and every
  bind means the wrong thing.
* Membership proofs through several binds normalize with `ExceptT.run_bind` before the
  `Set` reasoning; the smallest cases are `Set.mem_singleton`/`Set.mem_biUnion`.
-/

set_option autoImplicit false

namespace DC

attribute [scoped instance] Set.monad

/-- Nondeterminism alone: the value is the set of outcomes, one per combination of picks. -/
abbrev NDR (α : Type) := Set α

/-- Nondeterminism and raising: definitionally `Set (DRE α)` under `.run` — each
    outcome an answer or the failure. -/
abbrev NDRE (α : Type) := ExceptT Error Set α

end DC
