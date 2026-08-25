import Mathlib.Data.Set.Functor
import Spec.Defs.Raise
import Spec.Defs.Store

/-!
# Nondeterminism: the stacks, the pick, and the duty monad

**This file is not a specification.** It holds no protocol content — nothing here renders a
definition or a figure of the protocol. It is the rendering's nondeterminism vocabulary;
`CONTEXT.md` carries the decision trail.

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

## `toLists`

`s.toLists` is the set of duplicate-free orderings of `s` — a predicate, not an
enumeration: no list is ever built, so none is ever chosen. `propose_block` picks one for
the block's carried votes, `let gfList ←ᵖ votes.toLists`. (In the root `Finset` namespace
for dot notation — a `DC` name would be invisible to it, the measured trap; the plural
keeps it apart from Mathlib's noncomputable `Finset.toList`.)

## The duty monad, `NDREB`

The vocabulary that lets a duty *broadcast* — the protocol's own verb — instead of
returning its messages. A duty is `Store → … → NDREB (Store …)`: the store stays an
explicit input and output — which is also what keeps the instant autoparams attachable —
while the **outbox** threads through the monad. `broadcast m` puts a message in it;
composition is function call, and a caller never unions sends: an earlier duty's
broadcasts are already in the outbox when a later duty runs.

`NDREB` is `StateT` of the outbox over `NDRE`, so under the `abbrev` a duty is a function
`outbox → NDRE (α × outbox)`. Two consequences worth reading off that type: the base is
`NDRE` because the duty *bodies* pick and raise — the walk's tie, the picked listing, the
`σ[·]` and timestamp reads — which no smaller base admits; and the outbox sits *inside*
the nondeterminism, so each outcome carries its own sends (a duty that picks broadcasts
per pick, and a failing outcome broadcast nothing).

## Consuming a stack

Inside a stack, compose by `←`. At the boundary, a stack is consumed as a **relation** —
`res ∈ (f …).run` — the lean-sts step shape; there is deliberately no computable exit, every
exit being a choice this vocabulary exists to avoid. Statements about all outcomes — the
failure is never among them, the outcome set is a singleton — are `Analysis/` matter over
`.run`.

The same holds one level up: there is no run inside the spec — the figures compose duties
by calling them. The one boundary is `NDREB.outcomes`: the set of outcomes of a duty run
with nothing sent, each an answer — a `DutyResult`, the store afterwards with the
broadcasts — or the failure. The sts wiring consumes a duty as
`res ∈ (S.onTick t p).outcomes`, and `Analysis/` statements quantify over the same set.
`DutyResult` itself lives in `Store.lean` and survives only at this boundary.

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

/-- The lift core does not ship: a bare `Except` value into `ExceptT ε m`, so a raising
    read — `let σB ← S.σ[B]` — binds in `NDRE` with the same spelling `DRE`
    routines use. -/
scoped instance {ε : Type} {m : Type → Type} [Monad m] :
    MonadLift (Except ε) (ExceptT ε m) := ⟨fun e => ExceptT.mk (pure e)⟩

/-- What a pick may pick from: a `Set`, or a `Finset` read as its members. -/
class Pickable (σ : Type → Type) where
  /-- The set a pick ranges over. -/
  toSet : {α : Type} → (s : σ α) → Set α

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

/-- `s.toLists`: every duplicate-free ordering of `s` — a predicate, never an
    enumeration. In the root `Finset` namespace for dot notation; the plural keeps it
    apart from Mathlib's noncomputable `Finset.toList`. -/
def _root_.Finset.toLists {α : Type} [DecidableEq α] (s : Finset α) : Set (List α) :=
  { l | l.Nodup ∧ l.toFinset = s }

/-- `for x in (s : Finset α) do …`, in any monad `Set` lifts into: pick a listing, loop
    the list — every visitation order among the outcomes. A loop whose body is order-free
    (`merge_view`'s union) converges to one value on every listing, so its outcome set is
    a singleton; a loop whose body is not order-free gets every order's result as an
    outcome, which is exactly the honest reading. -/
scoped instance {α : Type} {m : Type → Type} [Monad m] [MonadLiftT Set m] [DecidableEq α] :
    ForIn m (Finset α) α where
  forIn s init body := do
    let l ← liftM s.toLists
    forIn l init body

variable {Validator : Type} [Roots] [DecidableEq Validator]

/-- The duty monad — nondeterministic result with exception and **broadcasts**, the
    effect-inventory name continuing `DRE`/`NDR`/`NDRE`. The outbox threads over the
    nondeterministic-raising base; the store
    is deliberately not in here — a duty takes and returns it explicitly. -/
abbrev NDREB (Validator : Type) (α : Type) :=
  StateT (Finset (Message Validator)) NDRE α

/-- The protocol's own verb: put a message in the outbox. -/
def broadcast (m : Message Validator) : NDREB Validator Unit :=
  modify (· ∪ {m})

/-- The outcome set of a duty run with nothing sent: each element the failure, or a
    `DutyResult` — the store afterwards and everything broadcast along the way. The
    consumption boundary: the sts step and every `Analysis/` statement read a duty as
    `res ∈ (…).outcomes`, and nothing inside `Spec/` consumes one at all. -/
def NDREB.outcomes (d : NDREB Validator (Store Validator)) :
    Set (DRE (DutyResult Validator)) :=
  (do
    let (S, out) ← d.run ∅
    return { state := S, send := out } : NDRE (DutyResult Validator)).run

end DC
