import Spec.Defs.Model
import Spec.Defs.FinsetM
import Spec.Defs.Raise

/-!
# Notation for rendering the protocol's figures as pseudocode

**This file is not a specification.** It holds no protocol content — no state, no routine,
nothing that can be checked against the protocol. It is the notation layer that lets the
figure files carry the protocol's own assignment statements — `σ.h ← σ.h + 1`,
`σ.target_participation, σ.progress ← false^V` — its cardinality bars, `|votes|`, and its
set-builders whose condition raises, `{x ∈ᴹ s | p}`.

The macros are protocol-free — nothing here names anything from the protocol — and
`scoped`, active only inside this namespace. The decisions:

**A routine is a plain `def … : T := Id.run do`.** No `function` command that would default
the result type from the state binder: the type is worth having visible at the declaration.

**No `while` or `repeat` macro.** Lean 4.32.2's `Lean.Loop.forIn` is `whileM`
(`Init/While.lean`), a least fixed point, so a figure's `while` would be written directly
with no bound. Proving anything about a routine written that way needs the `lean-proof-idioms`
skill; writing one does not.

**The assignment macros claim bare identifiers as well as dotted ones.** So a figure's
`σ ← process_attestation(σ, a)` is written with the same arrow as its `σ.s ← B.slot`,
rather than the two spellings sitting side by side. What that costs is
`x ← someMonadicAction`, Lean's monadic reassignment of a mutable variable, which becomes
unwritable while this namespace is open. Nothing here wants it: the routines are all
`Id.run do`, where it does nothing, and `let x ← e` is different syntax, so a `do` block in
another monad is untouched. A mistake is a type error, never a silent one.

## `←` renders as `←` only where it re-assigns

The protocol writes `←` both for introducing a name and for overwriting one. Lean
distinguishes them, and so do the figure files:

* **introduces** a name → `let x := e`, or `let mut x := e` when a later line overwrites it;
* **re-assigns** an existing one → `x ← e`, the macros below.

## `⇐` where the right-hand side computes

The protocol's arrow says nothing about whether the routine on its right picks, raises or
merely returns; here that difference is worth seeing, so an assignment fed by a
computation wears a second arrowhead — `Σ.sg_root[r] ⇐ get_sg_root(Σ, r)`, `H ⇐ arg max`.
It binds the value and writes it, and the `Option` a field wraps is supplied by coercion,
so no `some` is written. Three arrows, then, each saying one thing: `←` re-assigns a
value, `⇐` binds a computation's, `←ᵖ` picks (`Nondet.lean`).

The alternative — teaching `←` itself to accept either — was built and measured: a class
dispatching on the right-hand side works where that side types itself, and breaks where
the *assignment* is what types it, which is how two of the protocol's own lines
elaborate (`σ.nj ← …` through the `Decidable` coercion, `σ.progress ← fun _ => false`
through the field). Repairing those would have put ascriptions into the figures.

## Hazard

Parser tokens are global even for `scoped` syntax, so **a field name must never become an
atom**. That is why each macro matches `$x:ident` and takes the name apart with `getPrefix`,
rather than declaring a `".h"`-style token.
-/

set_option autoImplicit false

namespace DC

open Lean

/-- `σ.f ← e`, assignment to a field of a record-valued local, as the pseudocode writes it;
    and `x ← e`, assignment to a bare local. See the module header on why both are claimed.

    The expansion is `σ := { σ with f := e }`, so the `σ` on the right-hand side is the
    state *at that statement*. -/
scoped syntax (name := stateAssign) (priority := high) ident " ← " term : doElem

macro_rules
  | `(doElem| $x:ident ← $e) => do
      let n := x.getId
      let pre := n.getPrefix
      if pre.isAnonymous then
        `(doElem| $x:ident := $e)
      else
        let v := mkIdent pre
        let f := mkIdent (Name.mkSimple n.getString!)
        `(doElem| $v:ident := { $v with $f:ident := $e })

/-- `σ.f, σ.g ← e`, the protocol's simultaneous assignment, as in `advance_height`'s
    `σ.target_participation, σ.progress ← false^V`. Both sides get the same `e`, which is
    what that line means. -/
scoped syntax (name := pairAssign) (priority := high) ident ", " ident " ← " term : doElem

macro_rules
  | `(doElem| $x:ident, $y:ident ← $e) =>
      `(doElem| do
          $x:ident ← $e
          $y:ident ← $e)

/-- `σ.arr[i] ← e`, an indexed write to a function-valued field, and `x[i] ← e` to a
    function-valued local. `σ.target_participation[i] ← true` is the case
    `process_attestation` needs. -/
scoped syntax (name := idxAssign) (priority := high) ident noWs "[" term "]" " ← " term :
  doElem

macro_rules
  | `(doElem| $x:ident[$i] ← $e) => do
      let n := x.getId
      let pre := n.getPrefix
      if pre.isAnonymous then
        `(doElem| $x:ident := Function.update $x:ident $i $e)
      else
        let v := mkIdent pre
        let f := mkIdent (Name.mkSimple n.getString!)
        `(doElem| $v:ident :=
            { $v with $f:ident := Function.update (($v).$f:ident) $i $e })

/-- `σ.f ⇐ e`, and `x ⇐ e` to a bare local: assignment whose right-hand side computes.
    The expansion binds it — `σ := { σ with f := (← e) }` — so a routine that picks or
    raises can feed a field, and the arrowhead is what tells a reader it does. -/
scoped syntax (name := stateAssignBind) (priority := high) ident " ⇐ " term : doElem

macro_rules
  | `(doElem| $x:ident ⇐ $e) => do
      let n := x.getId
      let pre := n.getPrefix
      if pre.isAnonymous then
        `(doElem| do
            let val ← ($e)
            $x:ident := val)
      else
        let v := mkIdent pre
        let f := mkIdent (Name.mkSimple n.getString!)
        `(doElem| do
            let val ← ($e)
            $v:ident := { $v with $f:ident := val })

/-- `σ.arr[i] ⇐ e`, the indexed write whose value computes, and `x[i] ⇐ e` to a
    function-valued local: `Σ.sg_root[r] ⇐ get_sg_root(Σ, r)`, the healing tick's line.
    An `Option`-valued field takes the bound value through the coercion, no `some`. -/
scoped syntax (name := idxAssignBind) (priority := high)
  ident noWs "[" term "]" " ⇐ " term : doElem

macro_rules
  | `(doElem| $x:ident[$i] ⇐ $e) => do
      let n := x.getId
      let pre := n.getPrefix
      if pre.isAnonymous then
        `(doElem| do
            let val ← ($e)
            $x:ident := Function.update $x:ident $i val)
      else
        let v := mkIdent pre
        let f := mkIdent (Name.mkSimple n.getString!)
        `(doElem| do
            let val ← ($e)
            $v:ident := { $v with $f:ident := Function.update (($v).$f:ident) $i val })

/-- `{x ∈ᴹ s | p}`: the set-builder whose condition can raise — `Finset.filterM` in
    set-builder clothes. The plain `{x ∈ s | p}` is a pure filter, so a condition that reads
    a store map with the raising bracket has no monad to fail into; this form expands to
    `s.filterM (fun x => do return p)`, and a `(← …)` inside `p` lifts into that inner `do`
    `ᴹ` says monadic. The spelling is distinct from the pure builder's on purpose:
    overloading `∈` would make every pure filter ambiguous. The expansion pins the filter's
    monad to `DRE` — this is the *raising* builder — so that inside an `NDRE`
    block the filter still runs at the raising monad and lifts whole, rather than demanding
    fold instances the stack rightly lacks (a pick with no outcomes does not commute with an
    error; measured 2026-08-23).

    **It must be a `doElem`, claiming the whole `let … ← {…}` statement** — measured
    2026-08-23, and it is the recorded term-versus-doElem trap hit live: as a *term* macro
    the enclosing `do` scans the bind's right side before the macro expands, lifts the
    user's `(← …)` out of the builder, and the bound variable escapes its binder ("Unknown
    identifier `vote`"). As a `doElem` the macro owns the statement, so the arrow lands
    inside the `do` the expansion itself emits, which shields it. -/
scoped syntax (name := filterMBind) (priority := high)
  "let " ident " ← " "{" ident " ∈ᴹ " term " | " term "}" : doElem

/-- The `let mut` form of the raising set-builder. No current use — `goldfish_vote`'s
    freeze filter was the case until the stored votes carried their own times — kept as
    part of the builder's vocabulary. -/
scoped syntax (name := filterMBindMut) (priority := high)
  "let " "mut " ident " ← " "{" ident " ∈ᴹ " term " | " term "}" : doElem

macro_rules
  | `(doElem| let $y:ident ← {$x:ident ∈ᴹ $s | $p}) =>
      `(doElem| let $y:ident ←
          (Finset.filterM (fun $x => do return $p) $s : DRE _))
  | `(doElem| let mut $y:ident ← {$x:ident ∈ᴹ $s | $p}) =>
      `(doElem| let mut $y:ident ←
          (Finset.filterM (fun $x => do return $p) $s : DRE _))

/-- `{f x | x ∈ s}`, the image comprehension — `s.map' fun x => f x` — and its
    conditioned form `{f x | x ∈ s, p x}`, filter then project: Python's
    `{f(x) for x in s if p(x)}`. Mathlib's sep-builder `{x ∈ s | p}` and the `Set`
    builders parse untouched beside them (measured). -/
scoped syntax (name := finsetImg) (priority := high)
  "{" term " | " ident " ∈ " term "}" : term

/-- The conditioned form of the image comprehension above. -/
scoped syntax (name := finsetImgCond) (priority := high)
  "{" term " | " ident " ∈ " term ", " term "}" : term

macro_rules
  | `({$f | $x:ident ∈ $s}) => `(Finset.map' $s (fun $x => $f))
  | `({$f | $x:ident ∈ $s, $p}) =>
      `(Finset.map' (Finset.filter (fun $x => $p) $s) (fun $x => $f))

/-- `|s|` for `Finset.card s`, as the protocol writes it: `|equivocators| + |supporters|`. Mathlib's shape for the `abs` bars — `atomic`, whitespace-free — so
    `|{v ∈ K | p v}|` parses with the set-builder's own `|` inside, and a bar in a `match`
    alternative is untouched (both measured).

    What it costs, measured: two macros on one spelling do not overload, so
    while this namespace is open the `abs` bars stop elaborating — `|x| : Int` becomes
    `Finset.card x` and fails. Nothing in this subtree takes an absolute value; write
    `abs x` if one ever does. A mistake is a type error, never a silent one. -/
scoped macro:max atomic("|" noWs) s:term noWs "|" : term => `(Finset.card $s)

end DC
