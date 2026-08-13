import Decoupled.Spec.Basic

/-!
# Notation for rendering the paper's figures as pseudocode

**This file is not a specification.** It holds no protocol content — no state, no routine,
nothing that can be checked against the paper. It is the notation layer that lets the
figure files carry the paper's own assignment statements: `σ.h ← σ.h + 1`,
`σ.target_participation, σ.progress ← false^V`.

Everything the imperative rendering deviates on is decided here, in one place, so that a
figure file is transcription and nothing else. A reviewer checking a routine against the
paper needs the three macros below and nothing more; each expands to a reassignment of the
enclosing `do` block's `let mut`.

Taken from the first attempt's own notation layer, on instruction, together with the `do`
shape it settled on. It is the one part of that attempt this project reuses rather than
re-derives, because it makes no claim about the paper. What it decided, and this file keeps:

**A routine is a plain `def … : T := Id.run do`.** No `function` command that would default
the result type from the state binder: the type is worth having visible at the declaration.

**No `while` or `repeat` macro.** Lean 4.32.2's `Lean.Loop.forIn` is `whileM`
(`Init/While.lean`), a least fixed point, so the paper's `while` is written directly with no
bound. Proving anything about a routine written that way needs the `lean-proof-idioms`
skill; writing one does not.

**The assignment macros claim bare identifiers as well as dotted ones.** So the paper's
`σ ← process_slots(σ, B.slot)` is written with the same arrow as its `σ.s ← σ.s + 1`, rather
than the two spellings sitting side by side. What that costs is `x ← someMonadicAction`,
Lean's monadic reassignment of a mutable variable, which becomes unwritable while this
namespace is open. Nothing here wants it: the routines are all `Id.run do`, where it does
nothing, and `let x ← e` is different syntax, so a `do` block in another monad is
untouched. A mistake is a type error, never a silent one.

## `←` renders as `←` only where it re-assigns

The paper writes `←` both for introducing a name and for overwriting one. Lean distinguishes
them, and so do the figure files:

* **introduces** a name → `let x := e`, or `let mut x := e` when a later line overwrites it;
* **re-assigns** an existing one → `x ← e`, the macros below.

## Hazard

Parser tokens are global even for `scoped` syntax, so **a field name must never become an
atom**. That is why each macro matches `$x:ident` and takes the name apart with `getPrefix`,
rather than declaring a `".h"`-style token.
-/

set_option autoImplicit false

namespace Decoupled

open Lean

/-- `σ.f ← e`, assignment to a field of a record-valued local, as the pseudocode writes it;
    and `x ← e`, assignment to a bare local. See the module header on why both are claimed.

    The expansion is `σ := { σ with f := e }`, so the `σ` on the right-hand side is the
    state *at that statement*. That is what makes `advance_height`'s new `nj` read the
    already-incremented `h`, exactly as Figure 2 (`alg:attestation-processing`) does. -/
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

/-- `σ.f, σ.g ← e`, the paper's simultaneous assignment, as in `advance_height`'s
    `target_participation, progress ← false^V` (Figure 2, `alg:attestation-processing`).
    Both sides get the same `e`, which is what that line means. -/
scoped syntax (name := pairAssign) (priority := high) ident ", " ident " ← " term : doElem

macro_rules
  | `(doElem| $x:ident, $y:ident ← $e) =>
      `(doElem| do
          $x:ident ← $e
          $y:ident ← $e)

/-- `σ.arr[i] ← e`, an indexed write to a function-valued field, and `x[i] ← e` to a
    function-valued local. `target_participation[i] ← true` is the case Figure 2
    (`alg:attestation-processing`) needs. -/
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

end Decoupled
