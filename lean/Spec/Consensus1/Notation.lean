import Spec.Consensus1.Model

/-!
# Notation for rendering the draft's figures as pseudocode

**This file is not a specification.** It holds no protocol content — no state, no routine,
nothing that can be checked against the draft. It is the notation layer that lets the
figure files carry the draft's own assignment statements: `σ.h ← σ.h + 1`,
`σ.target_participation, σ.progress ← false^V`.

It is a duplicate — the third — of `Spec/Defs/Notation.lean`, under this subtree's own
namespace, because the renderings share nothing, not even by import, so each stays untouched
by the others (2026-08-19, and again 2026-08-22 for this copy). The macros are protocol-free,
so duplication carries no claim that could drift, and the scoped syntax is what makes three
copies legal: each is active only inside its own namespace. What the first file decided, and
this copy keeps:

**A routine is a plain `def … : T := Id.run do`.** No `function` command that would default
the result type from the state binder: the type is worth having visible at the declaration.

**No `while` or `repeat` macro.** Lean 4.32.2's `Lean.Loop.forIn` is `whileM`
(`Init/While.lean`), a least fixed point, so a draft `while` would be written directly with
no bound. Proving anything about a routine written that way needs the `lean-proof-idioms`
skill; writing one does not.

**The assignment macros claim bare identifiers as well as dotted ones.** So a figure's
`σ ← process_attestation(σ, a)` is written with the same arrow as its `σ.s ← B.slot`,
rather than the two spellings sitting side by side. What that costs is
`x ← someMonadicAction`, Lean's monadic reassignment of a mutable variable, which becomes
unwritable while this namespace is open. Nothing here wants it: the routines are all
`Id.run do`, where it does nothing, and `let x ← e` is different syntax, so a `do` block in
another monad is untouched. A mistake is a type error, never a silent one.

## `←` renders as `←` only where it re-assigns

The draft writes `←` both for introducing a name and for overwriting one. Lean
distinguishes them, and so do the figure files:

* **introduces** a name → `let x := e`, or `let mut x := e` when a later line overwrites it;
* **re-assigns** an existing one → `x ← e`, the macros below.

## Hazard

Parser tokens are global even for `scoped` syntax, so **a field name must never become an
atom**. That is why each macro matches `$x:ident` and takes the name apart with `getPrefix`,
rather than declaring a `".h"`-style token.
-/

set_option autoImplicit false

namespace Consensus1

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

/-- `σ.f, σ.g ← e`, the draft's simultaneous assignment, as in `advance_height`'s
    `σ.target_participation, σ.progress ← false^V`. Both sides get the same `e`, which is
    what that line means. -/
scoped syntax (name := pairAssign) (priority := high) ident ", " ident " ← " term : doElem

macro_rules
  | `(doElem| $x:ident, $y:ident ← $e) =>
      `(doElem| do
          $x:ident ← $e
          $y:ident ← $e)

/-- `σ.arr[i] ← e`, an indexed write to a function-valued field, and `x[i] ← e` to a
    function-valued local. `σ.target_participation[i] ← true` is the case Figure 1
    needs. -/
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

/-- `σ.arr[i][j] ← e`, a doubly indexed write to a map-of-maps field, and `x[i][j] ← e` to
    a map-of-maps local. `Σ.head[r][i] ← (α.head, Σ.t)` is the case Figure 6 needs. Not in
    the old notation layer, which never met a two-level map. -/
scoped syntax (name := idx2Assign) (priority := high)
  ident noWs "[" term "]" noWs "[" term "]" " ← " term : doElem

macro_rules
  | `(doElem| $x:ident[$i][$j] ← $e) => do
      let n := x.getId
      let pre := n.getPrefix
      if pre.isAnonymous then
        `(doElem| $x:ident :=
            Function.update $x:ident $i (Function.update ($x:ident $i) $j $e))
      else
        let v := mkIdent pre
        let f := mkIdent (Name.mkSimple n.getString!)
        `(doElem| $v:ident :=
            { $v with $f:ident :=
                (Function.update (($v).$f:ident) $i
                  (Function.update ((($v).$f:ident) $i) $j $e)) })

end Consensus1
