import Spec.Defs.Nondet
import Spec.Defs.Store

/-!
# Parked definitions: compiled, unconsumed

**This file is not a specification.** It holds machinery that lost its last consumer and is
kept compiling here instead of deleted (Roberto, 2026-08-23), so reviving a piece is a move
back to its home file rather than an excavation. Each entry says where it came from and what
would revive it. Nothing under `Spec/` may import this file: a revived definition
moves out first.
-/

set_option autoImplicit false

namespace Consensus1

open Lean

/-- `σ.arr[i][j] ← e`, a doubly indexed write to a map-of-maps field, and `x[i][j] ← e` to a
    map-of-maps local. From `Notation.lean`; written for the *older* draft's per-round
    tables (`Σ.head[r][i] ← …`), which the newer draft dropped, so no `Consensus1` figure
    writes a two-level map. Revived by any store field of shape `Nat → κ → Option V`. -/
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

/-- `d.withSend prior`: a `DutyResult` with an earlier duty's broadcasts unioned into
    its own. From `Store.lean`; its one consumer was `Store.onTick`'s composition, which
    the `NDREB` adoption (2026-08-24, `Duty.lean`) dissolved — the outbox carries earlier
    sends, so nothing unions. Revived by any composition done on `DutyResult` values
    rather than in the monad. -/
def DutyResult.withSend {Validator : Type} [Roots] [DecidableEq Validator]
    (d : DutyResult Validator) (prior : Finset (Message Validator)) :
    DutyResult Validator :=
  { d with send := prior ∪ d.send }

/-- The autoparam extraction from an option: `x.value`, its `x ≠ ⊥` hypothesis
    discharged from a dependent `if _ : x ≠ ⊥` by the instants' own tactic. From
    `Model.lean`, superseded 2026-08-24 by the raising lift in `Raise.lean` —
    `let y ← x` behind a plain `≠ ⊥` test — which took its three consumers. Revived by a
    *pure* body that must extract, where no lift can fire. The measured trap it carries:
    dot notation resolves fields in the type's own namespace only, hence the `_root_.`
    (a `Consensus1.Option.value` is invisible to `x.value`). -/
def _root_.Option.value {α : Type} (x : Option α)
    (h : x ≠ ⊥ := by solve_by_elim [And.left, And.right]) : α :=
  x.get (Option.ne_none_iff_isSome.mp h)

/-- `for x in (s : Finset α) do …`, in any monad `Set` lifts into: pick a listing, loop the
    list — every visitation order among the outcomes. From `Nondet.lean`; after the
    2026-08-23 migration no spec routine loops over a `Finset` (`ghost` loops a range, the
    handlers loop `List`s, the order-free loops became the sets they build), so the
    instance has no consumer. Revived by the first loop whose body is not order-free. -/
scoped instance {α : Type} {m : Type → Type} [Monad m] [MonadLiftT Set m] [DecidableEq α] :
    ForIn m (Finset α) α where
  forIn s init body := do
    let l ← liftM (listings s)
    forIn l init body

end Consensus1
