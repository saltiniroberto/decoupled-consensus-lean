import Spec.Defs.Nondet
import Spec.Defs.Store

/-!
# Parked definitions: compiled, unconsumed

**This file is not a specification.** It holds machinery with no current consumer, kept
compiling here instead of deleted, so reviving a piece is a move into a spec file rather
than an excavation. Each entry says what it is and what would revive it. Nothing under
`Spec/` may import this file: a revived definition moves out first.
-/

set_option autoImplicit false

namespace DC

/-- `d.withSend prior`: a `DutyResult` with an earlier duty's broadcasts unioned into
    its own. In the duty monad the outbox carries earlier sends, so nothing unions.
    Revived by any composition done on `DutyResult` values rather than in the monad. -/
def DutyResult.withSend {Validator : Type} [Roots] [DecidableEq Validator]
    (d : DutyResult Validator) (prior : Finset (Message Validator)) :
    DutyResult Validator :=
  { d with send := prior ∪ d.send }

/-- The autoparam extraction from an option: `x.value`, its `x ≠ ⊥` hypothesis
    discharged from a dependent `if _ : x ≠ ⊥` by the instants' own tactic. The raising
    lift in `Raise.lean` — `let y ← x` behind a plain `≠ ⊥` test — covers the monadic
    bodies, so this has no consumer. Revived by a *pure* body that must extract, where no
    lift can fire. The measured trap it carries:
    dot notation resolves fields in the type's own namespace only, hence the `_root_.`
    (a `DC.Option.value` is invisible to `x.value`). -/
def _root_.Option.value {α : Type} (x : Option α)
    (h : x ≠ ⊥ := by solve_by_elim [And.left, And.right]) : α :=
  x.get (Option.ne_none_iff_isSome.mp h)

/-- `for x in (s : Finset α) do …`, in any monad `Set` lifts into: pick a listing, loop the
    list — every visitation order among the outcomes. No spec routine loops over a
    `Finset` (`ghost` loops a range, the handlers loop `List`s, the order-free loops are
    written as the sets they build), so the instance has no consumer. Revived by the
    first loop whose body is not order-free. -/
scoped instance {α : Type} {m : Type → Type} [Monad m] [MonadLiftT Set m] [DecidableEq α] :
    ForIn m (Finset α) α where
  forIn s init body := do
    let l ← liftM (listings s)
    forIn l init body

end DC
