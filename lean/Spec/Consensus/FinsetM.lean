import Mathlib.Data.Finset.Fold

/-!
# A filter over a `Finset` that propagates the monad's effect

**This file is not a specification.** It holds no protocol content, and nothing in it names
anything from the draft. It is general Lean machinery, sitting below the figures so that a
figure file states what the draft says and nothing else.

`Finset.filter` is pure, so a predicate that can fail has nowhere to put the failure. This is
the version that does. `Store.viableLeaves` (Figure 2) is the caller: it reads the state map
per leaf, and a missing entry has to reach whoever asked.

## `Finset.fold` is the only route, and its two instance arguments are the whole design

A `Finset` is a `Multiset` with a nodup proof, and a `Multiset` is a list up to permutation,
so **there is no computable loop over one**: no `ForIn` instance exists, and `Finset.toList`
depends on `Classical.choice`, so picking an order needs choice. Measured 2026-08-21.

`Finset.fold` is available instead, at the price of a commutative and associative combining
operation — and supplying those two instances *is* what it means for a monad to be usable
over a set. A monad whose effects notice the order cannot supply them, and should not:
`StateM` is the example, where two writes in different orders leave different states.

Computable: `#eval` runs it, and `Finset.fold` itself is choice-free. The `Classical.choice`
that appears in the axiom list of anything built on this comes from `Finset.union_comm` inside
a commutativity instance, which is a `Prop` field and erased at compile time.
-/

set_option autoImplicit false

namespace Finset

variable {α : Type} {m : Type → Type}

/-- Combine two monadic sets: run both, take the union. -/
def unionM [DecidableEq α] [Monad m] (x y : m (Finset α)) : m (Finset α) := do
  let a ← x
  let b ← y
  return a ∪ b

/-- `s.filterM p`: keep the members `p` accepts, in any monad whose `unionM` does not care
    about the order the set is traversed in. -/
def filterM [DecidableEq α] [Monad m]
    [Std.Commutative (unionM (α := α) (m := m))]
    [Std.Associative (unionM (α := α) (m := m))]
    (p : α → m Bool) (s : Finset α) : m (Finset α) :=
  s.fold unionM (pure ∅) fun a => do
    if ← p a then return {a} else return ∅

end Finset
