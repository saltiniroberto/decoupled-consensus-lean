import Mathlib.Data.Finset.Fold

/-!
# Monadic filter and image over a `Finset`

**This file is not a specification.** It holds no protocol content, and nothing in it names
anything from the protocol. It is general Lean machinery in the root `Finset` namespace.

`Finset.filter` and `Finset.image` are pure, so a predicate or function that can fail has
nowhere to put the failure. These are the versions that do. The callers are the set
operations over raising reads: `ghost`'s eligibility filter,
`Store.viable` and `Store.updateFinality` (Figure 7), each reading the state map per
member, where a missing entry has to reach whoever asked.

## `Finset.fold` is the only route, and its two instance arguments are the whole design

A `Finset` is a `Multiset` with a nodup proof, and a `Multiset` is a list up to permutation,
so **there is no computable loop over one**: no `ForIn` instance exists, and `Finset.toList`
depends on `Classical.choice`, so picking an order needs choice. Measured 2026-08-21.

`Finset.fold` is available instead, at the price of a commutative and associative combining
operation — and supplying those two instances *is* what it means for a monad to be usable
over a set. A monad whose effects notice the order cannot supply them, and should not:
`StateM` is the example, where two writes in different orders leave different states.
`unionM` is the operation, so the instances a monad supplies for `filterM` serve `imageM`
unchanged; `Raise.lean` supplies them for `DRE`, and why they are *false* at `NDRE` is
recorded there and in `Nondet.lean`.

Computable: `#eval` runs it, and `Finset.fold` itself is choice-free. The `Classical.choice`
that appears in the axiom list of anything built on this comes from `Finset.union_comm` inside
a commutativity instance, which is a `Prop` field and erased at compile time.
-/

set_option autoImplicit false

namespace Finset

variable {α β : Type} {m : Type → Type}

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

/-- `s.imageM f`: the image of `s` under an effectful `f`, in any monad whose `unionM` does
    not care about the order the set is traversed in. -/
def imageM [DecidableEq β] [Monad m]
    [Std.Commutative (unionM (α := β) (m := m))]
    [Std.Associative (unionM (α := β) (m := m))]
    (f : α → m β) (s : Finset α) : m (Finset β) :=
  s.fold unionM (pure ∅) fun a => do return {← f a}

end Finset
