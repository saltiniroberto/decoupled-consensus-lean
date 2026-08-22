import Mathlib.Data.Finset.Sort
import Spec.Consensus.FinsetM

/-!
# A monadic image and a sorted list over a `Finset`

**This file is not a specification.** It holds no protocol content, and nothing in it names
anything from the draft. It is general Lean machinery in the root `Finset` namespace, the way
`Spec/Consensus/FinsetM.lean` is.

`Finset.image` is pure, so a function that can fail has nowhere to put the failure. `imageM`
is the version that does. `FG.updateFinality` (Figure 7) is the caller: line 15's
`max{Σ.σ[B].h : B ∈ T_F(Σ)}` reads the state map per live block, and a missing entry has to
reach whoever asked.

`toSortedList` is `Finset.toList` without the choice; its docstring says how.

## Why this file imports across the subtrees

`Finset.unionM` and `Finset.filterM` live in `Spec/Consensus/FinsetM.lean`. The renderings
share no protocol content, but that file holds none — it is root-namespace machinery, and a
second copy of a root-namespace declaration would be a name collision, not a duplicate
(measured when this subtree was laid out; `CONTEXT.md`, 2026-08-22). So this file imports it
rather than copying it, and adds the one combinator the other rendering never needed. The
addition sits here rather than there because that subtree stays as it was (Roberto,
2026-08-22).

The design constraint is the one that file states: `Finset.fold` is the only computable route
over a `Finset`, and it costs a commutative and associative combining operation. `unionM` is
that operation, so the instances a monad supplies for `filterM` serve `imageM` unchanged.
-/

set_option autoImplicit false

namespace Finset

variable {α β : Type} {m : Type → Type}

/-- `s.imageM f`: the image of `s` under an effectful `f`, in any monad whose `unionM` does
    not care about the order the set is traversed in. -/
def imageM [DecidableEq β] [Monad m]
    [Std.Commutative (unionM (α := β) (m := m))]
    [Std.Associative (unionM (α := β) (m := m))]
    (f : α → m β) (s : Finset α) : m (Finset β) :=
  s.fold unionM (pure ∅) fun a => do return {← f a}

/-- `s.toSortedList`: the members of `s` as one canonical list, sorted by the order the
    instance supplies. `Finset.toList` without the choice: sorting is permutation-invariant,
    so it descends to the `Finset` quotient and stays computable, where `toList` must pick a
    representative and needs `Classical.choice` for it. `proposeBlock` (Figure 2, line 25)
    is the caller. -/
def toSortedList [LinearOrder α] (s : Finset α) : List α :=
  s.sort (· ≤ ·)

end Finset
