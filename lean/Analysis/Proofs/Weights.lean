import Spec
-- `Spec` imports only `…Finset.Defs`, enough to *state* a weight sum but not to reason about one.
-- `Finset.sum_union_inter` and `Finset.sum_le_sum_of_subset` live here.
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Proofs: weights and thresholds

The arguments behind Section 2's lemmas. `Analysis/Lemmas.lean` holds the statements of record and
calls into here in one line, so that a statement can be read against the paper without a proof
between it and the reader.

Nothing here is a statement of record: `MAPPING.md` names only the `lem…` declarations in
`Analysis/Lemmas.lean`, and the citation check enforces that. Names here are free, and are the
paper's phrase without the `lem` prefix.
-/

set_option autoImplicit false

namespace Decoupled.Proofs

open Decoupled

/-- A union and an intersection together weigh what the two sets weigh, and the union sits inside
    the electorate. Both halves of Lemma 2 rest on this. -/
theorem weightInterGe {Node : Type} [DecidableEq Node] [Electorate Node] {Q Q' : Finset Node}
    (hQV : Q ⊆ Electorate.V) (hQ'V : Q' ⊆ Electorate.V) :
    weight Q + weight Q' ≤ W Node + weight (Q ∩ Q') := by
  have key : weight (Q ∪ Q') + weight (Q ∩ Q') = weight Q + weight Q' := by
    simp only [weight]; exact Finset.sum_union_inter
  have hle : weight (Q ∪ Q') ≤ W Node := by
    simp only [weight, W]
    exact Finset.sum_le_sum_of_subset (Finset.union_subset hQV hQ'V)
  omega

/-- Lemma 1 (`lem:integer-thresholds`). Pure `Nat` arithmetic once `q` and `m` are unfolded: `q` is
    `(2W + 2) / 3` and `m` is `W / 2 + 1`, and `omega` handles division by a literal. -/
theorem integerThresholds {Node : Type} [Electorate Node] (b : Nat) (hb : 3 * b < W Node) :
    W Node - b ≥ q Node ∧ q Node ≥ m Node ∧ m Node > b ∧ q Node > b ∧
      2 * q Node - W Node > b := by
  simp only [q, m]
  omega

/-- Lemma 2 (`lem:quorum-intersection`), the bound. -/
theorem quorumIntersection {Node : Type} [DecidableEq Node] [Electorate Node]
    {Q Q' : Finset Node} (hQV : Q ⊆ Electorate.V) (hQ'V : Q' ⊆ Electorate.V)
    (hQ : Quorum Q) (hQ' : Quorum Q') :
    weight (Q ∩ Q') ≥ 2 * q Node - W Node := by
  have h := weightInterGe hQV hQ'V
  unfold Quorum at hQ hQ'
  omega

/-- Lemma 2's "consequently their intersection contains non-Byzantine weight". Needs Assumption 1's
    `b` and its bound, which the bound above does not. -/
theorem quorumIntersectionNonByzantine {Node : Type} [DecidableEq Node] [Electorate Node]
    {Q Q' : Finset Node} (hQV : Q ⊆ Electorate.V) (hQ'V : Q' ⊆ Electorate.V)
    (hQ : Quorum Q) (hQ' : Quorum Q') (b : Nat) (hb : 3 * b < W Node) :
    weight (Q ∩ Q') > b := by
  have h := weightInterGe hQV hQ'V
  unfold Quorum at hQ hQ'
  simp only [q] at hQ hQ'
  omega

end Decoupled.Proofs
