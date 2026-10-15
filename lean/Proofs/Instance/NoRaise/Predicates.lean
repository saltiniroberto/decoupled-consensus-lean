import Spec.Node

/-!
# The conditions under which the spec's tick does not raise

Predicates over the spec's types: `DistinctRoots`, `Stamped` and `GradesDue`, under which the
no-raise lemmas are stated, and `ParentClosed` and `StoreOk`, which define the store and node types
of `Model.spec`.
-/

set_option autoImplicit false

namespace SpecRecord.NoRaise

open Spec

variable {V : Type}

/-- No two distinct blocks of the tree `T` share a root. -/
def DistinctRoots (T : Finset (Block V)) : Prop :=
  ∀ B ∈ T, ∀ B' ∈ T, B.root = B'.root → B = B'

/-- Everything the store `st` holds has a stamp: every block of its tree, every Goldfish vote of
    `st.gf_votes s`, and the SG vote `Protocol.sgVote a` of every attestation `a` of
    `st.attestations r`. -/
def Stamped (st : Store V) : Prop :=
  (∀ B ∈ st.T, st.timestamp_block B ≠ none) ∧
  (∀ s, ∀ u ∈ st.gf_votes s, st.timestamp_vote u ≠ none) ∧
  (∀ r, ∀ a ∈ st.attestations r, st.timestamp_sg_vote (Protocol.sgVote a) ≠ none)

/-- The tree `T` holds the parent of each of its blocks. -/
def ParentClosed (T : Finset (Block V)) : Prop :=
  ∀ B ∈ T, B.parent ∈ T

/-- The store `st` is `Stamped`, its tree has `DistinctRoots` and is `ParentClosed`, and its tree
    holds its finalized block `st.F`. -/
def StoreOk (st : Store V) : Prop :=
  Stamped st ∧ DistinctRoots st.T ∧ ParentClosed st.T ∧ st.F ∈ st.T

/-- The store's clock is non-negative, the saved grades are aligned to the clock's round, and every
    grade result a duty of that round may read is computed, as far as the node's wake value
    requires. -/
def GradesDue (C : Config) (n : NodeState V) : Prop :=
  0 ≤ n.st.t ∧
  n.st.saved_grades.round = C.round_of (C.slotOf n.st.t) ∧
  ∀ a, n.awakeSince = some a →
    let c := n.st.saved_grades
    (a ≤ grade1_window_start C c.round → c.current.g1 ≠ .pending) ∧
    (a ≤ grade2_window_start C c.round → c.current.g2 ≠ .pending) ∧
    (a ≤ grade2_window_start C c.round → C.opening c.round + C.Δ ≤ n.st.t →
      c.current.g0 ≠ .pending) ∧
    (a ≤ grade2_window_start C (c.round + 1) → C.opening (c.round + 1) - C.Δ ≤ n.st.t →
      c.next.g2 ≠ .pending)

end SpecRecord.NoRaise
