module
public import Goldilocks

@[expose] public section

/-!
# The vocabulary of the statements about accountable safety

The definitions the statements about accountable safety at the chain level read
(`AccountableStatements.lean`):

- `E2 a a'` and `E1 a a'`, the two slashing conditions on a pair of attestations of one
  validator;
- `RootsNameBlocksOn B B'`, `RootCollisionOn B B'` and `RootCollisionIn tree`, whether two
  different blocks share a root;
- `SlashableBetween B B'`, at least `2q − n` validators each with a pair of attestations, one
  included on each of two chains, meeting a slashing condition.


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- `E2 a a'`: the two attestations are target votes at one height for different blocks.

The variables:
- `a`, `a'`: the two attestations.

Read aloud: `a` and `a'` are two target votes at one height for different blocks. -/
def E2 (a a' : Attestation V) : Prop :=
  a.h = a'.h ∧ a.τ = false ∧ a'.τ = false ∧ a.T ≠ a'.T

omit [DecidableEq V] [Fintype V] in
/-- `E1 a a'`: the attestation `a` carries a finality pair `(h, T)`, and `a'` is a vote at the
height `h`, a target vote or a timeout, naming a block other than `T`.

The variables:
- `a`: the attestation carrying the finality pair; `a'`: the vote at its height.

Read aloud: `a` carries the finality pair `(h, T)` and `a'` is a vote at `h` naming a block other
than `T`. -/
def E1 (a a' : Attestation V) : Prop :=
  ∃ p : FinalityPair, a.finality_pair = some p ∧ a'.h = p.hf ∧ a'.T ≠ p.Tf

omit [Fintype V] in
/-- `RootsNameBlocksOn B B'`: no two different blocks of the two chains ending at `B` and `B'`
share a root.

The variables:
- `B`, `B'`: the two blocks whose chains are read.

Read aloud: two blocks, each `B`, `B'` or an ancestor of one of them, with the same root are the
same block. -/
def RootsNameBlocksOn (B B' : Block V) : Prop :=
  ∀ X Y : Block V, (X.AncestorEq B ∨ X.AncestorEq B') → (Y.AncestorEq B ∨ Y.AncestorEq B') →
    X.root = Y.root → X = Y

omit [Fintype V] in
/-- `RootCollisionOn B B'`: two different blocks of the two chains ending at `B` and `B'` share a
root.

The variables:
- `B`, `B'`: the two blocks whose chains are read.

Read aloud: two different blocks, each `B`, `B'` or an ancestor of one of them, have the same
root. -/
def RootCollisionOn (B B' : Block V) : Prop :=
  ∃ X Y : Block V, (X.AncestorEq B ∨ X.AncestorEq B') ∧ (Y.AncestorEq B ∨ Y.AncestorEq B') ∧
    X.root = Y.root ∧ X ≠ Y

omit [Fintype V] in
/-- `RootCollisionIn tree`: two different blocks of `tree` share a root.

The variables:
- `tree`: the set of blocks.

Read aloud: two different blocks of `tree` have the same root. -/
def RootCollisionIn (tree : Finset (Block V)) : Prop :=
  ∃ X ∈ tree, ∃ Y ∈ tree, X.root = Y.root ∧ X ≠ Y

/-- `SlashableBetween B B'`: at least `2 * quorum V - validator_count V` validators each signed
two attestations, one included in `B` or an ancestor of `B` and the other in `B'` or an ancestor
of `B'`, in either order, that together meet `E1` or `E2`.

The variables:
- `B`, `B'`: the two blocks whose chains hold the attestations.

Read aloud: at least `2q − n` validators each signed two attestations, one included on each of
the two chains, that together meet E1 or E2. -/
def SlashableBetween (B B' : Block V) : Prop :=
  ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
    ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
      ((on_chain a B = true ∧ on_chain a' B' = true) ∨
        (on_chain a' B = true ∧ on_chain a B' = true)) ∧
      (E1 a a' ∨ E2 a a')

end GoldilocksCorrectness.Statements.Routines
