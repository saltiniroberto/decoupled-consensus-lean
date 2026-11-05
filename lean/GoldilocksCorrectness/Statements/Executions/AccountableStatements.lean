module
public import GoldilocksCorrectness.Proofs.Executions.Accountable

@[expose] public section

/-!
# The statements about accountable safety over executions

The audited statements about the finalized blocks of the validators of an execution, each proved
in `GoldilocksCorrectness/Proofs/Executions/FinalizedFromChain.lean` or
`GoldilocksCorrectness/Proofs/Executions/Accountable.lean`:

- every validator's finalized block, at every step, is the finalized block of the chain state of a
  block of its tree;
- Lemma 73: two validators' finalized blocks, read at any two steps, that conflict leave
  `2q − n` slashable validators across a chain of each tree, or two different blocks of the two
  trees taken together share a root.
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (FinalizedFromChain)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (SlashableBetween RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- At every step of every execution, every validator's finalized block is the finalized block of
the chain state of a block of its tree (`FinalizedFromChain`).

Why: the initial finalized block is the genesis block, the finalized block of the genesis block's
chain state; the only routine that moves the finalized block, the finality update run when a block
is accepted, writes the finalized block of the chain state computed for that block, which is the
block's own because its parent is in the tree (Lemma 11).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: at every step of every execution, every validator's finalized block is the finalized
block of the chain state of a block the validator holds. -/
theorem finalizedFromChain_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    FinalizedFromChain S.C (x[i][v].st).S :=
  GoldilocksCorrectness.Proofs.Executions.finalizedFromChain_of_exec S Sched x i v

/-- **Lemma 73, accountable safety over executions.** When the finalized block of `p₁`'s node
state after `i` steps and that of `p₂`'s node state after `j` steps conflict (neither is the other
or an ancestor of the other), the tree of the first holds a block `b₁` and the tree of the second a
block `b₂` such that at least `2q − n` validators each signed two attestations, one included on
`b₁`'s chain and one on `b₂`'s, in either order, meeting E1 or E2 (`SlashableBetween b₁ b₂`); or
two different blocks of the two trees taken together share a root (`RootCollisionIn`).

Why: each finalized block is the finalized block of the chain state of a block of its tree, and
Lemma 70 applies to those two blocks; a root shared by two blocks of their two chains is shared in
the two trees, which hold every ancestor of their blocks.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`, `j`: the two steps; `p₁`, `p₂`:
  the two validators.



Read aloud: take any execution, any two steps and any two validators whose finalized blocks
conflict; then either at least `2q − n` validators each signed two attestations, one included on a
chain of the first tree and one on a chain of the second, meeting E1 or E2, or two different blocks
of the two trees share a root. -/
theorem lem73_accountable_safety (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i j : ℕ) (p₁ p₂ : V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (x[i][p₁].st).S.F.compatible (x[j][p₂].st).S.F = false) :
    (∃ b₁ ∈ (x[i][p₁].st).S.T, ∃ b₂ ∈ (x[j][p₂].st).S.T, SlashableBetween b₁ b₂) ∨
      RootCollisionIn ((x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) :=
  GoldilocksCorrectness.Proofs.Executions.lem73_accountable_safety S Sched x i j p₁ p₂ hConflict

end GoldilocksCorrectness.Statements.Executions
