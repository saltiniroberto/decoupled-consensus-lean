module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Accountable

@[expose] public section

/-!
# AccountableStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/AccountableStatements.lean` over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`, proved in
`Record/Restated/Proofs/Executions/FinalizedFromChain.lean` and
`Record/Restated/Proofs/Executions/Accountable.lean`: every validator's finalized block is the
finalized block of the chain state of a block of its tree, and Lemma 73.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (FinalizedFromChain SlashableBetween)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- At every step of every execution, every validator's finalized block is the finalized block of
the chain state of a block of its tree (`FinalizedFromChain`).

Why: the initial finalized block is the genesis block, the finalized block of the genesis block's
chain state; the only routine that moves the finalized block, the finality update run when a block
is accepted, writes the finalized block of the chain state computed for that block, which is the
block's own because its parent is in the tree (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: at every step of every execution, every validator's finalized block is the finalized
block of the chain state of a block the validator holds. -/
theorem finalizedFromChain_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    FinalizedFromChain M S.C (x.st i v) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.finalizedFromChain_of_exec M F) S A x R E i v

/-- **Lemma 73, accountable safety over executions.** When the finalized block of `p₁`'s node
state after `i` steps and that of `p₂`'s node state after `j` steps conflict (neither is the other
or an ancestor of the other), the tree of the first holds a block `b₁` and the tree of the second a
block `b₂` such that at least `2q − n` validators each signed two attestations, one included on
`b₁`'s chain and one on `b₂`'s, in either order, meeting E1 or E2 (`SlashableBetween M b₁ b₂`); or
two different blocks of the two trees taken together share a root (`RootCollisionIn`).

Why: each finalized block is the finalized block of the chain state of a block of its tree, and
Lemma 70 applies to those two blocks; a root shared by two blocks of their two chains is shared in
the two trees, which hold every ancestor of their blocks.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`, `j`: the two steps; `p₁`, `p₂`:
  the two validators.



Read aloud: take any execution, any two steps and any two validators whose finalized blocks
conflict; then either at least `2q − n` validators each signed two attestations, one included on a
chain of the first tree and one on a chain of the second, meeting E1 or E2, or two different blocks
of the two trees share a root. -/
theorem lem73_accountable_safety (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i j : ℕ) (p₁ p₂ : V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (x.st i p₁).finalized.compatible (x.st j p₂).finalized = false) :
    (∃ b₁ ∈ (x.st i p₁).tree, ∃ b₂ ∈ (x.st j p₂).tree, SlashableBetween M b₁ b₂) ∨
      RootCollisionIn ((x.st i p₁).tree ∪ (x.st j p₂).tree) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem73_accountable_safety M F Fx) S A x R E i j p₁ p₂ hConflict

end GoldilocksCorrectness.Record.Statements.Executions

