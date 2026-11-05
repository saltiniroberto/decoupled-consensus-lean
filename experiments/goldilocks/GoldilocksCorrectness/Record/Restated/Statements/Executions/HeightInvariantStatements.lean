module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.FrameDefs

@[expose] public section

/-!
# HeightInvariantStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HeightInvariantStatements.lean` over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`, proved in
`Record/Restated/Proofs/Executions/HeightInvariant.lean`: Lemma 57b at every step and before every
time, and the entry block in box 2, read with the greatest chain-state height `hMax M S.C n` of the
node's tree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (hMax)

open GoldilocksCorrectness.Record.Statements.Routines (BoxTwo)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 57b, the justified block entered its height.** At every step of every execution,
every validator's justified block is the genesis block, or the `T_h` of the chain state its FG
state holds for it, the block that took that block's chain into its height, is that block itself
(`JustifiedIsEntry`).

Why: a chain state's justified block is the genesis block (at the justification height `0`) or
the `T_h` of one of its ancestors-or-self (Lemma 47 (f)), and a `T_h` is its own `T_h`. The only
writer of a validator's justified block is the finality update, which writes the justified block
of the chain state it reads, the chain state of an accepted block; so the property holds along an
execution by induction on the step, from the initial justified block, the genesis block. The FG
state's chain state of its justified block is the computed one, since the justified block is in
the tree (Lemmas 11 and 57).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: a validator's justified block is the genesis block or the block that took its chain
into its height. -/
theorem lem57b_justified_is_entry (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    JustifiedIsEntry M S.C (x.st i v) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem57b_justified_is_entry M F) S A x R E i v

/-- Lemma 57b before a time `t`: `v`'s node state before `t` satisfies `JustifiedIsEntry`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.

Read aloud: before every time, a validator's justified block is the genesis block or entered its
height. -/
theorem justifiedIsEntry_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    JustifiedIsEntry M S.C (x.stateBefore t v) :=
  (lem57b_justified_is_entry M F) S A x R E (x.stepBefore t) v

/-- **The entry block in box 2.** When `v`'s FG state before `t` is in box 2 with the justified
block `J₀` (`BoxTwo`: `h_max = h_j + 1`, not contested, `S.J = J₀`), `J₀` is not the genesis
block, `J₀` is `B` or an ancestor of `B`, and `B`'s chain-state height is `h_max − 1`, then the
block that took `B`'s chain into its height (`(M.chainStateOf S.C B).T_h`) is `J₀`.

Why: `J₀`'s chain-state height is the justification height `h_j = h_max − 1` (Lemma 57's
`JustifiedHeight`, `J₀` not the genesis block), which is `B`'s; two blocks of one chain at one
height have the same `T_h` (Lemma 47 (e)), and `J₀`'s `T_h` is `J₀` (Lemma 57b).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `B`: the block on `J₀`'s chain; `J₀`: the justified block.

Read aloud: in box 2, a block on `J₀`'s chain at height `h_max − 1` has `J₀` as the block that took
its chain into that height. -/
theorem entry_block_of_boxTwo (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (B J₀ : Block V)
    -- `v`'s FG state before `t` is in box 2 with the justified block `J₀`
    (hBox : BoxTwo M S.C (x.stateBefore t v) J₀)
    -- `J₀` is not the genesis block
    (hJ₀ : J₀ ≠ Block.genesis)
    -- `J₀` is `B` or an ancestor of `B`
    (hJB : J₀.AncestorEq B)
    -- `B`'s chain-state height is `h_max − 1`
    (hH : (M.chainStateOf S.C B).h = hMax M S.C (x.stateBefore t v) - 1) :
    -- then the block that took `B`'s chain into its height is `J₀`
    (M.chainStateOf S.C B).T_h = J₀ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.entry_block_of_boxTwo M F) S A x R E t v B J₀ hBox hJ₀ hJB hH

end GoldilocksCorrectness.Record.Statements.Executions

