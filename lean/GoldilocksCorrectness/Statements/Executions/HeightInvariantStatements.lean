module
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.FrameDefs
public import GoldilocksCorrectness.Proofs.Executions.HeightInvariant

@[expose] public section

/-!
# The justified block entered its height

The audited statements of Lemma 57b, `lem57b_justified_is_entry` (with its `stateBefore` form
`justifiedIsEntry_of_stateBefore`), an invariant theorem of its own beside the node invariant of
Lemma 11, and of the bridge `entry_block_of_boxTwo` it gives in box 2. All are proved in
`GoldilocksCorrectness/Proofs/Executions/HeightInvariant.lean`; the definition `JustifiedIsEntry`
is in `GoldilocksCorrectness/Statements/Executions/HeightInvariantDefs.lean`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (BoxTwo)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

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
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: a validator's justified block is the genesis block or the block that took its chain
into its height. -/
theorem lem57b_justified_is_entry (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    JustifiedIsEntry (x[i][v].st).S :=
  GoldilocksCorrectness.Proofs.Executions.lem57b_justified_is_entry S Sched x i v

/-- Lemma 57b before a time `t`: `v`'s node state before `t` satisfies `JustifiedIsEntry`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.

Read aloud: before every time, a validator's justified block is the genesis block or entered its
height. -/
theorem justifiedIsEntry_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    JustifiedIsEntry (stateBefore x t v).S :=
  lem57b_justified_is_entry S Sched x (stepBefore x t) v

/-- **The entry block in box 2.** When `v`'s FG state before `t` is in box 2 with the justified
block `J₀` (`BoxTwo`: `h_max = h_j + 1`, not contested, `S.J = J₀`), `J₀` is not the genesis
block, `J₀` is `B` or an ancestor of `B`, and `B`'s chain-state height is `h_max − 1`, then the
block that took `B`'s chain into its height (`(chainStateOf S.C B).T_h`) is `J₀`.

Why: `J₀`'s chain-state height is the justification height `h_j = h_max − 1` (Lemma 57's
`JustifiedHeight`, `J₀` not the genesis block), which is `B`'s; two blocks of one chain at one
height have the same `T_h` (Lemma 47 (e)), and `J₀`'s `T_h` is `J₀` (Lemma 57b).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `B`: the block on `J₀`'s chain; `J₀`: the justified block.

Read aloud: in box 2, a block on `J₀`'s chain at height `h_max − 1` has `J₀` as the block that took
its chain into that height. -/
theorem entry_block_of_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (B J₀ : Block V)
    -- `v`'s FG state before `t` is in box 2 with the justified block `J₀`
    (hBox : BoxTwo (stateBefore x t v).S J₀)
    -- `J₀` is not the genesis block
    (hJ₀ : J₀ ≠ Block.genesis)
    -- `J₀` is `B` or an ancestor of `B`
    (hJB : J₀.AncestorEq B)
    -- `B`'s chain-state height is `h_max − 1`
    (hH : (chainStateOf S.C B).h = (stateBefore x t v).S.h_max - 1) :
    -- then the block that took `B`'s chain into its height is `J₀`
    (chainStateOf S.C B).T_h = J₀ :=
  GoldilocksCorrectness.Proofs.Executions.entry_block_of_boxTwo S Sched x t v B J₀ hBox hJ₀ hJB hH

end GoldilocksCorrectness.Statements.Executions
