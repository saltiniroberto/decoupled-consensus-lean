module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Statements.Executions.PhaseDefs

@[expose] public section

/-!
# PhaseDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/PhaseDefs.lean` over a model `M`:
the sequence of honest round opening slots and the round's members, read at the model's times; for
an execution `x` of `protocolOf M S`, the family of the front, the quiet round and the round that
fails to be quiet only at the vote time. The definitions that read the setup's numbers only
(`healFrontSlots`, `InSpan`, `OutsideSpans`, `OpeningsOutsideSpans`,
`OpeningsOutsideWaitsAndWindows`, their decidability instances) have no twin; the twins read the
landed ones.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

export GoldilocksCorrectness.Record.Statements.AbstractTrace (roundMembers)

omit [RootOrder] in
/-- A sequence of honest round opening slots `r 0 * R < … < r m * R`, read at the model `M`'s
times. -/
structure HonestOpeningSeq (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (r : ℕ → ℕ) (m tFirst tLast : ℕ) :
    Prop where
  /-- The rounds increase. -/
  mono : ∀ i : ℕ, i < m → r i < r (i + 1)
  /-- The first slot of the first opening starts at or after `tFirst`. -/
  first : tFirst ≤ M.slotStart S.C (r 0 * S.C.R)
  /-- The last opening's action time, two delays after its slot's start, is at most `tLast`. -/
  last : M.supportCutoff S.C (r m * S.C.R) ≤ tLast
  /-- Every validator's tick to a clock value at most the last opening's support cutoff is at a
  real time at most `tLast`: step `k` of the execution `x` is the tick of `u` to the clock value
  `c`, with `c` at most that cutoff, and `x`'s real time of step `k` is at most `tLast`. -/
  lastTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
    c ≤ M.supportCutoff S.C (r m * S.C.R) → (x.time k : ℝ) ≤ tLast
  /-- The proposer of every opening, the last included, is outside the adversary set at the
  support cutoff of its own slot, two delays after the slot's start. -/
  honest : ∀ i : ℕ, i ≤ m →
    S.P.proposer (r i * S.C.R) ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R))
  /-- The first slot of opening `i + 2` is at most `δt + 1` slots after the first slot of
  opening `i`. A block that leaves a height by the timeout branch has a slot at least `δt` after
  the slot of that height's entry, and that entry is a strict descendant of the previous
  opening's proposal; so no such block is a strict ancestor of the next opening's proposal. -/
  spacing : ∀ i : ℕ, i + 2 ≤ m → r (i + 2) * S.C.R ≤ r i * S.C.R + S.C.δt + 1

omit [RootOrder] in
/-- `TicksToUpdatesBy M S x t`: at the time `t`, no slot's update is half run. For every slot `σ`
whose update, the support cutoff `M.supportCutoff S.C (σ + 1)` of the next slot, is at most `t`, or
to whose update some validator ticked at a real time at most `t`: every tick to a clock value at
most that cutoff, step `k` of `x` being the tick of `u` to the clock value `c`, is at a real time at
most `t`.

The two triggers are the two ways a statement names a slot: by its update being at most `t`, and by
a tick to it at a real time at most `t` (a tick may come up to the clock's lead before the cutoff).

The variables:
- `M`: the model; `S`: the setup; `x`: the execution; `t`: the time.

Read aloud: at `t`, every slot whose update is due or begun has had that update run by every
validator that runs it, and so has every earlier clock value. -/
def TicksToUpdatesBy (S : Setup V) {Msg N : Type} (x : Trace V Msg N) (t : ℕ) : Prop :=
  ∀ (σ k : ℕ) (u : V) (c : ℕ),
    (M.supportCutoff S.C (σ + 1) ≤ t ∨
      ∃ (k' : ℕ) (u' : V), x.lbl k' = Event.tick u' (M.supportCutoff S.C (σ + 1)) ∧ (x.time k' : ℝ) ≤ t) →
    x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (σ + 1) → (x.time k : ℝ) ≤ t

omit [RootOrder] in
/-- `FrontFamily M S Sched x Hon s' C`: `C` is the block of a lock entry some member of `Hon` holds
live in the state its tick to the vote time of slot `s' + 1` starts from, or the root of some
member's fork choice in that state.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the members; `s'`: the slot; `C`: the block.

Read aloud: the family of the available chain's front at slot `s'`: the members' live lock blocks
and their fork-choice roots as their ticks to the vote time of the next slot read them. -/
def FrontFamily (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : Finset V) (s' : ℕ) (C : Block V) : Prop :=
  (∃ w ∈ Hon, ∃ e ∈ (x.tickInput w (M.voteTime S.C (s' + 1))).lockEntries,
    M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
      ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true ∧ e.B = C) ∨
  (∃ w ∈ Hon, M.get_fc_root (x.tickInput w (M.voteTime S.C (s' + 1))) = C)

/-- `QuietRound M S Sched x Hon B s s''`: the round whose first slot is `s`, whose proposal is `B`
and whose next honest round opening slot is `s''` is quiet, each clause read at the members of the
slot it reads:

- in the state its tick to the vote time of slot `s` starts from, every member of `Hon s` has its
  fork-choice root `B.parent` or an ancestor of it, and its `head_height_floor` (the least
  chain-state height at which a block is viable in its state) at most the chain-state height of
  `B.parent`;
- in the state its tick to `M.supportCutoff S.C (s + 1)` starts from, every member of `Hon s` has
  its fork-choice root `B` or an ancestor of `B`, and its `head_height_floor` at most the
  chain-state height of `B`;
- for every slot `s'` of the round with `s ≤ s'` and `s' + 2 ≤ s''`, every member of
  `Hon (s' + 1)` satisfies `StepFrameAt M S Sched x B s'`: its root is compatible with `B` before
  the vote time of slot `s' + 1`, a viable head is on `B`'s chain in its voter tree when the root
  is on `B`'s chain, and its finalized block is compatible with `B` before the support cutoff of
  slot `s' + 2`.

`Hon s'` is the set the round reads at slot `s'`, the validators honest at the update of slot
`s'`; the phase passes `Hon s' := roundMembers M S Sched (s' + 1)`. The members of `Hon s` are
honest at `M.supportCutoff S.C (s + 1)`, after the first two clauses read; the members of
`Hon (s' + 1)` are honest at `M.supportCutoff S.C (s' + 2)`, the last time
`StepFrameAt M S Sched x B s'` reads. Lemma 80 over per-slot member sets,
`lem80wq_round_height_advances_steps`, reads these clauses.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.

 the first two clauses read each member's own state at
its own tick.

Read aloud: the members find the proposal's parent viable at the vote time, the proposal viable at
the action time, and every step of the round keeps their roots and finalized blocks compatible
with the proposal. -/
def QuietRound (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ) : Prop :=
  (∀ w ∈ Hon s, (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent ∧
    M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h) ∧
  (∀ v ∈ Hon s, (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))).AncestorEq B ∧
    M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤
      (M.chainStateOf S.C B).h) ∧
  (∀ s', s ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)

/-- `ParentKindRound M S Sched x Hon B s s''`: the round whose first slot is `s`, whose proposal is
`B` and whose next honest round opening slot is `s''` fails to be quiet only by the vote-time clause
on `head_height_floor`:

- some member of `Hon s` has its `head_height_floor` before the vote time of slot `s` greater
  than the chain-state height of `B.parent`;
- before the vote time of slot `s`, every member of `Hon s` has its fork-choice root `B.parent`
  or an ancestor of it;
- before the action time `M.supportCutoff S.C (s + 1)`, every member of `Hon s` has its fork-choice
  root `B` or an ancestor of `B`, and its `head_height_floor` at most the chain-state height of
  `B`;
- for every slot `s'` of the round with `s ≤ s'` and `s' + 2 ≤ s''`, every member of
  `Hon (s' + 1)` satisfies `StepFrameAt M S Sched x B s'`.

Such a round does not switch the honest chain; the count of the phase bounds how many there are.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.



Read aloud: a round that is not quiet only because some member, at the vote time, does not find
a block at the chain-state height of the proposal's parent viable. -/
def ParentKindRound (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ) : Prop :=
  (∃ w ∈ Hon s, (M.chainStateOf S.C B.parent).h <
      M.head_height_floor (x.stateBefore (M.voteTime S.C s) w)) ∧
  (∀ w ∈ Hon s, (M.get_fc_root (x.stateBefore (M.voteTime S.C s) w)).AncestorEq B.parent) ∧
  (∀ v ∈ Hon s, (M.get_fc_root (x.stateBefore (M.supportCutoff S.C (s + 1)) v)).AncestorEq B ∧
    M.head_height_floor (x.stateBefore (M.supportCutoff S.C (s + 1)) v) ≤
      (M.chainStateOf S.C B).h) ∧
  (∀ s', s ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)

end GoldilocksCorrectness.Record.Statements.Executions

