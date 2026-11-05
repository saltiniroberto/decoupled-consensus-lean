module
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Statements.Executions.SleepyDefs

@[expose] public section

/-!
# The phase after healing: the definitions

The definitions the lemmas of the phase read:

- `HonestOpeningSeq S Sched r m tFirst tLast`, a sequence of honest round openings;
- `roundMembers S Sched s''`, the validators honest through the round whose next honest round opening slot
  is `s''`;
- `healFrontSlots S`, the number of slots after `tGAT` before the first opening of the sequence;
- `FrontFamily S Sched x Hon s'`, the family of the available chain's front at slot `s'`;
- `QuietRound S Sched x Hon B s s''`, a round whose clauses hold at the members of the slot each
  reads;
- `ParentKindRound S Sched x Hon B s s''`, a round that fails to be quiet only by the vote-time
  clause on `head_height_floor`;
- `InSpan`, `OutsideSpans`, `OpeningsOutsideSpans` and `OpeningsOutsideWaitsAndWindows`, the
  premise that enough openings of a sequence fall outside every placement of a few spans of slots,
  of two lengths.


-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- A sequence of honest round openings `r 0 < r 1 < … < r m`, the first opening at or after
`tFirst` and the last one's action time, two delays after its slot's start, at most `tLast`. -/
structure HonestOpeningSeq (S : Setup V) (Sched : Schedule V) (r : ℕ → ℕ) (m tFirst tLast : ℕ) :
    Prop where
  /-- The rounds increase. -/
  mono : ∀ i : ℕ, i < m → r i < r (i + 1)
  /-- The first slot of the first opening starts at or after `tFirst`. -/
  first : tFirst ≤ slotStart S (r 0 * S.C.R)
  /-- The last opening's action time, two delays after its slot's start, is at most `tLast`. -/
  last : supportCutoff S (r m * S.C.R) ≤ tLast
  /-- The proposer of every opening, the last included, is outside the adversary set at the
  support cutoff of its own slot, two delays after the slot's start. -/
  honest : ∀ i : ℕ, i ≤ m →
    S.P.proposer (r i * S.C.R) ∉ Sched.adv ((supportCutoff S (r i * S.C.R) : ℕ) : Int)
  /-- The first slot of opening `i + 2` is at most `δt + 1` slots after the first slot of
  opening `i`. A block that leaves a height by the timeout branch has a slot at least `δt` after
  the slot of that height's entry, and that entry is a strict descendant of the previous
  opening's proposal; so no such block is a strict ancestor of the next opening's proposal. -/
  spacing : ∀ i : ℕ, i + 2 ≤ m → r (i + 2) * S.C.R ≤ r i * S.C.R + S.C.δt + 1

omit [RootOrder] in
/-- `roundMembers S Sched s''`: the validators outside the adversary set at the support cutoff of
slot `s''`. A round whose next honest round opening slot is `s''` reads its invariants at this set; the next
opening's proposer is one of them (`HonestOpeningSeq.honest`), and the validators honest at a
later time are among them.

The variables:
- `S`: the setup; `Sched`: the schedule; `s''`: the next honest round opening slot.

Read aloud: the members of a round are the validators honest through that round. -/
def roundMembers (S : Setup V) (Sched : Schedule V) (s'' : ℕ) : Finset V :=
  Finset.univ \ Sched.adv ((supportCutoff S s'' : ℕ) : Int)

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `healFrontSlots S`: the number of slots after `tGAT` before the first opening of the sequence:
`k + 1` for the wake rule, `2k − 1` for the available chain's healing, one for the first opening's
duty window.

The variables:
- `S`: the setup.

Read aloud: `3k + 1`. -/
def healFrontSlots (S : Setup V) : ℕ := 3 * S.C.k + 1

/-- `FrontFamily S Sched x Hon s' C`: `C` is the block of a lock entry some member of `Hon` holds
live before the vote time of slot `s' + 1`, or the root of some member's fork choice then.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the members; `s'`: the slot; `C`: the block.

Read aloud: the family of the available chain's front at slot `s'`: the members' live lock blocks
and their fork-choice roots before the vote time of the next slot. -/
def FrontFamily (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : Finset V) (s' : ℕ) (C : Block V) : Prop :=
  (∃ w ∈ Hon, ∃ e ∈ (stateBefore x (voteTime S (s' + 1)) w).A.lock_entries,
    is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
      ((voteTime S (s' + 1) : ℕ) : Int) e = true ∧ e.B = C) ∨
  (∃ w ∈ Hon, get_fc_root (stateBefore x (voteTime S (s' + 1)) w).S = C)

/-- `QuietRound S Sched x Hon B s s''`: the round whose first slot is `s`, whose proposal is `B`
and whose next honest round opening slot is `s''` is quiet, each clause read at the members of the
slot it reads:

- before the vote time of slot `s`, every member of `Hon s` has its fork-choice root `B.parent`
  or an ancestor of it, and its `head_height_floor` (the least chain-state height at which a
  block is viable in its state) at most the chain-state height of `B.parent`;
- before the action time `supportCutoff S (s + 1)`, every member of `Hon s` has its fork-choice
  root `B` or an ancestor of `B`, and its `head_height_floor` at most the chain-state height of
  `B`;
- for every slot `s'` of the round with `s ≤ s'` and `s' + 2 ≤ s''`, every member of
  `Hon (s' + 1)` satisfies `StepFrameAt S Sched x B s'`: its root is compatible with `B` before
  the vote time of slot `s' + 1`, a viable head is on `B`'s chain in its voter tree when the root
  is on `B`'s chain, and its finalized block is compatible with `B` before the support cutoff of
  slot `s' + 2`.

`Hon s'` is the set the round reads at slot `s'`, the validators honest at the update of slot
`s'`; the phase passes `Hon s' := roundMembers S Sched (s' + 1)`. The members of `Hon s` are
honest at `supportCutoff S (s + 1)`, after the first two clauses read; the members of
`Hon (s' + 1)` are honest at `supportCutoff S (s' + 2)`, the last time `StepFrameAt S Sched x B s'`
reads. Lemma 80 over per-slot member sets, `lem80wq_round_height_advances_steps`, reads these
clauses.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.



Read aloud: the members find the proposal's parent viable at the vote time, the proposal viable at
the action time, and every step of the round keeps their roots and finalized blocks compatible
with the proposal. -/
def QuietRound (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ) : Prop :=
  (∀ w ∈ Hon s, (get_fc_root (stateBefore x (voteTime S s) w).S).AncestorEq B.parent ∧
    head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C B.parent).h) ∧
  (∀ v ∈ Hon s, (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B ∧
    head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ≤ (chainStateOf S.C B).h) ∧
  (∀ s', s ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)

/-- `ParentKindRound S Sched x Hon B s s''`: the round whose first slot is `s`, whose proposal is
`B` and whose next honest round opening slot is `s''` fails to be quiet only by the vote-time clause
on `head_height_floor`:

- some member of `Hon s` has its `head_height_floor` before the vote time of slot `s` greater
  than the chain-state height of `B.parent`;
- before the vote time of slot `s`, every member of `Hon s` has its fork-choice root `B.parent`
  or an ancestor of it;
- before the action time `supportCutoff S (s + 1)`, every member of `Hon s` has its fork-choice
  root `B` or an ancestor of `B`, and its `head_height_floor` at most the chain-state height of
  `B`;
- for every slot `s'` of the round with `s ≤ s'` and `s' + 2 ≤ s''`, every member of
  `Hon (s' + 1)` satisfies `StepFrameAt S Sched x B s'`.

Such a round does not switch the honest chain; the count of the phase bounds how many there are.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.



Read aloud: a round that is not quiet only because some member, at the vote time, does not find
a block at the chain-state height of the proposal's parent viable. -/
def ParentKindRound (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ) : Prop :=
  (∃ w ∈ Hon s, (chainStateOf S.C B.parent).h < head_height_floor (stateBefore x (voteTime S s) w).S) ∧
  (∀ w ∈ Hon s, (get_fc_root (stateBefore x (voteTime S s) w).S).AncestorEq B.parent) ∧
  (∀ v ∈ Hon s, (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B ∧
    head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ≤ (chainStateOf S.C B).h) ∧
  (∀ s', s ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)

/-- `InSpan a L s`: the slot `s` lies in the span of `L` slots starting at slot `a`, that is
`a ≤ s < a + L`.

The variables:
- `a`: the first slot of the span; `L`: its length in slots; `s`: the slot.

Read aloud: the span `[a, a + L)` holds `s`. -/
def InSpan (a L s : ℕ) : Prop := a ≤ s ∧ s < a + L

instance instDecidableInSpan (a L s : ℕ) : Decidable (InSpan a L s) :=
  inferInstanceAs (Decidable (a ≤ s ∧ s < a + L))

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `OutsideSpans S r waits Lwait wins Lwin i`: the first slot `r i * R` of opening `i` is outside
every span `[waits j, waits j + Lwait)` and every span `[wins j, wins j + Lwin)`.

The variables:
- `S`: the setup; `r`: the sequence of rounds; `i`: the index of the honest round opening slot;
- `waits`, `Lwait`: the first slots and the length of the spans of the first kind;
- `wins`, `Lwin`: the first slots and the length of the spans of the second kind.

Read aloud: opening `i` escapes every span. -/
def OutsideSpans (S : Setup V) (r : ℕ → ℕ) {nWait nWin : ℕ} (waits : Fin nWait → ℕ) (Lwait : ℕ)
    (wins : Fin nWin → ℕ) (Lwin : ℕ) (i : ℕ) : Prop :=
  (∀ j : Fin nWait, ¬ InSpan (waits j) Lwait (r i * S.C.R)) ∧
  (∀ j : Fin nWin, ¬ InSpan (wins j) Lwin (r i * S.C.R))

omit [DecidableEq V] [Fintype V] [RootOrder] in
instance instDecidableOutsideSpans (S : Setup V) (r : ℕ → ℕ) {nWait nWin : ℕ}
    (waits : Fin nWait → ℕ) (Lwait : ℕ) (wins : Fin nWin → ℕ) (Lwin : ℕ) (i : ℕ) :
    Decidable (OutsideSpans S r waits Lwait wins Lwin i) :=
  inferInstanceAs (Decidable ((∀ j : Fin nWait, ¬ InSpan (waits j) Lwait (r i * S.C.R)) ∧
    (∀ j : Fin nWin, ¬ InSpan (wins j) Lwin (r i * S.C.R))))

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `OpeningsOutsideSpans S r m nWait Lwait nWin Lwin need`: for every choice of `nWait` spans of
`Lwait` slots and `nWin` spans of `Lwin` slots, at least `need` of the openings `r 0, …, r m` have
their first slot `r i * R` outside every span.

The variables:
- `S`: the setup; `r`: the sequence of rounds; `m`: the index of the last honest round opening slot;
- `nWait`, `Lwait`: the number and the length, in slots, of the spans of the first kind;
- `nWin`, `Lwin`: the number and the length of the spans of the second kind;
- `need`: how many openings must fall outside every span.

Read aloud: however the spans are placed, at least `need` openings escape them all. -/
def OpeningsOutsideSpans (S : Setup V) (r : ℕ → ℕ) (m nWait Lwait nWin Lwin need : ℕ) : Prop :=
  ∀ (waits : Fin nWait → ℕ) (wins : Fin nWin → ℕ),
    need ≤ ((Finset.range (m + 1)).filter (OutsideSpans S r waits Lwait wins Lwin)).card

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `OpeningsOutsideWaitsAndWindows S r m`: for every choice of two spans of `δt` slots and five
spans of `k + 2` slots, at least 9 of the honest round opening slots `r 0, …, r m` have their first
slot outside all of them.

Where Lemma 89's proof places the spans. Write `T₁` for the time three delays into the slot `2k`
slots before the first opening's first slot, `H₂` for the greatest chain-state height of an
honest attestation sent before `T₁`, and `J₁`, `J₂` for the justified blocks at heights `H₂ − 1`
and `H₂`. The two spans of `δt` slots start at the slots of the entries of heights `H₂ − 1` and
`H₂` on the honest chain: an opening whose round waits for the timeout at a height has its first
slot in the span of that height. A fork-choice change is a member's root or `head_height_floor`
moving; there are four kinds: the root moves to `J₁`; `head_height_floor` rises to `H₂`; the root
moves to `J₂`; `head_height_floor` rises to `H₂ + 1`. Four spans of `k + 2` slots start at the
slot of the first occurrence of each kind (an honest round opening slot `s` reads the fork choice
from the vote time of slot `s − k − 1`, and the arrivals' spread over one delay adds one slot), and
the fifth at the first slot of the round in which an honest validator first fast-confirms a block
of height `H₂ + 1`.

The count `9 = 4 + 2 + 3`: at most four honest round opening slots outside the spans have a
fork-choice change in their round, one per kind, the one whose round holds the fast-confirming
round's first slot included; at most two are quiet at the heights `H₂ − 1` and `H₂`, rising or the
one whose round holds that slot; and three must have their first slot at least
`k + 2` slots after the first slot of the fast-confirming round, the third carrying to every
honest validator a justification height greater than the healed proposal's height `h(B₀)`
.

The variables:
- `S`: the setup; `r`: the sequence of rounds; `m`: the index of the last honest round opening slot.



Read aloud: nine honest round opening slots outside every two spans of `δt` slots and five spans
of `k + 2` slots. -/
def OpeningsOutsideWaitsAndWindows (S : Setup V) (r : ℕ → ℕ) (m : ℕ) : Prop :=
  OpeningsOutsideSpans S r m 2 S.C.δt 5 (S.C.k + 2) 9

end GoldilocksCorrectness.Statements.Executions
