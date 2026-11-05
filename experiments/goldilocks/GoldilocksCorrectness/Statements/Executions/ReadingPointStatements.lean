module
public import GoldilocksCorrectness.Proofs.Executions.ReadingPoints

@[expose] public section

/-!
# The Goldfish vote argument over reading points

Lemmas 62 to 64, proved in `GoldilocksCorrectness/Proofs/Executions/ReadingPoints.lean`. Each
reads the node states of its validators at times taken as parameters, with the inequalities
between those times as hypotheses, instead of at the times of the slot:

- Lemma 62 (`lem62_early_vote_reaches_at`): a vote that resolved early at one validator reaches
  another within one delay of the early cutoff;
- Lemma 63 (`lem63_supporters_counted_at`): the early supporters of a block's chain at a
  validator `v` have their votes and head blocks held by a voter `w`, as their only votes; with
  its two readings, on the sets of votes `w` counts (`supporters_vote_once_counted_at`) and on
  `w`'s pool (`supporters_vote_once_in_pool_at`);
- Lemma 64 (`lem64_goldfish_vote_extends_eligible_block_at`): `w`'s Goldfish fork choice ends on
  the chain of a block `v` finds eligible.

The times: `t_e`, the early cutoff (the supporters' votes resolve at `v` strictly before it);
`t_f`, the cutoff on the stamps of the votes and blocks `w` counts; `t_w`, the time `w`'s state is
read; `t_v`, the time `v`'s state is read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (VotesOnceFor VotesOnceInPoolFor CountedVotesAt
  VoterTreeAt)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 62, a vote that resolved early at one validator reaches another within one delay of
the early cutoff.** In an execution where every time is reached, corruption is permanent, blocks
and Goldfish votes are delivered within `Δ` after `GST`,: if `GST`
is at most `t_e`, `t_e + Δ S` is at most `t_w` and strictly before the start of slot `s + 2`, and
`v₂` is awake and honest at every time from `t_e` to `t_e + Δ S`, then every slot-`s` vote of
`v₁`'s pool before `t_v` that resolves (through the frame `Φ`) strictly before `t_e` is in `v₂`'s
pool of slot `s` before `t_w`, or that pool holds two distinct votes of the vote's validator.

Why: the vote's stamp is at most its resolution time, so `v₁` held it before `t_e`; `v₁` re-sent
it, and the re-send reaches `v₂` before `t_e + Δ S` (`pool_vote_reaches_before_add_delay`).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_v`: the time `v₁`'s state is read; `t_w`: the time `v₂`'s state is
  read;
- `v₁`: the validator holding the vote; `v₂`: the validator it reaches; `Φ`: the frame through
  which the vote resolves.

Read aloud: a vote that resolved before `t_e` at `v₁` is held by `v₂` at `t_w`, unless `v₂` holds
two votes of its validator.

Restated with the delivery premises up to `b`, the latest deadline being `t_e + Δ S` (`v₁`'s
re-send reaching `v₂`). -/
theorem lem62_early_vote_reaches_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_v t_w b : ℕ) (v₁ v₂ : V) (Φ : Frame V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    -- the network is synchronous from `t_e` on, so `v₁`'s re-send reaches `v₂` within one delay
    (hGST : GST ≤ t_e)
    -- what reaches `v₂` before `t_e + Δ S` it holds at `t_w`
    (h02 : t_e + Δ S ≤ t_w)
    -- the re-send arrives while slot-`s` votes are still admitted
    (hhi : t_e + Δ S < slotStart S (s + 2))
    -- `v₂` is awake and honest from `t_e` to `t_e + Δ S`, to receive the re-send
    (hv₂ : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S →
      v₂ ∈ Sched.awake (t : Int) ∧ v₂ ∉ Sched.adv (t : Int))
    -- the latest deadline the proof reads is at most the bound
    (hb : t_e + Δ S ≤ b) :
    ∀ vote ∈ (stateBefore x t_v v₁).A.pool s,
      (∃ y : Stamp, (stateBefore x t_v v₁).A.tau Φ vote = .ok (some y) ∧
        occurrenceBefore (some y) ((t_e : ℕ) : Int) = true) →
      vote ∈ (stateBefore x t_w v₂).A.pool s ∨
        ∃ u₁ ∈ (stateBefore x t_w v₂).A.pool s, ∃ u₂ ∈ (stateBefore x t_w v₂).A.pool s,
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index :=
  GoldilocksCorrectness.Proofs.Executions.lem62_early_vote_reaches_at S Sched x GST s t_e t_v t_w b
    v₁ v₂ Φ hDiv hMono hSync hCatch hGST h02 hhi hv₂ hb

/-- **Lemma 63, the early supporters' votes and heads reach the next voter, as their only
votes.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST`, a root names one
block among what honest validators hold, and a block reaches a validator only once it holds the
parent: under the inequalities between the times listed with the hypotheses, if `w` is awake and
honest at every time from `t_e` to `t_e + Δ S`, `v` at every time from `t_w` to `t_w + Δ S`, each
member of `Sup` is an early supporter of `B`'s chain on `v`'s state before `t_v` with the cutoff
`t_e` (`EarlySupporterAt`), and `w`'s finalized block before `t_w` is `B` or an ancestor of `B`,
then:
- each member `u` of `Sup` has a vote `vote_u` in `w`'s pool of slot `s` before `t_f`, stamped
  strictly before `t_f`; its head is the root of a block `H_u` of `w`'s tree before `t_f`, stamped
  strictly before `t_f`, that is `B` or a descendant of `B`, of slot at most `s`; and every
  slot-`s` vote of `u` that `w` re-sent before `t_w` is `vote_u`;
- every slot-`s` vote of a member of the slot-`s` committee that `w` re-sent before `t_w` is in
  `v`'s pool of slot `s` before `t_v`, or that pool holds two distinct votes of its validator.
The stamps are those of `w`'s state before `t_w`.

Why: `u`'s vote resolved at `v` before `t_e`, so `v` held it before `t_e`, re-sent it, and it
reaches `w` before `t_e + Δ S`; its head block too, held by `v` before `t_e` and compatible with
`w`'s finalized block (block propagation). A vote `w` re-sent before `t_w` reaches `v` before
`t_w + Δ S`, where `u` has one vote; so `w` holds no second vote of `u`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the time `w`'s state is
  read; `t_v`: the time `v`'s state is read;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block;
- `v`: the validator at which the members of `Sup` are early supporters; `w`: the voter.

Read aloud: the early supporters' votes and head blocks that `v` holds are held by `w` before
`t_f`, and `w` holds no other vote of theirs; and what `w` re-sent reaches `v` by `t_v`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(`w`'s re-sends reaching `v`; the re-sends from `v` reach `w` by `t_e + Δ S ≤ t_w + Δ S`). -/
theorem lem63_supporters_counted_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from `t_e` on, so re-sends from `t_e` arrive within one delay
    (hGST : GST ≤ t_e)
    -- `t_e` is a time of a tick, as block propagation reads it
    (h1 : 1 ≤ t_e)
    -- what `v` re-sent before `t_e` has reached `w` by `t_f`
    (h01 : t_e + Δ S ≤ t_f)
    -- what `w` holds before `t_f` it holds at `t_w`
    (h12 : t_f ≤ t_w)
    -- what `w` re-sent before `t_w` has reached `v` by `t_v`
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds before `t_e` has slot at most `s`
    (hslot : t_e < slotStart S (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < slotStart S (s + 2))
    -- `w` is awake and honest from `t_e` to `t_e + Δ S`, to receive `v`'s re-sends
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v` is awake and honest from `t_w` to `t_w + Δ S`, to receive `w`'s re-sends
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block before `t_w` is `B` or an ancestor of `B`
    (hF : (stateBefore x t_w w).S.F.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup, ∃ vote_u ∈ (stateBefore x t_f w).A.pool s, vote_u.val_index = u ∧
      (∃ τ : Stamp, (stateBefore x t_w w).A.timestamp_vote vote_u = some τ ∧
        τ < (((t_f : ℕ) : Int) : Stamp)) ∧
      (∃ H_u ∈ (stateBefore x t_f w).S.T, H_u.root = vote_u.head ∧ B.AncestorEq H_u ∧
        H_u.slot ≤ s ∧
        ∃ st : Stamp, (stateBefore x t_w w).A.timestamp_block H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
      ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index = u →
        (∃ j < stepBefore x t_w,
          (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
            x[j + 1].sent - x[j].sent ∧
          w ∉ Sched.adv (x[j].time : Int) ∧ slotStart S vote'.slot ≤ x[j].time) →
        vote' = vote_u) ∧
    (∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      (∃ j < stepBefore x t_w,
        (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
          x[j + 1].sent - x[j].sent ∧
        w ∉ Sched.adv (x[j].time : Int) ∧ slotStart S vote'.slot ≤ x[j].time) →
      vote' ∈ (stateBefore x t_v v).A.pool s ∨
        ∃ v₁ ∈ (stateBefore x t_v v).A.pool s, ∃ v₂ ∈ (stateBefore x t_v v).A.pool s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index) :=
  GoldilocksCorrectness.Proofs.Executions.lem63_supporters_counted_at S Sched x GST s t_e t_f t_w
    t_v b Sup B v w hDiv hMono hSync hCatch hRoots hParent hGST h1 h01 h12 h23 hslot hhi hw
    hv hSup hF hb

/-- Lemma 63 read on the sets of votes `w` counts. Under the hypotheses of Lemma 63, if moreover
the validators with a slot-`s` vote in `v`'s pool before `t_v` are fewer than twice `Sup`, and
`votes`, `support_votes` are the sets of votes the Goldfish vote of slot `s + 1` counts on `w`'s
state before `t_w` with the cutoff `t_f` (`CountedVotesAt`), then each member of `Sup` votes once
for `B`'s chain among them (`VotesOnceFor`), with its head block in `w`'s tree before `t_w` stamped
strictly before `t_f`; the validators with a vote in `votes` are fewer than twice `Sup`; and every
support vote is in `votes`.

Why: Lemma 63's vote of each member is a pool vote of `w` stamped and resolved before `t_f`, so a
counted support vote; every vote `w` counts was re-sent by `w` before `t_w` (as a pool vote or as a
vote included in a block of its tree), so it is the member's own vote, and its validator has a
vote in `v`'s pool before `t_v`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the time `w`'s state is
  read; `t_v`: the time `v`'s state is read;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block;
- `v`: the validator at which the members of `Sup` are early supporters; `w`: the voter;
- `votes`, `support_votes`: the two sets `w` counts.

Read aloud: everything `v` counted as early support for `B`'s chain is counted by `w` as support
for `B`'s chain, and `w` counts no voter that `v` did not see.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls). -/
theorem supporters_vote_once_counted_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (votes support_votes : Finset (GoldfishVote V))
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from `t_e` on, so re-sends from `t_e` arrive within one delay
    (hGST : GST ≤ t_e)
    -- `t_e` is a time of a tick, as block propagation reads it
    (h1 : 1 ≤ t_e)
    -- what `v` re-sent before `t_e` has reached `w` by `t_f`
    (h01 : t_e + Δ S ≤ t_f)
    -- what `w` holds before `t_f` it holds at `t_w`
    (h12 : t_f ≤ t_w)
    -- what `w` re-sent before `t_w` has reached `v` by `t_v`
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds before `t_e` has slot at most `s`
    (hslot : t_e < slotStart S (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < slotStart S (s + 2))
    -- `w` is awake and honest from `t_e` to `t_e + Δ S`, to receive `v`'s re-sends
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v` is awake and honest from `t_w` to `t_w + Δ S`, to receive `w`'s re-sends
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    -- the validators with a slot-`s` vote in `v`'s pool before `t_v` are fewer than twice `Sup`
    (hEligible : voters_count ((stateBefore x t_v v).A.pool s) < 2 * Sup.card)
    -- `w`'s finalized block before `t_w` is `B` or an ancestor of `B`
    (hF : (stateBefore x t_w w).S.F.AncestorEq B)
    -- `votes`, `support_votes` are the sets counted on `w`'s state before `t_w`, cutoff `t_f`
    (hCounted : CountedVotesAt (stateBefore x t_w w).A (fg_to_ac (stateBefore x t_w w).S)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup,
      VotesOnceFor (fg_to_ac (stateBefore x t_w w).S) votes support_votes s B u ∧
      ∃ H_u ∈ (stateBefore x t_w w).S.T, B.AncestorEq H_u ∧
        ∃ st : Stamp, (stateBefore x t_w w).A.timestamp_block H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
    voters_count votes < 2 * Sup.card ∧ support_votes ⊆ votes :=
  GoldilocksCorrectness.Proofs.Executions.supporters_vote_once_counted_at S Sched x GST s t_e t_f
    t_w t_v b Sup B v w votes support_votes hDiv hMono hSync hCatch hRoots hParent hGST h1
    h01 h12 h23 hslot hhi hw hv hSup hEligible hF hCounted hb

/-- Lemma 63 read on `w`'s pool. Under the hypotheses of Lemma 63, each member of `Sup` votes
once for `B`'s chain in `w`'s pool of slot `s` before `t_w` (`VotesOnceInPoolFor`).

Why: Lemma 63's vote of each member is in `w`'s pool before `t_w` and resolves there, its head block
being in `w`'s frame tree; every vote of `w`'s pool was re-sent by `w` before `t_w`, so a vote of
the member is that one.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the time `w`'s state is
  read; `t_v`: the time `v`'s state is read;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block;
- `v`: the validator at which the members of `Sup` are early supporters; `w`: the validator whose
  pool is read.

Read aloud: each early supporter of `B`'s chain at `v` has exactly one vote in `w`'s pool, and it
supports `B`'s chain there too.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls). -/
theorem supporters_vote_once_in_pool_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from `t_e` on, so re-sends from `t_e` arrive within one delay
    (hGST : GST ≤ t_e)
    -- `t_e` is a time of a tick, as block propagation reads it
    (h1 : 1 ≤ t_e)
    -- what `v` re-sent before `t_e` has reached `w` by `t_f`
    (h01 : t_e + Δ S ≤ t_f)
    -- what `w` holds before `t_f` it holds at `t_w`
    (h12 : t_f ≤ t_w)
    -- what `w` re-sent before `t_w` has reached `v` by `t_v`
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds before `t_e` has slot at most `s`
    (hslot : t_e < slotStart S (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < slotStart S (s + 2))
    -- `w` is awake and honest from `t_e` to `t_e + Δ S`, to receive `v`'s re-sends
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v` is awake and honest from `t_w` to `t_w + Δ S`, to receive `w`'s re-sends
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block before `t_w` is `B` or an ancestor of `B`
    (hF : (stateBefore x t_w w).S.F.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    ∀ u ∈ Sup,
      VotesOnceInPoolFor (stateBefore x t_w w).A (fg_to_ac (stateBefore x t_w w).S) s B u :=
  GoldilocksCorrectness.Proofs.Executions.supporters_vote_once_in_pool_at S Sched x GST s t_e t_f
    t_w t_v b Sup B v w hDiv hMono hSync hCatch hRoots hParent hGST h1 h01 h12 h23 hslot
    hhi hw hv hSup hF hb

/-- **Lemma 64, the next slot's Goldfish fork choice extends a block an honest validator finds
eligible.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST`, a root names one
block among what honest validators hold, and a block reaches a validator only once it holds the
parent: under the inequalities between the times listed with the hypotheses, if `w` is awake and
honest at every time from `t_e` to `t_e + Δ S`, `v` at every time from `t_w` to `t_w + Δ S`; on
`v`'s state before `t_v` each member of `Sup` is an early supporter of `B`'s chain with the
cutoff `t_e`, and the validators with a slot-`s` vote in `v`'s pool are fewer than twice `Sup`;
`votes`, `support_votes` are the sets the Goldfish vote of slot `s + 1` counts on `w`'s state
before `t_w` with the cutoff `t_f`, and `vbt` the voter's tree with the same cutoff; the Goldfish
fork choice at `t_w` from the anchor of `A'`, over the viable tree of `vbt`, counting those sets,
ends at `H_w`; on `w`'s state before `t_w`, the root of the fork choice is compatible with `B`,
and when that root is `B` or an ancestor of `B` some block of `vbt` that is `B` or a descendant of
`B` is a viable head; and the block of every lock entry of `A'` live at `t_w` is compatible with
`B` — then `H_w` is `B` or a descendant of `B`.

Why: when `B` is an ancestor of `w`'s finalized block, it is an ancestor of the root of the fork
choice (Lemma 46), of the anchor and of `H_w`. Otherwise `w`'s finalized block is an ancestor of
`B`, so the members of `Sup` vote once for `B`'s chain among the counted votes, and `w`'s voters are
fewer than twice `Sup` (Lemma 63, on the counted sets); the anchor is compatible with `B` (Lemma 6)
and starts towards `B` (Lemma 7, the blocks on the path being ancestors of a supporter's head,
stamped strictly before `t_f`), so the fork choice ends at `B` or a descendant of `B` (Lemma 2).



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the time of `w`'s fork
  choice; `t_v`: the time `v`'s state is read;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block `v` finds eligible;
- `v`: the validator that finds `B` eligible; `w`: the voter;
- `A'`: the AC state whose lock entries give the anchor; `votes`, `support_votes`: the sets `w`
  counts; `vbt`: `w`'s voter tree; `H_w`: the end of `w`'s fork choice.

Read aloud: if `B` is eligible at `v` with the cutoff `t_e`, the finality-gadget conditions hold
for `B` at `w`, and no live lock of `A'` conflicts with `B`, then `w`'s fork choice at `t_w`, over
what `w` holds by `t_f`, ends at `B` or a descendant of `B`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, through `supporters_vote_once_counted_at`, which it calls). -/
theorem lem64_goldfish_vote_extends_eligible_block_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (A' : ACState V) (votes support_votes : Finset (GoldfishVote V))
    (vbt : Finset (Block V)) (H_w : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from `t_e` on, so re-sends from `t_e` arrive within one delay
    (hGST : GST ≤ t_e)
    -- `t_e` is a time of a tick, as block propagation reads it
    (h1 : 1 ≤ t_e)
    -- what `v` re-sent before `t_e` has reached `w` by `t_f`
    (h01 : t_e + Δ S ≤ t_f)
    -- what `w` holds before `t_f` it holds at `t_w`
    (h12 : t_f ≤ t_w)
    -- what `w` re-sent before `t_w` has reached `v` by `t_v`
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds before `t_e` has slot at most `s`
    (hslot : t_e < slotStart S (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < slotStart S (s + 2))
    -- `w` is awake and honest from `t_e` to `t_e + Δ S`, to receive `v`'s re-sends
    (hw : ∀ t : ℕ, t_e ≤ t → t ≤ t_e + Δ S → w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v` is awake and honest from `t_w` to `t_w + Δ S`, to receive `w`'s re-sends
    (hv : ∀ t : ℕ, t_w ≤ t → t ≤ t_w + Δ S → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `B` is eligible at `v`'s state before `t_v` with the cutoff `t_e`: each member of `Sup` is
    -- an early supporter of `B`'s chain, and `v`'s voters are fewer than twice `Sup`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x t_v v).A (fg_to_ac (stateBefore x t_v v).S)
      ((t_e : ℕ) : Int) s B u)
    (hEligible : voters_count ((stateBefore x t_v v).A.pool s) < 2 * Sup.card)
    -- `votes`, `support_votes` are the sets counted on `w`'s state before `t_w`, cutoff `t_f`
    (hCounted : CountedVotesAt (stateBefore x t_w w).A (fg_to_ac (stateBefore x t_w w).S)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    -- `vbt` is `w`'s voter tree of slot `s + 1` on its state before `t_w`, cutoff `t_f`
    (hvbt : ∀ B' : Block V, B' ∈ vbt ↔ VoterTreeAt (stateBefore x t_w w).A
      (fg_to_ac (stateBefore x t_w w).S) ((t_f : ℕ) : Int) (s + 1) B')
    -- `w`'s Goldfish fork choice at `t_w`, from the anchor of `A'`, ends at `H_w`
    (hWalk : goldfish_fork_choice S.C (fg_to_ac (stateBefore x t_w w).S) ((t_w : ℕ) : Int)
      (get_anchor A' (fg_to_ac (stateBefore x t_w w).S) ((t_w : ℕ) : Int))
      (viable_tree (fg_to_ac (stateBefore x t_w w).S) vbt) votes support_votes s = .ok H_w)
    -- the root of `w`'s fork choice is compatible with `B`
    (hF2 : (fg_to_ac (stateBefore x t_w w).S).fc_root.compatible B = true)
    -- when that root is `B` or an ancestor of `B`, some block of `vbt` that is `B` or a
    -- descendant of `B` is a viable head
    (hF3 : (fg_to_ac (stateBefore x t_w w).S).fc_root.AncestorEq B →
      ∃ W ∈ vbt, W ∈ (fg_to_ac (stateBefore x t_w w).S).viable_heads ∧ B.AncestorEq W)
    -- the block of every lock entry of `A'` live at `t_w` is compatible with `B`
    (hLocks : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x t_w w).S) ((t_w : ℕ) : Int) e = true →
        e.B.compatible B = true)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    B.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem64_goldfish_vote_extends_eligible_block_at S Sched x
    GST s t_e t_f t_w t_v b Sup B v w A' votes support_votes vbt H_w hDiv hMono hSync hCatch
    hRoots hParent hGST h1 h01 h12 h23 hslot hhi hw hv hSup hEligible hCounted hvbt hWalk hF2
    hF3 hLocks hb

end GoldilocksCorrectness.Statements.Executions
