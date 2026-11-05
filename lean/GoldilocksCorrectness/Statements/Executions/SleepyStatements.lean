module
public import GoldilocksCorrectness.Proofs.Executions.Sleepy

@[expose] public section

/-!
# The sleepy model over executions

The audited statements about the sleepy model, proved in
`GoldilocksCorrectness/Proofs/Executions/Sleepy.lean`: an honest active validator of a slot is an
updater of it (`honestActiveAt_subset_updaterAt`); fewer than a third is fewer than a quorum
(`fewerThanQuorum_of_fewerThanThird`); Lemma 87, sleepiness with permanent corruption keeps every
set of validators corrupted by a time smaller than a quorum
(`lem87_adversary_fewer_than_quorum`); Lemma 88, committee sleepiness bounds the committee, the
pool and the counted votes of a slot by twice its honest active members
(`lem88_counting_of_committeeSleepiness`); a validator asleep before the duty window of a slot
holds no live lock entry at the slot's vote time (`lock_free_after_wake`); and an honest active
committee member votes (`honest_active_votes`).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (CountedVotes)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **An honest active validator is an updater.** Every validator of `honestActiveAt S Sched s` is
in `updaterAt S Sched s`.

Why: the duty window of slot `s` starts no later than that of slot `s + 1`, both windows end at
the support cutoff of slot `s + 1`, and honesty is read at that cutoff in both.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: a validator awake through the duties of slot `s` and honest at its update is awake
and honest through the update of slot `s`. -/
theorem honestActiveAt_subset_updaterAt (S : Setup V) (Sched : Schedule V) (s : ℕ) :
    honestActiveAt S Sched s ⊆ updaterAt S Sched s :=
  GoldilocksCorrectness.Proofs.Executions.honestActiveAt_subset_updaterAt S Sched s

omit [DecidableEq V] [RootOrder] in
/-- **Fewer than a third is fewer than a quorum.** When every set of validators each in the
adversary set at some time at most `t` has fewer than a third of the validators, every such set
has fewer than `quorum V` members.

Why: `3 · |A| < n` and `n ≤ 2 · quorum V` (Lemma 65 (b)) give `3 · |A| < 2 · quorum V`.

The variables:
- `Sched`: the schedule; `t`: the time up to which the adversary set is counted.

Read aloud: fewer than a third of the validators is fewer than a quorum. -/
theorem fewerThanQuorum_of_fewerThanThird (Sched : Schedule V) (t : Int)
    (h : AdversaryFewerThanThirdUntil Sched (validator_count V) t) : AdversaryFewerThanQuorumUntil Sched (quorum V) t :=
  GoldilocksCorrectness.Proofs.Executions.fewerThanQuorum_of_fewerThanThird Sched t h

omit [RootOrder] in
/-- **Lemma 87, fewer than a quorum ever corrupted.** With permanent corruption and `Sleepiness`
from any `anchor`, at every time `t`, every set of validators each in the adversary set at some
time at most `t` has fewer than `quorum V` members.

Why: pick a slot `s ≥ 1` starting at or after both `anchor` and `t`. With permanent corruption
every member of such a set is in the adversary set at the vote time of `s`; sleepiness there makes
that adversary set smaller than the validators outside it, so twice its size is less than the
number of validators, which is at most twice the quorum (Lemma 65 (b)).

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which sleepiness holds.

Read aloud: with permanent corruption and sleepiness from some time on, fewer than a quorum of
validators are ever corrupted. -/
theorem lem87_adversary_fewer_than_quorum (S : Setup V) (Sched : Schedule V) (anchor : ℕ)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    (hSleep : Sleepiness S Sched anchor) :
    ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t :=
  GoldilocksCorrectness.Proofs.Executions.lem87_adversary_fewer_than_quorum S Sched anchor hMono
    hSleep

/-- **Lemma 88, the counting hypotheses from committee sleepiness.** Write `Hs` for
`honestActiveAt S Sched s ∩ S.P.committee s`. With `CommitteeSleepiness` from `anchor`, and slot
`s + 1` starting at or after `anchor`: the committee of slot `s` has fewer than `2 · |Hs|`
members; the validators with a slot-`s` vote in the pool of `v`'s node state before any time `t`
are fewer than `2 · |Hs|`; and so are the validators of any set of slot-`s` votes that a
slot-`(s + 1)` Goldfish vote counts on that state (`CountedVotes`).

Why: committee sleepiness at slot `s + 1` says the committee members outside `Hs` are fewer than
`|Hs|`; every pool vote of slot `s` is from the committee (the node invariant), and so is every
counted vote (`countedVotes_committee`: a pool vote, or a vote included in a well-formed block of
slot `s + 1`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s`: the slot; `v`: the validator; `t`: the time.

Read aloud: under committee sleepiness, the committee, the pool and the counted votes of slot `s`
are each less than twice its honest active members. -/
theorem lem88_counting_of_committeeSleepiness (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (anchor s : ℕ) (v : V) (t : ℕ)
    (hSleepK : CommitteeSleepiness S Sched anchor)
    -- slot `s + 1` starts at or after `anchor`
    (hs : anchor ≤ slotStart S (s + 1)) :
    |S.P.committee s| < 2 * |honestActiveAt S Sched s ∩ S.P.committee s| ∧
    voters_count ((stateBefore x t v).A.pool s) <
      2 * |honestActiveAt S Sched s ∩ S.P.committee s| ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x t v).A (fg_to_ac (stateBefore x t v).S) (s + 1)
        votes support_votes →
      voters_count votes < 2 * |honestActiveAt S Sched s ∩ S.P.committee s|) :=
  GoldilocksCorrectness.Proofs.Executions.lem88_counting_of_committeeSleepiness S Sched x anchor
    s v t hSleepK hs

/-- **No live lock after a sleep.** In an execution that reaches every time, with permanent
corruption, a validator `u` asleep at some time from the duty window's start of slot `s` to
before the duty window's start of slot `s + 1` holds no lock entry live at the vote time of slot
`s + 1` on its node state before that time.

Why: a lock entry was added by `u`'s update of some slot `s₁ + 1`, at its support cutoff `c`, with
`u` awake and honest at `c` and awake since a time `τ` at most the duty window's start of slot
`s₁ + 1` (Lemma 39); so `u` was awake at every time from `τ` to `c`. If `u` slept at or after `c`,
then `s₁ + k < s` and the entry's deadline is at most the vote time of slot `s + 1`; if before,
then `τ` is at most the time of that sleep, against the awakeness from `τ` to `c`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the validator.

Read aloud: a validator that slept in the window before slot `s + 1`'s duty window holds no live
lock at slot `s + 1`'s vote time. -/
theorem lock_free_after_wake (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (u : V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `u` is asleep at some time from the duty window's start of slot `s` to before that of `s + 1`
    (hSlept : ∃ t : ℕ, dutyWindowStart S s ≤ t ∧ t < dutyWindowStart S (s + 1) ∧
      u ∉ Sched.awake (t : Int)) :
    ∀ e ∈ (stateBefore x (voteTime S (s + 1)) u).A.lock_entries,
      is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
        ((voteTime S (s + 1) : ℕ) : Int) e = false :=
  GoldilocksCorrectness.Proofs.Executions.lock_free_after_wake S Sched x s u hDiv hMono hSlept

/-- **An honest active committee member votes.** In an execution that reaches every time, with
permanent corruption, a validator `u` of
`honestActiveAt S Sched s` in the committee of slot `s` puts on the wire, at its tick at the vote
time of slot `s`, a Goldfish vote of `u` for slot `s`.

Why: `u` is awake from the duty window's start of slot `s` to the vote time and honest there, so
its tick at the vote time answers and passes the duty test (`awakeSince_le_dutyWindowStart_b`);
the tick of the available chain then runs the Goldfish vote duty, which sends `u`'s vote since `u`
is in the committee; and the step puts what the tick sends on the wire.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the validator;
- `i`: the step of the tick; `vote`: the vote sent.

Read aloud: an honest active member of slot `s`'s committee sends its slot-`s` vote at the vote
time. -/
theorem honest_active_votes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (u : V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `u` is awake through the duties of slot `s` and honest at its update
    (hu : u ∈ honestActiveAt S Sched s)
    -- `u` is in the committee of slot `s`
    (hK : u ∈ S.P.committee s) :
    ∃ (i : ℕ) (vote : GoldfishVote V), x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
      vote.val_index = u ∧ vote.slot = s ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent :=
  GoldilocksCorrectness.Proofs.Executions.honest_active_votes S Sched x s u hDiv hMono hu hK

end GoldilocksCorrectness.Statements.Executions
