module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements

@[expose] public section

/-!
# SleepyStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/SleepyStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the sleepy model, an honest
active validator of a slot is an updater of it, Lemmas 87 and 88, a validator asleep before the duty
window holds no live lock entry, and an honest active committee member puts its Goldfish vote on the
wire. Each is the theorem of the same name of `Record/Restated/Proofs/Executions/Sleepy.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

open Framework.StsMultisetLog (SignedMsg)
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

/-- **An honest active validator is an updater.** Every validator of `honestActiveAt M S Sched s` is
in `updaterAt M S Sched s`.

Why: the duty window of slot `s` starts no later than that of slot `s + 1`, both windows end at
the member's tick to the support cutoff of slot `s + 1`, and honesty is read at that cutoff in both;
a member counted from its tick to the earlier start is awake after every step whose time is the
later start, since those steps come after that tick (the environment's `tick_active` and the run's
monotone time).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `s`: the slot.

Read aloud: a validator awake through the duties of slot `s` and honest at its update is awake
and honest through the update of slot `s`. -/
theorem honestActiveAt_subset_updaterAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s : ℕ) :
    honestActiveAt M S A x s ⊆ updaterAt M S A x s :=
  (GoldilocksCorrectness.Record.Proofs.Executions.honestActiveAt_subset_updaterAt M F) S A x R E s

omit [RootOrder] in
/-- **Fewer than a third is fewer than a quorum.** When every set of validators each in the
adversary set at some time at most `t` has fewer than a third of the validators, every such set
has fewer than `quorum V` members.

Why: `3 · |A| < n` and `n ≤ 2 · quorum V` (Lemma 65 (b)) give `3 · |A| < 2 · quorum V`.

The variables:
- `M`: the model; `F`: its facts;
- `Sched`: the schedule; `t`: the time up to which the adversary set is counted.

Read aloud: fewer than a third of the validators is fewer than a quorum. -/
theorem fewerThanQuorum_of_fewerThanThird (A : Activity V) (x : Trace V (NamedObject V) M.N) (t : ℕ)
    (h : A.AdversaryFewerThanThirdUntil x (validator_count V) t) :
    A.AdversaryFewerThanQuorumUntil x (quorum V) t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fewerThanQuorum_of_fewerThanThird M F) A x t h

/-- **Lemma 87, fewer than a quorum ever corrupted.** With permanent corruption and `Sleepiness`
from any `anchor`, at every time `t`, every set of validators each in the adversary set at some
time at most `t` has fewer than `quorum V` members.

Why: pick a slot `s ≥ 1` starting at or after both `anchor` and `t`. With permanent corruption
every member of such a set is in the adversary set at the vote time of `s`; sleepiness there makes
that adversary set smaller than the validators outside it, so twice its size is less than the
number of validators, which is at most twice the quorum (Lemma 65 (b)).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which sleepiness holds.
- `R`: the run's facts (the time moves by at most one per step and never back).

Read aloud: with permanent corruption and sleepiness from some time on, fewer than a quorum of
validators are ever corrupted. -/
theorem lem87_adversary_fewer_than_quorum (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (anchor : ℕ)
    -- corruption is permanent
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSleep : Sleepiness M S A x anchor) :
    ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem87_adversary_fewer_than_quorum M F U) S A
    anchor R E hSleep

/-- **Lemma 88, the counting hypotheses from committee sleepiness.** Write `Hs` for
`honestActiveAt M S Sched s ∩ S.P.committee s`. With `CommitteeSleepiness` from `anchor`, and slot
`s + 1` starting at or after `anchor`: the committee of slot `s` has fewer than `2 · |Hs|`
members; the validators with a slot-`s` vote in the pool of `v`'s node state before any time `t`
are fewer than `2 · |Hs|`; and so are the validators of any set of slot-`s` votes that a
slot-`(s + 1)` Goldfish vote counts on that state (`CountedVotes`).

Why: committee sleepiness at slot `s + 1` says the committee members outside `Hs` are fewer than
`|Hs|`; every pool vote of slot `s` is from the committee (the node invariant), and so is every
counted vote (`countedVotes_committee`: a pool vote, or a vote included in a well-formed block of
slot `s + 1`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s`: the slot; `v`: the validator; `t`: the time; `T`: the time up to
  which committee sleepiness is read.

Read aloud: under committee sleepiness read up to a time no earlier than the update of slot `s`, the
committee, the pool and the counted votes of slot `s` are each less than twice its honest active
members. -/
theorem lem88_counting_of_committeeSleepiness (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (anchor s : ℕ) (v : V) (t : ℕ)
    {T : ℕ} (hSleepK : CommitteeSleepinessUntil M S A x anchor T)
    -- slot `s + 1` starts at or after `anchor`
    (hs : anchor ≤ M.slotStart S.C (s + 1))
    -- the update of slot `s` is at most `T`
    (hT : M.supportCutoff S.C (s + 1) ≤ T) :
    |S.P.committee s| < 2 * |honestActiveAt M S A x s ∩ S.P.committee s| ∧
    M.voters_count (M.votesHeldSet (x.stateBefore t v) s) <
      2 * |honestActiveAt M S A x s ∩ S.P.committee s| ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.stateBefore t v) (s + 1)
        votes support_votes →
      M.voters_count votes < 2 * |honestActiveAt M S A x s ∩ S.P.committee s|) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem88_counting_of_committeeSleepiness M F) S A
    x R E anchor s v t hSleepK hs hT

/-- **No live lock after a sleep.** In an execution that reaches every time, with permanent
corruption, a validator `u` asleep at some time from the duty window's start of slot `s` to
before the duty window's start of slot `s + 1` holds no lock entry live at the vote time of slot
`s + 1` on the state its tick to that vote time starts from.

Why: a lock entry was added by `u`'s update of some slot `s₁ + 1`, at its support cutoff `c`, with
`u` awake and honest at `c` and awake since a time `τ` at most the duty window's start of slot
`s₁ + 1` (Lemma 39); so `u` was awake at every time from `τ` to `c`. If `u` slept at or after `c`,
then `s₁ + k < s` and the entry's deadline is at most the vote time of slot `s + 1`; if before,
then `τ` is at most the time of that sleep, against the awakeness from `τ` to `c`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the validator.

Read aloud: a validator that slept in the window before slot `s + 1`'s duty window holds no live
lock at slot `s + 1`'s vote time. -/
theorem lock_free_after_wake (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `u` is asleep at some time from the duty window's start of slot `s` to before that of `s + 1`,
    -- and did not come back up at that time with a tick to it after which it stayed awake through it
    (hSlept : ∃ t : ℕ, M.dutyWindowStart S.C s ≤ t ∧ t < M.dutyWindowStart S.C (s + 1) ∧
      u ∉ A.awakeAtTimeOrFromTick x t) :
    ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
      M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lock_free_after_wake M F U) S A x R s u E
    hSkew hSlept

/-- **An honest active committee member votes.** In an execution that reaches every time, with
permanent corruption, a validator `u` of
`honestActiveAt M S Sched s` in the committee of slot `s` puts on the wire, at its tick at the vote
time of slot `s`, a Goldfish vote of `u` for slot `s`.

Why: `u` is awake from the duty window's start of slot `s` to the vote time and honest there, so
its tick at the vote time answers and passes the duty test (`awakeSince_le_dutyWindowStart_b`);
the tick of the available chain then runs the Goldfish vote duty, which sends `u`'s vote since `u`
is in the committee; and the step puts what the tick sends on the wire.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the validator;
- `i`: the step of the tick; `vote`: the vote sent.

Read aloud: an honest active member of slot `s`'s committee sends its slot-`s` vote at the vote
time. -/
theorem honest_active_votes (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `u` is awake through the duties of slot `s` and honest at its update
    (hu : u ∈ honestActiveAt M S A x s)
    -- `u` is in the committee of slot `s`
    (hK : u ∈ S.P.committee s) :
    ∃ (i : ℕ) (vote : GoldfishVote V), x.lbl i = Event.tick u (M.voteTime S.C s) ∧
      vote.val_index = u ∧ vote.slot = s ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i :=
  (GoldilocksCorrectness.Record.Proofs.Executions.honest_active_votes M F U) S A x R s u E hSkew
    hu hK

end GoldilocksCorrectness.Record.Statements.Executions

