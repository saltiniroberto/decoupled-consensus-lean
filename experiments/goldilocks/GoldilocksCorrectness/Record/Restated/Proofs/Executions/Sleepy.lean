module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Steps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ScoreACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# Sleepy, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Sleepy.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the sleepy model, an honest active validator of
a slot is an updater of it, Lemmas 87 and 88, a validator asleep before the duty window holds no
live lock entry, and an honest active committee member puts its Goldfish vote on the wire. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  duty_window_start_mono lt_of_t_lt one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_cast
  supportCutoff_eq supportCutoff_slot t_add t_le_of_le t_one voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.bind_nil
  DREBEmits.broadcast_then DREBEmits.dite DREBEmits.ite DREBEmits.liftM DREBEmits.monadLift
  DREBEmits.pure)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff wake_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_eq_toNat duty_window_start_eq t_eq_mul)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_iff)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem65b_quorum_threshold)
open GoldilocksCorrectness.Proofs.Routines (awake_since_record_awake)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- An honest active validator of slot `s` is an updater of slot `s`. The proof; the audited
statement is in `Statements/Executions/SleepyStatements.lean`.

Why: both sets' windows end at the member's tick to the support cutoff of slot `s + 1`; the duty
window of slot `s` starts no later than that of slot `s + 1` (`duty_window_start_mono`), and the reader
counts at a later opening value every member it counts at an earlier one
(`Activity.mem_activeThroughoutToTick_of_le`); awake up to its tick, the member is active up to it, a tick
being by an active validator and corruption permanent (`EnvFactsBy.mem_activeThroughoutToTick_of_awakeThroughoutToTick`);
an updater is asked nothing after its tick.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `s`: the slot.

Read aloud: a validator awake through the duties of slot `s` and honest at its update is awake and
honest through the update of slot `s`. -/
theorem honestActiveAt_subset_updaterAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s : ℕ) :
    honestActiveAt M S A x s ⊆ updaterAt M S A x s := by
  -- the same end, a later start (`duty_window_start_mono`, the reader monotone in its start), awake up to
  -- the tick is active up to it (a tick is by an active validator)
  intro u hu
  unfold honestActiveAt activeAt at hu
  unfold updaterAt
  obtain ⟨h1, -⟩ := Finset.mem_sdiff.1 hu
  exact Activity.mem_activeThroughoutToTick_of_le
    (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s))
    (E.mem_activeThroughoutToTick_of_awakeThroughoutToTick h1)

omit [RootOrder] in
/-- Fewer than a third of the validators is fewer than a quorum. The proof; the audited statement
is in `Statements/Executions/SleepyStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `Sched`: the schedule; `t`: the time.

Read aloud: fewer than a third of the validators is fewer than a quorum. -/
theorem fewerThanQuorum_of_fewerThanThird (A : Activity V) (x : Trace V (NamedObject V) M.N) (t : ℕ)
    (h : A.AdversaryFewerThanThirdUntil x (validator_count V) t) :
    A.AdversaryFewerThanQuorumUntil x (quorum V) t := by
  intro A hA
  have h1 := h A hA
  have h2 := (lem65b_quorum_threshold (V := V)).2
  omega

omit [RootOrder] in
/-- Fewer than two thirds of the validators corrupted up to `t` gives fewer than a quorum corrupted
up to `t`: `quorum V = (2 n + 2) / 3`, so `3 c < 2 n` gives `c < quorum V`.

The variables:
- `A`: the activity; `t`: the time.

Read aloud: the two-thirds premise at `t` gives the quorum premise at `t`. -/
theorem adversaryFewerThanQuorumUntil_of_adversaryFewerThanTwoThirdsUntil (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (t : ℕ) (h : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t) :
    A.AdversaryFewerThanQuorumUntil x (quorum V) t := fun X hX => by
  have h1 := h X hX
  have h2 := (lem65b_quorum_threshold (V := V)).1
  omega

omit [RootOrder] in
/-- The converse: fewer than a quorum corrupted up to `t` gives fewer than two thirds, since
`c < (2 n + 2) / 3` gives `3 c < 2 n`.

The variables:
- `A`: the activity; `t`: the time.

Read aloud: the two forms are the same condition. -/
theorem adversaryFewerThanTwoThirdsUntil_of_adversaryFewerThanQuorumUntil (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (t : ℕ) (h : A.AdversaryFewerThanQuorumUntil x (quorum V) t) :
    A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t := fun X hX => by
  have h1 := h X hX
  unfold quorum at h1
  omega

/-- **Lemma 87, fewer than a quorum ever corrupted.** The proof; the audited statement is in
`Statements/Executions/SleepyStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which sleepiness holds.
- `R`: the run's facts (the time moves by at most one per step and never back).

Read aloud: with permanent corruption and sleepiness from some time on, fewer than a quorum of
validators are ever corrupted. -/
theorem lem87_adversary_fewer_than_quorum (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (anchor : ℕ)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSleep : Sleepiness M S A x anchor) :
    ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t := by
  -- the slot `anchor + t + 1` starts at or after `anchor`, and its vote time is at least `t`; every
  -- validator of `X` is in the adversary set by that vote time, so `X` is at most the validators
  -- corrupted by it, which sleepiness bounds by fewer than half of all validators
  intro t X hX
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (anchor + t + 1) = 4 * Δ S * (anchor + t + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S _
  have hge : anchor + t + 1 ≤ M.slotStart S.C (anchor + t + 1) := by
    rw [hss]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
    (anchor + t + 1)
  have hts : (t : ℝ) ≤ ((M.voteTime S.C (anchor + t + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show t ≤ M.voteTime S.C (anchor + t + 1) by omega)
  have hsub : X ⊆ A.corruptedAtTime x (M.voteTime S.C (anchor + t + 1)) := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := hX v hv
    exact Activity.mem_corruptedAtTime.2 ⟨i, le_trans hi hts, hvi⟩
  have h1 := hSleep (anchor + t + 1) (by omega) (by omega)
  have h2 := Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ
    (activeAt M S A x (anchor + t + 1 - 1)))
    (le_refl (A.corruptedAtTime x (M.voteTime S.C (anchor + t + 1)))))
  have h3 : (Finset.univ \ A.corruptedAtTime x (M.voteTime S.C (anchor + t + 1))).card +
      (A.corruptedAtTime x (M.voteTime S.C (anchor + t + 1))).card = validator_count V := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    rfl
  have h4 := (lem65b_quorum_threshold (V := V)).2
  have h5 := Finset.card_le_card hsub
  omega

/-- **Kit fact, counted votes are from the committee, at a step.** Every vote of a set of slot-`s` votes that
a slot-`(s + 1)` Goldfish vote counts on `v`'s node state at the step `i` (`CountedVotes`) is from a
member of the committee of slot `s`: a pool vote by the node invariant's filing of the pool, a
vote included in a slot-`(s + 1)` block of the frame's tree by that block's well-formedness.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `s`: the slot;
  `v`: the validator; `votes`, `support_votes`: the counted sets.

Read aloud: the votes a Goldfish vote of slot `s + 1` counts are from slot `s`'s committee. -/
theorem countedVotes_committee_st (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i s : ℕ) (v : V)
    (votes support_votes : Finset (GoldfishVote V))
    (hC : CountedVotes M S.C (x.st i v) (s + 1)
      votes support_votes) :
    ∀ vote ∈ votes, vote.val_index ∈ S.P.committee s := by
  intro vote hv
  rcases (hC.1 vote).1 hv with ⟨hp, -⟩ | hinc
  · rw [Nat.add_sub_cancel] at hp
    exact (GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E i v s vote hp
  · simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F),
      Nat.add_sub_cancel] at hinc
    obtain ⟨B, ⟨hB, hBs⟩, hvB, -⟩ := hinc
    have hBT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1
    have hne : B ≠ Block.genesis := by
      rintro rfl
      exact Nat.succ_ne_zero s hBs.symm
    have hwf := (((F.nd.nodeInvCore_treeClosed ((lem11_node_invariantCore_of_run M F) S x R i v).1)).2 B hBT hne).2.1
    rw [F.rd.block_well_formed_iff] at hwf
    have h := ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B hwf.1.2).2.2 vote hvB
    rwa [hBs, Nat.add_sub_cancel] at h

/-- **Kit fact, counted votes are from the committee.** Every vote of a set of slot-`s` votes that
a slot-`(s + 1)` Goldfish vote counts on `v`'s node state before `t` (`CountedVotes`) is from a
member of the committee of slot `s`: a pool vote by the node invariant's filing of the pool, a
vote included in a slot-`(s + 1)` block of the frame's tree by that block's well-formedness.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `s`: the slot;
  `v`: the validator; `votes`, `support_votes`: the counted sets.

Read aloud: the votes a Goldfish vote of slot `s + 1` counts are from slot `s`'s committee. -/
theorem countedVotes_committee (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t s : ℕ) (v : V)
    (votes support_votes : Finset (GoldfishVote V))
    (hC : CountedVotes M S.C (x.stateBefore t v) (s + 1)
      votes support_votes) :
    ∀ vote ∈ votes, vote.val_index ∈ S.P.committee s := by
  exact (countedVotes_committee_st M F) S A x R E (x.stepBefore t) s v votes support_votes hC

/-- **Lemma 88, the counting hypotheses from committee sleepiness.** The proof; the audited
statement is in `Statements/Executions/SleepyStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s`: the slot; `v`: the validator; `t`: the time; `T`: the time up to
  which committee sleepiness is read (the update of slot `s`, `M.supportCutoff S.C (s + 1)`, is at
  most `T`).

Read aloud: under committee sleepiness read up to a time no earlier than the update of slot `s`, the
committee, the pool and the counted votes of slot `s` are each less than twice its honest active
members. -/
theorem lem88_counting_of_committeeSleepiness (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (anchor s : ℕ) (v : V) (t : ℕ)
    {T : ℕ} (hSleepK : CommitteeSleepinessUntil M S A x anchor T)
    (hs : anchor ≤ M.slotStart S.C (s + 1)) (hT : M.supportCutoff S.C (s + 1) ≤ T) :
    |S.P.committee s| < 2 * |honestActiveAt M S A x s ∩ S.P.committee s| ∧
    M.voters_count (M.votesHeldSet (x.stateBefore t v) s) <
      2 * |honestActiveAt M S A x s ∩ S.P.committee s| ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.stateBefore t v) (s + 1)
        votes support_votes →
      M.voters_count votes < 2 * |honestActiveAt M S A x s ∩ S.P.committee s|) := by
  have hK := hSleepK (s + 1) (by omega) hs hT
  rw [Nat.add_sub_cancel] at hK
  have hsub : S.P.committee s \ (honestActiveAt M S A x s ∩ S.P.committee s) ⊆
      S.P.committee s \ honestActiveAt M S A x s := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
    tauto
  have hMaj : |S.P.committee s \ (honestActiveAt M S A x s ∩ S.P.committee s)| <
      |honestActiveAt M S A x s ∩ S.P.committee s| :=
    lt_of_le_of_lt (Finset.card_le_card hsub) hK
  refine ⟨?_, ?_, ?_⟩
  · have := Finset.card_le_card_sdiff_add_card (s := S.P.committee s)
      (t := honestActiveAt M S A x s ∩ S.P.committee s)
    omega
  · exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F) ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_stateBefore M F) S A x R E t v s)
      hMaj
  · intro votes support_votes hC
    exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      ((countedVotes_committee M F) S A x R E t s v votes support_votes hC) hMaj

/-- An honest active member of the committee of slot `s` puts a slot-`s` Goldfish vote on the
wire at its tick at the vote time of slot `s`. The proof; the audited statement is in
`Statements/Executions/SleepyStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the
  validator.

Read aloud: an honest active member of slot `s`'s committee sends its slot-`s` vote at the vote
time. -/
theorem honest_active_votes (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hu : u ∈ honestActiveAt M S A x s)
    (hK : u ∈ S.P.committee s) :
    ∃ (i : ℕ) (vote : GoldfishVote V), x.lbl i = Event.tick u (M.voteTime S.C s) ∧
      vote.val_index = u ∧ vote.slot = s ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hk : 2 ≤ S.C.k := S.C.k_ge_two
  have hvt : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hslot : M.slot S.C (M.voteTime S.C s) = s := (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  -- the spec's slot of the vote time (the tick's facts read it), the model's by `U`
  have hslot' : S.C.slot ((M.voteTime S.C s : ℕ) : Int) = s := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact hslot
  have hvc : ((M.voteTime S.C s : ℕ) : Int) =
      S.C.t_ (S.C.slot ((M.voteTime S.C s : ℕ) : Int)) + S.C.Δ := by
    rw [hslot']; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S s
  -- the three clock values, read as real numbers: the duty window's start `4Δs + Δ − 4Δk`, the vote
  -- time `4Δs + Δ`, the support cutoff of slot `s + 1` `4Δs + 6Δ`
  have hdR := duty_window_start_real S s
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) + (Δ S : ℝ) := by
    rw [hvt, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    push_cast; ring
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) + 6 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)]
    push_cast; ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  -- `u` is active from the duty window's start up to its tick to the support cutoff of slot `s + 1`
  -- (a tick is by an active validator), so up to its tick to the vote time, strictly inside that
  -- window by the two clock bounds' margins (`hSkew`)
  have hw : u ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.supportCutoff S.C (s + 1)) :=
    E.mem_activeThroughoutToTick_of_awakeThroughoutToTick (Finset.mem_sdiff.1 hu).1
  have hv := (mem_activeThroughoutToTick_of_inside M F) R E (c := M.voteTime S.C s) hw (by omega)
    (by rw [hdR, hvR]; linarith) (by rw [hvR, hcR]; linarith)
  obtain ⟨k', hl, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hdw : duty_window_start S.C s < ((M.voteTime S.C s : ℕ) : ℤ) := by
    have h : ((duty_window_start S.C s : ℤ) : ℝ) < (((M.voteTime S.C s : ℕ) : ℤ) : ℝ) := by
      push_cast; rw [hdR, hvR]; linarith
    exact_mod_cast h
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv hdw
  -- the outcome the tick took; what it sends is on the wire at that step
  obtain ⟨n', sent, hrun, -, hsent⟩ := R.tick k' u _ hl
  have hrun' : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C s))
      ((M.voteTime S.C s : ℕ) : Int) := by
    unfold Trace.tickInput; rw [hts]; exact hrun
  have hnv : (x.tickInput u (M.voteTime S.C s)).v = u := by
    unfold Trace.tickInput; rw [hts]
    exact (lem11_node_invariant M F S A x R E k' u (E.not_mem_corrupted_of_tick hl)).2.1
  -- the outcome's wake time is the input state's, so it passes the duty window's wake test
  have hT1 := F.tk.tick_clock_validator_awakeSince S.C S.P S.X _ _ n' sent hrun'
  have hWS' : M.awake_since n' (duty_window_start S.C (S.C.slot ((M.voteTime S.C s : ℕ) : Int))) =
      true := by
    simp only [F.rd.awake_since_eq, hT1.2.2, hτ, hslot', decide_eq_true_eq]
    exact hτle
  -- the tick at the vote time of an awake committee member sends its vote (the tick fact
  -- `tick_emits_vote`)
  obtain ⟨h, hh⟩ := F.tk.tick_emits_vote S.C S.P S.X _ _ n' sent hrun' hvc hWS'
    (by rw [hnv, hslot']; exact hK)
  rw [hnv, hslot'] at hh
  refine ⟨k', ⟨u, s, h⟩, hl, rfl, rfl, ?_⟩
  rw [hsent, add_tsub_cancel_left]
  exact Multiset.mem_map.2 ⟨_, Multiset.mem_coe.2 hh, rfl⟩

/-- A validator asleep at some time from the duty window's start of slot `s` to before the duty
window's start of slot `s + 1` holds no lock entry live at the vote time of slot `s + 1`. The
proof; the audited statement is in `Statements/Executions/SleepyStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the
  validator.

Read aloud: a validator that slept in the window before slot `s + 1`'s duty window holds no live
lock at slot `s + 1`'s vote time. -/
theorem lock_free_after_wake (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hSlept : ∃ t : ℕ, M.dutyWindowStart S.C s ≤ t ∧ t < M.dutyWindowStart S.C (s + 1) ∧
      u ∉ A.awakeAtTimeOrFromTick x t) :
    ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
      M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false := by
  intro e he
  obtain ⟨t₀, h1, h2, hAsleep⟩ := hSlept
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the entry's provenance: `u`'s update of a slot `s₁ + 1`, at its tick to the support cutoff of slot `s₁ + 1`, before
  -- the step `u`'s tick to the vote time of slot `s + 1` starts from, from a state awake since a time `τ` at most the
  -- duty window's start of slot `s₁ + 1` (Lemma 39)
  have he' : e ∈ (x.st (x.tickStep u (M.voteTime S.C (s + 1))) u).lockEntries := he
  obtain ⟨s₁, hd, hk₁lt, hl₁, ⟨τ, hτ, hτle⟩, -⟩ :=
    (lem39_lock_entry_provenance M F U) S A x R _ u e E he'
  -- `u` ticks to the vote time of slot `s + 1` (that step is after the update's, so it is not the default `0`)
  have hex : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s + 1)) := by
    by_contra hne
    have h0 : x.tickStep u (M.voteTime S.C (s + 1)) = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hne]
    omega
  have hlV := x.lbl_tickStep hex
  -- `s₁ < s`: `u`'s clock does not go back between its two ticks (`clock_mono`)
  have hcv := E.clock_mono _ _ u _ _ hk₁lt (E.not_mem_corrupted_of_tick hlV) (Or.inl hl₁) (Or.inl hlV)
  have hΔ : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
  have hcC := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s₁ + 1)
  have hvC := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s + 1)
  have hts₁ := t_add S s₁ 1
  have hts := t_add S s 1
  have h1t := t_one S
  have hcv' : ((M.supportCutoff S.C (s₁ + 1) : ℕ) : Int) ≤ ((M.voteTime S.C (s + 1) : ℕ) : Int) := by
    exact_mod_cast hcv
  have hs₁ : s₁ < s := lt_of_t_lt S (by omega)
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_eq_false_iff M F)]
  left
  by_cases hcase : x.time (x.tickStep u (M.supportCutoff S.C (s₁ + 1))) ≤ ((t₀ : ℕ) : ℝ)
  · -- asleep at or after the update's real time: the update's clock value is less than `t₀ + Δ` (`hSkew`), so
    -- `s₁ + k < s` and the entry's deadline is at most the vote time of slot `s + 1`
    have hta := (E.tick_active _ _ _ hl₁).2.1
    have hcR : ((M.supportCutoff S.C (s₁ + 1) : ℕ) : ℝ) < ((t₀ : ℕ) : ℝ) + ((Δ S : ℕ) : ℝ) := by linarith
    have hcN : M.supportCutoff S.C (s₁ + 1) < t₀ + Δ S := by exact_mod_cast hcR
    have hcI : ((M.supportCutoff S.C (s₁ + 1) : ℕ) : Int) < ((t₀ : ℕ) : Int) + S.C.Δ := by
      rw [← GoldilocksCorrectness.Proofs.Routines.Δ_cast S]
      exact_mod_cast hcN
    have h2' : @LT.lt Int _ (t₀ : Int) (duty_window_start S.C (s + 1)) :=
      Int.lt_toNat.1 (by
        rw [← (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
        exact h2)
    have hdws : @Eq Int (duty_window_start S.C (s + 1))
        (S.C.t_ (s + 1) + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int)) := duty_window_start_eq S.C (s + 1)
    have htk : @Eq Int (S.C.t_ S.C.k) (4 * S.C.Δ * (S.C.k : Int)) := t_eq_mul S.C S.C.k
    have hkt := t_add S s₁ S.C.k
    have hlt : s₁ + S.C.k < s := lt_of_t_lt S (by omega)
    have hle := t_le_of_le S (Nat.le_of_lt hlt)
    have hd' : @Eq Int e.d (S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ) := hd
    show @LE.le Int _ e.d ((M.voteTime S.C (s + 1) : ℕ) : Int)
    omega
  · -- asleep before the update's real time: `u` was awake at `t₀`, from the start or from its tick to `τ ≤ t₀`
    exfalso
    rw [not_le] at hcase
    apply hAsleep
    have hbefore : ∀ i : ℕ, x.time i ≤ ((t₀ : ℕ) : ℝ) → i < x.tickStep u (M.supportCutoff S.C (s₁ + 1)) :=
      fun i hi => (lt_of_time_lt M) x R (lt_of_le_of_lt hi hcase)
    have hτle' : @LE.le Int _ τ (duty_window_start S.C (s₁ + 1)) := hτle
    have hmono : @LE.le Int _ (duty_window_start S.C (s₁ + 1)) (duty_window_start S.C s) :=
      duty_window_start_mono S (by omega)
    have hds : @LE.le Int _ (duty_window_start S.C s) ((M.dutyWindowStart S.C s : ℕ) : Int) :=
      (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S s
    have h1' : ((M.dutyWindowStart S.C s : ℕ) : Int) ≤ ((t₀ : ℕ) : Int) := by exact_mod_cast h1
    rcases (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨_, hl₁⟩ hτ with
        ⟨-, hall⟩ | ⟨k₀, τ', -, hl₀, hτ'eq, haw₀⟩
    · refine Activity.mem_awakeAtTimeOrFromTick.2 (Or.inl fun i hi _ => hall i (hbefore i ?_).le)
      exact_mod_cast hi
    · refine Activity.mem_awakeAtTimeOrFromTick.2 (Or.inr ⟨k₀, τ', ?_, hl₀, fun i hi1 hi2 => haw₀ i hi1 (hbefore i ?_).le⟩)
      · rw [hτ'eq]
        omega
      · exact_mod_cast hi2

/-- **A live lock at the next vote time keeps a validator in the previous slot's active set.** A
validator `u` that ticks to the support cutoff of slot `s + 1` and is active from the duty window's
start of slot `s + 1` up to that tick (`A.activeThroughoutToTick`), and holds, before the vote time of
slot `s + 1`, a lock entry live there, is in `activeAt M S A x s`.

Why: the entry was added by `u`'s tick to the support cutoff of a slot `s₁ + 1` with `s₁ < s`, from a
state awake since a time `τ` at most the duty window's start of slot `s₁ + 1`
(`lockTracedAfterTick_of_mem`). Live at the vote time of slot `s + 1`, its deadline
`S.C.t_ (s₁ + S.C.k) + 5 · S.C.Δ` is after that vote time, so `s < s₁ + S.C.k`, and the duty window of
slot `s + 1` starts before that tick. Up to the tick, `u` is awake from the start, or from its tick to
the time `τ` (`awake_of_tickInput_awakeSince_of_tick`), and `τ` is at most the duty window's start of
slot `s`; after the tick, the steps are read as times after the duty window's start of slot `s + 1`,
where `u`'s reader holds. When `u` came back up at `τ` equal to the duty window's start of slot `s`,
that start is at least `1` and the reader's second case counts `u` from its tick there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`, `hWS`: the setup, the activity, the execution, its run facts, its
  environment facts, its wake shape; `s`: the slot; `u`: the validator.

Read aloud: a validator active up to its update of slot `s` that still holds a live lock at the next
vote time was active through the duties of slot `s` up to its update. -/
theorem mem_activeAt_of_live_lock (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hw : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hL : ∃ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
      M.is_live (x.tickInput u (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true) :
    u ∈ activeAt M S A x s := by
  obtain ⟨e, he, hl⟩ := hL
  have hΔ := one_le_Δ S
  have hv' : ∀ s : ℕ, M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc' : ∀ s : ℕ, M.supportCutoff S.C s = M.voteTime S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  -- `u`'s tick `k'` to the support cutoff `c₀` of slot `s + 1`, and its activity up to it
  obtain ⟨k', hk', hact⟩ := Activity.mem_activeThroughoutToTick.1 hw
  have hlive' := hl
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive'
  -- where `e` comes from (Lemma 39 at `u`'s tick to the vote time): `u`'s update of a slot `σ + 1`
  -- at its tick to the support cutoff `c₁`, at an earlier step, from a state awake since `τ`
  have he' : e ∈ (x.st (x.tickStep u (M.voteTime S.C (s + 1))) u).lockEntries := he
  obtain ⟨σ, hd, hk₁, hl₁, ⟨τ, hτ, hτle⟩, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R
      (x.tickStep u (M.voteTime S.C (s + 1))) u e E he'
  -- the tick to the vote time comes after it, so `c₁` is at most that vote time, and `σ + 1 ≤ s`
  have hexT : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s + 1)) := by
    by_contra hno
    have h0 : x.tickStep u (M.voteTime S.C (s + 1)) = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hno]
    omega
  have hlT := x.lbl_tickStep hexT
  have hle₁ := E.clock_mono _ _ u _ _ hk₁ (E.not_mem_corrupted_of_tick hlT) (Or.inl hl₁) (Or.inl hlT)
  have hσ : σ + 1 ≤ s := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s + 1 ≤ σ + 1 by omega)
    have h1 := hc' (σ + 1)
    have h2 := hv' (σ + 1)
    have h3 := hv' (s + 1)
    omega
  -- live at the vote time, the lock is of a slot `σ` with `s + 1 ≤ σ + k` (Lemma 41)
  have hσk : s + 1 ≤ σ + S.C.k := by
    by_cases hkle : S.C.k ≤ s + 1
    · have h41 := (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
        (s + 1 - S.C.k) σ (M.voteTime S.C (s + 1)) e hd hlive'.1 (by
          rw [show s + 1 - S.C.k + S.C.k = s + 1 by omega])
      omega
    · omega
  -- the tick to `c₁` comes before the tick to `c₀`
  have hc₁c₀ : M.supportCutoff S.C (σ + 1) < M.supportCutoff S.C (s + 1) := by
    have := hc' (s + 1)
    omega
  have h1' : x.tickStep u (M.supportCutoff S.C (σ + 1)) < k' := by
    rcases lt_trichotomy (x.tickStep u (M.supportCutoff S.C (σ + 1))) k' with h | h | h
    · exact h
    · rw [h, hk'] at hl₁
      have := (Event.tick.inj hl₁).2
      omega
    · have := E.clock_mono _ _ u _ _ h (E.not_mem_corrupted_of_tick hl₁) (Or.inl hk') (Or.inl hl₁)
      omega
  -- the reader's start tick comes at or before the tick to `c₁`: `u` is active from the tick to `c₁`
  -- up to its tick to `c₀`
  have hdw : duty_window_start S.C (s + 1) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℤ) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (s + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_supportCutoff M.toSlotLayout
      F.sched U) S (show s + 1 ≤ σ + 1 + S.C.k by omega)
    have h2' : ((M.dutyWindowStart S.C (s + 1) : ℕ) : ℤ) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℤ) := by
      exact_mod_cast h2
    exact h1.trans h2'
  have hact₁ : ∀ i : ℕ, x.tickStep u (M.supportCutoff S.C (σ + 1)) ≤ i → i ≤ k' → u ∈ A.active i := by
    rcases hact with hall | ⟨k, -, c, hca, hlk, hkw⟩
    · exact fun i _ h => hall i h
    · have hkk₁ : k ≤ x.tickStep u (M.supportCutoff S.C (σ + 1)) := by
        by_contra hlt'
        have hlt'' := Nat.lt_of_not_le hlt'
        have hcc := E.clock_mono _ _ u _ _ hlt'' (E.not_mem_corrupted_of_tick hlk) (Or.inl hl₁) (Or.inl hlk)
        have hca' : (c : ℤ) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℤ) := hca.trans hdw
        have hceq : c = M.supportCutoff S.C (σ + 1) := by omega
        rw [hceq] at hlk
        have := E.tick_unique _ _ u _ hl₁ hlk
        omega
      exact fun i h1 h2 => hkw i (hkk₁.trans h1) h2
  -- awake from the tick that wrote `τ`, at most the duty window's start of slot `σ + 1`, or from the
  -- start, up to the tick to `c₀`
  show u ∈ A.awakeThroughoutToTick x (duty_window_start S.C s) (M.supportCutoff S.C (s + 1))
  have hτ' : (x.tickInput u (M.supportCutoff S.C (σ + 1))).awakeSince = some τ := hτ
  refine Activity.mem_awakeThroughoutToTick.2 ⟨k', hk', ?_⟩
  rcases (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨_, hl₁⟩ hτ' with
      ⟨-, hall⟩ | ⟨k₀, τ', hk₀, hl₀, hτ'eq, haw₀⟩
  · left
    intro i hi
    rcases le_or_gt i (x.tickStep u (M.supportCutoff S.C (σ + 1))) with h | h
    · exact hall i h
    · exact Activity.mem_awake_of_mem_active (hact₁ i h.le hi)
  · right
    refine ⟨k₀, by omega, τ', ?_, hl₀, fun i h1 h2 => ?_⟩
    · rw [hτ'eq]
      exact hτle.trans (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (by omega))
    · rcases le_or_gt i (x.tickStep u (M.supportCutoff S.C (σ + 1))) with h | h
      · exact haw₀ i h1 h
      · exact Activity.mem_awake_of_mem_active (hact₁ i h.le h2)

/-- **Active through the previous slot's duties, or no live lock.** A validator `u` that ticks to the
support cutoff of slot `s + 1` and is active from the duty window's start of slot `s + 1` up to that
tick is in `activeAt M S A x s`, or holds, before the vote time of slot `s + 1`, no lock entry live
there.

Why: `mem_activeAt_of_live_lock` when some entry is live; otherwise the second disjunct.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`, `hWS`: the setup, the activity, the execution, its run facts, its
  environment facts, its wake shape; `s`: the slot; `u`: the validator.

Read aloud: a validator active up to its update of slot `s` was active through the duties of slot `s`,
or holds no live lock at the next vote time. -/
theorem mem_activeAt_or_lockFree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hw : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))) :
    u ∈ activeAt M S A x s ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false := by
  by_cases hL : ∃ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
      M.is_live (x.tickInput u (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true
  · exact Or.inl ((mem_activeAt_of_live_lock M F U) S A x R s u E hw hL)
  · refine Or.inr fun e he => ?_
    cases h : M.is_live (x.tickInput u (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e
    · rfl
    · exact absurd ⟨e, he, h⟩ hL

end GoldilocksCorrectness.Record.Proofs.Executions

