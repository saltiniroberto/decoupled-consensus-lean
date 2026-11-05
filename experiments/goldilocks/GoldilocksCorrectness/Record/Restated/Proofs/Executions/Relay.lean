module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameACStore
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Relay, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Relay.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: a vote an honest validator holds, in its pool or
included in a block of its tree, was re-sent by it as a Goldfish-vote object (the model's
`relayedObjects`). The delivery of such a re-send is read at the receiver's tick
(`pool_vote_at_tick_of_send`, `ReadingPoints.lean`); The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_le_iff slot_mono_int voteTime_cast
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (Carried DREBSpec.of_outcome forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (ac_on_block_new_slot on_goldfish_vote_new_slot
  receive_gfVote_cases)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_frame on_block_eq tick_prov tick_sends)

open GoldilocksCorrectness.Proofs.Routines (receive_new receive_new_slot)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq block_well_formed_iff
  fgState_initial_eq initial_eq on_ac_message_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The times -/

section Times

open Goldilocks.Sts (Setup)

end Times

/-! ## The admission's slot -/

section Admission

variable [RootOrder]

end Admission

/-! ## Along an execution -/

section Relays

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup relayedObjects)

variable [RootOrder]

/-- A Goldfish vote that enters a validator's pool of slot `s` at the step `k` was put on the wire
by that validator at that step, as a Goldfish-vote object; the validator was honest at the step's
time; and its clock value after the step is at least the start of slot `s`.

Why: the step is the validator's tick or a delivery to it. A tick adds a vote only as its own
Goldfish vote, sent at the vote time of its slot (a block it proposes holds only votes of its
pool, `lem19_tick_proposes`); a delivery adds only votes the delivered object carries, which the
wiring re-sends each as an object, and admits a vote only up to the current slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step; `w`: the validator;
  `s`: the slot; `vote`: the vote.

Read aloud: a vote entering `w`'s pool at a step was put on the wire by `w`, honest then, at that
step, with its clock value then at least the start of the vote's slot. -/
theorem step_pool_relayed (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {w : V} {s : Slot} {vote : GoldfishVote V}
    -- `vote` is in `w`'s votes of slot `s` after the step
    (hv : vote ∈ (x.st (k + 1) w).votesHeld s)
    -- `vote` is not in `w`'s votes of slot `s` before the step
    (hn : vote ∉ (x.st k w).votesHeld s) :
    (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k ∧
      w ∉ A.corrupted k ∧ M.slotStart S.C s ≤ x.clockValue (k + 1) w := by
  have hslot : vote.slot = s :=
    ((F.nd.nodeInvCore_poolKeyed ((lem11_node_invariantCore_of_run M F) S x R (k + 1) w).1)
      s vote hv).1
  -- the model's slot of a natural-number time is the spec's (`U`: both are the time divided by the
  -- slot's length)
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  rcases (step_cases_per_step M F) x R E k w with h | ⟨t, n', sent, hl, hmem, hrun, h, hw⟩ |
      ⟨sm, hl, hact, h⟩ | ⟨⟨tR, keep, hl⟩, -, -⟩
  · rw [h] at hv
    exact absurd hv hn
  · -- the validator's tick at `t`, at the step `k`, from its state there
    have hti : x.tickInput w t = x.st k w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [h] at hv
    have hP := F.tk.tick_prov S.C S.P S.X _ (t : Int) n' sent hrun
    obtain ⟨o, ho, hc⟩ := hP.1 s vote hv (by
      change vote ∉ M.votesHeld (x.tickInput w t) s
      rw [hti]
      exact hn)
    rcases hc with rfl | ⟨B', rfl, hvB⟩
    · -- the tick's own Goldfish vote, sent at the vote time of its slot
      refine ⟨hw _ ho, Activity.not_mem_corrupted_of_mem_active hmem, ?_⟩
      obtain ⟨-, hs, ht⟩ := (F.tk.tick_sends S.C S.P S.X _ (t : Int) n' sent hrun).1 vote ho
      rw [← hs, hslot] at ht
      have hvt : M.voteTime S.C s = t := by
        have h1 : ((M.voteTime S.C s : ℕ) : Int) = S.C.t_ s + S.C.Δ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S s
        exact_mod_cast h1.trans ht.symm
      have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
      have h3 := one_le_Δ S
      rw [x.clockValue_succ_of_tick hl]
      omega
    · -- a block the tick proposes holds only votes of the pool
      exfalso
      have hInv : M.nodeInv S.C S.P S.X (x.tickInput w t) := by
        rw [hti]
        exact ((lem11_node_invariant M F S A x R E k w) (Activity.not_mem_corrupted_of_mem_active hmem)).1
      obtain ⟨-, -, -, -, H, votes, support, hvotes, -, -, hB⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n' _ sent B'
          hrun hInv ho
      rw [hB] at hvB
      have hvv : vote ∈ votes := hvB
      rw [hvotes] at hvv
      change vote ∈ M.votesHeld (x.tickInput w t) _ at hvv
      rw [hti] at hvv
      have hs' : vote.slot = S.C.slot (t : Int) - 1 :=
        ((F.nd.nodeInvCore_poolKeyed ((lem11_node_invariantCore_of_run M F) S x R k w).1)
          _ vote hvv).1
      rw [← hs', hslot] at hvv
      exact hn hvv
  · -- a delivery to the validator
    rw [h] at hv
    have hc := (F.rcv.receive_new S.C S.P S.X _ sm.msg).1 s vote hv hn
    have hle := F.rcv.receive_new_slot S.C S.P S.X _ sm.msg s vote hv hn
    -- the clock, a natural number, is at most the delivery's time, and its slot is at least `s`
    have hc0 := (clock_nonneg M F) x R E k w
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (x.st k w).t = (n : Int) :=
      ⟨(x.st k w).t.toNat, (Int.toNat_of_nonneg hc0).symm⟩
    have hle' : vote.slot ≤ S.C.slot ((n : ℕ) : Int) := by rw [← hn]; exact hle
    rw [hslot] at hle'
    have hsn : M.slotStart S.C s ≤ n :=
      ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S s _).2
        (hsl _ ▸ hle')
    -- the clock value after the delivery is the one before it, `n`
    have hnk : x.clockValue (k + 1) w = n := by
      rw [x.clockValue_succ_of_not (fun t h => by rw [hl] at h; cases h)
        (fun t keep h => by rw [hl] at h; cases h)]
      have h := (clock_eq_clockValue M F) x R k w
      rw [hn] at h
      exact_mod_cast h.symm
    exact ⟨(step_sent_of_delivery M F) R hl ((GoldilocksCorrectness.Record.Proofs.Routines.gfVote_mem_relayedObjects M F) hc),
      Activity.not_mem_corrupted_of_mem_active hact, hnk ▸ hsn⟩
  · -- `w`'s wake keeps its votes
    exfalso
    apply hn
    have hV := (wake_case_votesHeld M F) x R hl
    change vote ∈ M.votesHeld (x.st (k + 1) w) s at hv
    rw [hV] at hv
    exact hv

/-- A Goldfish vote of a validator's pool at a step was put on the wire by that validator, as a
Goldfish-vote object, at an earlier step, at which it was honest, with its clock value after that
step at least the start of the vote's slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step; `w`: the validator;
  `s`: the slot; `vote`: the vote; `i`: the step of the re-send.

Read aloud: a vote `w` holds was re-sent by `w`, honest then, after its slot began. -/
theorem pool_vote_relayed (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (w : V) (s : Slot) (vote : GoldfishVote V)
    (hv : vote ∈ M.votesHeldSet (x.st k w) s) :
    ∃ i < k,
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      w ∉ A.corrupted i ∧ M.slotStart S.C s ≤ x.clockValue (i + 1) w := by
  induction k with
  | zero =>
      rw [(getElem_zero_st M F) x R] at hv
      have h := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv
      rw [F.init.initial_votesHeld] at h
      exact absurd h List.not_mem_nil
  | succ k ih =>
      by_cases hk : vote ∈ M.votesHeldSet (x.st k w) s
      · obtain ⟨i, hi, h⟩ := ih hk
        exact ⟨i, by omega, h⟩
      · exact ⟨k, by omega, (step_pool_relayed M F U) S A x R E (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv)
          (fun h => hk (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))⟩

/-- A Goldfish vote of a validator's pool before the time `t` was put on the wire by that
validator, as a Goldfish-vote object, at a step before `stepBefore M x t`, at which it was honest,
with its clock value after that step at least the start of the vote's slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the validator;
  `s`: the slot; `vote`: the vote; `i`: the step of the re-send.

Read aloud: a vote `w` holds before `t` was re-sent by `w` before `t`. -/
theorem pool_vote_relayed_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (w : V) (s : Slot) (vote : GoldfishVote V)
    (hv : vote ∈ M.votesHeldSet (x.stateBefore t w) s) :
    ∃ i < x.stepBefore t,
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      w ∉ A.corrupted i ∧ M.slotStart S.C s ≤ x.clockValue (i + 1) w :=
  (pool_vote_relayed M F U) S A x R E (x.stepBefore t) w s vote hv

/-- A Goldfish vote of a validator's pool after the step `k` that was not in the pool after the
earlier step `k₀` was put on the wire by that validator, as a Goldfish-vote object, at a step from
`k₀` on and before `k`, at which it was honest, with its clock value after that step at least the
start of the vote's slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `k₀`, `k`: the two steps; `w`: the
  validator; `s`: the slot; `vote`: the vote; `i`: the step of the re-send.

Read aloud: a vote `w` came to hold between two steps was re-sent by `w`, honest then, between
them, after its slot began. -/
theorem pool_vote_relayed_after (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k₀ k : ℕ} {w : V} {s : Slot} {vote : GoldfishVote V}
    -- `vote` is not in `w`'s pool of slot `s` after `k₀` steps, and is after `k` steps
    (hn : vote ∉ M.votesHeldSet (x.st k₀ w) s) (hv : vote ∈ M.votesHeldSet (x.st k w) s) :
    ∃ i, k₀ ≤ i ∧ i < k ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      w ∉ A.corrupted i ∧ M.slotStart S.C s ≤ x.clockValue (i + 1) w := by
  induction k with
  | zero =>
      rw [(getElem_zero_st M F) x R] at hv
      have h := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv
      rw [F.init.initial_votesHeld] at h
      exact absurd h List.not_mem_nil
  | succ k ih =>
      by_cases hk : vote ∈ M.votesHeldSet (x.st k w) s
      · obtain ⟨i, h0, hi, h⟩ := ih hk
        exact ⟨i, h0, by omega, h⟩
      · have hk₀ : k₀ ≤ k := by
          by_contra hlt
          -- the pool only grows: held after `k + 1 ≤ k₀` steps, so after `k₀` steps
          exact hn ((pool_mono M F) x R E w (show k + 1 ≤ k₀ by omega) s hv)
        exact ⟨k, hk₀, by omega, (step_pool_relayed M F U) S A x R E
          (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv)
          (fun h => hk (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))⟩

/-- A Goldfish vote included in a non-genesis block of a validator's tree before the time `t` was
put on the wire by that validator, as a Goldfish-vote object, at a step before `stepBefore M x t`,
at which it was honest, with its clock value after that step at least the start of the vote's slot.

Why: at the step the block entered the tree, the validator either received it, and the wiring
re-sent each of its votes as an object, or proposed it, and its votes were already in its pool,
which the validator re-sent earlier (`pool_vote_relayed`). A received block's votes are of the slot
before the block's, which is at most the slot of the validator's clock.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the validator;
  `B'`: the block; `vote`: a vote it includes; `i`: the step of the re-send.

Read aloud: a vote included in a block `w` holds before `t` was re-sent by `w` before `t`. -/
theorem included_vote_relayed_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (w : V) (B' : Block V) (vote : GoldfishVote V)
    (hB : B' ∈ (x.stateBefore t w).tree) (hne : B' ≠ Block.genesis) (hvote : vote ∈ B'.votes) :
    ∃ i < x.stepBefore t,
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      w ∉ A.corrupted i ∧ M.slotStart S.C vote.slot ≤ x.clockValue (i + 1) w := by
  classical
  -- the step at which `B'` entered `w`'s tree
  have hex : ∃ m : ℕ, B' ∈ (x.st m w).tree := ⟨x.stepBefore t, hB⟩
  have h0 : B' ∉ (x.st 0 w).tree := by
    rw [(getElem_zero_st M F) x R, F.init.initial_tree]
    intro h
    exact hne (Finset.mem_singleton.1 h)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ x.stepBefore t := Nat.find_min' hex hB
  obtain ⟨i, hi⟩ : ∃ i : ℕ, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hni : B' ∉ (x.st i w).tree := Nat.find_min hex (by omega)
  have hi1 : B' ∈ (x.st (i + 1) w).tree := hi ▸ Nat.find_spec hex
  have hit : i < x.stepBefore t := by omega
  -- the model's slot of a natural-number time is the spec's (`U`)
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  rcases (step_cases_per_step M F) x R E i w with h | ⟨t', n', sent, hl, hmem, hrun, h, -⟩ |
      ⟨sm, hl, hact, h⟩ | ⟨⟨tR, keep, hl⟩, -, -⟩
  · rw [h] at hi1
    exact absurd hi1 hni
  · -- `w` proposed `B'` at its tick, from its state at the step `i`: `B'`'s votes were in its pool
    have hti : x.tickInput w t' = x.st i w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    have hBn := hi1
    rw [h] at hBn
    have hP := F.tk.tick_prov S.C S.P S.X _ (t' : Int) n' sent hrun
    obtain ⟨hBs, -⟩ := hP.2 B' hBn (by rw [hti]; exact hni)
    have hInv : M.nodeInv S.C S.P S.X (x.tickInput w t') := by
      rw [hti]
      exact ((lem11_node_invariant M F S A x R E i w) (Activity.not_mem_corrupted_of_mem_active hmem)).1
    obtain ⟨-, -, -, -, H, votes, support, hvotes, -, -, hBdef⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n' _ sent B'
        hrun hInv hBs
    rw [hBdef] at hvote
    have hvv : vote ∈ votes := hvote
    rw [hvotes] at hvv
    change vote ∈ M.votesHeld (x.tickInput w t') _ at hvv
    rw [hti] at hvv
    have hs' : vote.slot = S.C.slot (t' : Int) - 1 :=
      ((F.nd.nodeInvCore_poolKeyed ((lem11_node_invariantCore_of_run M F) S x R i w).1)
        _ vote hvv).1
    obtain ⟨j, hj, hsend, hhon, hstart⟩ := (pool_vote_relayed M F U) S A x R E i w
      (S.C.slot (t' : Int) - 1) vote (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 hvv)
    refine ⟨j, by omega, hsend, hhon, ?_⟩
    rw [hs']
    exact hstart
  · -- `w` received `B'`, and re-sent each of its votes
    have hi1' := hi1
    rw [h] at hi1'
    obtain ⟨hmsg, -⟩ := (F.rcv.receive_new S.C S.P S.X _ sm.msg).2 B' hi1' hni
    have hsend : (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i := by
      refine (step_sent_of_delivery M F) R hl ?_
      rw [hmsg]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.gfVote_mem_relayedObjects_block M F) hvote
    -- the slot: `vote.slot = B'.slot - 1 ≤ B'.slot ≤` the slot of `w`'s clock after the step
    have hwf := (((F.nd.nodeInvCore_treeClosed ((lem11_node_invariantCore_of_run M F) S x R
      (i + 1) w).1)).2 B' hi1 hne)
    have hwf' := hwf.2.1
    rw [F.rd.block_well_formed_iff] at hwf'
    have hvs : vote.slot = B'.slot - 1 :=
      ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B' hwf'.1.2).1 vote hvote
    obtain ⟨-, -, hBslot⟩ := (step_tree_new M F) x R E hi1 hni
    -- `w`'s clock after the step is its clock value then
    have hn : (x.st (i + 1) w).t = ((x.clockValue (i + 1) w : ℕ) : Int) := (clock_eq_clockValue M F) x R (i + 1) w
    have hsn : M.slotStart S.C vote.slot ≤ x.clockValue (i + 1) w := by
      refine ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S _ _).2 ?_
      rw [hvs, hsl, ← hn]
      exact le_trans (Nat.sub_le _ _) hBslot
    exact ⟨i, hit, hsend, Activity.not_mem_corrupted_of_mem_active hact, hsn⟩
  · -- `w`'s wake keeps its tree
    rw [(wake_case_tree M F) x R hl] at hi1
    exact absurd hi1 hni

end Relays

end GoldilocksCorrectness.Record.Proofs.Executions

