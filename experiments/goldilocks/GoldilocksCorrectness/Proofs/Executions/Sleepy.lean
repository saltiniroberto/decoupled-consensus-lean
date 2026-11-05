module
public import GoldilocksCorrectness.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Proofs.Executions.Wake
public import GoldilocksCorrectness.Proofs.Executions.Steps
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Routines.Score
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.Node

@[expose] public section

/-!
# The sleepy model over executions

The proofs of the statements of `GoldilocksCorrectness/Statements/Executions/SleepyStatements.lean`:
an honest active validator of a slot is an updater of it; fewer than a third is fewer than a
quorum; Lemma 87, sleepiness with permanent corruption keeps every set of validators corrupted by
a time smaller than a quorum; Lemma 88, committee sleepiness bounds the committee, the pool and the
counted votes of a slot by twice its honest active members; a validator asleep in the window
before the duty window of a slot holds no live lock entry at that slot's vote time; and an honest
active committee member puts its Goldfish vote on the wire at the vote time.

The kit facts they need: the counted votes of a slot are from its committee
(`countedVotes_committee`); what the Goldfish vote duty, the tick of the available chain and the
node's tick send, in the direction "the vote is sent" (`goldfish_vote_emits_vote`,
`ac_on_tick_emits_vote`, `tick_emits_vote`); and the arithmetic of `S.C.t_` (`t_add`, `t_one`,
`lt_of_t_lt`).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  duty_window_start_mono lt_of_t_lt one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_cast
  supportCutoff_eq supportCutoff_slot t_add t_le_of_le t_one voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.bind_nil
  DREBEmits.broadcast_then DREBEmits.dite DREBEmits.ite DREBEmits.liftM DREBEmits.monadLift
  DREBEmits.pure)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (is_live_eq_false_iff)

open GoldilocksCorrectness.Proofs.Routines (tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff mem_included_votes_iff wake_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_eq_toNat duty_window_start_eq t_eq_mul)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (CountedVotes lem65b_quorum_threshold)
open GoldilocksCorrectness.Proofs.Routines (mem_participants_iff ac_valid_payload_facts
  voters_count_lt_of_committee_majority awake_since_record_awake)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- An honest active validator of slot `s` is an updater of slot `s`. The proof; the audited
statement is in `Statements/Executions/SleepyStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot. -/
theorem honestActiveAt_subset_updaterAt (S : Setup V) (Sched : Schedule V) (s : ℕ) :
    honestActiveAt S Sched s ⊆ updaterAt S Sched s := by
  intro v hv
  unfold honestActiveAt activeAt at hv
  unfold updaterAt
  rw [Finset.mem_sdiff] at hv ⊢
  refine ⟨?_, hv.2⟩
  rw [mem_awakeThroughout_iff] at hv ⊢
  have hle : ((dutyWindowStart S s : ℕ) : Int) ≤ ((dutyWindowStart S (s + 1) : ℕ) : Int) := by
    exact_mod_cast dutyWindowStart_mono S (Nat.le_succ s)
  intro t h1 h2
  exact hv.1 t (le_trans hle h1) h2

omit [DecidableEq V] [RootOrder] in
/-- Fewer than a third of the validators is fewer than a quorum. The proof; the audited statement
is in `Statements/Executions/SleepyStatements.lean`.

The variables:
- `Sched`: the schedule; `t`: the time. -/
theorem fewerThanQuorum_of_fewerThanThird (Sched : Schedule V) (t : Int)
    (h : AdversaryFewerThanThirdUntil Sched (validator_count V) t) : AdversaryFewerThanQuorumUntil Sched (quorum V) t := by
  intro A hA
  have h1 := h A hA
  have h2 := (lem65b_quorum_threshold (V := V)).2
  omega

omit [RootOrder] in
/-- **Lemma 87, fewer than a quorum ever corrupted.** The proof; the audited statement is in
`Statements/Executions/SleepyStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which sleepiness holds. -/
theorem lem87_adversary_fewer_than_quorum (S : Setup V) (Sched : Schedule V) (anchor : ℕ)
    (hMono : Sched.MonotoneCorruption)
    (hSleep : Sleepiness S Sched anchor) :
    ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t := by
  intro t A hA
  have hΔ := one_le_Δ S
  have hss : slotStart S (anchor + t.toNat + 1) = 4 * Δ S * (anchor + t.toNat + 1) :=
    slotStart_eq S _
  have hge : anchor + t.toNat + 1 ≤ slotStart S (anchor + t.toNat + 1) := by
    rw [hss]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hvt := voteTime_eq S (anchor + t.toNat + 1)
  have hts : t ≤ ((voteTime S (anchor + t.toNat + 1) : ℕ) : Int) := by
    have : t ≤ (t.toNat : Int) := Int.self_le_toNat t
    omega
  have hsub : A ⊆ Sched.adv ((voteTime S (anchor + t.toNat + 1) : ℕ) : Int) := by
    intro v hv
    obtain ⟨t', ht', hvt'⟩ := hA v hv
    exact hMono t' _ (le_trans ht' hts) hvt'
  have h1 := hSleep (anchor + t.toNat + 1) (by omega) (by omega)
  have h2 := Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ
    (activeAt S Sched (anchor + t.toNat + 1 - 1)))
    (le_refl (Sched.adv ((voteTime S (anchor + t.toNat + 1) : ℕ) : Int))))
  have h3 : (Finset.univ \ Sched.adv ((voteTime S (anchor + t.toNat + 1) : ℕ) : Int)).card +
      (Sched.adv ((voteTime S (anchor + t.toNat + 1) : ℕ) : Int)).card = validator_count V := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    rfl
  have h4 := (lem65b_quorum_threshold (V := V)).2
  have h5 := Finset.card_le_card hsub
  omega

/-- **Kit fact, counted votes are from the committee.** Every vote of a set of slot-`s` votes that
a slot-`(s + 1)` Goldfish vote counts on `v`'s node state before `t` (`CountedVotes`) is from a
member of the committee of slot `s`: a pool vote by the node invariant's filing of the pool, a
vote included in a slot-`(s + 1)` block of the frame's tree by that block's well-formedness.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `s`: the slot;
  `v`: the validator; `votes`, `support_votes`: the counted sets.

Read aloud: the votes a Goldfish vote of slot `s + 1` counts are from slot `s`'s committee. -/
theorem countedVotes_committee (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t s : ℕ) (v : V)
    (votes support_votes : Finset (GoldfishVote V))
    (hC : CountedVotes S.C (stateBefore x t v).A (fg_to_ac (stateBefore x t v).S) (s + 1)
      votes support_votes) :
    ∀ vote ∈ votes, vote.val_index ∈ S.P.committee s := by
  intro vote hv
  rcases (hC.1 vote).1 hv with ⟨hp, -⟩ | hinc
  · rw [Nat.add_sub_cancel] at hp
    exact pool_committee_of_stateBefore S Sched x t v s vote hp
  · simp only [mem_included_votes_iff,
      Nat.add_sub_cancel] at hinc
    obtain ⟨B, ⟨hB, hBs⟩, hvB, -⟩ := hinc
    have hBT := ((mem_fg_to_ac_tree _ _).1 hB).1
    have hne : B ≠ Block.genesis := by
      rintro rfl
      exact Nat.succ_ne_zero s hBs.symm
    have hwf := (((lem11_node_invariant S Sched x (stepBefore x t) v).1.2.2.1).2 B hBT hne).2.1
    rw [block_well_formed_iff] at hwf
    have h := (ac_valid_payload_facts S.P B hwf.1.2).2.2 vote hvB
    rwa [hBs, Nat.add_sub_cancel] at h

/-- **Lemma 88, the counting hypotheses from committee sleepiness.** The proof; the audited
statement is in `Statements/Executions/SleepyStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s`: the slot; `v`: the validator; `t`: the time. -/
theorem lem88_counting_of_committeeSleepiness (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (anchor s : ℕ) (v : V) (t : ℕ)
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hs : anchor ≤ slotStart S (s + 1)) :
    |S.P.committee s| < 2 * |honestActiveAt S Sched s ∩ S.P.committee s| ∧
    voters_count ((stateBefore x t v).A.pool s) <
      2 * |honestActiveAt S Sched s ∩ S.P.committee s| ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x t v).A (fg_to_ac (stateBefore x t v).S) (s + 1)
        votes support_votes →
      voters_count votes < 2 * |honestActiveAt S Sched s ∩ S.P.committee s|) := by
  have hK := hSleepK (s + 1) (by omega) hs
  rw [Nat.add_sub_cancel] at hK
  have hsub : S.P.committee s \ (honestActiveAt S Sched s ∩ S.P.committee s) ⊆
      S.P.committee s \ honestActiveAt S Sched s := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
    tauto
  have hMaj : |S.P.committee s \ (honestActiveAt S Sched s ∩ S.P.committee s)| <
      |honestActiveAt S Sched s ∩ S.P.committee s| :=
    lt_of_le_of_lt (Finset.card_le_card hsub) hK
  refine ⟨?_, ?_, ?_⟩
  · have := Finset.card_le_card_sdiff_add_card (s := S.P.committee s)
      (t := honestActiveAt S Sched s ∩ S.P.committee s)
    omega
  · exact voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x t v s)
      hMaj
  · intro votes support_votes hC
    exact voters_count_lt_of_committee_majority
      (countedVotes_committee S Sched x t s v votes support_votes hC) hMaj

/-- An honest active member of the committee of slot `s` puts a slot-`s` Goldfish vote on the
wire at its tick at the vote time of slot `s`. The proof; the audited statement is in
`Statements/Executions/SleepyStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the
  validator. -/
theorem honest_active_votes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (u : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hu : u ∈ honestActiveAt S Sched s)
    (hK : u ∈ S.P.committee s) :
    ∃ (i : ℕ) (vote : GoldfishVote V), x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
      vote.val_index = u ∧ vote.slot = s ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent := by
  have hΔ := one_le_Δ S
  have hvt : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S s, Nat.mul_add, Nat.mul_one]
  have hslot : S.C.slot ((voteTime S s : ℕ) : Int) = s := slot_eq_of_mem S (by omega) (by omega)
  have hvc : ((voteTime S s : ℕ) : Int) =
      S.C.t_ (S.C.slot ((voteTime S s : ℕ) : Int)) + S.C.Δ := by
    rw [hslot]; exact voteTime_cast S s
  have hdw : dutyWindowStart S s < voteTime S s := by
    have h1 := dutyWindowStart_mono S (Nat.le_add_right s 1)
    have h2 := dutyWindowStart_succ_le_slotStart S s
    omega
  have hcut : voteTime S s ≤ supportCutoff S (s + 1) := by
    have h1 := supportCutoff_eq S (s + 1)
    have h2 := voteTime_eq S (s + 1)
    omega
  unfold honestActiveAt activeAt at hu
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff] at hu
  have hAwake : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ voteTime S s →
      u ∈ Sched.awake (t' : Int) :=
    fun t' h1 h2 => hu.1 t' (by exact_mod_cast h1) (by exact_mod_cast (le_trans h2 hcut))
  have hHon : u ∉ Sched.adv ((voteTime S s : ℕ) : Int) :=
    fun h => hu.2 (hMono _ _ (by exact_mod_cast hcut) h)
  have h1 : 1 ≤ voteTime S s := by omega
  have hl := (stepBefore_spec x hDiv h1).1
  have hvA := hAwake _ (le_of_lt hdw) le_rfl
  obtain ⟨n', sent, hrun, -⟩ := tick_step_outcome x hl hvA hHon
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_le_dutyWindowStart_b S Sched x s (voteTime S s) u hDiv hMono
    hdw hAwake hHon
  have hnv : (tickInputState x (stepBefore x (voteTime S s)) (voteTime S s) u).v = u := by
    have h := (lem11_node_invariant S Sched x (stepBefore x (voteTime S s)) u).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  have hL := (tick_emits_vote S.C S.P S.X _ _).of_outcome hrun
  obtain ⟨h, hh⟩ := hL hvc (awake_since_record_awake hτ (by rw [hslot]; exact hτle))
    (by rw [hnv, hslot]; exact hK)
  rw [hnv, hslot] at hh
  exact ⟨_, ⟨u, s, h⟩, hl, rfl, rfl,
    step_sent_of_tick_send hl (Finset.mem_sdiff.2 ⟨hvA, hHon⟩) hrun hh⟩

/-- A validator asleep at some time from the duty window's start of slot `s` to before the duty
window's start of slot `s + 1` holds no lock entry live at the vote time of slot `s + 1`. The
proof; the audited statement is in `Statements/Executions/SleepyStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the
  validator. -/
theorem lock_free_after_wake (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (u : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSlept : ∃ t : ℕ, dutyWindowStart S s ≤ t ∧ t < dutyWindowStart S (s + 1) ∧
      u ∉ Sched.awake (t : Int)) :
    ∀ e ∈ (stateBefore x (voteTime S (s + 1)) u).A.lock_entries,
      is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
        ((voteTime S (s + 1) : ℕ) : Int) e = false := by
  intro e he
  obtain ⟨s₁, hd, hc₁, ⟨τ, hτ, hτle⟩, -⟩ := lem39_lock_entry_provenance S Sched x _ u e hDiv he
  obtain ⟨⟨hAw, hHon⟩, -⟩ := update_state_of_lock_entry S Sched x _ s₁ u e hDiv he hd hc₁
  obtain ⟨t₀, h1, h2, hAsleep⟩ := hSlept
  have hc1 : 1 ≤ supportCutoff S (s₁ + 1) := (supportCutoff_slot S s₁).2
  have hwin := awake_of_tickInput_awakeSince x hDiv hMono hc1 hτ hAw hHon
  have hΔ : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
  have hcC := supportCutoff_cast S (s₁ + 1)
  have hvC := voteTime_cast S (s + 1)
  have hts₁ := t_add S s₁ 1
  have hts := t_add S s 1
  have h1t := t_one S
  have hc₁' : ((supportCutoff S (s₁ + 1) : ℕ) : Int) < ((voteTime S (s + 1) : ℕ) : Int) := by
    exact_mod_cast hc₁
  -- `s₁ < s`: the update at the support cutoff of slot `s₁ + 1` is before the vote time of `s + 1`
  have hs₁ : s₁ < s := lt_of_t_lt S (by omega)
  by_cases hcase : supportCutoff S (s₁ + 1) ≤ t₀
  · -- asleep after the update: the entry's deadline is past
    have h2' : @LT.lt Int _ (t₀ : Int) (duty_window_start S.C (s + 1)) :=
      Int.lt_toNat.1 (by rw [← dutyWindowStart_eq_toNat]; exact h2)
    have hdws : @Eq Int (duty_window_start S.C (s + 1))
        (S.C.t_ (s + 1) + S.C.Δ - 4 * S.C.Δ * (S.C.k : Int)) := duty_window_start_eq S.C (s + 1)
    have htk : @Eq Int (S.C.t_ S.C.k) (4 * S.C.Δ * (S.C.k : Int)) := t_eq_mul S.C S.C.k
    have hcase' : ((supportCutoff S (s₁ + 1) : ℕ) : Int) ≤ ((t₀ : ℕ) : Int) := by
      exact_mod_cast hcase
    have hkt := t_add S s₁ S.C.k
    have hlt : s₁ + S.C.k < s := lt_of_t_lt S (by omega)
    have hle := t_le_of_le S (Nat.le_of_lt hlt)
    have hd' : @Eq Int e.d (S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ) := hd
    rw [is_live_eq_false_iff]
    left
    show @LE.le Int _ e.d ((voteTime S (s + 1) : ℕ) : Int)
    omega
  · -- asleep before the update: `u` was awake then, since `τ`
    exfalso
    have hτle' : @LE.le Int _ τ (duty_window_start S.C (s₁ + 1)) := hτle
    have hmono : @LE.le Int _ (duty_window_start S.C (s₁ + 1)) (duty_window_start S.C s) :=
      duty_window_start_mono S (by omega)
    have hds : @LE.le Int _ (duty_window_start S.C s) ((dutyWindowStart S s : ℕ) : Int) :=
      duty_window_start_le_dutyWindowStart S s
    have h1' : ((dutyWindowStart S s : ℕ) : Int) ≤ ((t₀ : ℕ) : Int) := by exact_mod_cast h1
    exact hAsleep (hwin t₀ (show @LE.le Int _ τ (t₀ : Int) by omega) (by omega))

end GoldilocksCorrectness.Proofs.Executions
