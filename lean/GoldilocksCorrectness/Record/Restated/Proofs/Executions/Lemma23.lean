module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ReadingPoints
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Executions.CountAgreement
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma23, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma23.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 23, an honest proposer and the next slot's
honest voter count alike. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem viewFreeze_cast
  viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes ProposalCountedVotes ResolvesAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (compatible_iff goldfish_score_eq_ok
  resolved_eq_ok_true tau_eq_ok_some tau_head_of_eq_some tau_eq_some_blockStamp ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Kit theorem, a vote that entered the holder's pool before its tick to `t_e` reaches the receiver by its
tick to `t_e + Δ S`, the receiver's window in the step form.** `pool_vote_reaches_at_tick_core` with the
receiver `v₂` active after every step from a real time `tW`, at most `t_e + Δ S − max (Δ S) Δs` and at most
`t_e − ΔClockAhead`, up to its tick `kR` to `t_e + Δ S`, read at that tick: `v₁` re-sent the vote when it
entered its pool (`step_pool_relayed`); from the read time `t_e + Δ S − max (Δ S) Δs` on, the delivery route
(`pool_vote_at_tick_of_send`), before it the sync route (`pool_vote_at_tick_of_held`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- as `pool_vote_reaches_at_tick_core`'s; `tW`: the start of `v₂`'s window; `kR`: `v₂`'s tick to `t_e + Δ S`.

Read aloud: a vote the holder took in before its tick to `t_e` is in the receiver's pool at its tick to
`t_e + Δ S`, or the receiver holds two votes of its validator. -/
theorem pool_vote_reaches_at_tick_steps (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e b : ℕ) (v₁ v₂ : V)
    (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet
      ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject
      (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    (hhi : t_e + Δ S < M.slotStart S.C (s + 2)) (hb : t_e + Δ S ≤ b) (h1 : 1 ≤ t_e)
    -- `v₁` is active for the sync delay after the read time `t_e + Δ S − max (Δ S) Δs`
    (hv₁ : v₁ ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v₁` ticks to `t_e` at `kₑ`; the vote entered its pool of slot `s` at the step `e`, before
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v₁ t_e)
    (e : ℕ) (hek : e < kₑ) (hne : vote ∉ M.votesHeldSet (x.st e v₁) s)
    (he1 : vote ∈ M.votesHeldSet (x.st (e + 1) v₁) s)
    -- `v₂` ticks to `t_e + Δ S` at `kR`, active after every step from the real time `tW` up to `kR`
    (tW : ℝ) (htW : tW ≤ (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)) (htWe : tW ≤ (t_e : ℝ) - ΔClockAhead)
    (kR : ℕ) (hkR : x.lbl kR = Event.tick v₂ (t_e + Δ S))
    (hwin : ∀ j : ℕ, tW ≤ x.time j → j ≤ kR → v₂ ∈ A.active j) :
    vote ∈ M.votesHeldSet (x.st kR v₂) s ∨
      ∃ u₁ ∈ M.votesHeldSet (x.st kR v₂) s, ∃ u₂ ∈ M.votesHeldSet (x.st kR v₂) s,
        u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hsent, hhon, hrel0⟩ := (step_pool_relayed M F U) S A x R E
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 he1)
    (fun h => hne (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))
  have hvₑ : v₁ ∉ A.corrupted kₑ := E.not_mem_corrupted_of_tick hkₑ
  have hrel : M.slotStart S.C s ≤ t_e :=
    le_trans hrel0 (le_trans (E.clockValue_mono (show e + 1 ≤ kₑ by omega) hvₑ)
      (E.clockValue_le_of_set hvₑ (Or.inl hkₑ)))
  have heT : x.time (e + 1) ≤ (t_e : ℝ) + ΔClockBehind :=
    le_trans (htime (show e + 1 ≤ kₑ by omega)) (E.tick_active kₑ v₁ t_e hkₑ).2.2
  have hslot : vote.slot = s := (pool_slot_of_exec M F) S A x R E (e + 1) v₁ s vote he1
  have hcomm : vote.val_index ∈ S.P.committee s := (pool_committee_of_exec M F) S A x R E (e + 1) v₁ s vote he1
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hcb : max (Δ S) Δs ≤ t_e + Δ S := by omega
  have ht₀e : (t_e + Δ S) - max (Δ S) Δs ≤ t_e := by omega
  have ht₀eR : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ t_e := by exact_mod_cast ht₀e
  by_cases hlate : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ x.time (e + 1)
  · exact (pool_vote_at_tick_of_send M F U) S A x R GST s t_e b v₁ v₂ vote E hNet hSkew hRedeliver
      (by omega) hb hhi hslot hcomm hrel h1 e hsent hhon heT tW (le_trans htW hlate) htWe kR hkR hwin
  · push_neg at hlate
    have h0 : (0 : ℝ) ≤ x.time (e + 1) := (time_nonneg M) x R (e + 1)
    have h1t : 1 ≤ (t_e + Δ S) - max (Δ S) Δs := by
      have : (0 : ℝ) < ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) := lt_of_le_of_lt h0 hlate
      exact_mod_cast this
    have hiek : e < x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) := ((lt_stepBefore_iff M) x R E).2 hlate
    obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E h1t
    have hΔsR : (0 : ℝ) ≤ Δs := by positivity
    have hvk : v₁ ∈ A.active (x.stepBefore ((t_e + Δ S) - max (Δ S) Δs)) :=
      Activity.mem_activeThroughout.1 hv₁ _ (by linarith) hk2
    exact (pool_vote_at_tick_of_held M F U) S A x R GST s t_e b v₁ v₂ vote E hSkew hRedeliver Sy hb hhi
      hslot hcomm hrel h1 ((t_e + Δ S) - max (Δ S) Δs) (by omega) (by omega)
      (by linarith) _ hk1 hk2 hvk
      ((pool_mono M F) x R E v₁ (show e + 1 ≤ x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) by omega) s he1)
      (fun i h1 h2 => Activity.mem_activeThroughout.1 hv₁ i h2 (le_trans h1 (htime (Nat.le_succ i))))
      tW htW htWe kR hkR hwin

/-- **Kit theorem, a block in a validator's tree at its tick to `c` has a slot starting by `c`.** When `v`
ticks to a positive clock value `c` at step `k`, active after every step from the real time
`c − ΔClockAhead` up to `k`, every block other than the genesis block of `v`'s tree at `k` has a slot whose
start is at most `c`: it entered the tree at a step whose clock value bounds its slot
(`tree_block_relayed_entry`, `clock_eq_clockValue`), at most `v`'s clock value at `k` (`clockValue_mono`),
less than `c` (`clockValue_lt_of_tick_of_active`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the tick's step; `v`: the
  validator; `c`: the tick's clock value; `H`: the block.

Read aloud: what a validator holds when its clock reaches `c` is of a slot started by `c`. -/
theorem slotStart_le_of_mem_tickInput (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k c : ℕ} {v : V} {H : Block V}
    (hl : x.lbl k = Event.tick v c) (hc : 0 < c)
    (hwin : ∀ j : ℕ, (c : ℝ) - ΔClockAhead ≤ x.time j → j ≤ k → v ∈ A.active j)
    (hH : H ∈ (x.st k v).tree) (hg : H ≠ Block.genesis) :
    M.slotStart S.C H.slot ≤ c := by
  obtain ⟨i, hi, -, -, hslot, -⟩ := (tree_block_relayed_entry M F) x R E hH hg
  rw [(clock_eq_clockValue M F) x R (i + 1) v] at hslot
  have hcv1 : x.clockValue (i + 1) v ≤ x.clockValue k v :=
    E.clockValue_mono (show i + 1 ≤ k by omega) (E.not_mem_corrupted_of_tick hl)
  have hcv2 : x.clockValue k v < c := (clockValue_lt_of_tick_of_active M F) E hl hc hwin
  have hsl : M.slot S.C (x.clockValue (i + 1) v) = S.C.slot ((x.clockValue (i + 1) v : ℕ) : Int) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have h1 : M.slotStart S.C H.slot ≤ x.clockValue (i + 1) v :=
    (F.sched.slotStart_le_iff S _ _).2 (by rw [hsl]; exact hslot)
  omega

/-- **Lemma 23, an honest proposer and the next slot's honest voter count alike.** The proof; the
audited statement is in `Statements/Executions/CountAgreementStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes;
- `B`: the proposal of slot `s + 1`; `p`: its proposer; `w`: the voter of slot `s + 1`;
- `votes_p`, `support_p`: the sets `p`'s proposal counts; `votes_w`, `support_w`: the sets `w`'s
  vote counts.

Roots name blocks until the real time of `w`'s tick to `M.voteTime S.C (s + 1)`: the proof compares the
blocks `w` holds at that tick with those `p` holds at its tick to the start `t₁` of slot `s + 1`, and takes
blocks `p` holds at its tick as held by `w` at its tick (`block_at_tick_of_held_tick`).

 each is
active at every step from the first one whose time is `ΔClockAhead` before `t₁ − max (Δ S) Δs` up to that
tick, and in every configuration in force at a real time of `[t₁ − max (Δ S) Δs, t₁ − max (Δ S) Δs + Δs]` (the
holder clause of the sync fact); what `w` stamped before the view freeze of slot `s` reaches `p` by its tick
(`pool_vote_reaches_at_tick_steps`, `block_at_tick_of_held_tick`) (`mem_T_before_add_delay`).

Read aloud: the votes the honest proposer `p` counts at the start of slot `s + 1` and those the
honest voter `w` counts at the vote time of slot `s + 1` give the same score to every block that has
both finalized blocks as ancestors, and the same number of voters.

`w`'s tree, pool, finalized block and scores are read at the state its own tick to the vote time of slot `s + 1`
starts from (`x.tickInput w (M.voteTime S.C (s + 1))`; rule R3, finding F-50-5), as Lemma 24, the proof's
caller, reads them. -/
theorem lem23_proposer_and_voter_count_alike (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (B : Block V) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.slotStart S.C (s + 1))
    -- `p` ticks to the start of slot `s + 1` at a step `kP` and is active after every step from the first one
    -- whose time is `ΔClockAhead` before `M.slotStart S.C (s + 1) - max (Δ S) Δs` up to `kP`
    (hp : ∃ kP : ℕ, x.lbl kP = Event.tick p (M.slotStart S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kP →
        p ∈ A.active j)
    -- `w` ticks to the vote time of slot `s + 1` at a step `kW` and is active after every step from the same
    -- first one up to `kW`
    (hw : ∃ kW : ℕ, x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kW →
        w ∈ A.active j)
    -- `p` and `w` are active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the
    -- window's start `M.slotStart S.C (s + 1) - max (Δ S) Δs` (:'s holder clause)
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldW : w ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hBw : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree)
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B) :
    ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput p (M.slotStart S.C (s + 1))) s votes_p support_p →
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      (∀ D : Block V, (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq D →
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq D → ∃ n : ℕ,
          goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s
            D = .ok n ∧
          goldfish_score (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes_w support_w s
            D = .ok n) ∧
      M.voters_count votes_p = M.voters_count votes_w := by
  -- the delivery premises up to the vote time of slot `s + 1`, the deadline of the relays
  have E' := E.upTo (M.voteTime S.C (s + 1))
  have Sy' := Sy.upTo (M.voteTime S.C (s + 1))
  obtain ⟨kP, hkP, hpwin⟩ := hp
  obtain ⟨kW, hkW, hwwin⟩ := hw
  -- the states read: `p`'s tick input at `kP`, `w`'s at `kW`
  have hPin : x.tickInput p (M.slotStart S.C (s + 1)) = x.st kP p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E' hkP]
  have hWin : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kW w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E' hkW]
  rw [hPin, hWin]
  rw [hWin] at hBw hOnly
  rw [(tickStep_eq_of_lbl M) x E' hkW] at hRoots
  intro votes_p support_p votes_w support_w hPCV hCV
  obtain ⟨hVp, hSupP⟩ := hPCV
  obtain ⟨hCv, hCs⟩ := hCV
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- step 0: the times
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E'.ahead_nonneg
  have hB0 := E'.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfz : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfzΔ : M.viewFreeze S.C s + Δ S = M.slotStart S.C (s + 1) := by omega
  have hfzc : ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) =
      (((M.viewFreeze S.C s : ℕ) : Int) : Stamp) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
  -- the slot of `t₁`, read by the spec's clock (the model's slot of a natural-number time is the
  -- spec's, `U`)
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _) (by omega)
  -- the window's start `a`, one delay or one sync delay before the start of slot `s + 1`
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  obtain ⟨a, hadef⟩ : ∃ a : ℕ, a = M.slotStart S.C (s + 1) - max (Δ S) Δs := ⟨_, rfl⟩
  rw [← hadef] at hpwin hwwin hHoldP hHoldW
  have ha : a + max (Δ S) Δs = M.slotStart S.C (s + 1) := by omega
  have haf : a ≤ M.viewFreeze S.C s := by omega
  have hGSTa : GST ≤ a := by omega
  have hssR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = (M.viewFreeze S.C s : ℝ) + Δ S := by
    rw [← hfzΔ]; push_cast; ring
  have hvtR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = (M.viewFreeze S.C s : ℝ) + 2 * Δ S := by
    rw [hv₃, ← hfzΔ]; push_cast; ring
  have hafR : (a : ℝ) ≤ M.viewFreeze S.C s := by exact_mod_cast haf
  -- the real times of the two ticks
  have hkPt := (E'.tick_active kP p _ hkP).2.1
  have hkPt2 := (E'.tick_active kP p _ hkP).2.2
  have hkWt := (E'.tick_active kW w _ hkW).2.1
  rw [hssR] at hkPt hkPt2
  rw [hvtR] at hkWt
  have hpkP : p ∉ A.corrupted kP := E'.not_mem_corrupted_of_tick hkP
  have hwkW : w ∉ A.corrupted kW := E'.not_mem_corrupted_of_tick hkW
  have hkPW : kP < kW := (lt_of_time_lt M) x R (by linarith)
  -- `w` ticks to the view freeze of slot `s` and to the start of slot `s + 1`, and `p` to the view
  -- freeze, inside their windows
  have hvf1 : 1 ≤ M.viewFreeze S.C s := by omega
  obtain ⟨kU, hkU, -, hkU2⟩ := E'.tick_of_active (M.viewFreeze S.C s) hvf1 w (fun i h1 h2 =>
    hwwin i (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
  have hss1 : 1 ≤ M.slotStart S.C (s + 1) := by omega
  obtain ⟨kS, hkS, -, -⟩ := E'.tick_of_active (M.slotStart S.C (s + 1)) hss1 w (fun i h1 h2 =>
    hwwin i (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
  obtain ⟨k₂, hk₂, -, -⟩ := E'.tick_of_active (M.viewFreeze S.C s) hvf1 p (fun i h1 h2 =>
    hpwin i (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
  have hkUW : kU < kW := (lt_of_time_lt M) x R (by linarith)
  have hwkU : w ∉ A.corrupted kU := E'.not_mem_corrupted_of_tick hkU
  have hpwin' : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kP → p ∈ A.active i :=
    fun i h1 h2 => hpwin i (by linarith) h2
  have hwwin' : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kW → w ∈ A.active i :=
    fun i h1 h2 => hwwin i (by linarith) h2
  have hsbP : x.stepBefore a ≤ kP := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, (stepBefore_zero M) x R]
      exact Nat.zero_le _
    · exact ((stepBefore_lt_of_le_time M) x R E' h0 (by linarith)).le
  have hsbW : x.stepBefore a ≤ kW := le_trans hsbP hkPW.le
  -- step 1: `p`'s run and proposal (Lemma 19 over the record, from the tick's input state, which
  -- satisfies the node invariant: Lemma 11 at `p`'s tick)
  obtain ⟨i₁, hl₁, hm₁⟩ := hPropose
  have hi₁ : i₁ = kP := E'.tick_unique _ _ p _ hl₁ hkP
  rw [hi₁] at hl₁ hm₁
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E') hl₁ hm₁
  try rw [hPin] at hrun₁
  have hInv : M.nodeInv S.C S.P S.X (x.st kP p) :=
    (lem11_node_invariant M F S A x R E' kP p hpkP).1
  obtain ⟨-, -, -, -, Hp, votes_pl, support_pl, hvl, hsl, -, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hInv hB₁
  rw [hslot₁, Nat.add_sub_cancel] at hvl
  rw [hslot₁] at hBdef
  have hBvotes : B.votes = votes_pl := by rw [hBdef]; rfl
  have hBsupp : B.support_votes = support_pl := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  have hRp : RootsNameBlocksIn (M.fg_to_ac (x.st kP p)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E' kP p
  have hRw : RootsNameBlocksIn (M.fg_to_ac (x.st kW w)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E' kW w
  -- `B`'s votes are `p`'s pool of slot `s`, its support votes those that resolve at `p`
  have hpoolB : ∀ vote : GoldfishVote V,
      vote ∈ M.votesHeldSet (x.st kP p) s ↔ vote ∈ B.votes := by
    intro vote
    rw [hBvotes, hvl]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _
  have hsupB : ∀ vote : GoldfishVote V, vote ∈ B.support_votes ↔
      vote ∈ M.votesHeldSet (x.st kP p) s ∧
        ∃ y : Stamp, ResolvesAt M (x.st kP p) vote y := by
    intro vote
    rw [hBsupp, hsl vote, ← hBvotes, ← hpoolB vote]
  have hsupP' : ∀ vote : GoldfishVote V, vote ∈ support_p ↔ vote ∈ B.support_votes :=
    fun vote => (hSupP vote).trans (hsupB vote).symm
  have hslotp : ∀ vote ∈ M.votesHeldSet (x.st kP p) s, vote.slot = s :=
    fun vote hv => (pool_slot_of_exec M F) S A x R E' kP p s vote hv
  -- the votes and support votes `w` counts as included are `p`'s
  have hIncl : ∀ vote : GoldfishVote V, vote ∈ M.included_votes
      (M.fg_to_ac (x.st kW w)) (s + 1) ↔ vote ∈ M.votesHeldSet (x.st kP p) s := by
    intro vote
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F),
      Nat.add_sub_cancel]
    constructor
    · rintro ⟨B', ⟨hB', hBs⟩, hvB, -⟩
      rw [hOnly B' (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB').1 hBs] at hvB
      exact (hpoolB vote).2 hvB
    · intro hv
      exact ⟨B, ⟨hBw, hBslot⟩, (hpoolB vote).1 hv, hslotp vote hv⟩
  have hInclS : ∀ vote : GoldfishVote V, vote ∈ M.included_support_votes
      (M.fg_to_ac (x.st kW w)) (s + 1) ↔ vote ∈ support_p := by
    intro vote
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_support_votes_iff M F),
      Nat.add_sub_cancel]
    rw [hsupP' vote]
    constructor
    · rintro ⟨B', ⟨hB', hBs⟩, hvB, -⟩
      rw [hOnly B' (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB').1 hBs] at hvB
      exact hvB
    · intro hv
      exact ⟨B, ⟨hBw, hBslot⟩, hv, hslotp vote ((hsupB vote).1 hv).1⟩
  -- `p`'s counted votes are among `w`'s
  have hPW : ∀ vote ∈ votes_p, vote ∈ votes_w := by
    intro vote hv
    rw [hVp] at hv
    exact (hCv vote).2 (Or.inr ((hIncl vote).2 hv))
  -- step 2: a vote `w` counts is `p`'s, or its validator equivocates at `p`: a vote stamped at `w`
  -- before the view freeze of slot `s` entered `w`'s pool before its tick to the view freeze, and
  -- reaches `p` by its tick to `t₁` (`pool_vote_reaches_at_tick_steps`)
  have hkP' : x.lbl kP = Event.tick p (M.viewFreeze S.C s + Δ S) := by rw [hfzΔ]; exact hkP
  have hHoldW' : w ∈ A.activeThroughout x (((M.viewFreeze S.C s + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((M.viewFreeze S.C s + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    rw [hfzΔ, ← hadef]; exact hHoldW
  have hW2 : ∀ vote ∈ votes_w, vote ∈ votes_p ∨ vote.val_index ∈ equivocators votes_p := by
    intro vote hv
    rw [hVp]
    rcases (hCv vote).1 hv with ⟨hpw, τ, hτ, hτlt⟩ | hinc
    · rw [hfzc] at hτlt
      obtain ⟨e, hei, hne, he1, hst⟩ := (voteStamp_entry_clock M F R E') hpw
      rw [hτ, (clock_eq_clockValue M F) x R (e + 1) w] at hst
      have hτe : τ = (((x.clockValue (e + 1) w : ℕ) : Int) : Stamp) := Option.some.inj hst
      rw [hτe] at hτlt
      have hcvlt : x.clockValue (e + 1) w < M.viewFreeze S.C s := by
        have h := WithBot.coe_lt_coe.1 hτlt
        exact_mod_cast h
      have hek : e < kU := by
        by_contra hc
        have hwe : w ∉ A.corrupted (e + 1) := fun h => hwkW (E'.corrupted_mono _ _ (by omega) h)
        have hcv := E'.clockValue_mono (show kU + 1 ≤ e + 1 by omega) hwe
        rw [x.clockValue_succ_of_tick hkU] at hcv
        omega
      rcases (pool_vote_reaches_at_tick_steps M F U) S A x R GST s (M.viewFreeze S.C s)
          (M.voteTime S.C (s + 1)) w p vote E' hNet hSkew hRedeliver Sy' (by omega)
          (by rw [show s + 2 = s + 1 + 1 from rfl]; omega) (by omega) hvf1 hHoldW' kU hkU e hek hne he1
          ((a : ℝ) - ΔClockAhead) (by rw [hfzΔ, ← hadef]; linarith) (by linarith) kP hkP' hpwin
        with h | ⟨v₁, h₁, v₂, h₂, hne', hi₁', hi₂'⟩
      · exact Or.inl h
      · exact Or.inr ((GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff_two _ _).2 ⟨v₁, h₁, v₂, h₂, hne', hi₁', hi₂'⟩)
    · exact Or.inl ((hIncl vote).1 hinc)
  -- step 3: the equivocators and the participants agree
  have hEq : equivocators votes_p = equivocators votes_w := by
    ext u
    rw [GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff_two, GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff_two]
    constructor
    · rintro ⟨v₁, h₁, v₂, h₂, hne, hi₁', hi₂'⟩
      exact ⟨v₁, hPW v₁ h₁, v₂, hPW v₂ h₂, hne, hi₁', hi₂'⟩
    · rintro ⟨v₁, h₁, v₂, h₂, hne, hi₁', hi₂'⟩
      rcases hW2 v₁ h₁ with h₁' | he
      · rcases hW2 v₂ h₂ with h₂' | he
        · exact ⟨v₁, h₁', v₂, h₂', hne, hi₁', hi₂'⟩
        · rw [hi₂'] at he
          exact (GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff_two _ _).1 he
      · rw [hi₁'] at he
        exact (GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff_two _ _).1 he
  have hPart : participants votes_p = participants votes_w := by
    ext u
    rw [GoldilocksCorrectness.Proofs.Routines.mem_participants_iff, GoldilocksCorrectness.Proofs.Routines.mem_participants_iff]
    constructor
    · rintro ⟨vote, hv, hi⟩
      exact ⟨vote, hPW vote hv, hi⟩
    · rintro ⟨vote, hv, hi⟩
      rcases hW2 vote hv with h | he
      · exact ⟨vote, h, hi⟩
      · rw [hi] at he
        exact (GoldilocksCorrectness.Proofs.Routines.mem_participants_iff _ _).1 (GoldilocksCorrectness.Proofs.Routines.equivocators_subset_participants _ he)
  have hNonEq : ∀ vote ∈ votes_w, vote.val_index ∉ equivocators votes_w → vote ∈ votes_p := by
    intro vote hv hne
    refine (hW2 vote hv).resolve_right ?_
    rw [hEq]
    exact hne
  have hSW : ∀ vote ∈ support_w, vote ∈ votes_w := by
    intro vote hv
    rcases (hCs vote).1 hv with ⟨hpw, hτ, -⟩ | ⟨hinc, -⟩
    · exact (hCv vote).2 (Or.inl ⟨hpw, hτ⟩)
    · refine hPW vote ?_
      rw [hVp]
      exact ((hSupP vote).1 ((hInclS vote).1 hinc)).1
  -- step 4: the head blocks propagate, `p` to `w` by `w`'s tick to `t₃` and `w` to `p` by `p`'s tick
  -- to `t₁`, when the other's finalized block is an ancestor of them (the relay at ticks,
  -- `block_at_tick_of_held_tick`)
  have hToW : ∀ H ∈ (M.fg_to_ac (x.st kP p)).tree, (x.st kW w).finalized.AncestorEq H →
      H ∈ (M.fg_to_ac (x.st kW w)).tree := by
    intro H hH hFH
    have hHT : H ∈ (x.st kP p).tree :=
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).1
    refine ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨?_, hFH⟩
    by_cases hg : H = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E' kW w
    have hFa : (x.st (x.stepBefore a) p).finalized.compatible H = true :=
      (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E' p hsbP)
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).2))
    have hHs : M.slotStart S.C H.slot ≤ M.slotStart S.C (s + 1) :=
      (slotStart_le_of_mem_tickInput M F U) x R E' hkP (by omega)
        (fun j h1 h2 => hpwin j (by linarith) h2) hHT hg
    exact (block_at_tick_of_held_tick M F U) S A x R GST (M.voteTime S.C (s + 1))
      (M.slotStart S.C (s + 1)) kP a (M.voteTime S.C (s + 1)) (M.slotStart S.C (s + 1)) kW kS p w H
      E' hNet hSkew hRedeliver Sy' hRoots hParent hGSTa (by omega) (by omega) le_rfl hHoldP hkP hHT hFa
      hg hkW hwwin' hkS (by omega) hHs ((compatible_iff _ _).2 (Or.inl hFH))
  have hToP : ∀ H ∈ (M.fg_to_ac (x.st kW w)).tree, H ∈ (x.st kU w).tree →
      (x.st kP p).finalized.AncestorEq H → H ∈ (M.fg_to_ac (x.st kP p)).tree := by
    intro H hH hHU hFH
    refine ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨?_, hFH⟩
    by_cases hg : H = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E' kP p
    have hFa : (x.st (x.stepBefore a) w).finalized.compatible H = true :=
      (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E' w hsbW)
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).2))
    have hHs : M.slotStart S.C H.slot ≤ M.viewFreeze S.C s :=
      (slotStart_le_of_mem_tickInput M F U) x R E' hkU (by omega)
        (fun j h1 h2 => hwwin j (by linarith) (le_trans h2 hkUW.le)) hHU hg
    exact (block_at_tick_of_held_tick M F U) S A x R GST (M.voteTime S.C (s + 1))
      (M.viewFreeze S.C s) kU a (M.slotStart S.C (s + 1)) (M.viewFreeze S.C s) kP k₂ w p H
      E' hNet hSkew hRedeliver Sy'
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (htime hkPW.le) hRoots)
      hParent hGSTa (by omega) (by omega) (by omega) hHoldW hkU hHU hFa hg hkP hpwin' hk₂ (by omega) hHs
      ((compatible_iff _ _).2 (Or.inl hFH))
  -- step 4: a support vote of `p` whose head block `H` in `p`'s frame tree has `w`'s finalized
  -- block as an ancestor is one of `w`'s, with `H` in `w`'s frame tree
  have hSupPW : ∀ vote ∈ support_p,
      ∀ H ∈ (M.fg_to_ac (x.st kP p)).tree, H.root = vote.head →
        (x.st kW w).finalized.AncestorEq H →
        vote ∈ support_w ∧ H ∈ (M.fg_to_ac (x.st kW w)).tree := by
    intro vote hv H hH hr hFH
    obtain ⟨hvp, y, hy⟩ := (hSupP vote).1 hv
    obtain ⟨-, -, Hp', -, hHp', hr', hs', -, -⟩ := hy
    have hHH : Hp' = H := hRp Hp' hHp' H hH (hr'.trans hr.symm)
    rw [hHH] at hs'
    have hHw := hToW H hH hFH
    exact ⟨(hCs vote).2 (Or.inr ⟨(hInclS vote).2 hv, resolved_eq_ok_true hRw hHw hr hs'⟩), hHw⟩
  -- step 4: a support vote of `w` of a validator that does not equivocate, whose head block `H` in
  -- `w`'s frame tree has `p`'s finalized block as an ancestor, is one of `p`'s, with `H` in `p`'s
  -- frame tree
  have hSupWP : ∀ vote ∈ support_w, vote.val_index ∉ equivocators votes_w →
      ∀ H ∈ (M.fg_to_ac (x.st kW w)).tree, H.root = vote.head →
        (x.st kP p).finalized.AncestorEq H →
        vote ∈ support_p ∧ H ∈ (M.fg_to_ac (x.st kP p)).tree := by
    intro vote hv hne H hH hr hFH
    rcases (hCs vote).1 hv with ⟨hpw, -, y, hy, hylt⟩ | ⟨hinc, -⟩
    · -- the pool clause: the vote and its head block reached `p` by its tick to `t₁`
      obtain ⟨τv, τH, Hw, -, hHw, hrw, hsw, hτH, hyeq⟩ := hy
      have hHH : H = Hw := hRw H hH Hw hHw (hr.trans hrw.symm)
      have hτHy : τH ≤ y := by
        rw [hyeq]
        exact le_max_right _ _
      rw [hfzc] at hylt
      have hHwT : Hw ∈ (x.st kW w).tree :=
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHw).1
      have hHU : Hw ∈ (x.st kU w).tree :=
        (mem_T_tick_of_blockStamp_lt M F) x R E' hkU hwkW hHwT hτH (lt_of_le_of_lt hτHy hylt)
      have hHp : Hw ∈ (M.fg_to_ac (x.st kP p)).tree :=
        hToP Hw hHw hHU (by rw [← hHH]; exact hFH)
      have hvp : vote ∈ M.votesHeldSet (x.st kP p) s := by
        rw [← hVp]
        exact hNonEq vote (hSW vote hv) hne
      -- the vote and its head block are stamped in `p`'s state (the node invariant): the vote
      -- resolves there (`ResolvesAt`)
      obtain ⟨τv', hτv'⟩ := Option.ne_none_iff_exists'.1
        (F.nd.nodeInv_poolStamped hInv s vote (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hvp))
      obtain ⟨τH', hτH'⟩ := Option.ne_none_iff_exists'.1
        (F.nd.nodeInv_treeStamped hInv Hw (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHp).1)
      refine ⟨(hSupP vote).2 ⟨hvp, _, ⟨τv', τH', Hw, hτv', hHp, hrw, hsw, hτH', rfl⟩⟩, ?_⟩
      rw [hHH]
      exact hHp
    · -- the included clause: the vote is one of `p`'s support votes
      have hvs : vote ∈ support_p := (hInclS vote).1 hinc
      obtain ⟨-, y, hy⟩ := (hSupP vote).1 hvs
      obtain ⟨-, -, Hp', -, hHp', hr', -, -, -⟩ := hy
      refine ⟨hvs, ?_⟩
      have hHH : H = Hp' := hRoots H Hp'
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := kW) (v := w) hwkW le_rfl ((((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).1))
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := kP) (v := p) hpkP (htime hkPW.le) ((((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHp').1))
        (hr.trans hr'.symm)
      rw [hHH]
      exact hHp'
  -- step 5: the supporters agree of every block that has both finalized blocks as ancestors: a
  -- supporter's head block `H` is a descendant of that block, so of both finalized blocks
  have hSupEq : ∀ D : Block V, (x.st kP p).finalized.AncestorEq D →
      (x.st kW w).finalized.AncestorEq D →
      GoldilocksCorrectness.Proofs.Routines.supportersOf (M.fg_to_ac (x.st kP p)) votes_p support_p s D =
        GoldilocksCorrectness.Proofs.Routines.supportersOf (M.fg_to_ac (x.st kW w)) votes_w support_w s D := by
    intro D hFpD hFwD
    ext u
    rw [GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff, GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff]
    constructor
    · rintro ⟨vote, hv, hi, hne, hs', H, hH, hr, hD⟩
      obtain ⟨hvw, hT⟩ := hSupPW vote hv H hH hr (ancestorEq_trans hFwD hD)
      refine ⟨vote, hvw, hi, ?_, hs', H, hT, hr, hD⟩
      rw [← hEq]
      exact hne
    · rintro ⟨vote, hv, hi, hne, hs', H, hH, hr, hD⟩
      obtain ⟨hvp, hT⟩ := hSupWP vote hv (by rw [hi]; exact hne) H hH hr
        (ancestorEq_trans hFpD hD)
      refine ⟨vote, hvp, hi, ?_, hs', H, hT, hr, hD⟩
      rw [hEq]
      exact hne
  -- step 5: the scores and the voter counts
  refine ⟨fun D hFpD hFwD => ⟨_, goldfish_score_eq_ok hRp votes_p support_p s D, ?_⟩, ?_⟩
  · rw [goldfish_score_eq_ok hRw votes_w support_w s D, hEq, hSupEq D hFpD hFwD]
  · rw [(GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F), GoldilocksCorrectness.Proofs.Routines.voters_count_eq, GoldilocksCorrectness.Proofs.Routines.voters_count_eq, hPart]

end GoldilocksCorrectness.Record.Proofs.Executions

