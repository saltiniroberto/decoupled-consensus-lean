module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.NextSlotVoteStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Statements.Executions.HonestChainDefs
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma79, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma79.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the kit theorem
`live_locks_compatible_of_honestChainExtends_tick` and Lemma 79, the step of the slot invariant
restricted to a block. The page's routine-level theorems are the facts' fields or have their twins
in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_eq voteTime_cast voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor LocksRevoked VoterTreeAt)

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
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- The live locks of a member are compatible with `B`, read at the member's tick. When
`HonestChainExtends M S Sched x Hon B s'` holds, `w` is a member of `Hon` that ticks to the vote time of slot
`s' + 1` and is active at every step up to that tick, from the trace's start or from its own tick to a clock value
at most the duty window's start of slot `s' + 2`, and the clock value `c` is greater than the support
cutoff of slot `s' + 1` and at most the vote time of slot `s' + 2`, then every lock entry of the
state `w`'s tick to `c` starts from whose deadline is greater than `c` is on a block compatible with
`B`. The proof; the audited statement is in `Statements/Executions/HonestChainStatements.lean`. It reads the
tick's input, the state the tick's revocation and vote are computed from.

Why: the entry is traced (Lemma 39) to `w`'s tick to the support cutoff of a slot `s₁ + 1`, before its tick to `c`,
so `s₁ ≤ s'` (`clock_mono`). When `s₁ = s'`, the update of slot `s' + 1` saved a confirmation that clause 3 of the
invariant puts on `B`'s chain. When `s₁ < s'`, the entry is live at the vote time of slot `s' + 1` (Lemma 41); `w`'s
tick to that vote time is the one `hHon` names, after the tick to the support cutoff of slot `s₁ + 1` and before
the tick to `c` (`clock_mono`, `tick_unique`), with `w` awake in between (the reader's window, its opening tick at
or before the tick to the support cutoff by `clock_mono`), so that tick starts from a state awake for slot `s' + 1`,
and its revocation kept an entry on the entry's chain, which clause 2 of the invariant makes compatible with `B`. No
clock bound: the reader names the ticks the proof reads.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the validators the invariant is read at; `B`: the block; `s'`: the slot of the
  invariant; `c`: the clock value of the tick; `w`: the member.

Read aloud: between the update of slot `s' + 1` and the revocation of slot `s' + 2`, every lock that
has not expired in the state a member's tick starts from is on a block compatible with `B`. -/
theorem live_locks_compatible_of_honestChainExtends_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (Hon : Finset V) (B : Block V) (s' c : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hInv : HonestChainExtends M S A x Hon B s')
    (hw : w ∈ Hon)
    (hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)))
    (hc1 : M.supportCutoff S.C (s' + 1) < c)
    (hc2 : c ≤ M.voteTime S.C (s' + 2)) :
    ∀ e ∈ (x.tickInput w c).lockEntries, ((c : ℕ) : Int) < e.d →
      e.B.compatible B = true := by
  intro e he hlive
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hv' : ∀ s : ℕ, M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc' : ∀ s : ℕ, M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hss : ∀ s : ℕ, M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  -- where `e` comes from (Lemma 39): `w`'s tick `k₁` to the support cutoff of a slot `s₁ + 1`, before `w`'s tick to `c`
  obtain ⟨s₁, hd₁, hk₁lt, hlk₁, ⟨τ₀, hτ₀, hτ₀le⟩, h39⟩ :=
    (lockTracedAfterTick_of_mem M F U) S A x R E w (x.tickStep w c) e he
  set k₁ := x.tickStep w (M.supportCutoff S.C (s₁ + 1)) with hk₁def
  -- `w` ticks to `c`, at the step `j`
  obtain ⟨j₀, hj₀⟩ := x.exists_tick_of_lt_tickStep hk₁lt
  have hjs : x.tickStep w c = j₀ := (tickStep_eq_of_lbl M) x E hj₀
  rw [hjs] at hk₁lt
  have hwj : w ∉ A.corrupted j₀ := E.not_mem_corrupted_of_tick hj₀
  -- the outcome of `w`'s tick `k₁` (the step's own), awake for slot `s₁ + 1`
  have hti₁ : x.tickInput w (M.supportCutoff S.C (s₁ + 1)) = x.st k₁ w := rfl
  obtain ⟨n₁, sent₁, hrun₁, hst₁, -⟩ := R.tick k₁ w _ hlk₁
  rw [← hti₁] at hrun₁
  obtain ⟨e₀, -, -, -, -, ⟨C', hC', hBC⟩, -, heB₀, htr⟩ := h39 n₁ sent₁ hrun₁ ⟨τ₀, hτ₀, hτ₀le⟩
  have heC : e.B.AncestorEq C' := ancestorEq_trans heB₀ hBC
  -- the slot of `e` is at most `s'`: `w`'s clock does not go back between its two ticks
  have hcc : M.supportCutoff S.C (s₁ + 1) ≤ c := E.clock_mono k₁ j₀ w _ _ hk₁lt hwj (Or.inl hlk₁) (Or.inl hj₀)
  have hs₁ : s₁ ≤ s' := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s' + 2 ≤ s₁ + 1 by omega)
    have h1 := hv' (s' + 2)
    have h2 := hc' (s₁ + 1)
    have h3 := hv' (s₁ + 1)
    omega
  rcases Nat.lt_or_eq_of_le hs₁ with hlt | heq
  · -- `s₁ < s'`: the revocation at `w`'s tick to the vote time of slot `s' + 1` kept an entry for `e`
    have hk : s' + 1 ≤ s₁ + S.C.k := by
      by_cases hkle : S.C.k ≤ s' + 1
      · have h41 := (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S
          (s' + 1 - S.C.k) s₁ c e hd₁ hlive (by
            rw [show s' + 1 - S.C.k + S.C.k = s' + 1 by omega]
            have := hc' (s' + 1)
            omega)
        omega
      · omega
    -- the duty window's start of slot `s' + 2` is at least one delay before the support cutoff of slot `s₁ + 1`
    have hdw : M.dutyWindowStart S.C (s' + 2) + Δ S ≤ M.supportCutoff S.C (s₁ + 1) := by
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show s' + 2 ≤ s₁ + 1 + S.C.k by omega)
      have e1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₁ + 1 + S.C.k)
      have e2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₁ + 1)
      rw [Nat.mul_add] at e1
      have hcases := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (s' + 2)
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 2)] at hm
      have h2 := hc' (s₁ + 1)
      have h3 := hv' (s₁ + 1)
      omega
    have hc₃ : M.supportCutoff S.C (s₁ + 1) ≤ M.voteTime S.C (s' + 1) := by
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₁ + 1 ≤ s' by omega)
      have h1 := hc' (s₁ + 1)
      have h2 := hv' (s₁ + 1)
      have h3 := hv' (s' + 1)
      have h4 := hss s'
      omega
    have hc1' := hc' (s' + 1)
    -- `w`'s tick `k₃` to the vote time of slot `s' + 1`: the tick the reader `hHon` ends at
    obtain ⟨k₃, hl₃, hcase⟩ := Activity.mem_activeThroughoutToTick.1 hHon
    have hw₃ : w ∉ A.corrupted k₃ := E.not_mem_corrupted_of_tick hl₃
    -- the order of the three ticks: `k₁ ≤ k₃ < j₀`
    have hk₁₃ : k₁ ≤ k₃ := by
      by_contra h
      have h' : M.voteTime S.C (s' + 1) ≤ M.supportCutoff S.C (s₁ + 1) :=
        E.clock_mono k₃ k₁ w _ _ (by omega) (E.not_mem_corrupted_of_tick hlk₁) (Or.inl hl₃) (Or.inl hlk₁)
      have heqv : M.voteTime S.C (s' + 1) = M.supportCutoff S.C (s₁ + 1) := le_antisymm h' hc₃
      rw [heqv] at hl₃
      have := E.tick_unique _ _ w _ hl₃ hlk₁
      omega
    have hk₃j : k₃ < j₀ := by
      by_contra h
      rcases Nat.lt_or_eq_of_le (not_lt.1 h) with h' | h'
      · have := E.clock_mono j₀ k₃ w _ _ h' hw₃ (Or.inl hj₀) (Or.inl hl₃)
        omega
      · subst h'
        rw [hj₀] at hl₃
        injection hl₃ with _ h''
        omega
    -- `w` is awake after every step from `k₁` to `k₃`, so its tick to the vote time of slot `s' + 1` starts from a
    -- state awake since `τ₀`, at most the duty window's start of slot `s' + 1`
    have hAwSince : (x.tickInput w (M.voteTime S.C (s' + 1))).awakeSince = some τ₀ := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl₃]
      refine (awakeSince_kept_of_awake_steps M F) x R E hk₁₃ (fun i h1 h2 => ?_) hτ₀
      refine (Activity.mem_active.1 ?_).1
      rcases hcase with hall | ⟨k, -, c₀, hc₀a, hk, hbetween⟩
      · exact hall i (le_of_lt h2)
      · refine hbetween i ?_ (le_of_lt h2)
        -- `k`, `w`'s tick to `c₀ ≤ dutyWindowStart (s' + 2)`, comes at or before `k₁`: `w`'s clock does not go back
        have hc₀ : c₀ ≤ M.dutyWindowStart S.C (s' + 2) := by exact_mod_cast hc₀a
        by_contra hki
        have hk₁k : k₁ < k := by omega
        have := E.clock_mono k₁ k w _ _ hk₁k (E.not_mem_corrupted_of_tick hk) (Or.inl hlk₁) (Or.inl hk)
        omega
    have hAwake : AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) :=
      ⟨τ₀, hAwSince, le_trans hτ₀le (duty_window_start_mono S (show s₁ + 1 ≤ s' + 1 by omega))⟩
    -- the tick's outcome, the revocation of slot `s' + 1`
    have hti₃ : x.tickInput w (M.voteTime S.C (s' + 1)) = x.st k₃ w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl₃]
    obtain ⟨n₃, sent₃, hrun₃, hst₃, -⟩ := R.tick k₃ w _ hl₃
    rw [← hti₃] at hrun₃
    have hslot₃ : M.slot S.C (M.voteTime S.C (s' + 1)) = s' + 1 := by
      have := hv' (s' + 1)
      have := hss (s' + 1)
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
    have hsl : S.C.slot ((M.voteTime S.C (s' + 1) : ℕ) : Int) = s' + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact hslot₃
    have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1))) := by
      rw [hti₃]
      exact (lem11_node_invariant M F S A x R E k₃ w hw₃).1
    have hRevoke := F.tk2.tick_voteTime_locks S.C S.P S.X _ _ n₃ sent₃ hrun₃ hInvW
      (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s' + 1))
      (by rw [hsl]; exact hAwake)
    rw [hsl] at hRevoke
    -- the entry for `e` right after that tick, an entry of the tick's outcome, live then
    obtain ⟨e', he', hd', heB', -⟩ := htr (k₃ + 1) (by omega) (by omega)
    have he'A : e' ∈ n₃.lockEntries := by
      rw [← hst₃]
      exact he'
    have hlive' : M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) e' = true := by
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
      refine ⟨?_, GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s') hRevoke e'
        he'A⟩
      rw [hd']
      exact lt_trans (Int.ofNat_lt.2 (show M.voteTime S.C (s' + 1) < c by omega)) hlive
    exact compatible_of_ancestorEq_compatible heB'
      (hInv.2.1 w hw n₃ sent₃ hrun₃ hAwake e' he'A hlive')
  · -- `s₁ = s'`: the update of slot `s' + 1` saved `C'`, which clause 3 puts on `B`'s chain
    subst heq
    have hsv : (x.tickOutput w (M.supportCutoff S.C (s₁ + 1))).savedConfirmation s₁ = some C' := by
      unfold Trace.tickOutput
      rw [← hk₁def, hst₁]
      exact hC'
    have hBC' := hInv.2.2 w hw C' hsv
    exact compatible_of_ancestorEq_both heC hBC' ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))

open Classical in
/-- Lemma 79a, the first clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s'`: Lemma 26b,
which the proof calls at slot `s'`, takes them up to the voter's own tick to that cutoff, which can come after
its real time.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: under the invariant at slot `s'`, the members' votes of slot `s' + 1` are for blocks
they hold on `B`'s chain. -/
theorem lem79a_honestChainExtends_votes_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s'`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hInv : HonestChainExtends M S A x Hon B s')
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    -- no member is in the adversary set at a step where a validator outside it ticks to the vote time of slot
    -- `s' + 1` (the second honesty read,; Lemma 26b reads the voters' honesty at the member's tick)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.voteTime S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) votes
        support_votes →
      M.voters_count votes < 2 * Hs.card)
    (hF2 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
          (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W) :
    ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
  intro w hw vote hSend
  -- the times
  have hΔ := one_le_Δ S
  have hdw : M.dutyWindowStart S.C (s' + 1) ≤ M.slotStart S.C s' := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s'
  have hv₁ : M.voteTime S.C s' = M.slotStart S.C s' + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hc₁ : M.supportCutoff S.C s' = M.voteTime S.C s' + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
  have hv₂ : M.voteTime S.C (s' + 1) = M.voteTime S.C s' + 4 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S s'
  -- each voter of slot `s'` voted for a block it holds on `B`'s chain (clause 1)
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree ∧ B.AncestorEq H_u := by
    intro u hu
    obtain ⟨huHon, -, vote', -, -, hsent⟩ := hHs u hu
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hInv.1 u huHon vote' hsent
    subst hvt
    exact ⟨H_u, hsent, hHT, hBH⟩
  choose H hH using hvote
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  -- Lemma 12's receiver window for `w` and holder window for each voter, from the members' window
  have hwin := fun u (hu : u ∈ Hon) => (dutyWindow_gives_core_window_and_hold M F U) x R E hΔs hSkew
    hGST (hHon u hu)
  obtain ⟨kR, hkR, -⟩ := (hwin w hw).1
  have hkRs : x.tickStep w (M.supportCutoff S.C s') = kR := (tickStep_eq_of_lbl M) x E hkR
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held M F U)
    S A x R GST s' Hs H' B w vote E hNet hSkew hRedeliver Sy hΔs (by rw [hkRs]; exact hRoots kR w _ hkR le_rfl)
    hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1,
        (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hSend.choose_spec.1
          (hHonTick u (hHs u hu).1),
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersW w hw) (fun u hu => (hwin u (hHs u hu).1).2) (hwin w hw).1 (hF2 w hw) (hF3 w hw)
    (hInv.2.1 w hw) hSend

/-- Lemma 79b, the second clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

The landed conclusion reads every answer of the landed revocation of slot `s' + 2`; the twin
reads every node state that revocation may leave from `w`'s node state before the vote time of
slot `s' + 2` (`LocksRevoked`, the shape of Lemma 42's twin), so that its recovery is exact.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: under the invariant at slot `s'`, the live locks every revocation of slot `s' + 2` may
leave from a member's node state before that slot's vote time are compatible with `B`. -/
theorem lem79b_honestChainExtends_locks_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' : ℕ) (Hon : Finset V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hInv : HonestChainExtends M S A x Hon B s')
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1))) :
    ∀ w ∈ Hon, ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s' + 2)))
        ((M.voteTime S.C (s' + 2) : ℕ) : Int) (s' + 2) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s' + 2)))
          ((M.voteTime S.C (s' + 2) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro w hw n' hRevoke e' he' _
  have hΔ := one_le_Δ S
  have hv₂ : M.voteTime S.C (s' + 2) = M.voteTime S.C (s' + 1) + 4 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s' + 1)
  have hc₁ : M.supportCutoff S.C (s' + 1) = M.voteTime S.C (s' + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
  have hlt₂ : M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s' + 2) := by omega
  obtain ⟨e, heS, hlive_e, -, hB, -⟩ :=
    GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
      (Nat.le_add_left 1 (s' + 1)) hRevoke e' he'
  have hlt : ((M.voteTime S.C (s' + 2) : ℕ) : Int) < e.d :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hlive_e |>.1
  exact compatible_of_ancestorEq_compatible hB
    ((live_locks_compatible_of_honestChainExtends_tick M F U) S A x R Hon B s' (M.voteTime S.C (s' + 2)) w E
      hInv hw (hHon w hw) hlt₂ le_rfl e heS hlt)

open Classical in
/-- **Lemma 79c at one updater.** For one updater `v` of slot `s' + 1` and a set `Hs` of voters of slot `s' + 1`:
when every member of `Hs` is a member of the committee of slot `s' + 1` outside the adversary set at `v`'s tick to
the support cutoff of slot `s' + 2`, sent at its tick to the vote time of slot `s' + 1` a vote for a block it held
that is `B` or a descendant of `B`, and is an updater of slot `s' + 1`; when the voters of slot `s' + 1` of the pool
`v`'s tick to the support cutoff of slot `s' + 2` starts from are fewer than twice `Hs`; and when `v`'s finalized
block there is compatible with `B`: every confirmation of slot `s' + 1` that `v`'s tick saves is `B` or a
descendant of `B`.

Why: Lemma 78 at `v`, with the voters' blocks; the voters' holder windows from their updater windows
(`holder_window_of_updater_reader`); the roots at `v`'s own tick (`roots_at_own_tick_of_per_tick`). Nothing is read of
`v` beyond its own update, so the fact holds at an updater outside the set Lemma 79c's invariant is read at.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment facts;
  `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant; `Hs`: the honest voters of
  slot `s' + 1`; `B`: the block; `v`: the updater.

Read aloud: an updater whose pool's voters are fewer than twice a set of honest voters on `B`'s chain, and whose
finalized block is compatible with `B`, saves a confirmation of slot `s' + 1` on `B`'s chain. -/
theorem lem79c_confirmation_at_updater (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hs : Finset V) (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s' + 1))
    -- `v` runs the update of slot `s' + 1`
    (hv : v ∈ updaterAt M S A x (s' + 1))
    -- every voter of `Hs` is a committee member of slot `s' + 1`, outside the adversary set at `v`'s tick to the
    -- support cutoff of slot `s' + 2`, and voted at its tick to the vote time of slot `s' + 1` for a block it held on
    -- `B`'s chain
    (hHsv : ∀ u ∈ Hs, u ∈ S.P.committee (s' + 1) ∧
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s' + 2))) ∧
      ∃ H_u : Block V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s' + 1) H_u.root)⟩ :
            SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
        H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree ∧ B.AncestorEq H_u)
    -- every voter of `Hs` runs the update of slot `s' + 1`
    (hHsU : ∀ u ∈ Hs, u ∈ updaterAt M S A x (s' + 1))
    -- the slot-`(s' + 1)` voters of the pool `v`'s tick to the support cutoff of slot `s' + 2` starts from are fewer
    -- than twice `Hs`
    (hVotersV : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
      2 * Hs.card)
    -- `v`'s finalized block before that cutoff is compatible with `B`
    (hFv : (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 2))).savedConfirmation (s' + 1) = some C' →
      B.AncestorEq C' := by
  choose H hH using fun u (hu : u ∈ Hs) => (hHsv u hu).2.2
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  -- `v`'s tick to the support cutoff of slot `s' + 1`, inside its reader, for the roots
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hv
  exact (lem78_update_confirmation_extends_voter_majority_chain M F U) S A x R GST (s' + 1) Hs H' B v
    E hNet hSkew hRedeliver Sy hΔs ((roots_at_own_tick_of_per_tick M F) x E hRoots hkR) hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHsv u hu).1, (hHsv u hu).2.1, (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hHsU u hu))
    hVotersV hv hFv

open Classical in
/-- Lemma 79c, the third clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 78,
which the proof calls at slot `s' + 1`, reads them at each member's own tick to that cutoff.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the members' votes of slot `s' + 1` are on `B`'s chain, their confirmations of slot
`s' + 1` are too. -/
theorem lem79c_honestChainExtends_confirmations_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s' + 1))
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u)
    -- each member runs the update of slot `s' + 1`: it ticks to the support cutoff of slot `s' + 2`, active up to that
    -- tick from a tick at or before the duty window's start of slot `s' + 2`
    (hHon : ∀ v ∈ Hon, v ∈ updaterAt M S A x (s' + 1))
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s' + 2` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersV : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * Hs.card)
    (hFv : ∀ v ∈ Hon,
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    ∀ v ∈ Hon, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 2))).savedConfirmation (s' + 1) = some C' →
      B.AncestorEq C' := by
  intro v hv
  -- Lemma 79c at the member `v`: its voters are honest at `v`'s tick (`hHonTick`)
  refine (lem79c_confirmation_at_updater M F U) S A x R GST s' Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent
    hOwner hGST (hHon v hv) (fun u hu => ?_) (fun u hu => hHon u (hHs u hu).1) (hVotersV v hv) (hFv v hv)
  obtain ⟨huHon, huC, vote', -, -, hsent⟩ := hHs u hu
  obtain ⟨H_u, hHT, hvt, hBH⟩ := hVotes u huHon vote' hsent
  subst hvt
  exact ⟨huC, (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E (hHon v hv) (hHonTick u huHon),
    H_u, hsent, hHT, hBH⟩

open Classical in
/-- Lemma 79, the step of the restricted slot invariant. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 79c,
which the proof calls, reads them there; Lemma 79a reads them up to the support cutoff of slot `s'`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the invariant at slot `s'` gives the invariant at slot `s' + 1`, when the members stay
awake and honest through the next slot, the honest voters of each slot are a majority of the voters
the members count, and the members' finalized blocks and fork-choice roots are compatible with `B`.
-/
theorem lem79_honestChainExtends_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hInv : HonestChainExtends M S A x Hon B s')
    -- the members of `Hon` are active at every real time from the duty window's start of slot `s' + 1` to its vote
    -- time (Lemma 79a's read), and each runs the update of slot `s' + 1`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x (s' + 1))
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s' + 2` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    (hHs : ∀ s₀ : ℕ, s₀ = s' ∨ s₀ = s' + 1 → ∀ u ∈ Hs s₀, u ∈ Hon ∧ u ∈ S.P.committee s₀ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) votes
        support_votes →
      M.voters_count votes < 2 * (Hs s').card)
    (hVotersV : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    (hF2 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
          (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W)
    (hFv : ∀ v ∈ Hon,
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    HonestChainExtends M S A x Hon B (s' + 1) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  obtain ⟨hv0, hc0, -, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨hv2, hc2, -, hs2, -, -, -⟩ := (slot_times M F U) S (s' + 2)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hdw2 := duty_window_start_real S (s' + 2)
  push_cast at hdw2
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hv2R : ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 9 * Δ S := by
    rw [hv2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 2) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, show s' + 2 = s' + 1 + 1 by omega, hs1, hs0, hss]; push_cast; ring
  have hcc : M.supportCutoff S.C s' ≤ M.supportCutoff S.C (s' + 1) := by omega
  -- clause 1 (Lemma 79a), with the roots per tick up to the support cutoff of slot `s'`
  have h1 := (lem79a_honestChainExtends_votes_step M F U) S A x R GST s' Hon (Hs s') B E hNet hSkew hRedeliver Sy hΔs
    (fun k u c hk hc => hRoots k u c hk (le_trans hc hcc)) hParent hOwner hGST hInv hHon
    (fun u hu => (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E (hHonUpd u hu)
      (by
        have hv1c2 : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) + 5 * Δ S = ((M.supportCutoff S.C (s' + 2) : ℕ) : ℝ) := by
          rw [hv1R, hc2R]; ring
        linarith))
    (hHs s' (Or.inl rfl)) hVotersW hF2 hF3
  -- every member ticks to the vote time of slot `s' + 1`, active up to that tick from its tick to a
  -- clock value at most the duty window's start of slot `s' + 2`: its reader of slot `s' + 1`
  have hwin : ∀ w ∈ Hon, w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)) :=
    fun w hw => (reader_from_updater_under_skew M F U) S A x R s' w E hSkew (hHonUpd w hw)
  refine ⟨h1, ?_, ?_⟩
  · -- clause 2 (Lemma 79b), on the revocation the outcome of a member's tick to the vote time of slot `s' + 2` ran
    -- from its tick input (the field `tick_voteTime_locks_of_core` of `F.tk2`)
    intro w hw n' sent hrun hAwake e he hlive
    have hsl : S.C.slot ((M.voteTime S.C (s' + 1 + 1) : ℕ) : Int) = s' + 1 + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
        (by rw [show s' + 1 + 1 = s' + 2 by omega]; omega) (by rw [show s' + 1 + 1 = s' + 2 by omega]; omega)
    have hInvW := (lem11_node_invariantCore_of_run M F S x R (x.tickStep w (M.voteTime S.C (s' + 1 + 1))) w).1
    have hRevoke := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n' sent hrun hInvW
      (by
        rw [hsl]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s' + 1 + 1))
      (by rw [hsl]; exact hAwake)
    rw [hsl] at hRevoke
    exact (lem79b_honestChainExtends_locks_step M F U) S A x R s' Hon B E hInv hwin w hw n' hRevoke e he hlive
  · -- clause 3 (Lemma 79c)
    exact (lem79c_honestChainExtends_confirmations_step M F U) S A x R GST s' Hon (Hs (s' + 1)) B E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hOwner
      (le_trans hGST hcc) h1 hHonUpd hHonTick (hHs (s' + 1) (Or.inr rfl)) hVotersV hFv

end GoldilocksCorrectness.Record.Proofs.Executions

