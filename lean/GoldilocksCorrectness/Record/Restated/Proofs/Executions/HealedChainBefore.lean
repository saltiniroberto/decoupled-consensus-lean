module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedChainBefore, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedChainBefore.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the monotonicity facts in the time,
Lemma 81 bounded, the caches from one time unit after the hand-over and the updater condition
`UpdaterFinalizedOnChainAt` after the hand-over. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slotStart_mono slot_le_of_supportCutoff_lt
  supportCutoff_eq supportCutoff_lt_of_lt voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry ProgressCertOn)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The monotonicity facts in the time -/

omit [RootOrder] in
/-- Fewer than a third of the validators in the adversary set up to `t` implies the same up to
`t' ≤ t`. The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `Sched`: the schedule; `t'`, `t`: the two times.

Read aloud: if fewer than a third of the validators have been in the adversary set up to `t`, then
fewer than a third have been up to any earlier time. -/
theorem adversaryFewerThanThirdUntil_mono (A : Activity V) (x : Trace V (NamedObject V) M.N) {t' t : ℕ} (hle : t' ≤ t)
    (h : A.AdversaryFewerThanThirdUntil x (validator_count V) t) : A.AdversaryFewerThanThirdUntil x (validator_count V) t' :=
  fun A hA => h A (fun v hv => by
    obtain ⟨t'', h1, h2⟩ := hA v hv
    exact ⟨t'', le_trans h1 (by exact_mod_cast hle), h2⟩)

/-- Inclusion for the slots starting at or after `tE` implies it for the slots starting at or after
`tE' ≥ tE`. The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times.

Read aloud: if inclusion holds for every slot starting at or after `tE`, it holds for every slot
starting at or after any later time. -/
theorem confirmedIncluded_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) {tE tE' : ℕ} (hle : tE ≤ tE')
    (h : ConfirmedIncludedAfterHealing M S A x tE) :
    ConfirmedIncludedAfterHealing M S A x tE' :=
  fun s hs => h s (le_trans hle hs)

/-! ## Lemma 81 bounded -/

/-- **Roots named at every tick to a value at most `c₀` give roots named up to a real time `T`, when some
validator ticks to `c₀` and `T` is at least `ΔClockAhead` before `c₀`.**

Why: that tick is one of the ticks to a value at most `c₀`, and its real time is at least `c₀ − ΔClockAhead`
(`tick_active`), so at least `T`; roots named up to a time are named up to every earlier time
(`RootsNameBlocksUntil.mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `c₀`: the clock value; `k`: the step of `u`'s tick to
  `c₀`; `u`: the validator; `T`: the real time.

Read aloud: roots named at every tick to a value at most `c₀` are named up to any time at least
`ΔClockAhead` before `c₀`, once some validator ticks to `c₀`. -/
theorem roots_until_of_per_tick_of_tick {A : Activity V} (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {c₀ k : ℕ} {u : V} {T : ℝ}
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ c₀ →
      RootsNameBlocksUntil M A x (x.time k))
    (hk : x.lbl k = Event.tick u c₀) (hT : T + ΔClockAhead ≤ c₀) :
    RootsNameBlocksUntil M A x T :=
  (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
    (by have := (E.tick_active k u c₀ hk).2.1; linarith) (hRoots k u c₀ hk le_rfl)

/-- **Roots named at every tick to a value at most `c₀` give roots named up to the later of two validators'
ticks to a value `c ≤ c₀`, when each is counted active up to its tick to `c`.**

Why: each validator ticks to `c` (`Activity.mem_activeThroughoutToTick`), and roots are named up to its own
tick (`roots_at_own_tick_of_per_tick`); the later of the two times is one of them.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `c₀`, `c`: the clock values; `a₁`, `a₂`: the readers'
  starts; `v₁`, `v₂`: the validators.

Read aloud: roots are named up to the later of two active validators' ticks to `c`, when they are named at
every tick to a value at most `c₀ ≥ c`. -/
theorem roots_until_max_ticks_of_per_tick {A : Activity V} (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {c₀ c : ℕ} {a₁ a₂ : ℤ} {v₁ v₂ : V}
    (hRoots : ∀ (k : ℕ) (u : V) (c' : ℕ), x.lbl k = Event.tick u c' → c' ≤ c₀ →
      RootsNameBlocksUntil M A x (x.time k))
    (hc : c ≤ c₀) (h₁ : v₁ ∈ A.activeThroughoutToTick x a₁ c) (h₂ : v₂ ∈ A.activeThroughoutToTick x a₂ c) :
    RootsNameBlocksUntil M A x (max (x.time (x.tickStep v₁ c)) (x.time (x.tickStep v₂ c))) := by
  have hR : ∀ (k : ℕ) (u : V) (c' : ℕ), x.lbl k = Event.tick u c' → c' ≤ c →
      RootsNameBlocksUntil M A x (x.time k) := fun k u c' hk hc' => hRoots k u c' hk (le_trans hc' hc)
  obtain ⟨k₁, hk₁, -⟩ := Activity.mem_activeThroughoutToTick.1 h₁
  obtain ⟨k₂, hk₂, -⟩ := Activity.mem_activeThroughoutToTick.1 h₂
  rcases le_total (x.time (x.tickStep v₁ c)) (x.time (x.tickStep v₂ c)) with h | h
  · rw [max_eq_right h]
    exact (roots_at_own_tick_of_per_tick M F) x E hR hk₂
  · rw [max_eq_left h]
    exact (roots_at_own_tick_of_per_tick M F) x E hR hk₁

/-- **Lemma 81 bounded.** The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`. It is the proof of
`lem81_confirmations_chain` (`Proofs/Executions/Lemma81.lean`) with the induction on the slot
stopped before `n` (`lem81_inv_before`) and the final ordering read for the slots less than `n`:
the step to slot `s + 1 < n` reads the voter frame at `s + 1` and the updater frames at `s` and
`s + 1`; the ordering of two confirmations of slots `s < s'' < n` reads the invariant at `s''` and
the updater frame at `s''`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `n`: the bound on the slots; `B₀`: the block every updater of slot `s₀`
  saved.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C n`: the
induction (`lem81_inv_before`) takes blocks as held up to the support cutoff of slot `n - 1`, which an
honest committee member's tick to the support cutoff of slot `n` reaches (at a real time at least that
cutoff minus `ΔClockAhead`), and the ordering of two confirmations of one slot `s < n` reads Lemma 32
at `s`, up to the two updaters' ticks to the support cutoff of slot `s + 1`.

Read aloud: the frames at the slots before `n` already make the honest confirmations of the slots
before `n` one chain. -/
theorem lem81_chain_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C n →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C n)) (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    -- the frames at the slots after `s₀` and before `n`
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt M S A x s,
      VoterFrameOnChainAt M S A x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt M S A x s,
      UpdaterFinalizedOnChainAt M S A x s₀ s v) :
    ConfirmationsChainBefore M S A x s₀ n := by
  -- the support cutoff grows with the slot, by at least one delay per slot
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S h)
    · rw [h]
  have hcΔ : ∀ s : ℕ, M.supportCutoff S.C s + Δ S ≤ M.supportCutoff S.C (s + 1) := fun s => by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S s
    omega
  -- the times and the counting
  have hGSTs : ∀ s : ℕ, s₀ ≤ s → GST + max (Δ S) Δs ≤ M.supportCutoff S.C s := fun s hs =>
    le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hs)
  have hCom : ∀ s : ℕ, s₀ ≤ s → s < n →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| :=
    fun s hs hsn => (committee_majority_of_sleepiness M F) S A x anchor s hSleepK
      (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))) (hcm _ _ (by omega))
  -- the chain before `n`
  intro s s' v v' C C' hs hss' hs'n hv hv' hC hC'
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · -- roots up to the support cutoff of slot `n - 1`: an honest committee member of slot `n - 1` ticks to the
    -- support cutoff of slot `n`, at a real time at least that cutoff minus `ΔClockAhead`
    obtain ⟨u₀, hu₀⟩ : (S.P.committee (n - 1) ∩ honestActiveAt M S A x (n - 1)).Nonempty := by
      have := hCom (n - 1) (by omega) (by omega)
      exact Finset.card_pos.1 (by omega)
    have hn1 : n - 1 + 1 = n := by omega
    obtain ⟨k₀, hk₀, -⟩ := Activity.mem_activeThroughoutToTick.1
      ((honestActiveAt_subset_updaterAt M F) S A x R E (n - 1) (Finset.mem_inter.1 hu₀).2)
    rw [hn1] at hk₀
    have hRootsN1 : RootsNameBlocksUntil M A x (M.supportCutoff S.C (n - 1)) :=
      (roots_until_of_per_tick_of_tick M F) x E hRoots hk₀ (by
        have h1 := E.ahead_nonneg
        have h2 := E.behind_nonneg
        have h3 := hcΔ (n - 1)
        rw [hn1] at h3
        have h4 : ((M.supportCutoff S.C (n - 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C n : ℕ) : ℝ) := by
          exact_mod_cast h3
        linarith)
    -- the slot invariant and the lock invariant at every slot after the healed one and before `n`
    have hAll := (lem81_inv_before M F U) S A x R GST s₀ anchor n B₀ E hNet hSkew hRedeliver Sy hΔs
      hRootsN1 (fun k u c hk hc => hRoots k u c hk (le_trans hc (hcm _ _ (Nat.sub_le n 1)))) hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved hVoterFrame hUpdaterFrame
    obtain ⟨hInv', -⟩ := hAll s' (by omega) hs'n
    exact (chainInvFor_updater_confirmation M F U) S A x R GST s' (honestActiveAt M S A x s')
      (OnHonestChainBefore M S A x s₀ s') v' E hNet hSkew hRedeliver Sy hΔs
      (fun k u c hk hc => hRoots k u c hk (le_trans hc (hcm _ _ (by omega)))) hParent hOwner (hGSTs s' (by omega)) (subset_refl _)
      (hCom s' (by omega) (by omega)) hInv' hv'
      (fun D hD => hUpdaterFrame s' (by omega) hs'n v' hv' D hD) C
      ⟨s, hlt, hs, v, hv, C, hC, ancestorEq_refl C⟩ C' hC'
  · subst heq
    exact (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S
      A x R GST s v v' C C' E hNet hSkew hRedeliver Sy hΔs
      ((roots_until_max_ticks_of_per_tick M F) x E hRoots (hcm _ _ (show s + 1 ≤ n by omega)) hv hv')
      (by
        have := hGSTs s hs
        have := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
        have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
        have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
        omega)
      hv hv' hC hC'

/-! ## The caches from a step after the hand-over -/

/-- **The caches after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`. A step
at a time greater than `x[i₁].time` is after `i₁` (`lt_of_time_lt`), and Lemma 84 applies with
`t₀ := M.supportCutoff S.C (s₀ + 1)`, its agreement premise from Lemma 82.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i₁`: the step at the hand-over; `t`: the bound on the times of the steps.

Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each such step the proof reads Lemma 84 up to `t`.

Read aloud: at every step after the hand-over up to `t`, every honest validator's caches are on the
honest chain. -/
theorem caches_after_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hStart : ∀ u : V, u ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ u)) :
    ∀ (j : ℕ) (u : V), x.time i₁ < x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u) := by
  intro j u hlt hjt hu
  have hij : i₁ ≤ j := ((lt_of_time_lt M) x R hlt).le
  -- `u`, honest after `j`, is honest after every step whose time is at most that of `i₁`
  have hu₁ : u ∉ A.corruptedAtTime x (x.time i₁) := Activity.not_mem_corruptedAtTime.2 fun k hk =>
    E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R (lt_of_le_of_lt hk hlt)).le hu
  exact (lem84_caches_stay_on_chain_of_honest M F U Fx) S A x R s₀
    (M.supportCutoff S.C (s₀ + 1)) H i₁ t E hRoots hAdvQ
    ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E
      ) hOld hStart j u hu₁ hij hjt hu

/-- **The caches from any step after a hand-over step.** `caches_after_handover` read from a step
`i₂` at a time greater than that of `i₁`: at every step at a time at least that of `i₂` and at most
`t`, every honest validator's caches are on the honest chain.

 it now reads any step after `i₁`, and the clock value equal to
`i₁`'s time is no longer asked.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `E`: the environment
  facts; `s₀`: the healed slot; `H`: the threshold; `i₁`: the step at the hand-over; `t`: the bound
  on the times of the steps; `i₂`: a step after `i₁`.

Read aloud: from any step after the hand-over step, every honest validator's caches are on the
honest chain, at every step at a time at most `t`. -/
theorem caches_after_handover_of_clock (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      (hRoots : RootsNameBlocksUntil M A x t)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hStart : ∀ u : V, u ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ u))
    (i₂ : ℕ) (hi₂ : x.time i₁ < x.time i₂) :
    ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u) := fun j u hj hjt hu =>
  (caches_after_handover M F U Fx) S A x R s₀ H i₁ t E hRoots hAdvQ hOld hStart j u
    (lt_of_lt_of_le hi₂ hj) hjt hu

/-- **Kit fact, the caches on the state at a step from the caches on the state after it.** From the caches on the state
after every step `j` at a real time from `x[i₂].time` to `t`, the caches on the state at every step `j` at a real time after `x[i₂].time` and at most `t`. A proof-page helper.

The variables:
- `M`: the model; `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `s₀`: the healed slot; `H`:
  the threshold; `i₂`: the step from which the caches are on the chain; `t`: the bound on the real times.

Why: a step `j` at a real time after `x[i₂].time` comes after `i₂` (`lt_of_time_lt`), so `j = j' + 1` with `i₂ ≤ j'`; the
step `j'` is at a real time from `x[i₂].time` to `x.time j` (`time_mono`), and a validator outside the adversary set at `j`
is outside it at `j'`.

Read aloud: the caches on the state after each step from the hand-over time give the caches on the state at each step
strictly after it. -/
theorem cachesOnChain_st_of_succ (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₂ : ℕ) (t : ℝ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u)) :
    ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u) := by
  intro j u hj hjt hu
  have hlt : i₂ < j := (lt_of_time_lt M) x R hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact hCaches j' u ((time_mono M) x R (by omega))
    (le_trans ((time_mono M) x R (Nat.le_succ j')) hjt) (E.not_mem_corrupted_of_le (Nat.le_succ j') hu)

/-! ## The updater frame after the hand-over -/

/-- **Kit fact, the certificate route, with the attester's own saved confirmation.** As
`cert_entry_at_slot` (`Lemma91.lean`), with the confirmation of slot `sₐ` that the attester `uₐ`
itself saved at its tick to `M.supportCutoff S.C (sₐ + 1)` named: the entry `E` is that
confirmation or an ancestor of it. `cert_entry_at_slot`'s conclusion `OnHonestChainAt` names some
updater of slot `sₐ`; `updaterFrame_after_handover_until` needs the attester's own.

Why: `cert_entry_at_slot`'s proof, whose witness for `OnHonestChainAt` is the attester itself.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `H`: the bound on
  the old attestations' heights; `j`: the step; `w`: the holder; `Y`: the held block; `T`: the block
  the certificate names; `h`: its height.

Read aloud: a certificate above the threshold on a held chain names, by root, an entry that an
honest attester held when it ran the update of a slot `sₐ` at a tick before `j`, and that entry is
the attester's own saved confirmation of `sₐ` or an ancestor of it. -/
theorem cert_entry_at_slot_saved (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time j) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H < h) :
    ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < j ∧
      x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
      uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time j) ∧
      E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
      s₀ ≤ s_a ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root ∧
      ∃ C : Block V, (x.tickOutput uₐ (M.supportCutoff S.C (s_a + 1))).savedConfirmation s_a = some C ∧
        E.AncestorEq C := by
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) (M.supportCutoff S.C (s₀ + 1))) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) (M.supportCutoff S.C (s₀ + 1)) ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u :=
    fun i' hi' => hhonM i' (le_trans ((time_mono M) x R hi') (le_max_left _ _))
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations :=
    (lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
      ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
      (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  obtain ⟨sₐ, source, C, ht, hv, -, hsT, hSaved, hsrcC, hh, hT⟩ :=
    (attest_tick_update_source M F U) S A x R j' t' u a' E hl hsent
  have hge : M.supportCutoff S.C (s₀ + 1) ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast (Nat.lt_of_not_le hlt))
      (Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_right _ _))) hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  subst ht
  have hs₀ : s₀ ≤ sₐ := by
    by_contra hlt
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout
      F.sched) S (show sₐ + 1 < s₀ + 1 by omega)
    omega
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  have hET : (M.chainStateOf S.C source).T_h ∈ (x.st j' u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j' u
      source _ hsT hE3
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hTI : (M.chainStateOf S.C source).T_h ∈
      (x.tickInput u (M.supportCutoff S.C (sₐ + 1))).tree := by
    unfold Trace.tickInput
    rw [hts]
    exact hET
  exact ⟨sₐ, u, (M.chainStateOf S.C source).T_h, by rw [hts]; exact hj', by rw [hts]; exact hl, hv,
    Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_left _ _)), hTI,
    hs₀, hE1, hE2.trans (hh.trans hh'), hT'.symm.trans hT, C, hSaved, ancestorEq_trans hE3 hsrcC⟩

/-- **The updater frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`. At `v`'s tick step `k'` to the support
cutoff of slot `s + 1`, `v` is honest and the step is at a time after `x[i₂].time` (`hs`); the
certificate of `v`'s justified block names an entry held by an honest attester `uₐ` at its tick to
the support cutoff of a slot `sₐ`, before `k'` (`cert_entry_at_slot_saved`), which roots make the
justified block itself; the finalized block is an ancestor of the justified block (the caches), so
an ancestor of `uₐ`'s saved confirmation of `sₐ`. For `sₐ < s` it is on the honest chain before `s`,
compatible with every block `B` of it (`onHonestChainBefore_compatible`); for `sₐ = s`, `uₐ` is an
updater of slot `s` that ticked before `v`, whose confirmation has `B` as an ancestor (`hEarlier`);
`sₐ > s` is impossible, since a tick to a later support cutoff is at a real time after `v`'s tick
(`hSkew`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.

Roots name blocks, fewer than a quorum have been in the adversary set, and the caches hold, up to the
real time of `v`'s tick to the support cutoff of slot `s + 1`: the proof reads Lemma 91 (f)'s route
at that tick's step. The confirmations of slot `s` saved by the updaters that ticked to that cutoff
before `v` extend the chain before `s`: a certificate `v` holds at its tick may carry such an
updater's attestation of slot `s`, whose entry is an ancestor of that confirmation.

Read aloud: after the hand-over, an updater's finalized block never conflicts with the honest chain
before its slot. -/
theorem updaterFrame_after_handover_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₂ H s : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `v`'s tick to `M.supportCutoff S.C (s + 1)` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- every tick to the support cutoff of slot `s + 1` is at a real time after `x[i₂].time`
    (hs : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → x.time i₂ < x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    -- the slot-`s` confirmations of the updaters that ticked to that cutoff before `v` extend the chain before `s`
    (hEarlier : ∀ u ∈ updaterAt M S A x s,
      x.tickStep u (M.supportCutoff S.C (s + 1)) < x.tickStep v (M.supportCutoff S.C (s + 1)) →
      ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → ∀ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' → C.AncestorEq C')
    (hv : v ∈ updaterAt M S A x s) :
    UpdaterFinalizedOnChainAt M S A x s₀ s v := by
  intro B hB
  -- `v`'s tick to the support cutoff of slot `s + 1`
  have hv' := hv
  unfold updaterAt at hv'
  obtain ⟨k', hk', -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
  have hts : x.tickStep v (M.supportCutoff S.C (s + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  rw [hts] at hRoots hAdvQ hCaches hEarlier
  have hvk : v ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
  have hj : x.time i₂ < x.time k' := hs k' v hk'
  -- the certificate of `v`'s justified block names an entry an honest attester held at its tick
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k' v
  obtain ⟨hH, -, -, -, hFJ⟩ := hCaches k' v hj le_rfl hvk
  have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, uₐ, Eb, hk, hl, hua, -, hEb, hs₀a, -, -, hEr, C_a, hSa, hEbC⟩ :=
    (cert_entry_at_slot_saved M F U Fx) S A x R s₀ H k' v D _ _ E
      (hAdvQ.mono le_rfl) hOld hD ((progressCertOn_of_justificationCertOn M F) hJC) hH
  -- the entry and `J` have one root, and honest validators hold both
  have hJmem : (x.st k' v).justified ∈ (x.st k' v).tree :=
    (F.nd.nodeInv_justifiedInTree (lem11_node_invariant M F S A x R E k' v hvk).1)
  have hEJ : Eb = (x.st k' v).justified :=
    hRoots Eb _ ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
      ((time_mono M) x R hk.le) hEb)
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k') (v := v) hvk le_rfl hJmem) hEr.symm
  -- the finalized block is an ancestor of the attester's saved confirmation
  have hFC : (x.st k' v).finalized.AncestorEq C_a := by
    rw [← hEJ] at hFJ; exact ancestorEq_trans hFJ hEbC
  show (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true
  unfold Trace.tickInput
  rw [hts]
  rcases Nat.lt_trichotomy s_a s with hlt | heq | hgt
  · -- the entry's slot is before `s`: the finalized block is on the chain before `s`
    have hFb : OnHonestChainBefore M S A x s₀ s (x.st k' v).finalized :=
      ⟨s_a, hlt, hs₀a, uₐ, hua, C_a, hSa, hFC⟩
    exact (onHonestChainBefore_compatible M F) S A x s₀ s _ B hChain hFb hB
  · -- the entry's slot is `s`: the attester ticked before `v`, and its confirmation extends the chain
    subst heq
    have hBC := hEarlier uₐ hua hk B hB C_a hSa
    exact compatible_of_ancestorEq_both hFC hBC ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))
  · -- a tick to a later support cutoff is at a real time after `v`'s tick
    exfalso
    have h₁ := (E.tick_active _ _ _ hl).2.1
    have h₂ := (E.tick_active _ _ _ hk').2.2
    have h₃ := (time_mono M) x R hk.le
    have hA := E.ahead_nonneg
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s + 1 + 1 ≤ s_a + 1 by omega)
    have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (s + 1)
    have hcR : ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) = (M.supportCutoff S.C (s + 1) : ℕ) + 4 * Δ S := by
      rw [hc]; push_cast; ring
    have hmR : ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s_a + 1) : ℕ) := by
      exact_mod_cast hmono
    have hΔ : (1 : ℝ) ≤ Δ S := by exact_mod_cast GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
    linarith

/-- **The updater frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`. As `updaterFrame_after_handover_until`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.

Roots name blocks and fewer than a quorum have been in the adversary set up to the real time of
`v`'s tick to the support cutoff of slot `s + 1`; the slot-`s` confirmations of the updaters that
ticked to that cutoff before `v` extend the chain before `s`.

It is `updaterFrame_after_handover_until` with the caches restricted to the steps it reads.

Read aloud: after the hand-over, an updater's finalized block never conflicts with the honest chain
before its slot. -/
theorem updaterFrame_after_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₂ H s : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `v`'s tick to `M.supportCutoff S.C (s + 1)` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    -- every tick to the support cutoff of slot `s + 1` is at a real time after `x[i₂].time`
    (hs : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → x.time i₂ < x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    -- the slot-`s` confirmations of the updaters that ticked to that cutoff before `v` extend the chain before `s`
    (hEarlier : ∀ u ∈ updaterAt M S A x s,
      x.tickStep u (M.supportCutoff S.C (s + 1)) < x.tickStep v (M.supportCutoff S.C (s + 1)) →
      ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → ∀ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' → C.AncestorEq C')
    (hv : v ∈ updaterAt M S A x s) :
    UpdaterFinalizedOnChainAt M S A x s₀ s v :=
  (updaterFrame_after_handover_until M F U Fx) S A x R s₀ i₂ H s v E hSkew hRoots hAdvQ hOld (fun j u
    h₁ _ h₂ => hCaches j u h₁ h₂) hs hChain hEarlier hv

/--

Why: by strong induction on the step of the updater's tick. For `v`, every updater that ticked
before it ticked at a real time at most `t`, so it has the frame (the induction hypothesis), and
`hExt` makes its confirmation extend the chain before `s`: that is `hEarlier` of
`updaterFrame_after_handover_until`, which gives `v`'s frame.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `t`: the bound on the
  real times of the ticks.

Read aloud: after the hand-over, the finalized block of every updater of slot `s` that ran the
update by `t` never conflicts with the honest chain before `s`. -/
theorem updater_frames_at_slot (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₂ H s : ℕ) (t : ℝ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- every tick to the support cutoff of slot `s + 1` is at a real time after `x[i₂].time`
    (hs : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → x.time i₂ < x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    -- an updater of slot `s` whose frame holds saves a confirmation of slot `s` extending the chain before `s`
    (hExt : ∀ u ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s u →
      ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → ∀ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' → C.AncestorEq C') :
    ∀ v ∈ updaterAt M S A x s, x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t →
      UpdaterFinalizedOnChainAt M S A x s₀ s v := by
  suffices h : ∀ n : ℕ, ∀ v ∈ updaterAt M S A x s, x.tickStep v (M.supportCutoff S.C (s + 1)) = n →
      x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v from
    fun v hv ht => h _ v hv rfl ht
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hn ht
    refine (updaterFrame_after_handover_until M F U Fx) S A x R s₀ i₂ H s v E hSkew
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ht hRoots)
      (hAdvQ.mono (max_le_max ht le_rfl)) hOld
      (fun j u h₁ h₂ hu => hCaches j u h₁ (le_trans h₂ ht) hu) hs hChain ?_ hv
    intro u hu hlt C hC C' hC'
    exact hExt u hu (ih _ (hn ▸ hlt) u hu rfl (le_trans ((time_mono M) x R hlt.le) ht)) C hC C' hC'

section VotesStep
open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff viewFreeze dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_slot
  supportCutoff_succ_le viewFreeze_cast viewFreeze_eq voteTime_cast voteTime_eq voteTime_succ)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both compatible_symm')
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  CountedVotesAt EarlySupporterOf LocksRevoked TreeClosed VoterTree VoterTreeAt)

/-- **Kit fact, the votes clause of the chain step from the voters' frames.** The first clause of `HonestChainExtends` at slot
`s' + 1`, for every block of the family `𝓒` and every ancestor of a confirmation of slot `s'` that a validator of `Upd` saved, read
from the first two conjuncts of `StepFrameAt` at those blocks (`w`'s root at its tick to the vote time of slot `s' + 1` compatible
with the block, and a viable head of its voter tree extending the block when the root is the block or an ancestor of it), with the
other inputs of `lem89s_chain_step`. `lem89s_chain_step`'s first clause, whose proof reads `hStep` only through those two conjuncts;
the third conjunct (the finalized block at `w`'s tick to the support cutoff of slot `s' + 2`) is the updater's frame at slot
`s' + 1`, which `frames_after_healed_slot_until` derives from this clause.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `GST`: the time from which the network is synchronous;
  `s'`: the slot of the step; `Hon`, `Hon'`: the honest active validators of slots `s'` and `s' + 1` read; `Upd`: the updaters of slot
  `s'` read; `𝓒`: the family.

Why: `lem89s_chain_step`'s proof of its first clause, word for word: for a block of the family, Lemma 26b over the voters of slot `s'`;
for an ancestor of a new confirmation, Lemma 36b at that confirmation.

Read aloud: every Goldfish vote an honest active validator of slot `s' + 1` sends at its tick to the vote time extends every block
of the family and every ancestor of a confirmation of slot `s'`, provided its frame at that tick follows those blocks. -/
theorem votes_clause_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks also up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    -- ('s shape: Lemmas 78 and 32 read them up to the updaters' own ticks to that cutoff)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hHon : Hon ⊆ honestActiveAt M S A x s')
    (hHon' : Hon' ⊆ honestActiveAt M S A x (s' + 1))
    (hUpd : Upd ⊆ updaterAt M S A x s')
    (hHonUpd : Hon' ⊆ Upd)
    (hCommittee : |S.P.committee s'| < 2 * |S.P.committee s' ∩ Hon|)
    (hCommittee' : |S.P.committee (s' + 1)| < 2 * |S.P.committee (s' + 1) ∩ Hon'|)
    (hInv : ChainInvFor M S A x Hon 𝓒 s')
    (hNew : ∀ u ∈ Hon', u ∈ Hon ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = false)
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt M S A x 𝓒 s' u)
    (hConfExt : ∀ C : Block V, 𝓒 C → ∀ v ∈ Upd, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C.AncestorEq C')
    (hVF : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Upd, ∃ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧ C.AncestorEq C') →
      ∀ w ∈ Hon', (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible C = true ∧
        ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq C →
          ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
            (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
            W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧ C.AncestorEq W)) :
    ∀ B : Block V, (𝓒 B ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧ B.AncestorEq C') →
      ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
        ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
          vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
  intro B hB
  -- the times, as reals
  have hA0 := E.ahead_nonneg
  have hB0' := E.behind_nonneg
  obtain ⟨hv0, hc0, hf0, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨hv2, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s' + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hc0R : ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + 2 * Δ S := by
    rw [hc0, hss]; push_cast; ring
  have hf0R : ((M.viewFreeze S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + 3 * Δ S := by
    rw [hf0, hss]; push_cast; ring
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have hv2R : ((M.voteTime S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 9 * Δ S := by
    rw [hv2, hs1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, hs1, hs0, hss]; push_cast; ring
  have hdw1 := duty_window_start_real S (s' + 1)
  push_cast at hdw1
  have hdw2 := duty_window_start_real S (s' + 1 + 1)
  push_cast at hdw2
  have hdle2 := (duty_window_start_le_real M F U) S (s' + 1 + 1)
  have hdN2 : M.dutyWindowStart S.C (s' + 1 + 1) ≤ M.slotStart S.C (s' + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S (s' + 1)
  have hdN2R : ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) ≤ 4 * Δ S * s' + 4 * Δ S := by
    have : ((M.dutyWindowStart S.C (s' + 1 + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C (s' + 1) : ℕ) : ℝ) := by
      exact_mod_cast hdN2
    rw [hs0, hss] at this; push_cast at this; linarith
  have hmΔ : (Δ S : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_left _ _
  have hmΔs : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_right _ _
  -- `hGST` bounds the sync delay by the support cutoff of slot `s'`
  have hΔsle : Δs ≤ M.supportCutoff S.C s' := by have := le_max_right (Δ S) Δs; omega
  have hΔsleR : (Δs : ℝ) ≤ 4 * Δ S * s' + 2 * Δ S := by
    rw [← hc0R]; exact_mod_cast hΔsle
  have hmax1 : max (Δ S) Δs ≤ M.supportCutoff S.C (s' + 1) := by
    have := le_max_right (Δ S) Δs; have := le_max_left (Δ S) Δs
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hmaxR : ((max (Δ S) Δs : ℕ) : ℝ) = (max (Δ S) Δs : ℝ) := by push_cast; rfl
  -- the windows
  have hHonW : ∀ u ∈ Hon, u ∈ A.activeThroughoutToTick x (duty_window_start S.C s')
      (M.supportCutoff S.C (s' + 1)) := fun u hu => (honestActiveAt_window M F) S A s' u E (hHon hu)
  have hHon'W : ∀ u ∈ Hon', u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1))
      (M.supportCutoff S.C (s' + 1 + 1)) := fun u hu => (honestActiveAt_window M F) S A (s' + 1) u E (hHon' hu)
  have hHonU : ∀ u ∈ Hon, u ∈ updaterAt M S A x s' := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (duty_window_start_mono S (Nat.le_succ s')) (hHonW u hu)
  have hHon'U : ∀ u ∈ Hon', u ∈ updaterAt M S A x (s' + 1) := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (duty_window_start_mono S (Nat.le_succ (s' + 1))) (hHon'W u hu)
  have hRootsN : ∀ {k : ℕ} {u : V} {c : ℕ}, x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time (x.tickStep u c)) := fun {k u c} hk hc => by
    rw [(tickStep_eq_of_lbl M) x E hk]; exact hRootsTick k u c hk hc
  -- the live locks of a member after its revocation of slot `s' + 1`
  have hLk : ∀ u ∈ Hon', ∀ (n₃ : M.N) (sent₃ : List (NamedObject V)),
      .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput u (M.voteTime S.C (s' + 1))) (s' + 1) →
      ∀ e ∈ M.lockEntries n₃,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true →
        (∀ C : Block V, 𝓒 C → e.B.compatible C = true) ∧ ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D := by
    intro u hu n₃ sent₃ hR hA e he hl
    rcases hNew u hu with hu0 | hfree
    · exact ⟨fun C hC => (hInv C hC).2.1 u hu0 n₃ sent₃ hR hA e he hl,
        hLocks u hu0 n₃ sent₃ hR hA e he hl⟩
    · exact ((revoke_locks_empty_of_lockFree M F) S A x _ (s' + 1) _ n₃ (Nat.le_add_left 1 s')
        hfree ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s' + 1) u n₃ sent₃ hR hA) e
        he).elim
  -- the first clause at slot `s' + 1`
  have hClause1 : ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
    intro u hu vote hSend
    obtain ⟨iS, hiS, -⟩ := id hSend
    have hF := hVF B hB u hu
    rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
    · -- a block of the family: Lemma 26b over the voters of slot `s'`
      obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R s' (S.P.committee s' ∩ Hon) B E hSkew
        (fun u' hu' => ⟨hHon (Finset.mem_inter.1 hu').2, (Finset.mem_inter.1 hu').1⟩)
        (fun u' hu' => (hInv B hBold).1 u' (Finset.mem_inter.1 hu').2)
      obtain ⟨kR, hkR, hkRw⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew
        (hUpd (hHonUpd hu))
      exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held M F U)
        S A x R GST s' (S.P.committee s' ∩ Hon) H B u vote E hNet hSkew hRedeliver Sy hΔs
        (hRootsN hkR (by omega)) hParent hOwner hGST
        (fun u' hu' => ⟨(Finset.mem_inter.1 hu').1,
          (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hiS
            ((outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
              (hHonW u' (Finset.mem_inter.1 hu').2) (by rw [hv1R, hc1R]; linarith)),
          (hH u' hu').1, (hH u' hu').2.1, (hH u' hu').2.2⟩)
        (fun votes sv hC => by
          unfold Trace.tickInput at hC
          exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
            ((countedVotes_committee_st M F) S A x R E _ s' u votes sv hC) ((committee_sdiff_lt M F) _ _ hCommittee))
        (fun u' hu' => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST
          (hHonU u' (Finset.mem_inter.1 hu').2))
        ⟨kR, hkR, hkRw⟩ hF.1 hF.2
        (fun n₃ sent₃ hR hA e he hl => (hLk u hu n₃ sent₃ hR hA e he hl).1 B hBold) hSend
    · -- a block of a new confirmation: Lemma 36b at that confirmation
      obtain ⟨n'', sent'', hrun'', hAw'', hsave⟩ :=
        (update_of_saved_confirmation_of_updater M F U) S A x R s' v C' E (hUpd hv) hsv
      have hUp := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n'' sent'' hrun'' hAw''
      have hFC' := hVF C' (Or.inr ⟨v, hv, C', hsv, ancestorEq_refl C'⟩) u hu
      have hwVF : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.viewFreeze S.C s') :=
        (mem_activeThroughoutToTick_of_inside M F) R E (hHon'W u hu) (by omega)
          (by rw [hdw1, hf0R]; linarith) (by rw [hf0R, hc2R]; linarith)
      have hw₀ : u ∈ A.activeThroughout x ((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
        have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHon'W u hu)
          (a' := M.supportCutoff S.C (s' + 1) - max (Δ S) Δs)
          (e := M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs)
          (by rw [hdw1, Nat.cast_sub hmax1, hmaxR, hc1R]; linarith)
          (by
            have hle : M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (s' + 1) := by
              have := le_max_right (Δ S) Δs; omega
            have hleR : ((M.supportCutoff S.C (s' + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤
                ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by exact_mod_cast hle
            rw [hc1R] at hleR; rw [hc2R]; linarith)
        push_cast at h
        exact h
      obtain ⟨H_u, hHT, hvt, hCH⟩ := (lem36b_confirmed_block_extended_held M F U) S A x R GST s' C' v u
        n'' vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent (by omega) (hUpd hv)
        (duty_window_start S.C (s' + 1))
        (by
          have h3 : max (3 * Δ S) Δs ≤ M.viewFreeze S.C s' := by
            rcases max_choice (3 * Δ S) Δs with h | h <;> rw [h] <;> omega
          rw [Nat.cast_sub h3, hdw1, hf0R]
          rcases max_choice (3 * Δ S) Δs with h | h <;> rw [h] <;> push_cast
          · linarith
          · linarith)
        hwVF hw₀ hUp hsave hFC'.1 hFC'.2
        (fun n₃ sent₃ hR hA e he hl => by
          obtain ⟨D, hD, heD⟩ := (hLk u hu n₃ sent₃ hR hA e he hl).2
          exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hConfExt D hD v hv C' hsv))))
        hSend
      exact ⟨H_u, hHT, hvt, ancestorEq_trans hBC' hCH⟩
  exact hClause1

/-- **Kit fact, an updater's confirmation extends the family, from the votes clause.** `chainInvFor_updater_confirmation` with
`ChainInvFor`'s first clause in place of the whole invariant: its proof reads only that clause (`voters_of_votes_clause`). A
proof-page helper for `frames_after_healed_slot_until` (re-check 53 section 1.3), which holds the votes clause at a slot before it
holds the third clause there.

The variables: as `chainInvFor_updater_confirmation`.

Read aloud: every block of the family is an ancestor of, or equal to, the confirmation of slot `s` an updater holds right after the
support cutoff of slot `s + 1`, when the honest votes of slot `s` extend the family. -/
theorem votes_clause_updater_confirmation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (𝓒 : Block V → Prop)
    (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHon : Hon ⊆ honestActiveAt M S A x s)
    (hCommittee : |S.P.committee s| < 2 * |S.P.committee s ∩ Hon|)
    (hVotes : ∀ C : Block V, 𝓒 C → ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree, vote = GoldfishVote.mk u s H_u.root ∧ C.AncestorEq H_u)
    (hv : v ∈ updaterAt M S A x s)
    (hF : ∀ C : Block V, 𝓒 C →
      (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible C = true) :
    ∀ C : Block V, 𝓒 C → ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      C.AncestorEq C' := by
  intro C hC
  -- the voters: the committee members of `Hon`, each voting for a block it holds on `C`'s chain
  obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R s (S.P.committee s ∩ Hon) C E hSkew
    (fun u hu => ⟨hHon (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (fun u hu => hVotes C hC u (Finset.mem_inter.1 hu).2)
  -- `v`'s tick to the support cutoff of slot `s` (inside its reader), for the roots
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hv
  -- each voter is awake and honest from the duty window's start of slot `s + 1` up to its tick to the support cutoff
  -- of slot `s + 1` (its reader of `activeAt`, moved later)
  have hUpdU : ∀ u ∈ S.P.committee s ∩ Hon, u ∈ updaterAt M S A x s := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (duty_window_start_mono S (Nat.le_succ s))
      (E.mem_activeThroughoutToTick_of_awakeThroughoutToTick
        (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).1)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain M F U)
    S A x R GST s (S.P.committee s ∩ Hon) H C v E hNet hSkew hRedeliver Sy hΔs
    ((roots_at_own_tick_of_per_tick M F) x E hRoots hkR) hParent hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E hv
        (fun hX => (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).2 (Finset.mem_union_right _ hX)),
      (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hUpdU u hu))
    (by
      unfold Trace.tickInput
      exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
        ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v s)
        ((committee_sdiff_lt M F) _ _ hCommittee))
    hv (hF C hC)

end VotesStep

end GoldilocksCorrectness.Record.Proofs.Executions

