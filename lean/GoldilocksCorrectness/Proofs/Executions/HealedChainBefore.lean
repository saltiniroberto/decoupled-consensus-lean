module
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipDefs

@[expose] public section

/-!
# The chain before a slot, the caches from the hand-over, the updater frame

The proofs of the facts stated in
`GoldilocksCorrectness/Statements/Executions/HealedChainBeforeStatements.lean`:

- four monotonicity facts in the time: `adversaryFewerThanThirdUntil_mono`,
  `confirmedAgree_mono`, `confirmedMonotone_mono`, `confirmedIncluded_mono`;
- `lem81_chain_before`, Lemma 81 with the frames only at the slots `s` with `s₀ < s < n`: the
  updaters' confirmations of the slots from `s₀` to before `n` form one chain;
- `caches_after_handover`: from the first step one time unit after the hand-over, every honest
  validator's caches are on the honest chain (Lemmas 82 and 84);
- `updaterFrame_after_handover`: after the hand-over, every updater of slot `s` has the frame
  `UpdaterFinalizedOnChainAt` relative to the honest chain before `s` (Lemmas 46 and 91 (f)).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slotStart_mono slot_le_of_supportCutoff_lt
  supportCutoff_eq supportCutoff_lt_of_lt voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The monotonicity facts in the time -/

omit [DecidableEq V] [RootOrder] in
/-- Fewer than a third of the validators in the adversary set up to `t` implies the same up to
`t' ≤ t`. The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`.

The variables:
- `Sched`: the schedule; `t'`, `t`: the two times. -/
theorem adversaryFewerThanThirdUntil_mono (Sched : Schedule V) {t' t : Int} (hle : t' ≤ t)
    (h : AdversaryFewerThanThirdUntil Sched (validator_count V) t) : AdversaryFewerThanThirdUntil Sched (validator_count V) t' :=
  fun A hA => h A (fun v hv => by
    obtain ⟨t'', h1, h2⟩ := hA v hv
    exact ⟨t'', le_trans h1 hle, h2⟩)

/-- Agreement from `tE` implies agreement from any later `tE'`. The proof; the audited statement
is in `Statements/Executions/HealedChainBeforeStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times. -/
theorem confirmedAgree_mono (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    {tE tE' : ℕ} (hle : tE ≤ tE') (h : ConfirmedAgreeAfterHealing S Sched x tE) :
    ConfirmedAgreeAfterHealing S Sched x tE' :=
  fun v₁ v₂ i j h₁ h₂ hi hj => h v₁ v₂ i j h₁ h₂ (le_trans hle hi) (le_trans hle hj)

/-- Growth from `tE` implies growth from any later `tE'`. The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times. -/
theorem confirmedMonotone_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {tE tE' : ℕ} (hle : tE ≤ tE')
    (h : ConfirmedMonotoneAfterHealing S Sched x tE) :
    ConfirmedMonotoneAfterHealing S Sched x tE' :=
  fun v i j hij hj hi => h v i j hij hj (le_trans hle hi)

/-- Inclusion for the slots starting at or after `tE` implies it for the slots starting at or after
`tE' ≥ tE`. The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times. -/
theorem confirmedIncluded_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {tE tE' : ℕ} (hle : tE ≤ tE')
    (h : ConfirmedIncludedAfterHealing S Sched x tE) :
    ConfirmedIncludedAfterHealing S Sched x tE' :=
  fun s hs => h s (le_trans hle hs)

/-! ## Lemma 81 bounded -/

/-- **Lemma 81 bounded.** The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`. It is the proof of
`lem81_confirmations_chain` (`Proofs/Executions/Lemma81.lean`) with the induction on the slot
stopped before `n` (`lem81_inv_before`) and the final ordering read for the slots less than `n`:
the step to slot `s + 1 < n` reads the voter frame at `s + 1` and the updater frames at `s` and
`s + 1`; the ordering of two confirmations of slots `s < s'' < n` reads the invariant at `s''` and
the updater frame at `s''`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `n`: the bound on the slots; `B₀`: the block every updater of slot `s₀`
  saved.

Roots name blocks until `supportCutoff S n`: the induction (`lem81_inv_before`) takes blocks as
held up to the support cutoff of slot `n - 1`, and the ordering of two confirmations of slots `s
≤ s' < n` reads Lemma 32 at slot `s`, up to the support cutoff of slot `s + 1`. -/
theorem lem81_chain_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S n))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- the frames at the slots after `s₀` and before `n`
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    ConfirmationsChainBefore S Sched x s₀ n := by
  -- the support cutoff grows with the slot
  have hcm : ∀ a b : ℕ, a ≤ b → supportCutoff S a ≤ supportCutoff S b := fun a b h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact le_of_lt (supportCutoff_lt_of_lt S h)
    · rw [h]
  -- the times and the counting
  have hGSTs : ∀ s : ℕ, s₀ ≤ s → GST ≤ voteTime S s := fun s hs => by
    have h1 := voteTime_eq S s₀
    have h2 := voteTime_eq S s
    have h3 := slotStart_mono S hs
    omega
  have hCom : ∀ s : ℕ, s₀ ≤ s →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt S Sched s| :=
    fun s hs => committee_majority_of_sleepiness S Sched anchor s hSleepK
      (le_trans hAnchor (slotStart_mono S (by omega)))
  -- the slot invariant and the lock invariant at every slot after the healed one and before `n`
  have hAll := lem81_inv_before S Sched x GST s₀ anchor n B₀ hDiv hMono hSync hCatch
    (hRoots.mono (hcm _ _ (Nat.sub_le n 1))) hParent hOwner hGST hSleepK hAnchor hB₀slot hBase
    hBaseSaved hVoterFrame hUpdaterFrame
  -- the chain before `n`
  intro s s' v v' C C' hs hss' hs'n hv hv' hC hC'
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · obtain ⟨hInv', -⟩ := hAll s' (by omega) hs'n
    exact chainInvFor_updater_confirmation S Sched x GST s' (honestActiveAt S Sched s')
      (OnHonestChainBefore S Sched x s₀ s') v' hDiv hMono hSync hCatch
      (hRoots.mono (hcm _ _ (by omega))) hParent hOwner (hGSTs s' (by omega)) (subset_refl _)
      (hCom s' (by omega)) hInv' hv'
      (fun D hD => hUpdaterFrame s' (by omega) hs'n v' hv' D hD) C
      ⟨s, hlt, hs, v, hv, C, hC, ancestorEq_refl C⟩ C' hC'
  · subst heq
    have hc := supportCutoff_eq S s
    exact GoldilocksCorrectness.Statements.Executions.lem32_saved_confirmations_compatible_state S
      Sched x GST s v v' C C' hDiv hMono hSync hCatch (hRoots.mono (hcm _ _ (by omega)))
      (by have := hGSTs s hs; omega)
      (updaterAt_window S Sched s v hMono hv) (updaterAt_window S Sched s v' hMono hv') hC hC'

/-! ## The caches from one time unit after the hand-over -/

/-- **The caches from the first step one time unit after the hand-over.** The proof; the audited
statement is in `Statements/Executions/HealedChainBeforeStatements.lean`. `i₂` is the step after
`stepBefore x (x[i₁].time + 1)`, the first step at the time `x[i₁].time + 1` (`stepBefore_spec`); a
step at a time at least `x[i₂].time` is at a time greater than `x[i₁].time`, so after `i₁`
(`lt_of_time_lt`), and Lemma 84 applies with `t₀ := supportCutoff S (s₀ + 1)`, its agreement
premise from Lemma 82.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i₁`: the step at the hand-over; `t`: the bound on the times of the steps.

Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each such step the proof reads Lemma 84 up to `t`. -/
theorem caches_after_handover (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x t)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hStart : ∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][u].st)) :
    ∃ i₂ : ℕ, x[i₂].time = x[i₁].time + 1 ∧
      ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ t →
        u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st) := by
  obtain ⟨-, -, h₂⟩ := stepBefore_spec x hDiv (show 1 ≤ x[i₁].time + 1 by omega)
  refine ⟨stepBefore x (x[i₁].time + 1) + 1, h₂, fun j u hj hjt hu => ?_⟩
  have hij : i₁ ≤ j := (lt_of_time_lt x (show x[i₁].time < x[j].time by omega)).le
  exact GoldilocksCorrectness.Proofs.Executions.lem84_caches_stay_on_chain S Sched x s₀
    (supportCutoff S (s₀ + 1)) H i₁ t hU hMono hRoots hAdvQ
    (GoldilocksCorrectness.Proofs.Executions.lem82_honest_attestations_on_chain S Sched x s₀ hDiv
      hMono) hOld hStart j u hij hjt hu

/-! ## The updater frame after the hand-over -/

/-- **The updater frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`. At the step `jv` before the support
cutoff of slot `s + 1`, `v` is honest and the step is at a time at least `x[i₂].time`; every slot
`s_a` whose support cutoff of slot `s_a + 1` is at most that time is less than `s`
(`slot_le_of_supportCutoff_lt`), so the root of `v`'s fork choice is on the honest chain before
`s` (Lemma 91 (f)), compatible with every block `B` of it (`onHonestChainBefore_compatible`);
the finalized block is the root or an ancestor of it (Lemma 46), so it is compatible with `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.

Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 91 (f) at the step
before that time, whose bound is the time of that step.

Caches up to `supportCutoff S (s + 1)`: the proof reads `v`'s caches before the support cutoff of
slot `s + 1` (Lemma 91 (f) there). -/
theorem updaterFrame_after_handover_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₂ H s : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1))) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₂].time < supportCutoff S (s + 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hv : v ∈ updaterAt S Sched s) :
    UpdaterFinalizedOnChainAt S Sched x s₀ s v := by
  intro B hB
  -- the reading step before the support cutoff of slot `s + 1`
  obtain ⟨jv, hjv⟩ : ∃ jv, jv = stepBefore x (supportCutoff S (s + 1)) := ⟨_, rfl⟩
  have htv : x[jv].time + 1 = supportCutoff S (s + 1) := by
    rw [hjv]; exact time_stepBefore_add_one x hDiv (by omega)
  have hstv : stateBefore x (supportCutoff S (s + 1)) v = x[jv][v].st := by
    unfold stateBefore; rw [hjv]
  have hv' := hv
  rw [updaterAt, Finset.mem_sdiff] at hv'
  have hvj : v ∉ Sched.adv (x[jv].time : Int) := by
    intro ha
    apply hv'.2
    refine hMono _ _ ?_ ha
    have h3 : x[jv].time ≤ supportCutoff S (s + 1) := by omega
    exact_mod_cast h3
  have hiv : x[i₂].time ≤ x[jv].time := by omega
  have hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[jv].time → s_a < s := fun s_a h =>
    (slot_le_of_supportCutoff_lt S s_a s).2.1 (by omega)
  -- the root is on the chain before `s` (Lemma 91 (f))
  have hR := GoldilocksCorrectness.Proofs.Executions.lem91f_voter_root_on_chain_before_until S Sched
    x s₀ i₂ jv s H v hDiv hMono (hRoots.mono (by omega)) hU hAdvQ hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hiv hvj hs'
  rw [← hstv] at hR
  have hRB := onHonestChainBefore_compatible S Sched x s₀ s _ B hChain hR hB
  -- the finalized block is the root or an ancestor of it (Lemma 46)
  exact compatible_of_ancestorEq_compatible
    (F_ancestorEq_fc_root_of_stateBefore S Sched x (supportCutoff S (s + 1)) v)
    (by rw [← fc_root_eq]; exact hRB)

/-- **The updater frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedChainBeforeStatements.lean`. At the step `jv` before the support
cutoff of slot `s + 1`, `v` is honest and the step is at a time at least `x[i₂].time`; every slot
`s_a` whose support cutoff of slot `s_a + 1` is at most that time is less than `s`
(`slot_le_of_supportCutoff_lt`), so the root of `v`'s fork choice is on the honest chain before
`s` (Lemma 91 (f)), compatible with every block `B` of it (`onHonestChainBefore_compatible`);
the finalized block is the root or an ancestor of it (Lemma 46), so it is compatible with `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.

Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 91 (f) at the step
before that time, whose bound is the time of that step.

It is `updaterFrame_after_handover_until` with the caches restricted to the steps it reads. -/
theorem updaterFrame_after_handover (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₂ H s : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1))) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₂].time < supportCutoff S (s + 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hv : v ∈ updaterAt S Sched s) :
    UpdaterFinalizedOnChainAt S Sched x s₀ s v :=
  updaterFrame_after_handover_until S Sched x s₀ i₂ H s v hDiv hMono hRoots hU hAdvQ hOld (fun j u
    h₁ _ h₂ => hCaches j u h₁ h₂) hs hChain hv

end GoldilocksCorrectness.Proofs.Executions
