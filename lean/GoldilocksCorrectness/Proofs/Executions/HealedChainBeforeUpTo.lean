module
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatementsUpTo

@[expose] public section

/-!
# `HealedChainBefore.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedChainBefore.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem81_chain_before`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slotStart_mono supportCutoff_eq supportCutoff_lt_of_lt
  voteTime_eq voteTime_succ)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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
≤ s' < n` reads Lemma 32 at slot `s`, up to the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S n`: the induction (`lem81_inv_before_upTo`) reads deliveries due by the support cutoff of slot `n − 1`, and Lemma 32 at a slot `s < n` reads earlier. -/
theorem lem81_chain_before_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S n))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S n))
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
  have hAll := lem81_inv_before_upTo S Sched x GST s₀ anchor n B₀ hDiv hMono
    (hSync.mono (hcm _ _ (Nat.sub_le n 1))) (hCatch.mono (hcm _ _ (Nat.sub_le n 1)))
    (hRoots.mono (hcm _ _ (Nat.sub_le n 1))) hParent hOwner hGST hSleepK hAnchor hB₀slot hBase
    hBaseSaved hVoterFrame hUpdaterFrame
  -- the chain before `n`
  intro s s' v v' C C' hs hss' hs'n hv hv' hC hC'
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · obtain ⟨hInv', -⟩ := hAll s' (by omega) hs'n
    exact chainInvFor_updater_confirmation_upTo S Sched x GST s' (honestActiveAt S Sched s')
      (OnHonestChainBefore S Sched x s₀ s') v' hDiv hMono
      (hSync.mono (hcm _ _ (by omega))) (hCatch.mono (hcm _ _ (by omega)))
      (hRoots.mono (hcm _ _ (by omega))) hParent hOwner (hGSTs s' (by omega)) (subset_refl _)
      (hCom s' (by omega)) hInv' hv'
      (fun D hD => hUpdaterFrame s' (by omega) hs'n v' hv' D hD) C
      ⟨s, hlt, hs, v, hv, C, hC, ancestorEq_refl C⟩ C' hC'
  · subst heq
    have hc := supportCutoff_eq S s
    have hcΔ : supportCutoff S s + Δ S ≤ supportCutoff S (s + 1) := by
      have := supportCutoff_eq S (s + 1)
      have := voteTime_succ S s
      omega
    exact GoldilocksCorrectness.Statements.Executions.lem32_saved_confirmations_compatible_state_upTo S
      Sched x GST s v v' C C' hDiv hMono (hSync.mono (le_trans hcΔ (hcm _ _ (show s + 1 ≤ n by omega))))
      (hCatch.mono (le_trans hcΔ (hcm _ _ (show s + 1 ≤ n by omega))))
      (hRoots.mono (hcm _ _ (by omega)))
      (by have := hGSTs s hs; omega)
      (updaterAt_window S Sched s v hMono hv) (updaterAt_window S Sched s v' hMono hv') hC hC'

end GoldilocksCorrectness.Proofs.Executions

