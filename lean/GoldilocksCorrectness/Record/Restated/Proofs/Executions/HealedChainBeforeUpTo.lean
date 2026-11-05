module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmationCompatibilityStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedChainBeforeUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedChainBeforeUpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 81 on the honest chain
before the healed slot, with the delivery premises up to the bound the theorems read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slotStart_mono supportCutoff_eq supportCutoff_lt_of_lt
  voteTime_eq voteTime_succ)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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

Restated with the delivery premises up to `M.supportCutoff S.C n`: the induction
(`lem81_inv_before_upTo`) reads deliveries due by the support cutoff of slot `n − 1`, and Lemma 32
at a slot `s < n` reads earlier.

Read aloud: after healing, every honest confirmation from the healed slot up to slot `n` is a
descendant of, or equal to, every block of the honest chain before the healed slot, with the
delivery premises up to the bound. -/
theorem lem81_chain_before_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C n)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C n))
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
    have hAll := (lem81_inv_before_upTo M F U) S A x R GST s₀ anchor n B₀ (E.mono (hcm _ _ (Nat.sub_le n 1))) hNet hSkew hRedeliver (Sy.mono (hcm _ _ (Nat.sub_le n 1))) hΔs
      hRootsN1 (fun k u c hk hc => hRoots k u c hk (le_trans hc (hcm _ _ (Nat.sub_le n 1)))) hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved hVoterFrame hUpdaterFrame
    obtain ⟨hInv', -⟩ := hAll s' (by omega) hs'n
    exact (chainInvFor_updater_confirmation_upTo M F U) S A x R GST s' (honestActiveAt M S A x s')
      (OnHonestChainBefore M S A x s₀ s') v' (E.mono (hcm _ _ (by omega))) hNet hSkew hRedeliver (Sy.mono (hcm _ _ (by omega))) hΔs
      (fun k u c hk hc => hRoots k u c hk (le_trans hc (hcm _ _ (by omega)))) hParent hOwner (hGSTs s' (by omega)) (subset_refl _)
      (hCom s' (by omega) (by omega)) hInv' hv'
      (fun D hD => hUpdaterFrame s' (by omega) hs'n v' hv' D hD) C
      ⟨s, hlt, hs, v, hv, C, hC, ancestorEq_refl C⟩ C' hC'
  · subst heq
    exact (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state_upTo M F U) S
      A x R GST s v v' C C' (E.mono (le_trans (hcΔ s) (hcm _ _ (show s + 1 ≤ n by omega)))) hNet hSkew hRedeliver (Sy.mono (le_trans (hcΔ s) (hcm _ _ (show s + 1 ≤ n by omega)))) hΔs
      ((roots_until_max_ticks_of_per_tick M F) x E hRoots (hcm _ _ (show s + 1 ≤ n by omega)) hv hv')
      (by
        have := hGSTs s hs
        have := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
        have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
        have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
        omega)
      hv hv' hC hC'

section VotesStepUpTo
open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff viewFreeze dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_slot
  supportCutoff_succ_le viewFreeze_cast viewFreeze_eq voteTime_cast voteTime_eq voteTime_succ)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both compatible_symm')
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  CountedVotesAt EarlySupporterOf LocksRevoked TreeClosed VoterTree VoterTreeAt)

/-- **Kit fact, the votes clause of the chain step from the voters' frames, with the delivery premises up to the support cutoff of slot `s' + 1`.** The first clause of `HonestChainExtends` at slot
`s' + 1`, for every block of the family `𝓒` and every ancestor of a confirmation of slot `s'` that a validator of `Upd` saved, read
from the first two conjuncts of `StepFrameAt` at those blocks (`w`'s root at its tick to the vote time of slot `s' + 1` compatible
with the block, and a viable head of its voter tree extending the block when the root is the block or an ancestor of it), with the
other inputs of `lem89s_chain_step_upTo`. `votes_clause_step` with its delivery premises up to that cutoff. `lem89s_chain_step`'s first clause, whose proof reads `hStep` only through those two conjuncts;
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
theorem votes_clause_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s' + 1)))
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
  have hcc0 : M.supportCutoff S.C s' ≤ M.supportCutoff S.C (s' + 1) := by omega
  have hcc32 : M.supportCutoff S.C s' + Δ S ≤ M.supportCutoff S.C (s' + 1) := by omega
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
    Activity.mem_activeThroughoutToTick_of_le (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s')) (hHonW u hu)
  have hHon'U : ∀ u ∈ Hon', u ∈ updaterAt M S A x (s' + 1) := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ (s' + 1))) (hHon'W u hu)
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
      exact (GoldilocksCorrectness.Record.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo M F U)
        S A x R GST s' (S.P.committee s' ∩ Hon) H B u vote (E.mono hcc0) hNet hSkew hRedeliver (Sy.mono hcc0) hΔs
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
      obtain ⟨H_u, hHT, hvt, hCH⟩ := (lem36b_confirmed_block_extended_held_upTo M F U) S A x R GST s' C' v u
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

/-- **Kit fact, an updater's confirmation extends the family, from the votes clause, with the delivery premises up to the support cutoff of slot `s + 1`.** `chainInvFor_updater_confirmation_upTo` with
`ChainInvFor`'s first clause in place of the whole invariant: its proof reads only that clause (`voters_of_votes_clause`). A
proof-page helper for `frames_after_healed_slot_until` (re-check 53 section 1.3), which holds the votes clause at a slot before it
holds the third clause there.

The variables: as `chainInvFor_updater_confirmation_upTo`.

Read aloud: every block of the family is an ancestor of, or equal to, the confirmation of slot `s` an updater holds right after the
support cutoff of slot `s + 1`, when the honest votes of slot `s` extend the family. -/
theorem votes_clause_updater_confirmation_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (𝓒 : Block V → Prop)
    (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
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
    Activity.mem_activeThroughoutToTick_of_le (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s))
      (E.mem_activeThroughoutToTick_of_awakeThroughoutToTick
        (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).1)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo M F U)
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

end VotesStepUpTo

end GoldilocksCorrectness.Record.Proofs.Executions

