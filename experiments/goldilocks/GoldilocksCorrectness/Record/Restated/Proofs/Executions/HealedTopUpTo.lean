module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedTop
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedChainBeforeUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedVoterFrameUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89HandoverVFUpTo
public import GoldilocksCorrectness.Proofs.Executions.HealedTop
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBeforeUpTo
public import GoldilocksCorrectness.Proofs.Executions.HealedVoterFrameUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverVFUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedTopUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedTopUpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the theorems of `HealedTop.lean` that name
a delivery premise (the frames at every slot after the healed slot and the facts after the
hand-over, for the readings up to a time `t`), restated with `SynchronyFromWakeUpTo` and
`CatchUpOnWakeUpTo` at a bound on the deadlines. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_of_anchor one_le_Δ slotStart_eq
  slotStart_mono supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono
  voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows Vocab.goldilocks
  acObject fgObject healFrontSlots)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Kit fact, the votes clause at the slot after `s'`, from the frames up to it, with the delivery premises up to the support cutoff of slot `s' + 1`.** Under
`lem81_inv_before`'s premises with the voter frames at the slots from `s₀ + 1` to `s' + 1` and the updater
frames at the slots from `s₀ + 1` to `s'`: every Goldfish vote an honest active validator of slot `s' + 1`
sends at its tick to the vote time extends every block on the honest chain before `s' + 1`. The first clause
of `ChainInvFor` at slot `s' + 1`, which `frames_after_healed_slot_until` needs before it holds the updater
frames at `s' + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee sleepiness holds;
  `s'`: the slot before the votes' slot; `B₀`: the block every updater of slot `s₀` saved.

Why: `votes_clause_after_healed_slot`'s proof with `votes_clause_step_upTo`, `lem81_inv_before_upTo` and
`chainInvFor_updater_confirmation_upTo`: `votes_clause_step` at `s'`, over the family of blocks that are `B₀` or an ancestor of it when `s' = s₀`
(the base invariants of `lem81_inv_before`), and over the honest chain before `s'` otherwise
(`lem81_inv_before` at `n := s' + 1`, the confirmations of slot `s'` extending it by
`chainInvFor_updater_confirmation` at the updater frames of `s'`); its voter frame input is the voter frame at
`s' + 1` read at each voter's tick to the vote time.

Read aloud: the honest votes of slot `s' + 1` extend the honest chain before `s' + 1`, once the frames up to
`s' + 1` hold for the voters and up to `s'` for the updaters. -/
theorem votes_clause_after_healed_slot_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor s' : ℕ) (B₀ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s' + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks up to the real time of every validator's tick to a clock value at most the support cutoff of
    -- slot `s' + 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s' + 1 + 1)))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hs' : s₀ ≤ s')
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s ≤ s' + 1 → ∀ w ∈ honestActiveAt M S A x s,
      VoterFrameOnChainAt M S A x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s ≤ s' → ∀ v ∈ updaterAt M S A x s,
      UpdaterFinalizedOnChainAt M S A x s₀ s v) :
    ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s' + 1) C →
      ∀ u ∈ honestActiveAt M S A x (s' + 1), ∀ vote : GoldfishVote V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
        ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
          vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ C.AncestorEq H_u := by
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E
  have hAnch : ∀ s : ℕ, s₀ ≤ s → anchor ≤ M.slotStart S.C (s + 1) := fun s hs =>
    le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hCom : ∀ s : ℕ, s₀ ≤ s → s ≤ s' + 1 →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| := fun s hs hsn =>
    (committee_majority_of_sleepiness M F) S A x anchor s hSleepK (hAnch s hs) (hcm _ _ (by omega))
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s' := le_trans hGST (hcm _ _ hs')
  -- the family at slot `s'`: its invariants, and the confirmations of slot `s'` extending it
  obtain ⟨𝓒, h𝓒in, h𝓒out, hInv, hLocks, hConfExt⟩ : ∃ 𝓒 : Block V → Prop,
      (∀ C : Block V, 𝓒 C → OnHonestChainBefore M S A x s₀ (s' + 1) C) ∧
      (∀ C : Block V, OnHonestChainBefore M S A x s₀ s' C → 𝓒 C) ∧
      ChainInvFor M S A x (honestActiveAt M S A x s') 𝓒 s' ∧
      (∀ u ∈ honestActiveAt M S A x s', LiveLocksOnFamilyAt M S A x 𝓒 s' u) ∧
      (∀ C : Block V, 𝓒 C → ∀ v ∈ updaterAt M S A x s', ∀ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' → C.AncestorEq C') := by
    rcases Nat.eq_or_lt_of_le hs' with heq | hlt
    · -- at the healed slot: the blocks that are `B₀` or an ancestor of it (`lem81_inv_before`'s base invariants)
      rw [← heq]
      obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt M S A x s₀).Nonempty :=
        Finset.card_pos.1 (by have := hCom s₀ le_rfl (by omega); omega)
      have hv₀ : u₀ ∈ updaterAt M S A x s₀ :=
        (honestActiveAt_subset_updaterAt M F) S A x R E s₀ (Finset.mem_inter.1 hu₀).2
      refine ⟨fun D => D.AncestorEq B₀,
        fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hC⟩,
        fun C ⟨σ, hσ, hσ₀, _⟩ => absurd hσ₀ (by omega),
        fun C hC => (honestChainExtends_of_ancestorEq M F) S A x _ B₀ C s₀ hC hBase,
        fun u hu n₃ sent₃ hrun hA => (liveLocksOnFamilyAt_base M F U) S A x R s₀ B₀ u n₃ E
          hB₀slot ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ + 1) u n₃ sent₃ hrun hA)
          (hBase.2.1 u hu n₃ sent₃ hrun hA), ?_⟩
      intro C hC v hv C' hC'
      rw [hBaseSaved v hv] at hC'
      cases hC'
      exact hC
    · -- after it: the honest chain before `s'`
      obtain ⟨hInv, hLocks⟩ := (lem81_inv_before_upTo M F U) S A x R GST s₀ anchor (s' + 1) B₀ (E.mono (hcm _ _ (by omega))) hNet hSkew hRedeliver
        (Sy.mono (hcm _ _ (by omega))) hΔs ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          (by exact_mod_cast hcm _ _ (by omega)) hRoots)
        (fun k u c hk hc => hRootsTick k u c hk (le_trans hc (hcm _ _ (by omega))))
        hParent hOwner hGST (CommitteeSleepinessUntil.mono M hSleepK (hcm _ _ (by omega))) hAnchor hB₀slot hBase
        hBaseSaved (fun s h1 h2 => hVoterFrame s h1 (by omega)) (fun s h1 h2 => hUpdaterFrame s h1 (by omega))
        s' hlt (Nat.lt_succ_self s')
      refine ⟨OnHonestChainBefore M S A x s₀ s', fun C ⟨σ, hσ, hAt⟩ => ⟨σ, by omega, hAt⟩, fun C hC => hC, hInv,
        hLocks, ?_⟩
      intro C hC v hv C' hC'
      exact (chainInvFor_updater_confirmation_upTo M F U) S A x R GST s' (honestActiveAt M S A x s') _ v
        (E.mono (hcm _ _ (Nat.le_succ s'))) hNet hSkew hRedeliver (Sy.mono (hcm _ _ (Nat.le_succ s'))) hΔs (fun k u c hk hc => hRootsTick k u c hk (le_trans hc (hcm _ _ (Nat.le_succ s')))) hParent
        hOwner hGSTs (subset_refl _) (hCom s' hs' (by omega)) hInv hv (hUpdaterFrame s' hlt le_rfl v hv) C hC C' hC'
  -- the votes clause of the chain step at `s'`, with the voter frames at `s' + 1` read at the voters' ticks
  have h := (votes_clause_step_upTo M F U) S A x R GST s' (honestActiveAt M S A x s') (honestActiveAt M S A x (s' + 1))
    (updaterAt M S A x s') 𝓒 E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGSTs
    (subset_refl _) (subset_refl _) (subset_refl _)
    ((honestActiveAt_succ_subset_updaterAt M F U) S A s' R E hSkew)
    (hCom s' hs' (by omega)) (hCom (s' + 1) (by omega) le_rfl) hInv
    (fun u hu => (mem_honestActiveAt_or_lockFree M F U) S A s' u R E hSkew hu) hLocks hConfExt
    (fun C hC w hw => by
      have hC' : OnHonestChainBefore M S A x s₀ (s' + 1) C := by
        rcases hC with hC | ⟨v, hv, C', hsv, hCC'⟩
        · exact h𝓒in C hC
        · exact ⟨s', Nat.lt_succ_self s', hs', v, hv, C', hsv, hCC'⟩
      obtain ⟨k, hk⟩ := (tick_voteTime_of_honestActiveAt_succ M F U) S A x R E hSkew s' w hw
      have hti : x.tickInput w (M.voteTime S.C (s' + 1)) = x.st k w := by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E hk]
      rw [hti]
      exact hVoterFrame (s' + 1) (by omega) le_rfl w hw C hC' k hk)
  intro C hC u hu vote hsend
  refine h C ?_ u hu vote hsend
  obtain ⟨σ, hσ, hσ₀, v, hv, C', hC', hCC'⟩ := hC
  rcases Nat.lt_or_ge σ s' with hlt | hge
  · exact Or.inl (h𝓒out C ⟨σ, hlt, hσ₀, v, hv, C', hC', hCC'⟩)
  · obtain rfl : σ = s' := by omega
    exact Or.inr ⟨v, hv, C', hC', hCC'⟩

/-- **Kit fact, the frames at one slot after the healed slot.** Under the premises of
`frames_after_healed_slot_until_upTo`: at every slot `s > s₀` whose support cutoff plus `ΔClockBehind` is at
most `t`, with committee sleepiness read up to the support cutoff of slot `s + 1`, every honest active
validator of `s` has its voter frame, and every updater of `s` whose tick to the support cutoff of slot
`s + 1` is at a real time at most `t` has its updater frame. The induction of
`frames_after_healed_slot_until_upTo`'s proof, stated on its own so that `healed_handover_facts_until_upTo`'s
proof reads it at a slot whose next support cutoff is after `t`.

Why: by strong induction on the slot, as `frames_after_healed_slot_until_upTo`'s proof.

The variables: as in `frames_after_healed_slot_until_upTo`.

Read aloud: the phase's frames at a slot `s`, when `s`'s own support cutoff is one clock bound before
`t` and committee sleepiness holds up to the next one. -/
theorem frames_at_slot_after_healed_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks t) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST t)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t)
    -- every updater of a slot from the healed slot `s₀` on, whose update is at most `t`, is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hi₂ : x.time i₂ < M.viewFreeze S.C s_m)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (hPhase : ∀ s : ℕ, s₀ < s → s < s_m →
      (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v))
    (hLast : ∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C s_m) →
      VoterFrameOnChainAt M S A x s₀ s_m w)
    :
    ∀ s : ℕ, s₀ < s → ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t →
      CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1)) →
      (∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t →
        UpdaterFinalizedOnChainAt M S A x s₀ s v) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  -- the slot times, as reals
  have hT : ∀ s : ℕ, ((M.voteTime S.C s : ℕ) : ℝ) = M.slotStart S.C s + Δ S ∧
      ((M.supportCutoff S.C s : ℕ) : ℝ) = M.slotStart S.C s + 2 * Δ S ∧
      ((M.viewFreeze S.C s : ℕ) : ℝ) = M.slotStart S.C s + 3 * Δ S ∧
      ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = M.slotStart S.C s + 4 * Δ S := fun s => by
    obtain ⟨h1, h2, h3, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
    exact ⟨by rw [h1]; push_cast; ring, by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring,
      by rw [h4]; push_cast; ring⟩
  have hssm : ∀ a b : ℕ, a ≤ b → ((M.slotStart S.C a : ℕ) : ℝ) ≤ M.slotStart S.C b := fun a b h => by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  -- the callees' caches row, on the state at each step strictly after the hand-over time
  have hCachesS := (cachesOnChain_st_of_succ M F) S A x R s₀ H i₂ (t : ℝ) E hCaches
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E
  -- roots at every tick to a clock value at most `c`, when `c + ΔClockBehind` is at most `t`
  have hRootsTickOf : ∀ c : ℕ, (c : ℝ) + ΔClockBehind ≤ t → ∀ (k : ℕ) (u : V) (c' : ℕ),
      x.lbl k = Event.tick u c' → c' ≤ c → RootsNameBlocksUntil M A x (x.time k) := by
    intro c hc k u c' hk hc'
    have h1 := (E.tick_active k u c' hk).2.2
    have h2 : (c' : ℝ) ≤ c := by exact_mod_cast hc'
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRoots
  -- an updater's tick to the support cutoff of the next slot is at most that cutoff plus `ΔClockBehind`
  have hUpdTick : ∀ σ : ℕ, ∀ v ∈ updaterAt M S A x σ,
      x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + ΔClockBehind := by
    intro σ v hv
    have hv' := hv
    unfold updaterAt at hv'
    obtain ⟨k', hk', -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
    rw [(tickStep_eq_of_lbl M) x E hk']
    exact (E.tick_active k' v _ hk').2.2
  -- the induction, at the slots `s` whose support cutoff plus `ΔClockBehind` is at most `t` and whose committee
  -- sleepiness is read up to the support cutoff of slot `s + 1` (from `hSleepK` when that cutoff is at most `t`, from
  -- `hSleepKTick` at an updater's own tick otherwise,)
  have key : ∀ s : ℕ, s₀ < s → ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t →
      CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1)) →
      (∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t →
        UpdaterFinalizedOnChainAt M S A x s₀ s v) := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs hcsR hKs
      obtain ⟨hvs, hcs, -, hss⟩ := hT s
      obtain ⟨-, hcs1, -, -⟩ := hT (s + 1)
      have hcst : M.supportCutoff S.C s ≤ t := by
        have : ((M.supportCutoff S.C s : ℕ) : ℝ) ≤ (t : ℝ) := by linarith
        exact_mod_cast this
      -- every frame at the slots after `s₀` and before `s`: every updater there ticked by `t`
      have hFrames : ∀ σ : ℕ, s₀ < σ → σ < s →
          (∀ w ∈ honestActiveAt M S A x σ, VoterFrameOnChainAt M S A x s₀ σ w) ∧
          (∀ v ∈ updaterAt M S A x σ, UpdaterFinalizedOnChainAt M S A x s₀ σ v) := by
        intro σ h1 h2
        have hσs : M.supportCutoff S.C (σ + 1) ≤ M.supportCutoff S.C s := hcm _ _ h2
        have hσR : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) ≤ M.supportCutoff S.C s := by exact_mod_cast hσs
        have hσσ : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ M.supportCutoff S.C s := by
          exact_mod_cast hcm _ _ (le_of_lt h2)
        obtain ⟨hV, hU⟩ := ih σ h2 h1 (by linarith)
          (CommitteeSleepinessUntil.mono M hKs (hcm _ _ (by omega : σ + 1 ≤ s + 1)))
        refine ⟨hV, fun v hv => hU v hv ?_⟩
        have := hUpdTick σ v hv
        linarith
      rcases Nat.lt_or_ge s s_m with hlt | hge
      · -- before the last honest round opening slot: Lemma 89's frames
        obtain ⟨hV, hU⟩ := hPhase s hs hlt
        refine ⟨fun w hw => hV w ?_, fun v hv _ => hU v hv⟩
        unfold roundMembers
        refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => ?_⟩
        unfold honestActiveAt at hw
        exact (Finset.mem_sdiff.1 hw).2 (Finset.mem_union_left _ h)
      · -- from it on: the chain before `s`, from the frames before `s`
        have hChain : ConfirmationsChainBefore M S A x s₀ s :=
          (lem81_chain_before_upTo M F U) S A x R GST s₀ anchor s B₀ (E.mono hcst) hNet hSkew hRedeliver (Sy.mono hcst) hΔs
            (hRootsTickOf _ hcsR) hParent hOwner hGST (CommitteeSleepinessUntil.mono M hSleepK hcst) hAnchor hB₀slot
            hBase hBaseSaved (fun σ h1 h2 => (hFrames σ h1 h2).1) (fun σ h1 h2 => (hFrames σ h1 h2).2)
        have hcut0 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ t := by
          exact_mod_cast le_trans (hcm _ _ (by omega : s₀ + 1 ≤ s)) hcst
        -- the voter frames at `s`
        have hVF : ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w := by
          intro w hw
          rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · -- at the last honest round opening slot: Lemma 89's added clause
            rw [← heq] at hw ⊢
            refine hLast w ((not_mem_corruptedAtTime_of_honestActiveAt M F) R E hw ?_)
            obtain ⟨h1, h2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s_m
            have := hcm _ _ (show s_m ≤ s_m + 1 by omega)
            omega
          · -- after it: the voter frame after the hand-over
            obtain ⟨k, hk⟩ := (tick_voteTime_of_honestActiveAt_succ M F U) S A x R E hSkew (s - 1) w
              (by rwa [show s - 1 + 1 = s by omega])
            rw [show s - 1 + 1 = s by omega] at hk
            have hke : x.tickStep w (M.voteTime S.C s) = k := (tickStep_eq_of_lbl M) x E hk
            have hkt : x.time (x.tickStep w (M.voteTime S.C s)) ≤ t := by
              rw [hke]
              have h1 := (E.tick_active k w _ hk).2.2
              linarith
            have hs1 : s₀ ≤ s - 1 := by omega
            have hvst : M.voteTime S.C s ≤ t := by
              obtain ⟨h1, h2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
              omega
            have hsvf : x.time i₂ < M.viewFreeze S.C (s - 1) := by
              obtain ⟨-, -, ha, -⟩ := hT s_m
              obtain ⟨-, -, hb, -⟩ := hT (s - 1)
              have := hssm _ _ (show s_m ≤ s - 1 by omega)
              linarith
            exact (voterFrame_after_handover_until_upTo M F U Fx) S A x R GST s₀ i₂ H s w (E.mono hvst) hNet hSkew hRedeliver
              (Sy.mono hvst) hΔs
              ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hkt hRoots) hParent
              (hAdvQ.mono (max_le hkt hcut0)) ((gst_sync_le_viewFreeze M F U) S hGST hs1)
              ((confirmation_holder_at_window_start_until M F U) S A x R E hSkew s₀ s anchor t Δs hSleepK hAnchor hcst
                hFrames hStay)
              (fun σ h1 h2 u hu => hStay σ h1 (le_trans (hcm _ _ (by omega : σ + 1 ≤ s)) hcst) u hu) hOld
              (fun j u h₁ h₂ hu => hCachesS j u h₁ (le_trans h₂ hkt) hu) hsvf hChain hw
        refine ⟨hVF, fun v hv hvt => ?_⟩
        -- the updater frames at `s`: the slot-`s` confirmations of the earlier updaters extend the chain before `s`,
        -- from the votes clause at `s`
        have hCom : |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| :=
          (committee_majority_of_sleepiness M F) S A x anchor s hKs
            (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
              (by omega))) le_rfl
        have hVotes : ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C →
            ∀ u ∈ honestActiveAt M S A x s, ∀ vote : GoldfishVote V,
              (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
                (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
              ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree, vote = GoldfishVote.mk u s H_u.root ∧
                C.AncestorEq H_u := by
          obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
          exact (votes_clause_after_healed_slot_upTo M F U) S A x R GST s₀ anchor s' B₀ (E.mono hcst) hNet hSkew hRedeliver
            (Sy.mono hcst) hΔs
            ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRoots)
            (hRootsTickOf _ hcsR) hParent hGST hKs hAnchor hB₀slot hBase
            hBaseSaved (by omega)
            (fun σ h1 h2 => by
              rcases Nat.lt_or_ge σ (s' + 1) with h | h
              · exact (hFrames σ h1 h).1
              · obtain rfl : σ = s' + 1 := by omega
                exact hVF)
            (fun σ h1 h2 => (hFrames σ h1 (by omega)).2)
        have hsTick : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) →
            x.time i₂ < x.time k := by
          intro k u hk
          have h1 := (E.tick_active k u _ hk).2.1
          obtain ⟨-, -, ha, -⟩ := hT s_m
          have := hssm _ _ hge
          linarith
        exact (updater_frames_at_slot M F U Fx) S A x R s₀ i₂ H s (t : ℝ) E hSkew hRoots
          (hAdvQ.mono (max_le le_rfl hcut0)) hOld hCachesS hsTick hChain
          (fun u hu hUF C hC C' hC' => (votes_clause_updater_confirmation_upTo M F U) S A x R GST s
            (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) u (E.mono hcst) hNet hSkew hRedeliver
            (Sy.mono hcst) hΔs
            (hRootsTickOf _ hcsR) hParent hOwner (le_trans hGST (hcm _ _ (by omega))) (subset_refl _) hCom hVotes hu
            hUF C hC C' hC') v hv hvt
  exact key

/-- **The frames at every slot after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: by strong induction on the slot `s > s₀`.
For `s < s_m`, Lemma 89's voter frame at `roundMembers M S Sched (s + 1)`, which contains the honest
active validators of `s`, and its updater frame at `updaterAt M S A x s`. For `s ≥ s_m`, the frames at the slots before `s` give
`ConfirmationsChainBefore M S Sched x s₀ s` (`lem81_chain_before`); then the voter frame at `s_m` is
Lemma 89's clause, the voter frame at `s > s_m` is `voterFrame_after_handover`, and the updater
frame at `s ≥ s_m` is `updaterFrame_after_handover`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s_m`: the last honest round opening slot; `i₂`:
  the step from which the caches are on the chain; `H`: the threshold; `anchor`: the time from
  which committee sleepiness holds; `t`: the bound on the slots' update times; `B₀`: the block
  every updater of slot `s₀` saved.

Roots name blocks until `t`: the conclusions are for the slots `s` whose update, at the support
cutoff of slot `s + 1`, is at most `t`; at such a slot the proof reads `lem81_chain_before` up to
the support cutoff of slot `s`, `voterFrame_after_handover` up to the vote time of slot `s` and
`updaterFrame_after_handover` up to the support cutoff of slot `s + 1`.

Caches up to `t`: at a slot `s` the proof reads the caches up to the support cutoff of slot `s + 1`,
at most `t` (`voterFrame_after_handover_until`, `updaterFrame_after_handover_until`).

Restated with the delivery premises up to `t`: the bound of its roots `hRoots`: the conclusions are
for the slots whose update is at most `t`, and at such a slot `s` the proof reads deliveries due by
the support cutoff of slot `s` (`lem81_chain_before_upTo`) and the vote time of slot `s`
(`voterFrame_after_handover_until_upTo`).

Read aloud: the phase's frames, carried past the hand-over by strong induction on the slot, at every
slot whose update is at most `t`, with the delivery premises up to `t`. -/
theorem frames_after_healed_slot_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks t) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST t)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchor` read up to `c`
    --
    (hSleepKTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x anchor c)
    -- every updater of a slot from the healed slot `s₀` on, whose update is at most `t`, is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hi₂ : x.time i₂ < M.viewFreeze S.C s_m)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (hPhase : ∀ s : ℕ, s₀ < s → s < s_m →
      (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v))
    (hLast : ∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C s_m) →
      VoterFrameOnChainAt M S A x s₀ s_m w) :
    (∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
    (∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt M S A x s,
      x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hT : ∀ s : ℕ, ((M.voteTime S.C s : ℕ) : ℝ) = M.slotStart S.C s + Δ S ∧
      ((M.supportCutoff S.C s : ℕ) : ℝ) = M.slotStart S.C s + 2 * Δ S ∧
      ((M.viewFreeze S.C s : ℕ) : ℝ) = M.slotStart S.C s + 3 * Δ S ∧
      ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = M.slotStart S.C s + 4 * Δ S := fun s => by
    obtain ⟨h1, h2, h3, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
    exact ⟨by rw [h1]; push_cast; ring, by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring,
      by rw [h4]; push_cast; ring⟩
  have key := (frames_at_slot_after_healed_until_upTo M F U Fx) S A x R GST s₀ s_m i₂ H anchor t B₀ E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hGST hSleepK hStay hAnchor hB₀slot hBase hBaseSaved hOld hi₂ hCaches hPhase hLast
  -- a slot whose next support cutoff is at most `t`: its own cutoff plus `ΔClockBehind` is at most `t`
  have hcsR_of : ∀ s : ℕ, M.supportCutoff S.C (s + 1) ≤ t →
      ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t := by
    intro s hst
    obtain ⟨-, hcs, -, hss⟩ := hT s
    obtain ⟨-, hcs1, -, -⟩ := hT (s + 1)
    have hstR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ t := by exact_mod_cast hst
    linarith
  refine ⟨fun s hs hst => (key s hs (hcsR_of s hst) (CommitteeSleepinessUntil.mono M hSleepK hst)).1,
    fun s hs v hv hvt => ?_⟩
  rcases Nat.lt_or_ge s s_m with hlt | hge
  · exact (hPhase s hs hlt).2 v hv
  -- from the last honest round opening slot on: committee sleepiness up to the support cutoff of slot `s + 1`,
  -- read at `v`'s own tick to it, at a real time at most `t`
  have hv' := hv
  unfold updaterAt at hv'
  obtain ⟨k, hk, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
  have hke : x.tickStep v (M.supportCutoff S.C (s + 1)) = k := (tickStep_eq_of_lbl M) x E hk
  have hkt : x.time k ≤ t := by rw [← hke]; exact hvt
  have hcsR : ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t := by
    obtain ⟨-, hcs, -, hss⟩ := hT s
    obtain ⟨-, hcs1, -, -⟩ := hT (s + 1)
    have h1 := (E.tick_active k v _ hk).2.1
    linarith
  exact (key s hs hcsR (hSleepKTick k v _ hk hkt)).2 v hv hvt

/-- **The facts after the hand-over, for the readings up to a time `t`.** The proof; the audited
statement is in `Statements/Executions/HealedTopStatements.lean`. Why: for `t ≥ tAwakeEnd`, either a
root collision has hit two blocks honest validators hold by `t`, or roots name blocks up to `t`
(`rootsNameBlocksUntil_or_collision`); then `healed_handover_facts`'s proof with every reading up to
`t`: Lemma 89 reads up to the support cutoff of the last opening's first slot, at most `tAwakeEnd`;
the caches from `i₂` up to `t` (`caches_after_handover`); the frames at the slots whose update is at
most `t` (`frames_after_healed_slot_until`); and the chain before the slot after each such slot
(`lem81_chain_before`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Restated with the delivery premises up to `b`: the conclusion gains the upper end `t ≤ b`, and at
such a `t` the proof reads deliveries due by `t` (`frames_after_healed_slot_until_upTo`,
`lem81_chain_before_upTo` at the slots whose update is at most `t`); the attestations (`hSyncF`,
`hCatchF`) up to `M.slotStart S.C (r m * S.C.R)`, the bound of `lem89_phase_upTo`.

Read aloud: for every time `t` after the phase, unless a collision has hit an honest proposal or two
blocks held by `t`, the honest chain after healing exists up to `t` and every honest validator's
caches stay on it up to `t`. -/
theorem healed_handover_facts_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
 {b : ℕ}
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (r m * S.C.R))) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C (r m * S.C.R)))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t) :
    t ≤ b →
      RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      ∃ (s₀ i₂ : ℕ) (B₀ : Block V),
        (M.supportCutoff S.C (s₀ + 1) < x.time i₂ ∧
          ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s₀ + 1)) → x.time k < x.time i₂) ∧
        x.time i₂ ≤ tAwakeEnd ∧
        (∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → x.time i₂ < M.slotStart S.C s ∧
          ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.slotStart S.C s) → x.time i₂ < x.time k) ∧
        r 0 * S.C.R ≤ s₀ ∧
        GST ≤ M.voteTime S.C s₀ ∧ anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1) ∧ s₀ ≤ B₀.slot ∧
        HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
        (∀ v ∈ updaterAt M S A x s₀,
          (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
        (∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) →
          v ∈ updaterAt M S A x s₀) ∧
        OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
        (∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
          u ∉ A.corrupted j →
          CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u)) ∧
        (∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
          u ∉ A.corrupted j →
          CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st (j + 1) u)) ∧
        (∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
          ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt M S A x s,
          x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v) ∧
        (∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
          x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ σ ∧
          ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
          ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
          (∀ C : Block V, OnHonestChainBefore M S A x s₀ σ C → C.AncestorEq C') ∧
          (s₀ ≤ σ → ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
          ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
          C'.compatible C'' = true)) := by
  intro htb
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  -- the slot times, as reals
  have hT : ∀ s : ℕ, ((M.voteTime S.C s : ℕ) : ℝ) = M.slotStart S.C s + Δ S ∧
      ((M.supportCutoff S.C s : ℕ) : ℝ) = M.slotStart S.C s + 2 * Δ S ∧
      ((M.viewFreeze S.C s : ℕ) : ℝ) = M.slotStart S.C s + 3 * Δ S ∧
      ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = M.slotStart S.C s + 4 * Δ S := fun s => by
    obtain ⟨h1, h2, h3, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
    exact ⟨by rw [h1]; push_cast; ring, by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring,
      by rw [h4]; push_cast; ring⟩
  have hssm : ∀ a b : ℕ, a ≤ b → ((M.slotStart S.C a : ℕ) : ℝ) ≤ M.slotStart S.C b := fun a b h => by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have htR : (tAwakeEnd : ℝ) ≤ t := by exact_mod_cast ht
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E
  rcases (rootsNameBlocksUntil_or_collision M) x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  -- Lemma 89 (`lem89_phase_upTo`), with its two rows at the last honest round opening slot's support cutoff: roots up to `t`
  -- restricted to each tick's real time, and the end from `hSeq.lastTick`
  have hLastR : ((M.supportCutoff S.C (r m * S.C.R) : ℕ) : ℝ) ≤ t := by
    have := hSeq.last
    exact_mod_cast le_trans this ht
  have hcb : M.supportCutoff S.C (r m * S.C.R) ≤ b := le_trans hSeq.last (le_trans ht htb)
  rcases (lem89_phase_upTo M F U Fx) S A x R GST tGAT tAwakeEnd m r (E.mono hcb) hNet hSkew hRedeliver (Sy.mono hcb) hΔs
      E_F hNet_F hSkew_F Sy_F hΔs_F hHoldF ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hLastR hRootsT)
      (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (le_trans (hSeq.lastTick k u c hk hc) htR) hRootsT)
      hParent hGST hThird hAwake hActive (CommitteeSleepinessUntil.mono M hCommittees ht) hSeq
      (fun k u c hk hc => hSeq.lastTick k u c hk hc) hOpenings with
    hCol | ⟨j, s₀, B₀, hjm, hs₀, hBase, hBaseSaved, hB₀, hOld, hPhase, hCachesVt, hLast⟩
  · exact Or.inl hCol
  right; right
  have hmono := r_lt_of_lt_of_mono r m hSeq.mono
  -- the first slot of the last opening is at least two slots after `s₀`
  have hsm : s₀ + 2 ≤ r m * S.C.R := by
    have h1 : (r j + 1) * S.C.R ≤ r m * S.C.R := Nat.mul_le_mul_right _ (hmono j m hjm le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  -- the first opening's slot is at most `s₀`
  have h0 : r 0 * S.C.R ≤ s₀ := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      omega
    · rw [hs₀]
      exact Nat.mul_le_mul_right _ (hmono 0 j hjpos (by omega)).le
  have hfirst := hSeq.first
  unfold healFrontSlots at hfirst
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at hfirst
  have e0 : 4 * Δ S * (r 0 * S.C.R) ≤ 4 * Δ S * s₀ := Nat.mul_le_mul_left _ h0
  have ek : 4 * Δ S * (S.C.k + 2) ≤ 4 * Δ S * (3 * S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hGST' : GST ≤ M.voteTime S.C s₀ := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    omega
  have hAnc : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1) := by
    rw [anchorCW_eq]
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add_one (4 * Δ S) s₀]
    omega
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ := (gst_sync_of_anchor M F U) S hGST hΔs hAnc (by linarith)
  have hB₀slot : s₀ ≤ B₀.slot := hB₀.ge
  -- the updaters of `s₀`: every validator honest at the support cutoff of slot `s₀ + 1` (`hActive`)
  have hscE : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (hcm _ _ (by omega)) hSeq.last
  have hdw0 : tGAT ≤ M.dutyWindowStart S.C s₀ := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s₀ hAnc
    omega
  have hUpd : ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) → v ∈ updaterAt M S A x s₀ :=
    fun v hv => (hActive s₀ hdw0 hscE v hv).2
  -- the step `i₂`: the tick of the last opening's proposer to that opening's support cutoff, an updater of the
  -- slot before (`hActive`), at a real time at most `tAwakeEnd` (`hSeq.lastTick`)
  have hsm1 : r m * S.C.R - 1 + 1 = r m * S.C.R := by omega
  have hdwm : tGAT ≤ M.dutyWindowStart S.C (r m * S.C.R - 1) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT
      (r m * S.C.R - 1) (by
        rw [hsm1]
        exact le_trans hAnc ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
          (by omega)))
    omega
  obtain ⟨-, hpU⟩ := hActive (r m * S.C.R - 1) hdwm (by rw [hsm1]; exact hSeq.last)
    (S.P.proposer (r m * S.C.R)) (by rw [hsm1]; exact hSeq.honest m le_rfl)
  have hpU' := hpU
  unfold updaterAt at hpU'
  obtain ⟨i₂, hi₂l, -⟩ := (Activity.mem_activeThroughoutToTick).1 hpU'
  rw [hsm1] at hi₂l
  have hi₂a := (E.tick_active i₂ _ _ hi₂l).2
  have hi₂E : x.time i₂ ≤ tAwakeEnd := hSeq.lastTick i₂ _ _ hi₂l le_rfl
  have hsc : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) < x.time i₂ := by
    obtain ⟨-, hc1, -, hs1⟩ := hT (s₀ + 1)
    obtain ⟨-, hcm', -, -⟩ := hT (r m * S.C.R)
    have := hssm (s₀ + 1 + 1) (r m * S.C.R) (by omega)
    linarith [hi₂a.1]
  -- every tick to the healed slot's update is before `i₂`: at most `cut(s₀ + 1) + ΔClockBehind`,
  -- while `i₂` is at least `cut(s_m) − ΔClockAhead` with `s₀ + 2 ≤ s_m`
  have hscTick : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s₀ + 1)) →
      x.time k < x.time i₂ := by
    intro k u hk
    have h1 := (E.tick_active k u _ hk).2.2
    obtain ⟨-, hc1, -, hs1⟩ := hT (s₀ + 1)
    obtain ⟨-, hcm', -, -⟩ := hT (r m * S.C.R)
    have := hssm (s₀ + 1 + 1) (r m * S.C.R) (by omega)
    linarith [hi₂a.1]
  have hx2s : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → x.time i₂ < M.slotStart S.C s ∧
      ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.slotStart S.C s) → x.time i₂ < x.time k := by
    intro s hs
    have hlt : r m * S.C.R < s := by
      by_contra hle
      push_neg at hle
      have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hle
      have h2 := hSeq.last
      obtain ⟨-, h3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
        (r m * S.C.R)
      omega
    have hss := hssm (r m * S.C.R + 1) s hlt
    obtain ⟨-, hc, -, h4⟩ := hT (r m * S.C.R)
    refine ⟨by linarith [hi₂a.2], fun k u hk => ?_⟩
    -- a tick to the start of slot `s` is at least `st(s) − ΔClockAhead`
    have h1 := (E.tick_active k u _ hk).2.1
    linarith [hi₂a.2]
  have hi₂vf : x.time i₂ < M.viewFreeze S.C (r m * S.C.R) := by
    obtain ⟨-, hc, hvf, -⟩ := hT (r m * S.C.R)
    linarith [hi₂a.2]
  -- the caches: each validator honest at a step `j` from `i₂` on ticked to the vote time of slot `s_m` before
  -- `i₂` (awake and honest through that tick's window, `hAwake`), where Lemma 89 puts its caches on the chain;
  -- Lemma 84 from that tick on
  have hcut0 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ t := le_trans hsc.le (le_trans hi₂E htR)
  have hvt_lt : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.voteTime S.C (r m * S.C.R)) →
      x.time k < x.time i₂ := by
    intro k u hk
    have h1 := (E.tick_active k u _ hk).2.2
    obtain ⟨hv, hc, -, -⟩ := hT (r m * S.C.R)
    linarith [hi₂a.1]
  have hfirstm : (tGAT : ℝ) ≤ M.slotStart S.C (r m * S.C.R) := by
    have h1 : tGAT ≤ M.slotStart S.C (r m * S.C.R) :=
      le_trans (le_trans (Nat.le_add_right _ _) hSeq.first)
        ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    exact_mod_cast h1
  have hvt1 : 1 ≤ M.voteTime S.C (r m * S.C.R) := by
    obtain ⟨h1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
    omega
  have hCachesBoth : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u) ∧
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st (j + 1) u) := by
    intro j u hj hjt hu
    obtain ⟨hv, hc, -, -⟩ := hT (r m * S.C.R)
    have hwin : ∀ i : ℕ, ((M.voteTime S.C (r m * S.C.R) : ℕ) : ℝ) - ΔClockAhead ≤ x.time i →
        x.time i ≤ ((M.voteTime S.C (r m * S.C.R) : ℕ) : ℝ) + ΔClockBehind → u ∈ A.active i := by
      intro i h1 h2
      have hij : i < j := (lt_of_time_lt M) x R (by linarith [hi₂a.1])
      have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_le hij.le hu
      have hti := (time_le_succ M) x R i
      exact Activity.mem_active.2 ⟨hAwake i u (by linarith) (by linarith) hui, hui⟩
    obtain ⟨ku, hku, -, -⟩ := E.tick_of_active _ hvt1 u hwin
    have hkui := hvt_lt ku u hku
    have hkuj : ku < j := (lt_of_time_lt M) x R (lt_of_lt_of_le hkui hj)
    have hke : x.tickStep u (M.voteTime S.C (r m * S.C.R)) = ku := (tickStep_eq_of_lbl M) x E hku
    have hStart : CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st ku u) := by
      have h1 := hCachesVt u (by rw [hke]; exact hku) (by
        rw [hke]
        exact Activity.not_mem_corruptedAtTime.2 fun k hk => E.not_mem_corrupted_of_le
          ((lt_of_time_lt M) x R (lt_of_le_of_lt hk (lt_of_lt_of_le hkui hj))).le hu)
      rwa [show x.tickInput u (M.voteTime S.C (r m * S.C.R)) = x.st ku u by
        unfold Trace.tickInput; rw [hke]] at h1
    have hFrom := (lem84_caches_stay_on_chain_from M F U Fx) S A x R s₀ (M.supportCutoff S.C (s₀ + 1))
      (M.chainStateOf S.C B₀).h ku t u E hRootsT (hAdvQ.mono (max_le le_rfl hcut0))
      ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E) hOld hStart
    -- the state at step `j`, and the state step `j` leaves
    refine ⟨hFrom j hkuj.le hjt hu, ?_⟩
    rcases (step_succ_cases M F) x R E j with ⟨-, h⟩ | ⟨ht₁, hc₁⟩
    · rw [h u]
      exact hFrom j hkuj.le hjt hu
    · exact hFrom (j + 1) (by omega) (by rw [ht₁]; exact hjt) (by rw [hc₁]; exact hu)
  have hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st (j + 1) u) :=
    fun j u h1 h2 h3 => (hCachesBoth j u h1 h2 h3).2
  -- the frames at the slots after `s₀`
  have hStay₀ : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs) := fun σ h1 => hStay σ (le_trans h0 h1)
  have hFr := (frames_after_healed_slot_until_upTo M F U Fx) S A x R GST s₀ (r m * S.C.R) i₂
    (M.chainStateOf S.C B₀).h (anchorCW S tGAT) t B₀ (E.mono htb) hNet hSkew hRedeliver (Sy.mono htb) hΔs hRootsT hParent hAdvQ hGSTs
    hCommittees hCommitteesTick hStay₀ hAnc hB₀slot hBase hBaseSaved hOld hi₂vf hCaches hPhase hLast
  have hKey := (frames_at_slot_after_healed_until_upTo M F U Fx) S A x R GST s₀ (r m * S.C.R) i₂
    (M.chainStateOf S.C B₀).h (anchorCW S tGAT) t B₀ (E.mono htb) hNet hSkew hRedeliver (Sy.mono htb) hΔs hRootsT hParent hAdvQ hGSTs
    hCommittees hStay₀ hAnc hB₀slot hBase hBaseSaved hOld hi₂vf hCaches hPhase hLast
  refine ⟨s₀, i₂, B₀, ⟨hsc, hscTick⟩, hi₂E, hx2s, h0, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld,
    fun j u h1 h2 h3 => (hCachesBoth j u h1 h2 h3).1, hCaches, hFr.1, hFr.2, ?_⟩
  -- the chain clause, at a slot `σ` some validator updated by `t`
  intro σ k u hk hkt
  have hka := E.tick_active k u _ hk
  have hcsR : ((M.supportCutoff S.C σ : ℕ) : ℝ) + ΔClockBehind ≤ t := by
    obtain ⟨-, hc, -, hs⟩ := hT σ
    obtain ⟨-, hc1, -, -⟩ := hT (σ + 1)
    linarith [hka.2.1]
  have hKs := hCommitteesTick k u _ hk hkt
  -- roots up to every tick to a clock value at most the support cutoff of slot `σ`
  have hRootsσ : ∀ (k' : ℕ) (u' : V) (c : ℕ), x.lbl k' = Event.tick u' c → c ≤ M.supportCutoff S.C σ →
      RootsNameBlocksUntil M A x (x.time k') := fun k' u' c hk' hc => by
    have h1 := (E.tick_active k' u' c hk').2.2
    have h2 : (c : ℝ) ≤ M.supportCutoff S.C σ := by exact_mod_cast hc
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRootsT
  -- two confirmations of slot `σ ≥ s₀` saved by updaters that ticked by `t` are compatible (Lemma 32)
  have hCompat : s₀ ≤ σ → ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
      ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
      C'.compatible C'' = true := by
    intro hσ v hv hvt C' hC' v' hv' hv't C'' hC''
    have hcΔb : M.supportCutoff S.C σ + Δ S ≤ b := by
      have h1 : ((M.supportCutoff S.C σ : ℕ) : ℝ) + Δ S ≤ t := by
        obtain ⟨-, hc, -, hs⟩ := hT σ
        obtain ⟨-, hc1, -, -⟩ := hT (σ + 1)
        linarith [hka.2.1]
      have h2 : M.supportCutoff S.C σ + Δ S ≤ t := by exact_mod_cast h1
      omega
    refine (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state_upTo M F U) S A x R
      GST σ v v' C' C'' (E.mono hcΔb) hNet hSkew hRedeliver (Sy.mono hcΔb) hΔs
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (max_le hvt hv't) hRootsT)
      ?_ hv hv' hC' hC''
    have := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
    have := hcm _ _ hσ
    omega
  rcases Nat.lt_or_ge s₀ σ with hσ | hσ
  · -- after the healed slot: the frames up to `σ` (`frames_at_slot_after_healed_until`), the chain before `σ`
    -- (`lem81_chain_before`), and the slot-`σ` confirmations extending it (Lemma 78 from the votes clause)
    have hcσt : M.supportCutoff S.C σ ≤ t := by
      have : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ t := by linarith
      exact_mod_cast this
    have hcσb : M.supportCutoff S.C σ ≤ b := le_trans hcσt htb
    have hFrσ : ∀ σ' : ℕ, s₀ < σ' → σ' ≤ σ →
        (∀ w ∈ honestActiveAt M S A x σ', VoterFrameOnChainAt M S A x s₀ σ' w) ∧
        (∀ v ∈ updaterAt M S A x σ', x.time (x.tickStep v (M.supportCutoff S.C (σ' + 1))) ≤ t →
          UpdaterFinalizedOnChainAt M S A x s₀ σ' v) := fun σ' h1 h2 =>
      hKey σ' h1 (by
          have : ((M.supportCutoff S.C σ' : ℕ) : ℝ) ≤ M.supportCutoff S.C σ := by exact_mod_cast hcm _ _ h2
          linarith)
        (CommitteeSleepinessUntil.mono M hKs (hcm _ _ (by omega)))
    -- an updater of a slot before `σ` ticks to the next support cutoff by `t`
    have hUpdBefore : ∀ σ' : ℕ, σ' < σ → ∀ v ∈ updaterAt M S A x σ',
        x.time (x.tickStep v (M.supportCutoff S.C (σ' + 1))) ≤ t := by
      intro σ' h v hv
      have hv' := hv
      unfold updaterAt at hv'
      obtain ⟨k', hk', -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
      rw [(tickStep_eq_of_lbl M) x E hk']
      have h1 := (E.tick_active k' v _ hk').2.2
      have h2 : ((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) ≤ M.supportCutoff S.C σ := by exact_mod_cast hcm _ _ h
      linarith
    have hChainσ : ConfirmationsChainBefore M S A x s₀ σ :=
      (lem81_chain_before_upTo M F U) S A x R GST s₀ (anchorCW S tGAT) σ B₀ (E.mono hcσb) hNet hSkew hRedeliver
        (Sy.mono hcσb) hΔs hRootsσ hParent
        hOwner hGSTs (CommitteeSleepinessUntil.mono M hCommittees hcσt) hAnc hB₀slot hBase hBaseSaved
        (fun s h1 h2 => (hFrσ s h1 h2.le).1) (fun s h1 h2 v hv => (hFrσ s h1 h2.le).2 v hv (hUpdBefore s h2 v hv))
    refine ⟨hChainσ, fun v hv hvt C' hC' => ⟨fun C hC => ?_, fun hs₀σ => hCompat hs₀σ v hv hvt C' hC'⟩⟩
    obtain ⟨σ₁, rfl⟩ : ∃ σ₁, σ = σ₁ + 1 := ⟨σ - 1, by omega⟩
    have hCom := (committee_majority_of_sleepiness M F) S A x (anchorCW S tGAT) (σ₁ + 1) hKs
      (le_trans hAnc ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (by omega))) le_rfl
    have hVotes := (votes_clause_after_healed_slot_upTo M F U) S A x R GST s₀ (anchorCW S tGAT) σ₁ B₀ (E.mono hcσb)
      hNet hSkew hRedeliver (Sy.mono hcσb) hΔs ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (by exact_mod_cast hcσt) hRootsT) hRootsσ hParent hGSTs hKs hAnc hB₀slot hBase hBaseSaved (by omega)
      (fun s h1 h2 => (hFrσ s h1 h2).1)
      (fun s h1 h2 v hv => (hFrσ s h1 (by omega)).2 v hv (hUpdBefore s (by omega) v hv))
    exact (votes_clause_updater_confirmation_upTo M F U) S A x R GST (σ₁ + 1) (honestActiveAt M S A x (σ₁ + 1))
      (OnHonestChainBefore M S A x s₀ (σ₁ + 1)) v (E.mono hcσb) hNet hSkew hRedeliver (Sy.mono hcσb) hΔs hRootsσ hParent hOwner
      (le_trans hGSTs (hcm _ _ (by omega))) (subset_refl _) hCom hVotes hv ((hFrσ (σ₁ + 1) hσ le_rfl).2 v hv hvt)
      C hC C' hC'
  · -- at or before the healed slot: the chain before `σ` and the honest chain before `σ` are empty
    refine ⟨by intro s s'' v v' C C' hs hss hs''; exact absurd hs'' (by omega), fun v hv hvt C' hC' =>
      ⟨fun C hC => by obtain ⟨σ', hlt, hs, -⟩ := hC; omega, fun hs₀σ => hCompat hs₀σ v hv hvt C' hC'⟩⟩

end GoldilocksCorrectness.Record.Proofs.Executions

