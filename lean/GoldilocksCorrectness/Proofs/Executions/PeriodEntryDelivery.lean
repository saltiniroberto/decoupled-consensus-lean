module
public import GoldilocksCorrectness.Proofs.Executions.PeriodCertificateEntry
public import GoldilocksCorrectness.Proofs.Executions.PeriodFastSupport
public import GoldilocksCorrectness.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Proofs.Routines.Attestation

@[expose] public section

/-! kit statements, new. The audited statement is in
`Statements/Executions/PeriodEntryDeliveryStatements.lean`.

- `fast_blocks_ancestorEq_saved_of_updater`: the fast blocks an updater of slot `s'` holds right
  after its update are ancestors of, or are, the confirmation it saved for `s'`
  (`fast_blocks_ancestorEq_saved`, connected to the execution by `update_state_of_duty`);
- `cert_entry_held_before_freeze`: at a slot whose previous votes were not owed inside the period,
  a certified block of a chain an honest active voter holds before its vote, of chain-state height
  greater than `B`'s and compatible with the voter's finalized block, was in the voter's tree
  before its view froze.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_succ_lt_supportCutoff one_le_Δ slotStart_eq slotStart_mono supportCutoff_eq
  supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_height_mono)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_of_ancestorEq_compatible
  fast_blocks_ancestorEq_saved)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The fast blocks of an update are ancestors of its saved confirmation.** For an updater `u`
of slot `s'`, when the state right after its tick at `supportCutoff S (s' + 1)` has saved `C'` as
the confirmation of slot `s'`, every fast block of that state is `C'` or an ancestor of `C'`.

Why: the tick ran the confirmation update of slot `s' + 1`, whose answer's saved confirmation and
fast blocks are the state's (`update_state_of_duty`); the update's fast blocks are blocks of its
path, the ancestors of the confirmation it saves (`fast_blocks_ancestorEq_saved`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the updater;
  `C'`: the saved confirmation. -/
theorem fast_blocks_ancestorEq_saved_of_updater (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' : ℕ) (u : V) (C' : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hu : u ∈ updaterAt S Sched s')
    (hSaved : (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.saved_confirmation s' = some C') :
    ∀ D ∈ (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.fast_blocks, D.AncestorEq C' := by
  intro D hD
  have hwin := updaterAt_window S Sched s' u hMono hu
  have hdc := dutyWindowStart_succ_lt_supportCutoff S s'
  obtain ⟨hAwc, hHonc⟩ := hwin _ hdc.le le_rfl
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_le_dutyWindowStart_b S Sched x (s' + 1)
    (supportCutoff S (s' + 1)) u hDiv hMono hdc (fun t' h1 h2 => (hwin t' h1 h2).1) hHonc
  obtain ⟨A'', hUpd, hsc, hfb, -, -⟩ :=
    update_state_of_duty S Sched x s' u hDiv ⟨hAwc, hHonc⟩ ⟨τ, hτ, hτle⟩
  rw [hfb] at hD
  rw [hsc] at hSaved
  exact fast_blocks_ancestorEq_saved S.C S.P _ A'' _ _ (s' + 1) C' (Nat.succ_ne_zero s') hUpd
    hSaved D hD

/-- **Kit fact K3: the certified entry reaches the voter before its view freezes.** The proof;
the audited statement is in `Statements/Executions/PeriodEntryDeliveryStatements.lean`. With
`s' = σ + 1`: K1 (`cert_entry_held_by_attester`) at the step before the vote time of `s'` gives an
honest attester `uₐ`, an updater of `sₐ` with `sₐ + 1 ≤ σ`, that held `T` before its tick at
`supportCutoff S (sₐ + 1)`, `T` an ancestor of a fast block `F` of that update. `u` is awake and
honest from `voteTime S σ` to `viewFreeze S σ`. When `b₁ ≤ supportCutoff S σ`, Lemma 89's delivery
(`mem_T_before_add_delay_of_held_at`) from the attester, with `GST` moved to `max b₁ GST`. When
`supportCutoff S σ ≤ b₀`: its twin before the period (`mem_T_before_add_delay_of_held_at_upTo`) at
`voteTime S σ`, from the attester when `sₐ + 1 ≤ σ − 1`; when `sₐ + 1 = σ = s + 1`, `F` is an
ancestor of the hand-over confirmation `B`, against `hTB`; when `sₐ + 1 = σ ≥ s + 2`, from an
honest active supporter of `F` at slot `sₐ` (K2, `fast_block_has_honest_supporter`).

The variables:
- `P`: the hypotheses; `s'`: the slot of the vote; `u`: the voter; `Y`: the held block; `T`: the
  certified block; `h`: its height. -/
theorem cert_entry_held_before_freeze {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (u : V)
    (Y T : Block V) (h : Height)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s'))
    (hs' : s + 2 ≤ s') (hgood : ¬ VotesOwedInPeriod S b₀ b₁ s')
    (hu : u ∈ honestActiveAt S Sched s')
    (hY : Y ∈ (stateBefore x (voteTime S s') u).S.T) (hTY : T.AncestorEq Y)
    (hJ : ProgressCertOn Y h T) (hTB : (chainStateOf S.C B).h < (chainStateOf S.C T).h)
    (hF : (stateBefore x (viewFreeze S (s' - 1)) u).S.F.compatible T = true) :
    T ∈ (stateBefore x (viewFreeze S (s' - 1)) u).S.T := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hF ⊢
  have hgood' : supportCutoff S σ ≤ b₀ ∨ b₁ ≤ supportCutoff S σ := by
    unfold VotesOwedInPeriod at hgood
    simp only [Nat.add_sub_cancel] at hgood
    omega
  -- the times of slots `σ`, `σ + 1`, `σ + 2`, over the atom `slotStart S σ`
  have hss1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss2 : slotStart S (σ + 1 + 1) = slotStart S (σ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvtσ := voteTime_eq S σ
  have hscσ := supportCutoff_eq S σ
  have hvfσ := viewFreeze_eq S σ
  have hvt1 := voteTime_eq S (σ + 1)
  have hsc2 := supportCutoff_eq S (σ + 1 + 1)
  have hvt2 := voteTime_eq S (σ + 1 + 1)
  -- the step before the vote time of `s'`, and `u` honest there
  have hv1 : 1 ≤ voteTime S (σ + 1) := by omega
  have hjt := time_stepBefore_add_one x P.hDiv hv1
  have huAdv : u ∉ Sched.adv ((supportCutoff S (σ + 1 + 1) : ℕ) : Int) :=
    (Finset.mem_sdiff.1 hu).2
  have hw : u ∉ Sched.adv ((x[stepBefore x (voteTime S (σ + 1))].time : ℕ) : Int) :=
    fun h' => huAdv (P.hMono _ _ (by omega) h')
  -- K1: the honest attester
  obtain ⟨sₐ, uₐ, Fₐ, htₐ, huₐ, hHonₐ, hFₐ, hTF, hTₐ⟩ :=
    cert_entry_held_by_attester S Sched x (stepBefore x (voteTime S (σ + 1))) u Y T h P.hDiv
      P.hMono P.hU (P.hAdvQ _) (hRoots.mono (by omega)) hw hY hTY hJ
  -- its tick is at or before the support cutoff of slot `σ`
  have hsₐ : sₐ + 1 ≤ σ := by
    have h1 := supportCutoff_eq S (sₐ + 1)
    have h2 := voteTime_eq S (sₐ + 1)
    have h4 := slotStart_eq S (sₐ + 1)
    have h5 := slotStart_eq S (σ + 1)
    by_contra hc
    have hle : σ + 1 ≤ sₐ + 1 := by omega
    have := Nat.mul_le_mul_left (4 * Δ S) hle
    omega
  -- `uₐ` is honest at the step before its tick
  have hc1ₐ : 1 ≤ supportCutoff S (sₐ + 1) := by rw [supportCutoff_eq, voteTime_eq]; omega
  have hjₐ := time_stepBefore_add_one x P.hDiv hc1ₐ
  have hHonₐ' : uₐ ∉ Sched.adv ((x[stepBefore x (supportCutoff S (sₐ + 1))].time : ℕ) : Int) :=
    fun h' => hHonₐ (P.hMono _ _ (by omega) h')
  -- the receiver: `u` is awake and honest from `voteTime S σ` to `viewFreeze S σ`
  have hσ1 : 1 ≤ σ := by omega
  have hdws : dutyWindowStart S (σ + 1) ≤ voteTime S σ := by
    have h1 := dutyWindowStart_le_supportCutoff S (s := σ + 1) (s' := σ - 1) (by omega)
    have h2 := supportCutoff_eq S (σ - 1)
    have h3 := voteTime_eq S (σ - 1)
    have h4 : slotStart S (σ - 1 + 1) = slotStart S (σ - 1) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    have h5 : σ - 1 + 1 = σ := by omega
    rw [h5] at h4
    omega
  have hwin := honestActiveAt_window S Sched (σ + 1) u P.hMono hu
  have hrecv : ∀ t' : ℕ, voteTime S σ ≤ t' → t' ≤ viewFreeze S σ →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int) :=
    fun t' h1 h2 => hwin t' (le_trans hdws h1) (by omega)
  rcases hgood' with hb | hb
  · -- the previous votes were due before the period
    have hGSTσ : GST ≤ voteTime S σ := le_trans P.hGST (voteTime_mono S (by omega))
    have hscvf : supportCutoff S σ ≤ viewFreeze S σ := by omega
    have hgrow := stateBefore_grows x P.hDiv u hscvf
    have twin : ∀ (t₁ : ℕ) (v : V), t₁ ≤ voteTime S σ →
        v ∉ Sched.adv ((x[stepBefore x t₁].time : ℕ) : Int) → T ∈ (stateBefore x t₁ v).S.T →
        T ∈ (stateBefore x (viewFreeze S σ) u).S.T := by
      intro t₁ v ht₁ hv hT
      have hvsc : voteTime S σ + Δ S = supportCutoff S σ := hscσ.symm
      have hcompat : (stateBefore x (voteTime S σ + Δ S) u).S.F.compatible T = true := by
        rw [hvsc]
        exact compatible_of_ancestorEq_compatible hgrow.2.1 hF
      have hmem := mem_T_before_add_delay_of_held_at_upTo P.hDiv P.hMono (t := voteTime S σ)
        ((synchronyFromWakeUpTo_of_outside P.hSync).mono (by omega))
        ((catchUpOnWakeUpTo_of_outside P.hCatch).mono (by omega))
        (hRoots.mono (by omega)) P.hParent ht₁ hGSTσ hv hT
        (fun t' h1 h2 => hrecv t' h1 (by omega)) hcompat
      rw [hvsc] at hmem
      exact hgrow.1 hmem
    rcases Nat.lt_or_ge (sₐ + 1) σ with hlt | hge
    · -- the attester's tick is at or before `voteTime S σ`
      have htv : supportCutoff S (sₐ + 1) ≤ voteTime S σ := by
        have h1 := supportCutoff_eq S (sₐ + 1)
        have h2 := voteTime_eq S (sₐ + 1)
        have h3 : slotStart S (sₐ + 1 + 1) = slotStart S (sₐ + 1) + 4 * Δ S := by
          rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
        have h4 := slotStart_mono S (show sₐ + 1 + 1 ≤ σ by omega)
        omega
      exact twin _ uₐ htv hHonₐ' hTₐ
    · have heq : sₐ + 1 = σ := by omega
      rcases Nat.lt_or_ge (s + 1) σ with hσs | hσs
      · -- `σ ≥ s + 2`: an honest active supporter of `Fₐ` at slot `sₐ`
        obtain ⟨v, hv, H_v, hHv, hFH⟩ := fast_block_has_honest_supporter S Sched x anchor sₐ uₐ
          P.hDiv P.hMono P.hOwner (hRoots.mono (by rw [heq]; omega)) P.hSleepK
          (le_trans P.hAnchor (slotStart_mono S (by omega))) huₐ Fₐ hFₐ
        have hTv : T ∈ (stateBefore x (voteTime S sₐ) v).S.T :=
          ancestors_mem_T_of_exec S Sched x _ v H_v T hHv (ancestorEq_trans hTF hFH)
        have hv1' : 1 ≤ voteTime S sₐ := by rw [voteTime_eq]; omega
        have hjv := time_stepBefore_add_one x P.hDiv hv1'
        have hvsc : voteTime S sₐ ≤ supportCutoff S (sₐ + 1) := by
          have := voteTime_mono S (show sₐ ≤ sₐ + 1 by omega)
          rw [supportCutoff_eq]
          omega
        have hvH : v ∉ Sched.adv ((x[stepBefore x (voteTime S sₐ)].time : ℕ) : Int) :=
          fun h' => (Finset.mem_sdiff.1 (Finset.mem_inter.1 hv).1).2 (P.hMono _ _ (by omega) h')
        exact twin _ v (voteTime_mono S (by omega)) hvH hTv
      · -- `σ = s + 1`: the hand-over update, whose fast blocks are ancestors of `B`
        have hsₐs : sₐ = s := by omega
        subst hsₐs
        exfalso
        have hFB := fast_blocks_ancestorEq_saved_of_updater S Sched x sₐ uₐ B P.hDiv P.hMono huₐ
          (P.hHand.2.1 uₐ huₐ).1 Fₐ hFₐ
        have hle := chainStateOf_height_mono S.C (ancestorEq_trans hTF hFB)
        exact absurd hle (Nat.not_le.mpr hTB)
  · -- the previous votes were due after the period
    have hvf : supportCutoff S σ + Δ S = viewFreeze S σ := by omega
    have htσ : supportCutoff S (sₐ + 1) ≤ supportCutoff S σ := supportCutoff_mono S hsₐ
    have hGST' : max b₁ GST ≤ supportCutoff S σ :=
      max_le hb (le_trans P.hGST (by
        have := voteTime_mono S (show s + 1 ≤ σ by omega)
        omega))
    have hmem := mem_T_before_add_delay_of_held_at P.hDiv P.hMono (t := supportCutoff S σ)
      (synchronyFromWake_of_outside_after P.hSync) (catchUpOnWake_of_outside_after P.hCatch)
      (hRoots.mono (by omega)) P.hParent htσ hGST' hHonₐ' hTₐ
      (fun t' h1 h2 => hrecv t' (by omega) (by omega)) (by rw [hvf]; exact hF)
    rw [hvf] at hmem
    exact hmem

end GoldilocksCorrectness.Proofs.Executions
