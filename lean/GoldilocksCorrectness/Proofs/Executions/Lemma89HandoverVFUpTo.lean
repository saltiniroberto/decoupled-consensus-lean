module
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverVF
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamilyUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HealedRoundUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb5UpTo

@[expose] public section

/-!
# `Lemma89HandoverVF.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89HandoverVF.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `F_compat_vf`, `root_compat_vf`, `viable_candidate_vf`, `voterFrame_source_vf`,
  `voterFrame_at_last_opening`, `handover_after_fast_block_vf`, `lem89_phase`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_mono supportCutoff_eq
  supportCutoff_mono times_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_T_h_spec
  chainStateOf_height_mono entry_eq_of_compatible lem47_chain_state_heights
  round_justified_of_spacing3)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_ancestorEq_of_tall floor_le_h_max)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)
open GoldilocksCorrectness.Statements.Routines (TreeClosed)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_h fg_contest_spec
  head_height_floor_of_not_contested root_cases)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn CountedVotes
  ProgressCertOn JustificationCertOn FrameShape lem49_tick_attests RecordConsistent)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible ancestorEq_of_parent?
  ancestorEq_node_iff create_attestation_timeout state_transition_cases)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- **The finalized block is compatible with every line source (copy with the end at slot
`σ + 1`).** `F_compat` with its end premise `supportCutoff S (σ + 2) ≤ tAwakeEnd` replaced by the
two bounds its proof reads, `supportCutoff S (σ + 1) ≤ tAwakeEnd` and `t ≤ tAwakeEnd`: at a time
`t ≥ 1` up to the support cutoff of slot `σ + 2` and up to `tAwakeEnd`, when the invariant holds
at every slot up to `σ`, an honest validator's finalized block is compatible with every line source
of a slot at most `σ`. The body is `F_compat`'s.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem F_compat_vf (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (ht1 : 1 ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ) :
    (stateBefore x t w).S.F.compatible X = true := by
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd1
  obtain ⟨D, hD, hFD⟩ :=
    GoldilocksCorrectness.Statements.Executions.finalizedFromChain_of_exec S Sched x
      (stepBefore x t) w
  show (x[stepBefore x t][w].st).S.F.compatible X = true
  rw [hFD]
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have hjE : x[stepBefore x t].time ≤ tAwakeEnd := by omega
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast htj.le) h)
  by_cases hle : (chainStateOf S.C D).h_F ≤ H₂
  · have htv : x[stepBefore x (aR S r)].time ≤ aR S r := time_stepBefore_le x _
    have hv' : v ∉ Sched.adv (x[stepBefore x (aR S r)].time : Int) :=
      fun h => P.hv (P.hMono _ _ (by exact_mod_cast htv) h)
    have hT : AdversaryFewerThanThirdUntil Sched (validator_count V)
        (max (x[stepBefore x t].time : Int) (x[stepBefore x (aR S r)].time : Int)) :=
      adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast hjE)
        (by exact_mod_cast (show x[stepBefore x (aR S r)].time ≤ tAwakeEnd by
          have : aR S r ≤ tAwakeEnd := hEndR
          omega))) P.hThird
    have hFL := lem68_honest_past_finalized S Sched x P.hU P.hRoots (stepBefore x t)
      (stepBefore x (aR S r)) w v D L hT hw' hv' hD (P.L_held_v hEndR).2
      (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE (le_trans htv hEndR))
    exact compatible_of_ancestorEq_compatible hFL
      (P.sources_compatible hG hEnd1 (P.source_L hEndR) hX hσ hμ)
  · have hlt : H₂ < (chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (chainStateOf S.C D).F ∈ (x[stepBefore x t][w].st).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w D _ hD hFanc
    obtain ⟨μ', E, hcut, hE, -, -, hEr⟩ := P.cert_source hjE hD
      (progressCertOn_of_justificationCertOn hJC) hlt
    have hμ' : μ' ≤ σ := by
      by_contra h
      have := supportCutoff_mono S (show σ + 2 ≤ μ' + 1 by omega)
      omega
    have hFE : (chainStateOf S.C D).F = E :=
      P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hFT⟩
        (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
    rw [hFE]
    exact P.sources_compatible hG hEnd1 hE hX hμ' hμ

/-- **The root is compatible with every line source (copy with the end at slot `σ + 1`).**
`root_compat` with its end premise `supportCutoff S (σ + 2) ≤ tAwakeEnd` replaced by
`supportCutoff S (σ + 1) ≤ tAwakeEnd` and `t ≤ tAwakeEnd`: from the view freeze of slot `r * R`
to the support cutoff of slot `σ + 2` and up to `tAwakeEnd`, when the invariant holds at every slot
up to `σ`, an honest validator's fork-choice root is compatible with every line source of a slot at
most `σ`. The body is `root_compat`'s, calling `F_compat_vf`.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem root_compat_vf (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (ht0 : viewFreeze S (r * S.C.R) ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ) :
    (get_fc_root (stateBefore x t w).S).compatible X = true := by
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd1
  have ht1 : 1 ≤ t := by
    obtain ⟨-, -, hf0, -, hΔ⟩ := times_eq S (r * S.C.R)
    omega
  obtain ⟨hLT, hσL, hM⟩ := P.L_tall hEndR ht0 hw
  by_cases hR : get_fc_root (stateBefore x t w).S = (stateBefore x t w).S.F
  · rw [hR]
    exact P.F_compat_vf hG hσ hEnd1 htE ht1 ht hw hX hμ
  have key : (stateBefore x t w).S.h_max = (stateBefore x t w).S.h_j + 1 ∧
      get_fc_root (stateBefore x t w).S = (stateBefore x t w).S.J := by
    rcases root_cases (stateBefore x t w).S with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have hjE : x[stepBefore x t].time ≤ tAwakeEnd := by omega
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast htj.le) h)
  rw [key.2]
  by_cases hlt : H₂ < (stateBefore x t w).S.h_j
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hD' : D ∈ (x[stepBefore x t][w].st).S.T := hD
    have hJT : (chainStateOf S.C D).J ∈ (x[stepBefore x t][w].st).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w D _ hD' hJanc
    obtain ⟨μ', E, hcut, hE, -, -, hEr⟩ := P.cert_source hjE hD'
      (progressCertOn_of_justificationCertOn hJC) hlt
    have hμ' : μ' ≤ σ := by
      by_contra h
      have := supportCutoff_mono S (show σ + 2 ≤ μ' + 1 by omega)
      omega
    have hJE : (chainStateOf S.C D).J = E :=
      P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hJT⟩
        (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
    rw [hJD, hJE]
    exact P.sources_compatible hG hEnd1 hE hX hμ' hμ
  · have hhj : (stateBefore x t w).S.h_j = H₂ := by
      have := key.1
      have h1 : (stateBefore x t w).S.h_j ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    have hLX := P.sources_compatible hG hEnd1 (P.source_L hEndR) hX hσ hμ
    by_cases h0 : (chainStateOf S.C D).h_j = 0
    · have hg := (chainStateOf_J_spec S.C D).2.1 h0
      rw [hJD, hg]
      exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))
    · have hJh := (chainStateOf_J_spec S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (stateBefore x t w).S.F.AncestorEq (stateBefore x t w).S.J := by
        have := F_ancestorEq_fc_root_of_stateBefore S Sched x t w
        rw [key.2] at this
        exact this
      have hFL : (stateBefore x t w).S.F.AncestorEq L := by
        rcases (compatible_iff _ _).1 (P.F_compat_vf hG hσ hEnd1 htE ht1 ht hw (P.source_L hEndR) hσ)
          with h | h
        · exact h
        · exfalso
          have h1 := chainStateOf_height_mono S.C (ancestorEq_trans h hFJ)
          rw [hJD, hJh, ← hhjD, hhj, P.hL] at h1
          exact Nat.lt_irrefl _ (Nat.lt_of_succ_le h1)
      have hRL := fc_root_ancestorEq_of_tall _ L hLT hFL (by
        rw [hσL, P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact compatible_of_ancestorEq_compatible hRL hLX

/-- **A viable block on a line source's chain (copy with the end at slot `σ + 1`).**
`viable_candidate` with its end premise `supportCutoff S (σ + 2) ≤ tAwakeEnd` replaced by
`supportCutoff S (σ + 1) ≤ tAwakeEnd` and `t ≤ tAwakeEnd`: from the vote time of slot `σ + 1` to
the support cutoff of slot `σ + 2` and up to `tAwakeEnd`, when the invariant holds at every slot up
to `σ` and an honest validator's root is a line source `X` of a slot at most `σ` or an ancestor of
it, some block `W`, `X` or a descendant of `X`, held by the validator before the view freeze of
slot `σ`, has a chain-state height at least its `head_height_floor`. The body is
`viable_candidate`'s.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem viable_candidate_vf (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (ht0 : voteTime S (σ + 1) ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (get_fc_root (stateBefore x t w).S).AncestorEq X) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (stateBefore x (viewFreeze S σ) w).S.T ∧
      head_height_floor (stateBefore x t w).S ≤ (chainStateOf S.C W).h := by
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd1
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := times_eq S σ
  obtain ⟨hvσ1, -, -, -, -⟩ := times_eq S (σ + 1)
  have hfv : viewFreeze S σ ≤ t := by omega
  have hfR : viewFreeze S (r * S.C.R) ≤ viewFreeze S σ := by
    have := slotStart_mono S hσ
    have := viewFreeze_eq S (r * S.C.R)
    omega
  have hEndE : t ≤ tAwakeEnd := htE
  have hwf : ∀ t' : ℕ, t' ≤ t → w ∉ Sched.adv (t' : Int) :=
    fun t' h h' => hw (P.hMono _ _ (by exact_mod_cast h) h')
  -- `w`'s finalized blocks up to `t` are ancestors of `X`
  have hFX : ∀ t' : ℕ, t' ≤ t → (stateBefore x t' w).S.F.AncestorEq X := fun t' h =>
    ancestorEq_trans (stateBefore_grows x P.hDiv w h).2.1
      (ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x t w) hRX)
  -- a line source of a slot at most `σ` on `X`'s chain is held before the view freeze of `σ`
  have hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource S Sched x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ (stateBefore x (viewFreeze S σ) w).S.T := by
    intro μ₁ X₁ hX₁ hμ₁ hXX₁
    have hf1 : viewFreeze S μ₁ ≤ viewFreeze S σ := by
      have := slotStart_mono S hμ₁
      have := viewFreeze_eq S μ₁
      omega
    have := P.source_held hX₁ (le_trans (supportCutoff_mono S (by omega)) hEnd1)
      (hwf _ (by omega)) ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans
        (hFX _ (by omega)) hXX₁)))
    exact (stateBefore_grows x P.hDiv w hf1).1 this
  obtain ⟨hLT, hσL, hM⟩ := P.L_tall hEndR (le_trans hfR hfv) hw
  have hXh := hheld hX hμ (ancestorEq_refl X)
  by_cases hMle : (stateBefore x t w).S.h_max ≤ H₂ + 1
  · have hfl := floor_le_h_max (stateBefore x t w).S
    rcases (compatible_iff _ _).1 (P.sources_compatible hG hEnd1 (P.source_L hEndR) hX hσ hμ)
      with h | h
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := chainStateOf_height_mono S.C h
      rw [P.hL] at this
      unfold Height at *
      omega
    · refine ⟨L, h, (stateBefore_grows x P.hDiv w hfR).1
        (P.L_held hEndR (hwf _ (le_trans hfR hfv))), ?_⟩
      rw [P.hL]
      unfold Height at *
      omega
  · have hM2 : H₂ + 2 ≤ (stateBefore x t w).S.h_max := by unfold Height at *; omega
    have ht1 : 1 ≤ t := by omega
    obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
    obtain ⟨μ', E, hcut, hE, hEe, hEh, hEY⟩ := P.tall_entry ht1 hEndE hw hY (by rw [hYh]; exact hM2)
    have hμ' : μ' ≤ σ := by
      by_contra h
      have := supportCutoff_mono S (show σ + 2 ≤ μ' + 1 by omega)
      omega
    rw [hYh] at hEh
    -- the state is not contested
    have hnc : fg_contest (stateBefore x t w).S = false := by
      cases hcs : fg_contest (stateBefore x t w).S
      · rfl
      exfalso
      obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ := fg_contest_spec _ hcs
      have hσB : (stateBefore x t w).S.σ B = chainStateOf S.C B :=
        (lem11_node_invariant S Sched x (stepBefore x t) w).1.2.2.2.2.2.1 B hBT
      have hBh' : ((stateBefore x t w).S.σ B).h = (stateBefore x t w).S.h_max := hBh
      rw [hσB] at hBh'
      clear hBh
      have hBh := hBh'
      obtain ⟨μB, EB, hcutB, hEB, hEBe, hEBh, hEBB⟩ := P.tall_entry ht1 hEndE hw hBT
        (by rw [hBh]; exact hM2)
      have hμB : μB ≤ σ := by
        by_contra h
        have := supportCutoff_mono S (show σ + 2 ≤ μB + 1 by omega)
        omega
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
      have htj : x[stepBefore x t].time < t := by
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have := time_stepBefore_succ_le x t'
        omega
      have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) := hwf _ htj.le
      have hlt : H₂ < (chainStateOf S.C D).h_j := by
        rw [← hhjD]
        unfold Height at *
        omega
      obtain ⟨hJC, hJanc, hJh⟩ := (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified
        S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hD' : D ∈ (x[stepBefore x t][w].st).S.T := hD
      have hJT : (chainStateOf S.C D).J ∈ (x[stepBefore x t][w].st).S.T :=
        ancestors_mem_T_of_exec S Sched x _ w D _ hD' hJanc
      obtain ⟨μJ, EJ, hcutJ, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source (by omega) hD'
        (progressCertOn_of_justificationCertOn hJC) hlt
      have hμJ : μJ ≤ σ := by
        by_contra h
        have := supportCutoff_mono S (show σ + 2 ≤ μJ + 1 by omega)
        omega
      have hJE : (chainStateOf S.C D).J = EJ :=
        P.hRoots _ _ ⟨stepBefore x t, w, hw', by omega, hJT⟩
          (inHonestTreeBy_mono x (le_trans hcutJ (by omega)) (P.source_inHonestTreeBy hEJ)) hEJr
      have hEE : EJ = EB := entry_eq_of_compatible S.C hEJe hEBe (by
          rw [hEJh, hEBh, ← hhjD, hBh, hbox]
          unfold Height at *
          omega)
        (P.sources_compatible hG hEnd1 hEJ hEB hμJ hμB)
      apply hJB
      rw [hJD, hJE, hEE]
      exact hEBB
    have hfloor : head_height_floor (stateBefore x t w).S = (stateBefore x t w).S.h_max - 1 :=
      head_height_floor_of_not_contested _ hnc
    rcases (compatible_iff _ _).1 (P.sources_compatible hG hEnd1 hX hE hμ hμ') with h | h
    · exact ⟨E, h, hheld hE hμ' h, by rw [hfloor, hEh]⟩
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := chainStateOf_height_mono S.C h
      rw [hfloor, ← hEh]
      exact this

/-- **The voter half of the step's frame conditions, with the end at slot `σ + 1`.** The first two
conjuncts of `StepFrameAt` (those `stepFrame_source` proves for the vote of slot `σ + 1`), under
`supportCutoff S (σ + 1) ≤ tAwakeEnd` in place of `stepFrame_source`'s
`supportCutoff S (σ + 2) ≤ tAwakeEnd`, and for every validator `w` outside the adversary set at
the vote time of slot `σ + 1` (in place of the support cutoff of slot `σ + 2`): when the invariant
holds at every slot up to `σ`, for every line source `X` of a slot at most `σ`, `w`'s root before
that vote time is compatible with `X`, and, when the root is `X` or an ancestor of `X`, some block
of `w`'s voter tree of slot `σ + 1` that is `X` or a descendant of `X` is a viable head.

Why: the vote time of slot `σ + 1` is at most the support cutoff of slot `σ + 1`, so at most
`tAwakeEnd`; `root_compat_vf` gives the root clause, `viable_candidate_vf` a viable candidate held
before the view freeze of slot `σ`, and `proposal_viable_head_at` puts it in the voter tree.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem voterFrame_source_vf (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd)
    (hw : w ∉ Sched.adv ((voteTime S (σ + 1) : ℕ) : Int)) {μ : ℕ} {X : Block V}
    (hX : LineSource S Sched x r H₂ μ X) (hμ : μ ≤ σ) :
    (fg_to_ac (stateBefore x (voteTime S (σ + 1)) w).S).fc_root.compatible X = true ∧
    ((fg_to_ac (stateBefore x (voteTime S (σ + 1)) w).S).fc_root.AncestorEq X →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (σ + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (σ + 1)) w).S) (σ + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (σ + 1)) w).S).viable_heads ∧
          X.AncestorEq W) := by
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := times_eq S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := times_eq S (σ + 1)
  obtain ⟨-, hcσ2, -, -, -⟩ := times_eq S (σ + 2)
  have hv1c : voteTime S (σ + 1) ≤ supportCutoff S (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢
    omega
  have hvE : voteTime S (σ + 1) ≤ tAwakeEnd := by omega
  have hfR : viewFreeze S (r * S.C.R) ≤ voteTime S (σ + 1) := by
    have := slotStart_mono S hσ
    have := viewFreeze_eq S (r * S.C.R)
    omega
  refine ⟨by rw [fc_root_eq]; exact P.root_compat_vf hG hσ hEnd1 hvE hfR hv1c hw hX hμ,
    fun hR tree htree => ?_⟩
  have hR' : (get_fc_root (stateBefore x (voteTime S (σ + 1)) w).S).AncestorEq X := by
    rw [← fc_root_eq]; exact hR
  obtain ⟨W, hXW, hWT, hφ⟩ := P.viable_candidate_vf hG hσ hEnd1 hvE le_rfl hv1c hw hX hμ hR'
  obtain ⟨hWt, hWv⟩ := proposal_viable_head_at S Sched x (viewFreeze S σ) (σ + 1) w W _ _ tree
    P.hDiv hWT (by rw [Nat.add_sub_cancel]) (by omega) ⟨rfl, rfl⟩
    (ancestorEq_trans hR' hXW) hφ htree
  exact ⟨W, hWt, hWv, hXW⟩

/-- **The voter frame at a slot whose support cutoff is in the phase.** For a slot `s` with
`supportCutoff S s ≤ tAwakeEnd` and a first slot `s₀ ≥ r * R + k`, every validator `w` outside the
adversary set at the vote time of slot `s` has `VoterFrameOnChainAt S Sched x s₀ s w`.

Why, as `frames_at_phase_slots` for its voter clause: a block on the honest chain before `s` from
`s₀` is on an updater's confirmation of a slot `s'` with `s₀ ≤ s' < s`, so it is a line source of
slot `s'` (`source_conf`, `s' ≥ r * R + k`); the line invariant holds at every slot up to `s − 1`
(`lineInv_all`, which needs only `supportCutoff S s ≤ tAwakeEnd`); `voterFrame_source_vf` at
`σ := s − 1` gives the two conjuncts.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem voterFrame_at_last_opening (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    {s₀ s : ℕ} (hs₀ : r * S.C.R + S.C.k ≤ s₀) (hEnd : supportCutoff S s ≤ tAwakeEnd) {w : V}
    (hw : w ∉ Sched.adv ((voteTime S s : ℕ) : Int)) : VoterFrameOnChainAt S Sched x s₀ s w := by
  rintro B ⟨s', hs', hs₀', u, hu, C, hC, hBC⟩
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 1 := ⟨s - 1, by omega⟩
  have hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ' := fun σ' h =>
    P.lineInv_all σ' (le_trans (supportCutoff_mono S (by omega)) hEnd)
  have hsrc := P.source_conf (show r * S.C.R + S.C.k ≤ s' by omega) (hon_of_updater S Sched hu)
    (le_trans (supportCutoff_mono S (by omega)) hEnd) hC hBC
  exact P.voterFrame_source_vf hG (by omega) hEnd hw hsrc (by omega)

end PartAHypsUpTo

/-- **The hand-over after the fast block, with the voter frame at slot `s_m` (copy).** The proof;
the audited statement is in `Statements/Executions/Lemma89Statements.lean`. The statement and body
of `handover_after_fast_block` with one clause added to the conclusion: every validator outside
the adversary set at the vote time of slot `s_m := rs m * R` has
`VoterFrameOnChainAt S Sched x s₀ s_m`. Why the clause: `PartAHyps.voterFrame_at_last_opening` at
`s := s_m`, with `s₀ = rs j * R ≥ r * R + k + 2 ≥ r * R + k` and `supportCutoff S s_m ≤ tAwakeEnd`
(`HonestOpeningSeq.last`).

Roots name blocks until `supportCutoff S (rs m * S.C.R)`: the bundle `PartAHyps` is built with its
end time `supportCutoff S (rs m * S.C.R)`; C4 at the honest round opening slots `j` and `j + 1`, C1,
C3, C6, C7 and the voter frame at slot `s_m` read up to that time.

Restated with the delivery premises up to `supportCutoff S (rs m * S.C.R)`: the bound of its roots `hRoots`, the end time of the bundle `PartAHypsUpTo` it builds, for the votes (`hSync`, `hCatch`); the attestations (`hSyncF`, `hCatchF`) up to `slotStart S (rs m * S.C.R)`: C4 at the honest round opening slot `i` reads them at `slotStart S (rs (i + 1) * S.C.R)` (`opening_rises_after_fast_block_opening_upTo`), with `i + 1 ≤ m`. -/
theorem handover_after_fast_block_vf_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m r H₂ : ℕ) (rs : ℕ → ℕ) (v : V)
    (L : Block V) (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (rs m * S.C.R)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (rs m * S.C.R)))
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs m * S.C.R)))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs m * S.C.R)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs m * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- the climb's output
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks) (hL : (chainStateOf S.C L).h = H₂ + 1)
    (j : ℕ) (hj2 : j + 2 ≤ m) (hsj : r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R) :
    RootCollisionAtOpening S Sched x rs m ∨
    (∃ (j' s₀ i₁ : ℕ) (B₀ : Block V),
      j' < m ∧ s₀ = rs j' * S.C.R ∧ x[i₁].time = voteTime S (rs m * S.C.R) ∧
      HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt S Sched s₀,
        (stateBefore x (supportCutoff S (s₀ + 1) + 1) u).A.saved_confirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        ∀ w ∈ roundMembers S Sched (s + 1),
          VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w) ∧
      (∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
        CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[i₁][u].st)) ∧
      (∀ w : V, w ∉ Sched.adv ((voteTime S (rs m * S.C.R) : ℕ) : Int) →
        VoterFrameOnChainAt S Sched x s₀ (rs m * S.C.R) w)) := by
  classical
  by_cases hNoCol : RootCollisionAtOpening S Sched x rs m
  · exact Or.inl hNoCol
  right
  -- the bundle with its end time `supportCutoff S (rs m * S.C.R)`
  have P : PartAHypsUpTo S Sched x GST tGAT (supportCutoff S (rs m * S.C.R)) r H₂ v L A' := ⟨hDiv,
    hMono, hSync, hCatch, hRoots, hParent, hOwner, hU, hGST,
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hSeq.last) hThird,
    fun t' h1 h2 => hAwake t' h1 (le_trans h2 hSeq.last), hCommittees, hAnchor, hOld, hv,
    hUpdate, hFast, hL⟩
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hle : ∀ a b : ℕ, a ≤ b → b ≤ m → rs a * S.C.R ≤ rs b * S.C.R := by
    intro a b hab hbm
    rcases Nat.lt_or_ge a b with h | h
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono a b h hbm))
    · rw [show a = b by omega]
  have hss : ∀ i, i < m → rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := by
    intro i hi
    have h' : (rs i + 1) * S.C.R ≤ rs (i + 1) * S.C.R :=
      Nat.mul_le_mul_right _ (hmono i (i + 1) (by omega) hi)
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have hEndO : ∀ i, i ≤ m → supportCutoff S (rs i * S.C.R) ≤ tAwakeEnd := fun i hi =>
    le_trans (supportCutoff_mono S (hle i m hi le_rfl)) hSeq.last
  have hEndP : ∀ i, i ≤ m → supportCutoff S (rs i * S.C.R) ≤ supportCutoff S (rs m * S.C.R) :=
    fun i hi => supportCutoff_mono S (hle i m hi le_rfl)
  -- the proposals
  have hP : ∀ i, i ≤ m → ∃ B : Block V, ProposalAt S Sched x (rs i * S.C.R) B :=
    fun i hi => opening_proposal_exists S Sched x tGAT tAwakeEnd m i rs hDiv hMono hAwake
      hSeq hi
  let Bf : ℕ → Block V := fun i =>
    if hi : i ≤ m then Classical.choose (hP i hi) else Block.genesis
  have hBf : ∀ i (hi : i ≤ m), ProposalAt S Sched x (rs i * S.C.R) (Bf i) := by
    intro i hi
    simp only [Bf, dif_pos hi]
    exact Classical.choose_spec (hP i hi)
  have hnc : ∀ i, i ≤ m → ¬ RootCollisionAtProposal S Sched x (rs i * S.C.R) (Bf i) :=
    fun i hi h => hNoCol ((GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold x rs m).2
      ⟨i, hi, Bf i, hBf i hi, h⟩)
  have hheld : ∀ i (hi : i ≤ m), (Bf i).slot = rs i * S.C.R ∧
      Bf i ∈ (stateBefore x (slotStart S (rs i * S.C.R) + 1) (S.P.proposer (rs i * S.C.R))).S.T :=
    fun i hi => opening_proposal_held S Sched x tGAT tAwakeEnd m i rs (Bf i) hDiv hMono hSeq hi
      hNoCol (hBf i hi)
  have hTC : ∀ i, TreeClosed S.P S.X (stateBefore x (slotStart S (rs i * S.C.R) + 1)
      (S.P.proposer (rs i * S.C.R))).S := fun i =>
    (lem11_node_invariant S Sched x (stepBefore x (slotStart S (rs i * S.C.R) + 1)) _).1.2.2.1
  -- C4 at the openings `j`, `j + 1`, `j + 2`
  have hC4 : ∀ i, j ≤ i → i + 1 ≤ m →
      (Bf i).AncestorEq (Bf (i + 1)) ∧
      (chainStateOf S.C (Bf i)).h + 1 ≤ (chainStateOf S.C (Bf (i + 1))).h ∧
      ((chainStateOf S.C (Bf (i + 1)).parent).h = (chainStateOf S.C (Bf i)).h →
        (chainStateOf S.C (Bf (i + 1))).J = (chainStateOf S.C (Bf i)).T_h) ∧
      ∀ u ∈ Hon S Sched (rs i * S.C.R),
        (stateBefore x (supportCutoff S (rs i * S.C.R + 1) + 1) u).A.saved_confirmation
          (rs i * S.C.R) = some (Bf i) := by
    intro i hji him
    rcases opening_rises_after_fast_block_opening_upTo S Sched x GST tGAT tAwakeEnd r H₂ (rs i * S.C.R)
        (rs (i + 1) * S.C.R) v L (Bf i) (Bf (i + 1)) A' hDiv hMono
        (hSync.mono (hEndP (i + 1) him)) (hCatch.mono (hEndP (i + 1) him))
        (hSyncF.mono (slotStart_mono S (hle (i + 1) m him le_rfl)))
        (hCatchF.mono (slotStart_mono S (hle (i + 1) m him le_rfl)))
        (hRoots.mono (hEndP (i + 1) him)) hParent hOwner hU hGST hThird hAwake hCommittees
        hAnchor hOld hv hL hUpdate
        hFast (le_trans hsj (hle j i hji (by omega))) (Dvd.intro_left _ rfl) (hss i (by omega))
        (hEndO (i + 1) him) (hSeq.honest i (by omega)) (hSeq.honest (i + 1) him)
        (hBf i (by omega)) (hBf (i + 1) him) with h | h
    · exact absurd h (hnc i (by omega))
    · exact h
  obtain ⟨h01, h01h, -, -⟩ := hC4 j le_rfl (by omega)
  obtain ⟨h12, h12h, h12J, -⟩ := hC4 (j + 1) (by omega) (by omega)
  rw [show j + 1 + 1 = j + 2 from rfl] at h12 h12h h12J
  have h0 := (lem47_chain_state_heights S.C (Bf j) (Bf j)).1.1
  -- C5 at the openings `j + 1` and `j + 2`
  have hT1 := chainStateOf_T_h_spec S.C (Bf (j + 1))
  have hB0T : (Bf j).AncestorEq (chainStateOf S.C (Bf (j + 1))).T_h := by
    rcases ancestorEq_compatible hT1.1 h01 with h | h
    · exfalso
      have := chainStateOf_height_mono S.C h
      rw [hT1.2] at this
      unfold Height at *
      omega
    · exact h
  have hB0ne : Bf j ≠ (chainStateOf S.C (Bf (j + 1))).T_h := by
    intro h
    have h' := hT1.2
    rw [← h] at h'
    unfold Height at *
    omega
  have hTmem : (chainStateOf S.C (Bf (j + 1))).T_h ∈ (stateBefore x
      (slotStart S (rs (j + 1) * S.C.R) + 1) (S.P.proposer (rs (j + 1) * S.C.R))).S.T :=
    ancestors_mem_T_of_exec S Sched x _ _ _ _ (hheld (j + 1) (by omega)).2 hT1.1
  have hslotT := slot_lt_of_ancestorEq_of_treeClosed (hTC (j + 1)) hTmem hB0T hB0ne
  rw [(hheld j (by omega)).1] at hslotT
  have hsp := hSeq.spacing j hj2
  have hJ2 : (chainStateOf S.C (Bf (j + 1))).h ≤ (chainStateOf S.C (Bf (j + 2))).h_j := by
    refine round_justified_of_spacing3 S.C (Bf (j + 1)) (Bf (j + 2)) h12 h12h ?_ ?_ ?_
    · rw [(hheld (j + 2) hj2).1]
      unfold Slot at *
      omega
    · intro Y hY hne
      exact slot_lt_of_ancestorEq_of_treeClosed (hTC (j + 2)) (hheld (j + 2) hj2).2 hY hne
    · intro hpar
      have hJ := h12J hpar
      refine ⟨?_, hJ⟩
      have hspec := chainStateOf_J_spec S.C (Bf (j + 2))
      by_cases hz : (chainStateOf S.C (Bf (j + 2))).h_j = 0
      · exfalso
        have hg := hspec.2.1 hz
        rw [hJ] at hg
        have h' := hT1.2
        rw [hg] at h'
        have hg1 : (chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
          chainStateOf_genesis_h S.C
        rw [hg1] at h'
        unfold Height at *
        omega
      · have h' := hspec.2.2 (Nat.one_le_iff_ne_zero.mpr hz)
        rw [hJ, hT1.2] at h'
        exact h'.symm
  -- the base facts at the healed round `s₀ := s_j`
  have hs₀ := hsj
  have hsj1 := hss j (by omega)
  have hEnd₀ : supportCutoff S (rs j * S.C.R + 2) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) (hEndO (j + 1) (by omega))
  have hp₀ := hSeq.honest j (by omega)
  have hBase := round_base_after_fast_block_opening_upTo S Sched x GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    v L (Bf j) A' hDiv hMono
    (hSync.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega))))
    (hCatch.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega))))
    (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega)))) hParent
    hOwner hU hGST hThird hAwake hCommittees hAnchor hOld hv hL hUpdate hFast hs₀
    (Dvd.intro_left _ rfl) hEnd₀ hp₀
    (hBf j (by omega))
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
    (hEndP j (by omega)) hp₀
  have hGs1 : LineInv S Sched x r H₂ (rs j * S.C.R - 1) :=
    P.lineInv_all _ (by
      rw [show rs j * S.C.R - 1 + 1 = rs j * S.C.R by omega]
      exact hEndP j (by omega))
  obtain ⟨hHCE, hSaved, hslot₀, -⟩ := healed_round_base_of_prev_votes_upTo S Sched x GST tGAT tAwakeEnd
    (rs j * S.C.R) (Bf j) hDiv hMono
    (hSync.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega))))
    (hCatch.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega))))
    (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega)))) hParent
    hOwner hU hGST hThird hAwake hCommittees (by omega)
    (le_trans hAnchor (slotStart_mono S (by omega)))
    (le_trans hAnchor (slotStart_mono S (by omega))) hEnd₀ hp₀ (hBf j (by omega)) hBase (hnc j (by omega))
    (fun u hu vote hvote => (hGs1 μA _ hAsrc (by omega)).1 u (Finset.mem_inter.1 hu).2 vote hvote)
  -- the old attestations
  have hOA := P.old_attestations_at_opening (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
    (Dvd.intro_left _ rfl) (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega)))
    hp₀
    (hBf j (by omega))
  -- `B₀`'s height is greater than `H₂`
  have hHB₀ : H₂ < (chainStateOf S.C (Bf j)).h := by
    obtain ⟨-, hPB⟩ := proposal_slot_parent S Sched x (show 1 ≤ rs j * S.C.R by omega)
      (hBf j (by omega))
    have hLP := P.parent_extends_sources (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
      (hEndP j (by omega)) hp₀ (hBf j (by omega)) (r * S.C.R) L
      (P.source_L (le_trans (supportCutoff_mono S (by omega)) (hEndP j (by omega)))) (by omega)
    have h1 := chainStateOf_height_mono S.C (ancestorEq_trans hLP hPB)
    rw [hL] at h1
    unfold Height at *
    omega
  -- the frames
  have hFrames := frames_at_phase_slots_upTo S Sched x GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    (rs m * S.C.R) v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hAnchor hOld hv hL hUpdate hFast hs₀ hSeq.last
  -- the step at the vote time of the last opening's slot, and the caches
  obtain ⟨i₁, hi₁⟩ := exists_handover_step S Sched x (rs m * S.C.R) hDiv
  have hm2 := hle (j + 2) m hj2 le_rfl
  have hsm1 : rs j * S.C.R + 1 ≤ rs m * S.C.R := by
    have := hle (j + 1) m (by omega) le_rfl
    omega
  have htGAT : tGAT ≤ slotStart S (rs (j + 2) * S.C.R) := by
    have h1 := hSeq.first
    have h2 := slotStart_mono S (hle 0 (j + 2) (by omega) hj2)
    omega
  have hCaches := caches_at_handover_of_held_upTo S Sched x GST tGAT tAwakeEnd (rs j * S.C.R)
    (chainStateOf S.C (Bf j)).h (rs (j + 2) * S.C.R) (rs m * S.C.R) i₁ (Bf (j + 2)) hDiv
    hMono (hSync.mono (by
      rw [hi₁]
      have := voteTime_eq S (rs m * S.C.R)
      have := supportCutoff_eq S (rs m * S.C.R)
      omega)) (hCatch.mono (by
      rw [hi₁]
      have := voteTime_eq S (rs m * S.C.R)
      have := supportCutoff_eq S (rs m * S.C.R)
      omega)) (hRoots.mono (by
      rw [hi₁]
      have := voteTime_eq S (rs m * S.C.R)
      have := supportCutoff_eq S (rs m * S.C.R)
      omega)) hParent hU hGST hThird hAwake hm2 htGAT hSeq.last
    (hSeq.honest (j + 2) hj2) (hheld (j + 2) hj2).2
    (fun u hu => P.F_before_vote_ancestor_proposal
      (show r * S.C.R + S.C.k + 2 ≤ rs (j + 2) * S.C.R by
        have := hle j (j + 2) (by omega) hj2
        omega)
      (hEndP (j + 2) hj2) (hSeq.honest (j + 2) hj2) (hBf (j + 2) hj2) hu)
    (by unfold Height at *; omega)
    (by
      intro w D T h hD hJc hh
      have hti : x[i₁].time ≤ tAwakeEnd := by
        rw [hi₁]
        have := hSeq.last
        have := voteTime_eq S (rs m * S.C.R)
        have := supportCutoff_eq S (rs m * S.C.R)
        omega
      have hPc : ProgressCertOn D h T := by
        obtain ⟨A, hA, hAv⟩ := hJc
        exact ⟨A, hA, fun u hu => by
          obtain ⟨a, h1, h2, h3, -, h5⟩ := hAv u hu
          exact ⟨a, h1, h2, h3, h5⟩⟩
      exact cert_entry_at_slot S Sched x (rs j * S.C.R) (chainStateOf S.C (Bf j)).h i₁ w D T h
        hDiv hMono hU (fewerThanQuorum_of_fewerThanThird Sched _
          (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hti) hThird)) hOA hD hPc hh)
    hi₁
  exact ⟨j, rs j * S.C.R, i₁, Bf j, by omega, rfl, hi₁, hHCE, hSaved, hslot₀, hOA,
    fun s h1 h2 w hw => hFrames s h1 h2 w hw, hCaches,
    fun w hw => P.voterFrame_at_last_opening (by omega) le_rfl hw⟩

/-- **Lemma 89 on the fast-confirmation route.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. Why: the climb (`climb_to_fast_block`) gives a root
collision at an honest round opening slot, or the fast block `L` of an honest update at the action
time of a round `r` with the first honest round opening slot `j` at least `k + 2` slots after
`r * R` and `j + 2 ≤ m`; the hand-over's copy with the voter frame
(`handover_after_fast_block_vf`) gives Lemma 89's conclusion from it.

Roots name blocks until `supportCutoff S (rs m * S.C.R)`: the hand-over's copy
(`handover_after_fast_block_vf`); the climb reads up to `aR S (rs (m - 1))`, before it.

Restated with the delivery premises up to `supportCutoff S (rs m * S.C.R)`: the bound of its roots `hRoots`, for the votes (`hSync`, `hCatch`); the attestations (`hSyncF`, `hCatchF`) up to `slotStart S (rs m * S.C.R)`, the bound of `handover_after_fast_block_vf_upTo`; the climb (`climb_to_fast_block_upTo`) reads less, `aR S (rs (m - 1))` and `slotStart S (rs (m - 1) * S.C.R)`. -/
theorem lem89_phase_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (rs m * S.C.R)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (rs m * S.C.R)))
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs m * S.C.R)))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs m * S.C.R)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs m * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening S Sched x rs m ∨
    (∃ (j s₀ i₁ : ℕ) (B₀ : Block V),
      j < m ∧ s₀ = rs j * S.C.R ∧ x[i₁].time = voteTime S (rs m * S.C.R) ∧
      HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt S Sched s₀,
        (stateBefore x (supportCutoff S (s₀ + 1) + 1) u).A.saved_confirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        ∀ w ∈ roundMembers S Sched (s + 1),
          VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w) ∧
      (∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
        CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[i₁][u].st)) ∧
      (∀ w : V, w ∉ Sched.adv ((voteTime S (rs m * S.C.R) : ℕ) : Int) →
        VoterFrameOnChainAt S Sched x s₀ (rs m * S.C.R) w)) := by
  -- the climb reads up to the action time of the round of the honest round opening slot `m − 1`
  have hcount : ∀ (waits : Fin 2 → ℕ) (w5 : Fin 5 → ℕ),
      9 ≤ ((Finset.range (m + 1)).filter
        (OutsideSpans S rs waits S.C.δt w5 (S.C.k + 2))).card := hm
  have hm1 : 1 ≤ m := by
    have h := hcount (fun _ => 0) (fun _ => 0)
    have := Finset.card_filter_le (Finset.range (m + 1))
      (OutsideSpans S rs (fun _ : Fin 2 => 0) S.C.δt (fun _ : Fin 5 => 0) (S.C.k + 2))
    rw [Finset.card_range] at this
    omega
  have hRm : aR S (rs (m - 1)) ≤ supportCutoff S (rs m * S.C.R) := by
    have h' : (rs (m - 1) + 1) * S.C.R ≤ rs m * S.C.R :=
      Nat.mul_le_mul_right _ (r_lt_of_lt_of_mono rs m hSeq.mono (m - 1) m (by omega) le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h'
    have hR := S.C.R_ge_two
    unfold aR
    exact supportCutoff_mono S (by omega)
  have hFm : slotStart S (rs (m - 1) * S.C.R) ≤ slotStart S (rs m * S.C.R) :=
    slotStart_mono S (Nat.mul_le_mul_right _
      (le_of_lt (r_lt_of_lt_of_mono rs m hSeq.mono (m - 1) m (by omega) le_rfl)))
  rcases climb_to_fast_block_upTo S Sched x GST tGAT tAwakeEnd m rs hDiv hMono
    (hSync.mono hRm) (hCatch.mono hRm) (hSyncF.mono hFm) (hCatchF.mono hFm) (hRoots.mono hRm) hParent hOwner hU hGST hThird hAwake hCommittees hSeq hm with
    hcol | ⟨r, H₂, v, L, A', hAnchor, hEnd, hOld, hv, hUpdate, hFast, hL, j, hj2, hsj, hfirst⟩
  · exact Or.inl hcol
  · exact handover_after_fast_block_vf_upTo S Sched x GST tGAT tAwakeEnd m r H₂ rs v L A' hDiv hMono hSync
      hCatch hSyncF hCatchF hRoots hParent hOwner hU hGST hThird hAwake hCommittees hSeq
      hAnchor hOld hv hUpdate hFast hL j hj2 hsj

end GoldilocksCorrectness.Proofs.Executions

