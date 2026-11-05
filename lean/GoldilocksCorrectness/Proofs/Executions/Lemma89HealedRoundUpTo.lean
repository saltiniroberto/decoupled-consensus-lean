module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HealedRound
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamilyUpTo
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Proofs.Executions.RoundBaseUpTo

@[expose] public section

/-!
# `Lemma89HealedRound.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89HealedRound.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `cert_source_round`, `root_source`, `tall_entry_round`, `floor_source`, `floor_le_of_sources`,
  `parent_extends_sources`, `late_locks_on_sources`, `round_base_after_fast_block_opening`,
  `healed_round_base_of_prev_votes`, `member_saves_confirmation`, `anchor_source`,
  `quiet_round_after_fast_block_opening`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_voteTime dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart round_slot_le_of_lt slotStart_mono supportCutoff_lt
  supportCutoff_mono times_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_height_mono
  entry_eq_of_compatible)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_ancestorEq_of_tall fc_root_eq floor_le_h_max
  mem_fg_to_ac_tree mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_cases_locked get_anchor_root_or_viable)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  fg_to_ac_F is_live_iff mem_viable_tree_iff pool_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (fg_contest_spec head_height_floor_of_not_contested
  root_cases)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn CountedVotes
  ProgressCertOn JustificationCertOn FrameShape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible ancestorEq_of_parent?)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open GoldilocksCorrectness.Statements.Routines (lem15_tick_updates_confirmation lem49_tick_attests)
open GoldilocksCorrectness.Proofs.Routines (ac_to_fg_source_mem ac_to_fg_source_fast
  tick_attest_awake awakeSince_of_record_awake create_attestation_cases)

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- `cert_source` with the source at a round's first slot: a progress certificate at a height
`h > H₂` on the chain of a block an honest validator holds after `j` steps, within the phase,
names the root of an entry block `E` at the height `h` that is a line source of the first slot of a
round `r' ≥ r` whose action time is at most `x[j].time`. The proof is `cert_source`'s, with the
round kept.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem cert_source_round (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x[j].time ≤ tAwakeEnd)
    (hY : Y ∈ (x[j][w].st).S.T) (hJ : ProgressCertOn Y h T) (hH : H₂ < h) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ supportCutoff S (r' * S.C.R + 1) ≤ x[j].time ∧
      LineSource S Sched x r H₂ (r' * S.C.R) E ∧ IsEntry S.C E ∧ (chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  have hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int) :=
    fewerThanQuorum_of_fewerThanThird Sched _
      (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hj) P.hThird)
  obtain ⟨A, hqA, hA⟩ := hJ
  obtain ⟨u, hu, hhon⟩ : ∃ u ∈ A, HonestThrough x j u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ (x[j].time : Int) ∧ v ∈ Sched.adv t' := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  obtain ⟨a, hau, hah, haT, hon⟩ := hA u hu
  have hrec := lem74_honest_attestations_recorded S Sched x P.hU j w Y a hY hon
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have htj : t' ≤ x[j].time := by
    rw [← (time_of_lbl_tickAllAwake x hl).2]
    exact time_mono x hj'
  have hge : aR S r ≤ t' := by
    by_contra hlt
    have hle := P.hOld j' t' u a' hl (Nat.lt_of_not_le hlt) hAw hHon hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  obtain ⟨r', rfl⟩ := attest_time_round S Sched x hl hsent
  have hrr : r ≤ r' := by
    by_contra hlt
    have : r' * S.C.R + 1 < r * S.C.R + 1 := by
      have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt)
        (show 0 < S.C.R by have := S.C.R_ge_two; omega)
      omega
    have := supportCutoff_lt S this
    exact absurd hge (Nat.not_le.mpr this)
  obtain ⟨A₀, X, hU, hXf, hXT, hXh, hXT'⟩ :=
    fast_source_of_attestation S Sched x r' u a' ⟨j', hl, hAw, hHon, hsent⟩
  obtain ⟨hE1, hE2, hE3⟩ := GoldilocksCorrectness.Proofs.Routines.isEntry_T_h S.C X
  have hEnd' : supportCutoff S (r' * S.C.R + 1) ≤ tAwakeEnd := le_trans htj hj
  have huH : u ∈ Hon S Sched (r' * S.C.R) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hHon⟩
  have hU' : update_confirmation S.C S.P
      (expireLocks (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).A
        ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).S)
      ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int) (r' * S.C.R + 1) = .ok A₀ := hU
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved S.C S.P _ A₀ _ _
      (r' * S.C.R + 1) X (Nat.le_add_left 1 _) hU' hXf
  rw [Nat.add_sub_cancel] at hC₀
  have hrR : r * S.C.R ≤ r' * S.C.R := Nat.mul_le_mul_right _ hrr
  have hst := state_saved_of_update S Sched x (r' * S.C.R) u A₀ P.hDiv P.hMono
    (P.member1 hrR huH hEnd') hU'
  have hkind : (r' * S.C.R = r * S.C.R ∧ X ∈ A₀.fast_blocks ∧ (chainStateOf S.C X).h = H₂ + 1) ∨
      (r * S.C.R + 1 ≤ r' * S.C.R ∧ (X ∈ A₀.fast_blocks ∨
        slow_test S.C (expireLocks (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).A
          ((supportCutoff S (r' * S.C.R + 1) : ℕ) : Int))
          (fg_to_ac (stateBefore x (supportCutoff S (r' * S.C.R + 1)) u).S) (r' * S.C.R) X =
            true)) ∨
      r * S.C.R + S.C.k ≤ r' * S.C.R := by
    rcases Nat.lt_or_eq_of_le hrr with hlt | heq
    · refine Or.inr (Or.inl ⟨?_, Or.inl hXf⟩)
      have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
      have h2 := S.C.R_ge_two
      rw [Nat.succ_mul] at h1
      omega
    · subst heq
      refine Or.inl ⟨rfl, hXf, ?_⟩
      have hle := held_height_le_before_action S Sched x tAwakeEnd r H₂ (aR S r) u X P.hU
        P.hThird P.hOld le_rfl hEnd' hXT
      rw [hXh, hh'] at hle ⊢
      exact Nat.le_antisymm hle (Nat.succ_le_of_lt hH)
  refine ⟨r', (chainStateOf S.C X).T_h, hrr, htj, ⟨u, huH, A₀, C₀, X, hU', hC₀,
    hst.trans hC₀, hE3, hXC₀, hkind⟩, hE1, by rw [hE2, hXh, hh'], ?_⟩
  rw [← hT', ← hXT']

/-- **The root is a line source of a round's first slot.** After the action time of round `r`, up
to the support cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to
`σ`: an honest validator's fork-choice root is a line source of the first slot of a round
`r' ≥ r` whose action time is before the reading.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem root_source (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) (ht0 : aR S r < t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) :
    ∃ r' : ℕ, r ≤ r' ∧ supportCutoff S (r' * S.C.R + 1) < t ∧
      LineSource S Sched x r H₂ (r' * S.C.R) (get_fc_root (stateBefore x t w).S) := by
  have hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (Nat.le_succ _)) hEnd
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd1
  have haR : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
  have ht0' : viewFreeze S (r * S.C.R) ≤ t := by
    obtain ⟨-, hc, hf, hs, hΔ⟩ := times_eq S (r * S.C.R)
    obtain ⟨-, hc1, -, -, -⟩ := times_eq S (r * S.C.R + 1)
    omega
  have ht1 : 1 ≤ t := by omega
  have hLsrc : ∀ Y : Block V, Y.AncestorEq L → ∃ r' : ℕ, r ≤ r' ∧
      supportCutoff S (r' * S.C.R + 1) < t ∧ LineSource S Sched x r H₂ (r' * S.C.R) Y :=
    fun Y hY => ⟨r, le_rfl, by omega, (P.source_L hEndR).anc hY⟩
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have hjE : x[stepBefore x t].time ≤ tAwakeEnd := by omega
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast htj.le) h)
  obtain ⟨hLT, hσL, hM⟩ := P.L_tall hEndR ht0' hw
  by_cases hR : get_fc_root (stateBefore x t w).S = (stateBefore x t w).S.F
  · rw [hR]
    obtain ⟨D, hD, hFD⟩ :=
      GoldilocksCorrectness.Statements.Executions.finalizedFromChain_of_exec S Sched x
        (stepBefore x t) w
    show ∃ r' : ℕ, r ≤ r' ∧ supportCutoff S (r' * S.C.R + 1) < t ∧
      LineSource S Sched x r H₂ (r' * S.C.R) (x[stepBefore x t][w].st).S.F
    rw [hFD]
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
      exact hLsrc _ (lem68_honest_past_finalized S Sched x P.hU P.hRoots (stepBefore x t)
        (stepBefore x (aR S r)) w v D L hT hw' hv' hD (P.L_held_v hEndR).2
        (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE (le_trans htv hEndR)))
    · have hlt : H₂ < (chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
      obtain ⟨hJC, -, hFanc, -⟩ :=
        (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2
          (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hFT : (chainStateOf S.C D).F ∈ (x[stepBefore x t][w].st).S.T :=
        ancestors_mem_T_of_exec S Sched x _ w D _ hD hFanc
      obtain ⟨r', E, hrr, hcut, hE, -, -, hEr⟩ := P.cert_source_round hjE hD
        (progressCertOn_of_justificationCertOn hJC) hlt
      have hFE : (chainStateOf S.C D).F = E :=
        P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hFT⟩
          (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
      rw [hFE]
      exact ⟨r', hrr, lt_of_le_of_lt hcut htj, hE⟩
  have key : (stateBefore x t w).S.h_max = (stateBefore x t w).S.h_j + 1 ∧
      get_fc_root (stateBefore x t w).S = (stateBefore x t w).S.J := by
    rcases root_cases (stateBefore x t w).S with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  rw [key.2]
  by_cases hlt : H₂ < (stateBefore x t w).S.h_j
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hD' : D ∈ (x[stepBefore x t][w].st).S.T := hD
    have hJT : (chainStateOf S.C D).J ∈ (x[stepBefore x t][w].st).S.T :=
      ancestors_mem_T_of_exec S Sched x _ w D _ hD' hJanc
    obtain ⟨r', E, hrr, hcut, hE, -, -, hEr⟩ := P.cert_source_round hjE hD'
      (progressCertOn_of_justificationCertOn hJC) hlt
    have hJE : (chainStateOf S.C D).J = E :=
      P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hJT⟩
        (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
    rw [hJD, hJE]
    exact ⟨r', hrr, lt_of_le_of_lt hcut htj, hE⟩
  · have hhj : (stateBefore x t w).S.h_j = H₂ := by
      have := key.1
      have h1 : (stateBefore x t w).S.h_j ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    by_cases h0 : (chainStateOf S.C D).h_j = 0
    · have hg := (chainStateOf_J_spec S.C D).2.1 h0
      rw [hJD, hg]
      exact hLsrc _ (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq L)
    · have hJh := (chainStateOf_J_spec S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (stateBefore x t w).S.F.AncestorEq (stateBefore x t w).S.J := by
        have := F_ancestorEq_fc_root_of_stateBefore S Sched x t w
        rw [key.2] at this
        exact this
      have hFL : (stateBefore x t w).S.F.AncestorEq L := by
        rcases (compatible_iff _ _).1 (P.F_compat hG hσ hEnd ht1 ht hw (P.source_L hEndR) hσ)
          with h | h
        · exact h
        · exfalso
          have h1 := chainStateOf_height_mono S.C (ancestorEq_trans h hFJ)
          rw [hJD, hJh, ← hhjD, hhj, P.hL] at h1
          exact Nat.lt_irrefl _ (Nat.lt_of_succ_le h1)
      have hRL := fc_root_ancestorEq_of_tall _ L hLT hFL (by
        rw [hσL, P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact hLsrc _ hRL

/-- `tall_entry` with the source at a round's first slot (`cert_source_round`).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem tall_entry_round (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {t : ℕ} {w : V}
    (ht1 : 1 ≤ t) (htE : t ≤ tAwakeEnd) (hw : w ∉ Sched.adv (t : Int)) {Y : Block V}
    (hY : Y ∈ (stateBefore x t w).S.T) (hYh : H₂ + 2 ≤ (chainStateOf S.C Y).h) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ supportCutoff S (r' * S.C.R + 1) < t ∧
      LineSource S Sched x r H₂ (r' * S.C.R) E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = (chainStateOf S.C Y).h - 1 ∧ E.AncestorEq Y := by
  have htj : x[stepBefore x t].time < t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := time_stepBefore_succ_le x t'
    omega
  have hjE : x[stepBefore x t].time ≤ tAwakeEnd := by omega
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (P.hMono _ _ (by exact_mod_cast htj.le) h)
  have hY' : Y ∈ (x[stepBefore x t][w].st).S.T := hY
  obtain ⟨Y', hY'Y, -, -, -, hT', hcert⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem67_first_advance S.C Y
      ((chainStateOf S.C Y).h - 1) (by unfold Height at *; omega) (by unfold Height at *; omega)
  have hY'T := ancestors_mem_T_of_exec S Sched x _ w Y Y' hY' hY'Y
  have hT'T := ancestors_mem_T_of_exec S Sched x _ w Y' _ hY'T hT'
  obtain ⟨r', E, hrr, hcut, hE, hEe, hEh, hEr⟩ := P.cert_source_round hjE hY'T hcert
    (by unfold Height at *; omega)
  have hTE := P.hRoots _ _ ⟨stepBefore x t, w, hw', hjE, hT'T⟩
    (inHonestTreeBy_mono x (le_trans hcut hjE) (P.source_inHonestTreeBy hE)) hEr
  refine ⟨r', E, hrr, lt_of_le_of_lt hcut htj, hE, hEe, hEh, ?_⟩
  rw [← hTE]
  exact ancestorEq_trans hT' hY'Y

/-- **`head_height_floor` (the least chain-state height a viable block may have) above the threshold is the height of a line source.** Up to the support cutoff of
slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ` and an honest
validator's `h_max` is at least `H₂ + 2`: its state is not contested, and its
`head_height_floor`, `h_max − 1`, is the chain-state height of a line source of the first slot of a
round whose action time is before the reading (the entry at `h_max − 1`, `tall_entry_round`; the
contest argument of `viable_candidate`).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem floor_source (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ')
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) (ht1 : 1 ≤ t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int))
    (hM2 : H₂ + 2 ≤ (stateBefore x t w).S.h_max) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ supportCutoff S (r' * S.C.R + 1) < t ∧
      LineSource S Sched x r H₂ (r' * S.C.R) E ∧
      head_height_floor (stateBefore x t w).S = (chainStateOf S.C E).h := by
  have hEnd1 : supportCutoff S (σ + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (Nat.le_succ _)) hEnd
  have hEndE : t ≤ tAwakeEnd := le_trans ht hEnd
  have hwf : ∀ t' : ℕ, t' ≤ t → w ∉ Sched.adv (t' : Int) :=
    fun t' h h' => hw (P.hMono _ _ (by exact_mod_cast h) h')
  obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  obtain ⟨r', E, hrr, hcut, hE, -, hEh, -⟩ := P.tall_entry_round ht1 hEndE hw hY
    (by rw [hYh]; exact hM2)
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
  exact ⟨r', E, hrr, hcut, hE, by rw [hfloor, hEh]⟩

/-- **`head_height_floor` is at most the height of a block on every early line source's chain.** Up to the
support cutoff of slot `σ + 2`, after the action time of round `r`, in the phase, when the
invariant holds at every slot up to `σ`: if every line source of the first slot of a round whose
action time is before the reading is an ancestor of, or equal to, `Q`, then an honest validator's
`head_height_floor` is at most `Q`'s chain-state height.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem floor_le_of_sources (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv S Sched x r H₂ σ')
    (hEnd : supportCutoff S (σ + 2) ≤ tAwakeEnd) (ht0 : aR S r < t)
    (ht : t ≤ supportCutoff S (σ + 2)) (hw : w ∉ Sched.adv (t : Int)) {Q : Block V}
    (hQ : ∀ (r' : ℕ) (E : Block V), r ≤ r' → supportCutoff S (r' * S.C.R + 1) < t →
      LineSource S Sched x r H₂ (r' * S.C.R) E → E.AncestorEq Q) :
    head_height_floor (stateBefore x t w).S ≤ (chainStateOf S.C Q).h := by
  have hEndR : supportCutoff S (r * S.C.R + 1) ≤ tAwakeEnd := by
    have : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
    omega
  have hLQ : L.AncestorEq Q := hQ r L le_rfl ht0 (P.source_L hEndR)
  have hLh := chainStateOf_height_mono S.C hLQ
  rw [P.hL] at hLh
  by_cases hM : (stateBefore x t w).S.h_max ≤ H₂ + 1
  · have := floor_le_h_max (stateBefore x t w).S
    unfold Height at *
    omega
  · obtain ⟨r', E, hrr, hcut, hE, hfl⟩ := P.floor_source hG hEnd (by omega) ht hw
      (by unfold Height at *; omega)
    rw [hfl]
    exact chainStateOf_height_mono S.C (hQ r' E hrr hcut hE)

/-- **The honest proposal's parent extends every early line source.** For a slot `s` at least
`k + 2` slots after `r * R`, with its support cutoff in the phase, the proposer of slot `s` honest
at that support cutoff and `B` its proposal: every line source of a slot `μ` with `μ + 2 ≤ s` is
an ancestor of, or equal to, `B`'s parent.

Why: the votes of slot `s − 1` of the committee's members extend every such source (the line
invariant at slot `s − 1`); the proposer's anchor is its root or an ancestor of a live lock, a
line source in both cases (`root_source`, `source_lock` with Lemma 41); its frame has a viable
head on every source's chain (`frame_source_at`); so the walk passes every source
(`family_ancestorEq_proposal_parent`).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem parent_extends_sources (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hEnd : supportCutoff S s ≤ tAwakeEnd) {B : Block V}
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hB : ProposalAt S Sched x s B) :
    ∀ (μ : ℕ) (Y : Block V), LineSource S Sched x r H₂ μ Y → μ + 2 ≤ s → Y.AncestorEq B.parent := by
  have hk := S.C.k_ge_two
  obtain ⟨σ₁, rfl⟩ : ∃ σ₁, s = σ₁ + 2 := ⟨s - 2, by omega⟩
  set p := S.P.proposer (σ₁ + 2) with hpdef
  have hG : ∀ σ', σ' ≤ σ₁ → LineInv S Sched x r H₂ σ' := P.lineInv_upto hEnd
  have hG1 : LineInv S Sched x r H₂ (σ₁ + 1) := P.lineInv_all (σ₁ + 1) hEnd
  have hσ : r * S.C.R ≤ σ₁ := by omega
  obtain ⟨hvs, hcs, hfs, hss, hΔ⟩ := times_eq S σ₁
  obtain ⟨hvs1, hcs1, hfs1, hss1, -⟩ := times_eq S (σ₁ + 1)
  obtain ⟨hvs2, hcs2, -, -, -⟩ := times_eq S (σ₁ + 2)
  rw [show σ₁ + 1 + 1 = σ₁ + 2 from rfl] at hss1
  have hEnd1 : supportCutoff S (σ₁ + 1 + 1) ≤ tAwakeEnd := hEnd
  have ht : slotStart S (σ₁ + 2) ≤ supportCutoff S (σ₁ + 2) := by omega
  have hpt : p ∉ Sched.adv ((slotStart S (σ₁ + 2) : ℕ) : Int) :=
    fun h => hp (P.hMono _ _ (by exact_mod_cast ht) h)
  have hdwR := P.dws (show r * S.C.R ≤ σ₁ + 1 by omega)
  have hdw1 := dutyWindowStart_le_voteTime S (σ₁ + 1)
  have haR : aR S r < slotStart S (σ₁ + 2) := by
    have : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
    have := supportCutoff_mono S (show r * S.C.R + 1 ≤ σ₁ + 1 by omega)
    omega
  -- the family: the line sources of slots `μ` with `μ + 2 ≤ σ₁ + 2`
  let 𝓒 : Block V → Prop := fun C => ∃ μ, μ ≤ σ₁ ∧ LineSource S Sched x r H₂ μ C
  -- the root of `p`'s fork choice is in the family
  have hroot : 𝓒 (get_fc_root (stateBefore x (slotStart S (σ₁ + 2)) p).S) := by
    obtain ⟨r', -, hcut, hsrc⟩ := P.root_source hG hσ hEnd haR ht hpt
    refine ⟨r' * S.C.R, ?_, hsrc⟩
    by_contra h
    have := supportCutoff_mono S (show σ₁ + 2 ≤ r' * S.C.R + 1 by omega)
    omega
  have hFrame : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (σ₁ + 2)) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S (σ₁ + 2)) p).S).viable_heads ∧
        C.AncestorEq W := by
    intro C ⟨μ, hμ, hC⟩
    obtain ⟨μR, hμR, hR⟩ := hroot
    have hfs := fun {μ' : ℕ} {X : Block V} (hX : LineSource S Sched x r H₂ μ' X) (hμ' : μ' ≤ σ₁) =>
      P.frame_source_at hG hσ hEnd
        (show voteTime S (σ₁ + 1) ≤ slotStart S (σ₁ + 2) by omega) ht hpt hX hμ'
    rcases (compatible_iff _ _).1 (P.sources_compatible hG
      (le_trans (supportCutoff_mono S (by omega)) hEnd) hR hC hμR hμ) with h | h
    · exact (hfs hC hμ).2.1 (by rw [fc_root_eq]; exact h)
    · obtain ⟨W, hW, hWv, hRW⟩ := (hfs hR hμR).2.1 (by rw [fc_root_eq]; exact ancestorEq_refl _)
      exact ⟨W, hW, hWv, ancestorEq_trans h hRW⟩
  have hAnch : 𝓒 (get_anchor (stateBefore x (slotStart S (σ₁ + 2)) p).A
      (fg_to_ac (stateBefore x (slotStart S (σ₁ + 2)) p).S) ((slotStart S (σ₁ + 2) : ℕ) : Int)) := by
    rcases get_anchor_cases_locked (stateBefore x (slotStart S (σ₁ + 2)) p).A
      (fg_to_ac (stateBefore x (slotStart S (σ₁ + 2)) p).S)
      ((slotStart S (σ₁ + 2) : ℕ) : Int) with h | ⟨-, e, he, hl, hAe⟩
    · rw [h, fc_root_eq]
      exact hroot
    · have hl' := hl
      simp only [is_live_iff] at hl'
      obtain ⟨μ₀, hd, hcut, -, hsrc⟩ := P.source_lock hpt
        (le_trans ht (le_trans (supportCutoff_mono S (by omega)) hEnd)) he
      have hlo : r * S.C.R + 1 ≤ μ₀ :=
        GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S (r * S.C.R + 1) μ₀
          (slotStart S (σ₁ + 2)) e hd hl'.1 (by
            obtain ⟨hvk, -, -, -, -⟩ := times_eq S (r * S.C.R + 1 + S.C.k)
            have := slotStart_mono S (show r * S.C.R + 1 + S.C.k + 1 ≤ σ₁ + 2 by omega)
            obtain ⟨-, -, -, hsk, -⟩ := times_eq S (r * S.C.R + 1 + S.C.k)
            omega)
      refine ⟨μ₀, ?_, (hsrc hlo).anc hAe⟩
      by_contra h
      have := supportCutoff_mono S (show σ₁ + 2 ≤ μ₀ + 1 by omega)
      omega
  -- the votes of slot `σ₁ + 1`
  have hmem := P.members_sets (show r * S.C.R ≤ σ₁ + 1 by omega) hEnd1
  have hHs : ∀ u ∈ S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1),
      u ∈ S.P.committee (σ₁ + 1) ∧ u ∉ Sched.adv (slotStart S (σ₁ + 1 + 1) : Int) ∧
      ∃ vote : GoldfishVote V, ∃ i : ℕ,
        x.lbl i = AtomicAction.tickAllAwake (voteTime S (σ₁ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent := by
    intro u hu
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x (σ₁ + 1) u
        P.hDiv P.hMono (hmem.1 hH) hK
    have hu' : u ∉ Sched.adv ((supportCutoff S (σ₁ + 1 + 1) : ℕ) : Int) := by
      unfold Hon roundMembers at hH
      exact (Finset.mem_sdiff.1 hH).2
    refine ⟨hK, fun h => hu' (P.hMono _ _ ?_ h), vote, i, hl, hsent⟩
    have : slotStart S (σ₁ + 1 + 1) ≤ supportCutoff S (σ₁ + 1 + 1) := by omega
    exact_mod_cast this
  have hExt : ∀ C : Block V, 𝓒 C → ∀ u ∈ S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1),
      ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (σ₁ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (σ₁ + 1)) u).S.T,
        vote = GoldfishVote.mk u (σ₁ + 1) H_u.root ∧ C.AncestorEq H_u := by
    intro C ⟨μ, hμ, hC⟩ u hu vote hv
    exact (hG1 μ C hC (by omega)).1 u (Finset.mem_inter.1 hu).2 vote hv
  have hVotersP := (counting_of_committee_majority S Sched x (σ₁ + 1) (slotStart S (σ₁ + 1 + 1))
    (Hon S Sched (σ₁ + 1)) p (P.committee (show r * S.C.R ≤ σ₁ + 1 by omega))).2.1
  have hpw : ∀ t : ℕ, voteTime S (σ₁ + 1) ≤ t → t ≤ supportCutoff S (σ₁ + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    P.window hp hEnd t (by omega) (by omega)
  have hfam := family_ancestorEq_proposal_parent_upTo S Sched x GST (σ₁ + 1)
    (S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1)) 𝓒 B p P.hDiv P.hMono
    (P.hSync.mono (le_trans (supportCutoff_mono S (by omega)) hEnd))
    (P.hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hEnd))
    (P.hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hEnd)) P.hParent P.hOwner
    (P.gst (show r * S.C.R ≤ σ₁ + 1 by omega)).2.1 hHs hExt
    hVotersP hpw hB hFrame hAnch
  intro μ Y hY hμ
  exact hfam Y ⟨μ, by omega, hY⟩

/-- **From slot `r * R + k` on, the live locks a member holds at the vote time of the next slot are
on line sources of slots `μ` with `μ + 1 ≤ s`.** Every such lock is of a slot `μ ≥ s + 1 − k`
(Lemma 41), so `μ ≥ r * R + 1`, and its block is a line source of slot `μ` (`source_lock`,
Lemma 39: the lock is on a confirmation fast or passing the slow test); the update of slot `μ` ran
before the vote time of slot `s + 1`, so `μ < s`.

The variables: `P`, the phase's hypotheses with the fast block `L` of `v`'s update at the action
time of round `r`; `s`, the slot; `u`, a member of `Hon S Sched s`.

Read aloud: one lock lifetime after the fast block's round, every live lock is on the line.

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem late_locks_on_sources (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hs : r * S.C.R + S.C.k ≤ s) (hEnd : voteTime S (s + 1) ≤ tAwakeEnd) {u : V}
    (hu : u ∈ Hon S Sched s) :
    LiveLocksOnFamilyAt S Sched x
      (fun C => ∃ μ : ℕ, μ + 1 ≤ s ∧ LineSource S Sched x r H₂ μ C) s u := by
  have hk := S.C.k_ge_two
  refine liveLocksOnFamilyAt_of_live S Sched x _ s u (fun e he hl => ?_)
  have hl' := hl
  simp only [is_live_iff] at hl'
  obtain ⟨hv1, hc1, -, -, hΔ⟩ := times_eq S (s + 1)
  have hu' : u ∉ Sched.adv ((voteTime S (s + 1) : ℕ) : Int) := by
    unfold Hon roundMembers at hu
    exact fun h => (Finset.mem_sdiff.1 hu).2 (P.hMono _ _ (by exact_mod_cast (show
      voteTime S (s + 1) ≤ supportCutoff S (s + 1) by omega)) h)
  obtain ⟨μ, hd, hcut, -, hsrc⟩ := P.source_lock hu' hEnd he
  have hlo : s + 1 - S.C.k ≤ μ :=
    GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S (s + 1 - S.C.k) μ
      (voteTime S (s + 1)) e hd hl'.1 (by rw [show s + 1 - S.C.k + S.C.k = s + 1 by omega])
  have hhi : μ < s := by
    by_contra h
    have := supportCutoff_mono S (show s + 1 ≤ μ + 1 by omega)
    omega
  exact ⟨μ, by omega, hsrc (by omega)⟩

end PartAHypsUpTo

/-- **C1, the round base at an opening after the fast block (copy with the round's first slot).**
The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`. Why: the
proposal's parent extends every line source of a slot at least two slots before `s`
(`parent_extends_sources`); the roots before the vote time of slot `s` and before the support
cutoff of slot `s + 1` are such sources (`root_source`; at the support cutoff, a round's first
slot before `s`, `round_slot_le_of_lt`); the `head_height_floor` values are at most the heights of such sources or of
`L` (`floor_le_of_sources`); the live locks are on line sources of slots before `s − 1`
.

Roots name blocks until `supportCutoff S (s + 2)`: the bundle `PartAHyps` is built with its end
time `supportCutoff S (s + 2)`, the latest time its kit reads here.

Restated with the delivery premises up to `supportCutoff S (s + 2)`: the bound of its roots `hRoots`, the end time of the bundle `PartAHypsUpTo` it builds. -/
theorem round_base_after_fast_block_opening_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L B : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 2)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 2)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s)
    (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hB : ProposalAt S Sched x s B) :
    RoundBaseAt S Sched x B s := by
  -- the bundle with its end time `supportCutoff S (s + 2)`
  have P : PartAHypsUpTo S Sched x GST tGAT (supportCutoff S (s + 2)) r H₂ v L A' := ⟨hDiv, hMono,
    hSync, hCatch, hRoots, hParent, hOwner, hU, hGST,
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) hThird,
    fun t' h1 h2 => hAwake t' h1 (le_trans h2 hEnd), hCommittees, hAnchor, hOld, hv, hUpdate,
    hFast, hL⟩
  have hEnd : supportCutoff S (s + 2) ≤ supportCutoff S (s + 2) := le_rfl
  have hk := S.C.k_ge_two
  have hG : ∀ σ', σ' ≤ s → LineInv S Sched x r H₂ σ' := P.lineInv_upto hEnd
  have hσ : r * S.C.R ≤ s := by omega
  obtain ⟨hvs, hcs, hfs, hss, hΔ⟩ := times_eq S s
  obtain ⟨hvs1, hcs1, -, hss1, -⟩ := times_eq S (s + 1)
  have hEnd0 : supportCutoff S s ≤ supportCutoff S (s + 2) :=
    le_trans (supportCutoff_mono S (by omega)) hEnd
  have hPar := P.parent_extends_sources (show r * S.C.R + S.C.k + 2 ≤ s by omega) hEnd0 hp hB
  have haR : aR S r < voteTime S s := by
    have : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
    have := supportCutoff_mono S (show r * S.C.R + 1 ≤ s - 1 by omega)
    obtain ⟨-, hc', -, hs', -⟩ := times_eq S (s - 1)
    rw [show s - 1 + 1 = s by omega] at hs'
    omega
  -- the sources of a round's first slot whose action time is before the vote time of slot `s`
  have hQv : ∀ (r' : ℕ) (E : Block V), r ≤ r' → supportCutoff S (r' * S.C.R + 1) < voteTime S s →
      LineSource S Sched x r H₂ (r' * S.C.R) E → E.AncestorEq B.parent := by
    intro r' E _ hcut hE
    refine hPar _ E hE ?_
    by_contra hn
    have := supportCutoff_mono S (show s ≤ r' * S.C.R + 1 by omega)
    omega
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  obtain ⟨i, hl, hsent⟩ := hB
  obtain ⟨-, -, hBpar?, -⟩ := proposal_parent_walk_end S Sched x s₀ i B _ hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hQc : ∀ (r' : ℕ) (E : Block V), r ≤ r' →
      supportCutoff S (r' * S.C.R + 1) < supportCutoff S (s₀ + 1 + 1) →
      LineSource S Sched x r H₂ (r' * S.C.R) E → E.AncestorEq B :=
    fun r' E _ hcut hE => ancestorEq_trans (hPar _ E hE (round_slot_le_of_lt S hsR hcut)) hPB
  have hmemv : ∀ w ∈ Hon S Sched (s₀ + 1), w ∉ Sched.adv ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) := by
    intro w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have hwv : w ∉ Sched.adv ((voteTime S (s₀ + 1) : ℕ) : Int) :=
      fun h => hmemv w hw (hMono _ _ (by exact_mod_cast (show voteTime S (s₀ + 1) ≤
        supportCutoff S (s₀ + 1 + 1) by omega)) h)
    have hvt : voteTime S (s₀ + 1) ≤ supportCutoff S (s₀ + 1 + 2) :=
      le_trans (by omega) (supportCutoff_mono S (show s₀ + 1 ≤ s₀ + 1 + 2 by omega))
    obtain ⟨r', hrr, hcut, hsrc⟩ := P.root_source hG hσ hEnd haR hvt hwv
    exact ⟨hQv r' _ hrr hcut hsrc, P.floor_le_of_sources hG hEnd haR hvt hwv hQv⟩
  · have hct : supportCutoff S (s₀ + 1 + 1) ≤ supportCutoff S (s₀ + 1 + 2) :=
      supportCutoff_mono S (by omega)
    have haR' : aR S r < supportCutoff S (s₀ + 1 + 1) := by omega
    obtain ⟨r', hrr, hcut, hsrc⟩ := P.root_source hG hσ hEnd haR' hct (hmemv w hw)
    exact ⟨hQc r' _ hrr hcut hsrc, P.floor_le_of_sources hG hEnd haR' hct (hmemv w hw) hQc⟩
  · intro A₁ hrev e he hlive
    have hws : w ∈ Hon S Sched s₀ := by
      unfold Hon roundMembers at hw ⊢
      obtain ⟨-, hw'⟩ := Finset.mem_sdiff.1 hw
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => hw' (hMono _ _
        (by exact_mod_cast supportCutoff_mono S (show s₀ + 1 ≤ s₀ + 1 + 1 by omega)) h)⟩
    have hvE : voteTime S (s₀ + 1) ≤ supportCutoff S (s₀ + 1 + 2) :=
      le_trans (le_trans (by omega) (supportCutoff_mono S (show s₀ + 1 ≤ s₀ + 1 + 2 by omega))) hEnd
    obtain ⟨D, ⟨μ, hμ, hsrc⟩, heD⟩ := P.late_locks_on_sources
      (show r * S.C.R + S.C.k ≤ s₀ by omega) hvE hws A₁ hrev e he hlive
    exact ancestorEq_trans heD (hPar μ D hsrc (by omega))

/-- **C3, Lemma 89's base facts at the healed round (copy with the previous slot's votes and no
root collision).** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. Why: `round_base_steps` with the members
`Hon S Sched s`, the previous slot's voters the committee's members of `Hon S Sched (s − 1)` with
`X` the proposer's anchor (`hPrev`), the proposer's viable head on its anchor's chain
(`anchor_has_viable_head`), the `head_height_floor` values ordered by delivery (`floor_le_of_delivery_unordered`),
the round base's three clauses, the slot's only block (`only_block_of_unforgeability`) and the
fresh root (`hNoCol`); then the restriction to the honest active validators and the updaters, the
saved confirmation read after the update (`state_saved_of_update`), and the parent in the viable
tree (`get_anchor_root_or_viable`).

Roots name blocks until `supportCutoff S (s + 1)`: the members' update of slot `s`
(`round_base_steps`), the latest time the proof reads.

Restated with the delivery premises up to `supportCutoff S (s + 1)`: the bound of its roots `hRoots`, the members' update of slot `s` (`round_base_steps_upTo`). -/
theorem healed_round_base_of_prev_votes_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hs1 : 1 ≤ s) (hAnchor : anchorCW S tGAT ≤ slotStart S (s + 1))
    (hA : anchorCW S tGAT ≤ slotStart S s)
    (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hB : ProposalAt S Sched x s B)
    (hBase : RoundBaseAt S Sched x B s)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x s B)
    (hPrev : ∀ u ∈ S.P.committee (s - 1) ∩ Hon S Sched (s - 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T,
        vote = GoldfishVote.mk u (s - 1) H_u.root ∧
        (get_anchor (stateBefore x (slotStart S s) (S.P.proposer s)).A
          (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S)
          ((slotStart S s : ℕ) : Int)).AncestorEq H_u) :
    HonestChainExtends S Sched x (honestActiveAt S Sched s) B s ∧
    (∀ u ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) u).A.saved_confirmation s = some B) ∧
    B.slot = s ∧
    B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S)
      (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S).tree := by
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hPrev
  set p := S.P.proposer (s₀ + 1) with hpdef
  have hk := S.C.k_ge_two
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := times_eq S s₀
  obtain ⟨hv1, hc1, hf1, hs1', -⟩ := times_eq S (s₀ + 1)
  obtain ⟨hv2, hc2, -, -, -⟩ := times_eq S (s₀ + 1 + 1)
  have hc12 : supportCutoff S (s₀ + 1 + 1) ≤ supportCutoff S (s₀ + 2) := le_rfl
  have hEnd2 : supportCutoff S (s₀ + 1 + 1) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) hEnd
  -- the anchor of committee sleepiness is before the start of slot `s₀ + 1`
  have hA0 : anchorCW S tGAT ≤ slotStart S (s₀ + 1) := hA
  have hdw0 := dutyWindowStart_of_anchor S tGAT s₀ hA0
  have hdw1 := dutyWindowStart_of_anchor S tGAT (s₀ + 1) hAnchor
  have hdwv0 := dutyWindowStart_le_voteTime S s₀
  have hdws := dutyWindowStart_succ_le_slotStart S s₀
  -- the windows
  have hwin : ∀ u : V, ∀ t₀ : ℕ, u ∉ Sched.adv (t₀ : Int) → t₀ ≤ tAwakeEnd →
      ∀ t : ℕ, tGAT ≤ t → t ≤ t₀ → u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := by
    intro u t₀ hu h₀ t h1 h2
    have hn : u ∉ Sched.adv (t : Int) := fun h => hu (hMono _ _ (by exact_mod_cast h2) h)
    exact ⟨hAwake t h1 (le_trans h2 h₀) u hn, hn⟩
  have hHonAdv : ∀ u ∈ Hon S Sched (s₀ + 1),
      u ∉ Sched.adv ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) := by
    intro u hu
    unfold Hon roundMembers at hu
    exact (Finset.mem_sdiff.1 hu).2
  have hHon : ∀ u ∈ Hon S Sched (s₀ + 1), ∀ t : ℕ, dutyWindowStart S (s₀ + 1) ≤ t →
      t ≤ supportCutoff S (s₀ + 1 + 1) → u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) :=
    fun u hu t h1 h2 => hwin u _ (hHonAdv u hu) hEnd2 t (by omega) h2
  have hpw : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (s₀ + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) :=
    hwin p _ hp (le_trans (supportCutoff_mono S (by omega)) hEnd)
  -- the members are honest active validators and updaters
  have hSubA : honestActiveAt S Sched (s₀ + 1) ⊆ Hon S Sched (s₀ + 1) := by
    intro u hu
    unfold honestActiveAt at hu
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hu).2⟩
  have hSubU : updaterAt S Sched (s₀ + 1) ⊆ Hon S Sched (s₀ + 1) := by
    intro u hu
    unfold updaterAt at hu
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hu).2⟩
  have hMemA1 := (roundMembers_subset_honestActiveAt S Sched tGAT tAwakeEnd (s₀ + 1) hMono hAwake
    (by omega) hEnd2).1
  have hMemA0 := (roundMembers_subset_honestActiveAt S Sched tGAT tAwakeEnd s₀ hMono hAwake
    (by omega) (le_trans (supportCutoff_mono S (by omega)) hEnd)).1
  -- the committees
  have hMaj0 := committee_majority_of_committeeSleepiness S Sched (anchorCW S tGAT) s₀ hCommittees hA0
  have hMaj1 := committee_majority_of_committeeSleepiness S Sched (anchorCW S tGAT) (s₀ + 1)
    hCommittees hAnchor
  -- the previous slot's votes, each for a block that extends the anchor
  have hex : ∀ u ∈ S.P.committee s₀ ∩ Hon S Sched s₀, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s₀) u).S.T ∧
      (get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S)
        ((slotStart S (s₀ + 1) : ℕ) : Int)).AncestorEq H_u := by
    intro u hu
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x s₀ u hDiv hMono
        (hMemA0 hH) hK
    obtain ⟨H_u, hT, hv, hAH⟩ := hPrev u hu vote ⟨i, hl, hsent⟩
    subst hv
    exact ⟨H_u, ⟨i, hl, hsent⟩, hT, hAH⟩
  choose Hc hHc using hex
  let Hf : V → Block V := fun u => if h : u ∈ S.P.committee s₀ ∩ Hon S Sched s₀ then Hc u h
    else Block.genesis
  have hHf : ∀ u (hu : u ∈ S.P.committee s₀ ∩ Hon S Sched s₀), Hf u = Hc u hu :=
    fun u hu => dif_pos hu
  have hHsPrev : ∀ u ∈ S.P.committee s₀ ∩ Hon S Sched s₀, u ∈ S.P.committee (s₀ + 1 - 1) ∧
      u ∉ Sched.adv (voteTime S (s₀ + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₀ + 1 - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₀ + 1 - 1) (Hf u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      Hf u ∈ (stateBefore x (voteTime S (s₀ + 1 - 1)) u).S.T ∧
      (get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S)
        ((slotStart S (s₀ + 1) : ℕ) : Int)).AncestorEq (Hf u) := by
    intro u hu
    rw [hHf u hu]
    simp only [Nat.add_sub_cancel]
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
    have hu' : u ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) := by
      unfold Hon roundMembers at hH
      exact (Finset.mem_sdiff.1 hH).2
    exact ⟨hK, fun h => hu' (hMono _ _ (by exact_mod_cast (show voteTime S (s₀ + 1) ≤
      supportCutoff S (s₀ + 1) by omega)) h), (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
  -- the slot's voters
  have hHs : ∀ u ∈ S.P.committee (s₀ + 1) ∩ Hon S Sched (s₀ + 1), u ∈ Hon S Sched (s₀ + 1) ∧
      u ∈ S.P.committee (s₀ + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ + 1 ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₀ + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent := by
    intro u hu
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
    obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ :=
      GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x (s₀ + 1) u hDiv
        hMono (hMemA1 hH) hK
    exact ⟨hH, hK, vote, hvi, hvs, i, hl, hsent⟩
  -- the proposer's tick and the slot's only block
  obtain ⟨i, hl, hsent⟩ := id hB
  obtain ⟨hBslot, -, -, hBend⟩ := proposal_parent_walk_end S Sched x s₀ i B p hl hsent
  have hpThrough : HonestThroughTime Sched ((voteTime S (s₀ + 1) : ℕ) : Int) p := by
    intro t' ht' h
    exact hp (hMono _ _ (le_trans ht' (by exact_mod_cast (show voteTime S (s₀ + 1) ≤
      supportCutoff S (s₀ + 1) by omega))) h)
  have hOnly : ∀ w ∈ Hon S Sched (s₀ + 1), ∀ B₁ ∈ (stateBefore x (voteTime S (s₀ + 1)) w).S.T,
      B₁.slot = s₀ + 1 → B₁ = B := fun w _ B₁ hB₁ hslot =>
    only_block_of_unforgeability S Sched x hU (s₀ + 1) (voteTime S (s₀ + 1)) B B₁ p w hpThrough
      rfl hB hB₁ hslot
  have hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S (s₀ + 1)) p).S.T, B₁.root ≠ B.root :=
    fun B₁ hB₁ he => hNoCol ⟨B₁, hB₁, he⟩
  -- the floors ordered by delivery
  have hFloorW : ∀ w ∈ Hon S Sched (s₀ + 1),
      head_height_floor (stateBefore x (slotStart S (s₀ + 1)) p).S ≤
        head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ∧
      head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ≤
        (chainStateOf S.C B.parent).h := by
    intro w hw
    refine ⟨?_, (hBase.1 w hw).2⟩
    have hvt : voteTime S (s₀ + 1) = slotStart S (s₀ + 1) + Δ S := hv1
    rw [hvt]
    exact floor_le_of_delivery_unordered_upTo S Sched x GST (slotStart S (s₀ + 1)) p w hDiv hMono
      (hSync.mono (by omega))
      (hCatch.mono (by omega)) (hRoots.mono (by omega)) hParent hU
      (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast (show slotStart S (s₀ + 1) + Δ S ≤
        tAwakeEnd by omega)) hThird) (by omega) (hpw _ (by omega) (by omega)).2
      (fun t h1 h2 => hHon w hw t (by omega) (by omega))
  have hVotersPrev : ∀ w ∈ Hon S Sched (s₀ + 1), ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s₀ + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S) (s₀ + 1) votes support_votes →
      voters_count votes < 2 * (S.P.committee s₀ ∩ Hon S Sched s₀).card := fun w _ =>
    (counting_of_committee_majority S Sched x s₀ (voteTime S (s₀ + 1)) (Hon S Sched s₀) w
      hMaj0).2.2
  obtain ⟨-, hHCE, hUpd⟩ := round_base_steps_upTo S Sched x GST (s₀ + 1) (Hon S Sched (s₀ + 1))
    (S.P.committee (s₀ + 1) ∩ Hon S Sched (s₀ + 1)) (S.P.committee s₀ ∩ Hon S Sched s₀) Hf
    (get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S) ((slotStart S (s₀ + 1) : ℕ) : Int))
    B p (head_height_floor (stateBefore x (slotStart S (s₀ + 1)) p).S)
    (fun w => head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    (get_fc_root (stateBefore x (slotStart S (s₀ + 1)) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    hDiv hMono hSync hCatch hRoots hParent hOwner (by omega)
      (by simp only [Nat.add_sub_cancel]; omega) hHon
    (fun t h1 h2 => hpw t (by simp only [Nat.add_sub_cancel] at h1; omega) (by omega)) hB
    hHsPrev hVotersPrev (ancestorEq_refl _) hBase.2.2 hOnly hRootNew hHs
    (fun v _ => (counting_of_committee_majority S Sched x (s₀ + 1) (supportCutoff S (s₀ + 1 + 1))
      (Hon S Sched (s₀ + 1)) v hMaj1).2.1)
    (counting_of_committee_majority S Sched x (s₀ + 1) 0 (Hon S Sched (s₀ + 1)) p hMaj1).1
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hFloorW
    (fun w hw => (hBase.1 w hw).1) (fun v hv => (hBase.2.1 v hv).1)
    (by
      obtain ⟨W, hW, hAW, hRW, hφW⟩ := anchor_has_viable_head S Sched x (slotStart S (s₀ + 1)) p
        (stateBefore x (slotStart S (s₀ + 1)) p).A ((slotStart S (s₀ + 1) : ℕ) : Int)
      exact ⟨W, hW, hAW, hRW, hφW⟩)
  refine ⟨honestChainExtends_mono S Sched x _ _ B _ hSubA hHCE, fun u hu => ?_, hBslot, ?_⟩
  · obtain ⟨A₁, hU₁, hS₁, -⟩ := hUpd u (hSubU hu)
    rw [state_saved_of_update S Sched x (s₀ + 1) u A₁ hDiv hMono
      (updaterAt_window S Sched (s₀ + 1) u hMono hu) hU₁]
    exact hS₁
  · rcases hBend with h | h
    · exact h
    · rw [h]
      rcases get_anchor_root_or_viable (stateBefore x (slotStart S (s₀ + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S)
        ((slotStart S (s₀ + 1) : ℕ) : Int) with h' | h'
      · rw [h']
        obtain ⟨W, hW⟩ := frame_has_viable_head S Sched x (slotStart S (s₀ + 1)) p
        obtain ⟨hWT, hFW, hRW, -⟩ := (mem_viable_heads_iff _ _).1 hW
        have hRT : (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).fc_root ∈
            (stateBefore x (slotStart S (s₀ + 1)) p).S.T :=
          ancestors_mem_T_of_exec S Sched x _ p W _ hWT hRW
        rw [mem_viable_tree_iff]
        exact ⟨(mem_fg_to_ac_tree _ _).2 ⟨hRT,
            by rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x _ p⟩,
          ancestorEq_refl _, W, Finset.mem_inter.2 ⟨(mem_fg_to_ac_tree _ _).2 ⟨hWT, hFW⟩, hW⟩, hRW⟩
      · exact h'

namespace PartAHypsUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- **A member saves a confirmation at every slot after the fast block's round.** For a slot
`σ ≥ r * R + 1` with its support cutoff of slot `σ + 1` in the phase, every member of
`Hon S Sched σ` saves some confirmation of slot `σ`: the root of its fork choice at its update is
a line source of a slot before `σ` (`root_source`), so every vote of slot `σ` of the committee's
members extends it, and so its finalized block (the line invariant); those votes reach it early
(Lemma 12) and are more than half of its pool's voters, so the update saves the end of its walk
(`update_confirmation_saves_of_supporters`).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem member_saves_confirmation (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    {σ : ℕ} (hσ : r * S.C.R + 1 ≤ σ) (hEnd : supportCutoff S (σ + 1) ≤ tAwakeEnd) {u : V}
    (hu : u ∈ Hon S Sched σ) :
    ∃ C : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) u).A.saved_confirmation σ = some C := by
  obtain ⟨σ₁, rfl⟩ : ∃ σ₁, σ = σ₁ + 1 := ⟨σ - 1, by omega⟩
  have hG : ∀ σ', σ' ≤ σ₁ → LineInv S Sched x r H₂ σ' := P.lineInv_upto hEnd
  have hG1 : LineInv S Sched x r H₂ (σ₁ + 1) := P.lineInv_all (σ₁ + 1) hEnd
  obtain ⟨hv1, hc1, -, hs1, hΔ⟩ := times_eq S (σ₁ + 1)
  obtain ⟨hv2, hc2, -, -, -⟩ := times_eq S (σ₁ + 1 + 1)
  have hvw := P.member1 (show r * S.C.R ≤ σ₁ + 1 by omega) hu hEnd
  have hdw : dutyWindowStart S (σ₁ + 1 + 1) ≤ slotStart S (σ₁ + 1) :=
    dutyWindowStart_succ_le_slotStart S (σ₁ + 1)
  have hdwc : dutyWindowStart S (σ₁ + 1 + 1) < supportCutoff S (σ₁ + 1 + 1) := by omega
  have hvc := hvw (supportCutoff S (σ₁ + 1 + 1)) hdwc.le le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (σ₁ + 1 + 1) (supportCutoff S (σ₁ + 1 + 1))
    u P.hDiv P.hMono hdwc (fun t h1 h2 => (hvw t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ := update_state_of_duty S Sched x (σ₁ + 1) u P.hDiv
    hvc hAw
  rw [hsave]
  -- the root of `u`'s fork choice is a line source of a slot before `σ₁ + 1`
  have haR : aR S r < supportCutoff S (σ₁ + 1 + 1) := by
    have : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
    rw [this]
    exact supportCutoff_lt S (by omega)
  obtain ⟨r', -, hcut, hρ⟩ := P.root_source hG (by omega)
    (show supportCutoff S (σ₁ + 2) ≤ tAwakeEnd from hEnd) haR le_rfl hvc.2
  have hr'σ : r' * S.C.R + 1 ≤ σ₁ + 1 := by
    by_contra h
    have := supportCutoff_mono S (show σ₁ + 1 + 1 ≤ r' * S.C.R + 1 by omega)
    omega
  have hInv := hG1 _ _ hρ hr'σ
  have hmem := P.members_sets (show r * S.C.R ≤ σ₁ + 1 by omega) hEnd
  have hex : ∀ w ∈ S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1), ∃ H_w : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (σ₁ + 1)) ∧
        (⟨w, NamedObject.gfVote (GoldfishVote.mk w (σ₁ + 1) H_w.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_w ∈ (stateBefore x (voteTime S (σ₁ + 1)) w).S.T ∧
      (get_fc_root (stateBefore x (supportCutoff S (σ₁ + 1 + 1)) u).S).AncestorEq H_w := by
    intro w hw
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hw
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x (σ₁ + 1) w
        P.hDiv P.hMono (hmem.1 hH) hK
    obtain ⟨H_w, hT, hv, hRH⟩ := hInv.1 w hH vote ⟨i, hl, hsent⟩
    subst hv
    exact ⟨H_w, ⟨i, hl, hsent⟩, hT, hRH⟩
  choose Hc hHc using hex
  let Hf : V → Block V := fun w => if h : w ∈ S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1) then
    Hc w h else Block.genesis
  have hHf : ∀ w (hw : w ∈ S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1)), Hf w = Hc w hw :=
    fun w hw => dif_pos hw
  have hFρ := F_ancestorEq_fc_root_of_stateBefore S Sched x (supportCutoff S (σ₁ + 1 + 1)) u
  have hHeld : ∀ w ∈ S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1),
      HeldEarlyVoteFor S.C (stateBefore x (supportCutoff S (σ₁ + 1 + 1)) u).A
        (fg_to_ac (stateBefore x (supportCutoff S (σ₁ + 1 + 1)) u).S) (σ₁ + 1) (Hf w) w :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until_upTo S Sched x GST
      (σ₁ + 1) (supportCutoff S (σ₁ + 1 + 1)) _ Hf u P.hDiv P.hMono
      (P.hSync.mono (le_trans (supportCutoff_mono S (by omega)) hEnd))
      (P.hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hEnd))
      (P.hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hEnd)) P.hParent P.hOwner
      (P.gst (show r * S.C.R ≤ σ₁ + 1 by omega)).2.1
      (supportCutoff_mono S (by omega))
      (fun w hw => by
        rw [hHf w hw]
        obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hw
        have hw' : w ∉ Sched.adv ((supportCutoff S (σ₁ + 1 + 1) : ℕ) : Int) := by
          unfold Hon roundMembers at hH
          exact (Finset.mem_sdiff.1 hH).2
        exact ⟨hK, hw', (hHc w hw).1, (hHc w hw).2.1⟩)
      (fun t h1 h2 => hvw t (by omega) (by omega))
      (fun w hw => by rw [hHf w hw]; exact ancestorEq_trans hFρ (hHc w hw).2.2)
  have hRoots₂ : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (σ₁ + 1 + 1)) u).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ u
  have hSup : ∀ w ∈ S.P.committee (σ₁ + 1) ∩ Hon S Sched (σ₁ + 1), EarlySupporterOf S.C
      (expireLocks (stateBefore x (supportCutoff S (σ₁ + 1 + 1)) u).A
        ((supportCutoff S (σ₁ + 1 + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (σ₁ + 1 + 1)) u).S) (σ₁ + 1 + 1 - 1)
      (fg_to_ac (stateBefore x (supportCutoff S (σ₁ + 1 + 1)) u).S).F w :=
    fun w hw => (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).2
      (heldEarlyVoteFor_earlySupporterOf S.C _ _ (σ₁ + 1) _ (Hf w) w (hHeld w hw)
        (by rw [hHf w hw, fg_to_ac_F]; exact ancestorEq_trans hFρ (hHc w hw).2.2))
  have hcount := (counting_of_committee_majority S Sched x (σ₁ + 1)
    (supportCutoff S (σ₁ + 1 + 1)) (Hon S Sched (σ₁ + 1)) u
    (P.committee (show r * S.C.R ≤ σ₁ + 1 by omega))).2.1
  have h := GoldilocksCorrectness.Proofs.Routines.update_confirmation_saves S.C S.P
    _ A'' _ _ (σ₁ + 1 + 1) _ (Nat.le_add_left 1 _) hRoots₂ hSup
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
        exact pool_slot_of_stateBefore S Sched x _ u (σ₁ + 1))
    (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hcount) hUpdate
  rw [Nat.add_sub_cancel] at h
  exact h

/-- **The proposer's anchor is an early line source.** For a slot `s` at least `k + 2` slots after
`r * R`, with its support cutoff in the phase and its proposer honest then, the anchor of the
proposer's walk at the start of slot `s` is a line source of a slot `μ` with `μ + 2 ≤ s`: the
root (`root_source`), or an ancestor of a live lock's block (`source_lock`, Lemma 41).

Restated with the delivery premises up to `tAwakeEnd`: the bound of the bundle `PartAHypsUpTo`. -/
theorem anchor_source (P : PartAHypsUpTo S Sched x GST tGAT tAwakeEnd r H₂ v L A') {s : ℕ}
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hEnd : supportCutoff S s ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int)) :
    ∃ μ : ℕ, μ + 2 ≤ s ∧ LineSource S Sched x r H₂ μ
      (get_anchor (stateBefore x (slotStart S s) (S.P.proposer s)).A
        (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S)
        ((slotStart S s : ℕ) : Int)) := by
  have hk := S.C.k_ge_two
  obtain ⟨σ₁, rfl⟩ : ∃ σ₁, s = σ₁ + 2 := ⟨s - 2, by omega⟩
  have hG : ∀ σ', σ' ≤ σ₁ → LineInv S Sched x r H₂ σ' := P.lineInv_upto hEnd
  obtain ⟨hvs, hcs, hfs, hss, hΔ⟩ := times_eq S σ₁
  obtain ⟨hvs1, hcs1, hfs1, hss1, -⟩ := times_eq S (σ₁ + 1)
  obtain ⟨hvs2, hcs2, -, -, -⟩ := times_eq S (σ₁ + 2)
  rw [show σ₁ + 1 + 1 = σ₁ + 2 from rfl] at hss1
  have ht : slotStart S (σ₁ + 2) ≤ supportCutoff S (σ₁ + 2) := by omega
  have hpt : S.P.proposer (σ₁ + 2) ∉ Sched.adv ((slotStart S (σ₁ + 2) : ℕ) : Int) :=
    fun h => hp (P.hMono _ _ (by exact_mod_cast ht) h)
  have haR : aR S r < slotStart S (σ₁ + 2) := by
    have : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
    have := supportCutoff_mono S (show r * S.C.R + 1 ≤ σ₁ + 1 by omega)
    omega
  have hroot : ∃ μ : ℕ, μ + 2 ≤ σ₁ + 2 ∧ LineSource S Sched x r H₂ μ
      (get_fc_root (stateBefore x (slotStart S (σ₁ + 2)) (S.P.proposer (σ₁ + 2))).S) := by
    obtain ⟨r', -, hcut, hsrc⟩ := P.root_source hG (show r * S.C.R ≤ σ₁ by omega) hEnd haR ht hpt
    refine ⟨r' * S.C.R, ?_, hsrc⟩
    by_contra h
    have := supportCutoff_mono S (show σ₁ + 2 ≤ r' * S.C.R + 1 by omega)
    omega
  rcases get_anchor_cases_locked (stateBefore x (slotStart S (σ₁ + 2)) (S.P.proposer (σ₁ + 2))).A
    (fg_to_ac (stateBefore x (slotStart S (σ₁ + 2)) (S.P.proposer (σ₁ + 2))).S)
    ((slotStart S (σ₁ + 2) : ℕ) : Int) with h | ⟨-, e, he, hl, hAe⟩
  · rw [h, fc_root_eq]
    exact hroot
  · have hl' := hl
    simp only [is_live_iff] at hl'
    obtain ⟨μ₀, hd, hcut, -, hsrc⟩ := P.source_lock hpt
      (le_trans ht (le_trans (supportCutoff_mono S (by omega)) hEnd)) he
    have hlo : r * S.C.R + 1 ≤ μ₀ :=
      GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S (r * S.C.R + 1) μ₀
        (slotStart S (σ₁ + 2)) e hd hl'.1 (by
          obtain ⟨hvk, -, -, -, -⟩ := times_eq S (r * S.C.R + 1 + S.C.k)
          have := slotStart_mono S (show r * S.C.R + 1 + S.C.k + 1 ≤ σ₁ + 2 by omega)
          obtain ⟨-, -, -, hsk, -⟩ := times_eq S (r * S.C.R + 1 + S.C.k)
          omega)
    refine ⟨μ₀, ?_, (hsrc hlo).anc hAe⟩
    by_contra h
    have := supportCutoff_mono S (show σ₁ + 2 ≤ μ₀ + 1 by omega)
    omega

end PartAHypsUpTo

/-- **C2, every round after the fast block is quiet relative to its own confirmations (copy with
the round's first slot and no root collision).** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. Why: the first two clauses are C1's
(`round_base_after_fast_block_opening`); the members save `B` (`healed_round_base_of_prev_votes`,
the previous slot's votes extending the proposer's anchor by `anchor_source` and the line
invariant), so `B` and every member's confirmation of a slot from `s − 1` on are line sources
(`source_conf`), and `stepFrame_source` gives the third and fourth; for the fifth, the next
proposer's root is a line source of a slot `μ ≤ s'' − 2` (`root_source`), on the chain of its
own confirmation when `μ = s'' − 2` and of any member's confirmation of slot `s'' − 2`
(`member_saves_confirmation`) otherwise, and `frame_source_at` gives the viable head.

Roots name blocks until `supportCutoff S s''`: the bundle `PartAHyps` is built with its end time
`supportCutoff S s''`, the latest time its kit reads here; C1 and C3 read up to
`supportCutoff S (s + 2)`.

Restated with the delivery premises up to `supportCutoff S s''`: the bound of its roots `hRoots`, the end time of the bundle `PartAHypsUpTo` it builds. -/
theorem quiet_round_after_fast_block_opening_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V) (L B : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s''))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s''))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s''))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : supportCutoff S s'' ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hq : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int))
    (hB : ProposalAt S Sched x s B)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x s B) :
    QuietRoundOnConfirmations S Sched x (Hon S Sched) B s s'' := by
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hEndA : ∀ σ : ℕ, σ ≤ s'' → supportCutoff S σ ≤ tAwakeEnd := fun σ h =>
    le_trans (supportCutoff_mono S h) hEnd
  have hBase := round_base_after_fast_block_opening_upTo S Sched x GST tGAT tAwakeEnd r H₂ s v L B A'
    hDiv hMono (hSync.mono (supportCutoff_mono S (by omega)))
    (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner
    hU hGST hThird hAwake hCommittees hAnchor hOld hv hL hUpdate hFast hs hsR (hEndA _ (by omega))
    hp hB
  -- the bundle with its end time `supportCutoff S s''`
  have P : PartAHypsUpTo S Sched x GST tGAT (supportCutoff S s'') r H₂ v L A' := ⟨hDiv, hMono,
    hSync, hCatch, hRoots, hParent, hOwner, hU, hGST,
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) hThird,
    fun t' h1 h2 => hAwake t' h1 (le_trans h2 hEnd), hCommittees, hAnchor, hOld, hv, hUpdate,
    hFast, hL⟩
  have hEndM : ∀ σ : ℕ, σ ≤ s'' → supportCutoff S σ ≤ supportCutoff S s'' := fun σ h =>
    supportCutoff_mono S h
  have hEnd : supportCutoff S s'' ≤ supportCutoff S s'' := le_rfl
  -- the members save `B`
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source (show r * S.C.R + S.C.k + 2 ≤ s by omega)
    (hEndM _ (by omega)) hp
  have hGs1 : LineInv S Sched x r H₂ (s - 1) :=
    P.lineInv_all (s - 1) (by rw [Nat.sub_add_cancel (by omega)]; exact hEndM _ (by omega))
  obtain ⟨-, hSaved, -, -⟩ := healed_round_base_of_prev_votes_upTo S Sched x GST tGAT tAwakeEnd s B hDiv
    hMono (hSync.mono (supportCutoff_mono S (by omega)))
    (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU
    hGST hThird hAwake hCommittees (by omega)
    (le_trans hAnchor (slotStart_mono S (by omega))) (le_trans hAnchor (slotStart_mono S (by omega)))
    (hEndA _ (by omega)) hp hB hBase hNoCol
    (fun u hu vote hvote => (hGs1 μA _ hAsrc (by omega)).1 u (Finset.mem_inter.1 hu).2 vote hvote)
  have hnon : ∀ σ : ℕ, r * S.C.R ≤ σ → ∃ u, u ∈ Hon S Sched σ := by
    intro σ hσ
    have h := P.committee hσ
    obtain ⟨u, hu⟩ : (S.P.committee σ ∩ Hon S Sched σ).Nonempty :=
      Finset.card_pos.1 (by omega)
    exact ⟨u, (Finset.mem_inter.1 hu).2⟩
  obtain ⟨u₀, hu₀⟩ := hnon s (by omega)
  have hu₀U := ((P.members_sets (show r * S.C.R ≤ s by omega) (hEndM _ (by omega))).2) hu₀
  have hBsrc : LineSource S Sched x r H₂ s B :=
    P.source_conf (by omega) hu₀ (hEndM _ (by omega)) (hSaved u₀ hu₀U) (ancestorEq_refl B)
  have hwadv : ∀ s' : ℕ, ∀ w ∈ Hon S Sched (s' + 1),
      w ∉ Sched.adv ((supportCutoff S (s' + 2) : ℕ) : Int) := by
    intro s' w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  refine ⟨hBase.1, hBase.2.1, fun s' hs1 hs2 w hw => ?_, fun s' hs1 hs2 σ hσ1 hσ2 u hu C hC w hw => ?_,
    ?_⟩
  · exact P.stepFrame_source (P.lineInv_upto (hEndM _ hs2)) (by omega) (hEndM _ hs2)
      (hwadv s' w hw) hBsrc hs1
  · have hCsrc : LineSource S Sched x r H₂ σ C :=
      P.source_conf (by omega) hu (hEndM _ (by omega)) hC (ancestorEq_refl C)
    exact P.stepFrame_source (P.lineInv_upto (hEndM _ hs2)) (by omega) (hEndM _ hs2)
      (hwadv s' w hw) hCsrc hσ2
  · obtain ⟨σ₂, rfl⟩ : ∃ σ₂, s'' = σ₂ + 2 := ⟨s'' - 2, by omega⟩
    set q := S.P.proposer (σ₂ + 2) with hqdef
    have hG : ∀ σ', σ' ≤ σ₂ → LineInv S Sched x r H₂ σ' := P.lineInv_upto hEnd
    obtain ⟨hvs1, hcs1, hfs1, hss1, hΔ⟩ := times_eq S (σ₂ + 1)
    obtain ⟨hvs2, hcs2, -, -, -⟩ := times_eq S (σ₂ + 2)
    rw [show σ₂ + 1 + 1 = σ₂ + 2 from rfl] at hss1
    have ht : slotStart S (σ₂ + 2) ≤ supportCutoff S (σ₂ + 2) := by omega
    have hqt : q ∉ Sched.adv ((slotStart S (σ₂ + 2) : ℕ) : Int) :=
      fun h => hq (hMono _ _ (by exact_mod_cast ht) h)
    have haR : aR S r < slotStart S (σ₂ + 2) := by
      have : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
      have := supportCutoff_mono S (show r * S.C.R + 1 ≤ σ₂ + 1 by omega)
      omega
    obtain ⟨r', -, hcut, hρ⟩ := P.root_source hG (show r * S.C.R ≤ σ₂ by omega) hEnd haR ht hqt
    have hr' : r' * S.C.R ≤ σ₂ := by
      by_contra h
      have := supportCutoff_mono S (show σ₂ + 2 ≤ r' * S.C.R + 1 by omega)
      omega
    -- a member's confirmation of slot `σ₂` on the root's chain
    obtain ⟨C, ⟨u, hu, hC⟩, hRC⟩ : ∃ C : Block V,
        (∃ u ∈ Hon S Sched σ₂,
          (stateBefore x (supportCutoff S (σ₂ + 1) + 1) u).A.saved_confirmation σ₂ = some C) ∧
        (get_fc_root (stateBefore x (slotStart S (σ₂ + 2)) q).S).AncestorEq C := by
      rcases Nat.lt_or_eq_of_le hr' with hlt | heq
      · obtain ⟨u, hu⟩ := hnon σ₂ (by omega)
        obtain ⟨C, hC⟩ := P.member_saves_confirmation (show r * S.C.R + 1 ≤ σ₂ by omega)
          (hEndM _ (by omega)) hu
        exact ⟨C, ⟨u, hu, hC⟩, (hG σ₂ le_rfl _ _ hρ (by omega)).2.2 u hu C hC⟩
      · rw [heq] at hρ
        obtain ⟨u, hu, A₀, C₀, X₀, -, -, hC₀, hρX₀, hX₀C₀, -⟩ := hρ
        exact ⟨C₀, ⟨u, hu, hC₀⟩, ancestorEq_trans hρX₀ hX₀C₀⟩
    have hCsrc : LineSource S Sched x r H₂ σ₂ C :=
      P.source_conf (by omega) hu (hEndM _ (by omega)) hC (ancestorEq_refl C)
    rw [← fc_root_eq] at hRC
    obtain ⟨W, hW, hWv, hCW⟩ := (P.frame_source_at hG (show r * S.C.R ≤ σ₂ by omega) hEnd
      (show voteTime S (σ₂ + 1) ≤ slotStart S (σ₂ + 2) by omega) ht hqt hCsrc le_rfl).2.1 hRC
    exact ⟨C, ⟨u, hu, hC⟩, hRC, W, hW, hWv, hCW⟩

end GoldilocksCorrectness.Proofs.Executions

