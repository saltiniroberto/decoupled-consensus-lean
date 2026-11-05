module
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Proofs.Executions.Lemma34
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Blocks

@[expose] public section

/-!
# Lemma 43: two live locks made after `GST` are compatible

The proof of `lem43_live_locks_after_GST_compatible`, stated in
`GoldilocksCorrectness/Statements/Executions/HealingStatements.lean`, and the facts about times
and blocks it reads.

## The route

Lemma 39 gives the slots `s''`, `s'` of the two entries, with `v`'s and `w`'s updates of slots
`s'' + 1` and `s' + 1`. The statement is symmetric in `v` and `w`, so the proof is written for
`s' ≤ s''` (`live_locks_compatible_of_deadline_le`) and applied twice. Both slots are at least
`s₁` (the deadline bounds), and `s' ≥ s − k − 1`, since `e_w` is live at `t ≥ slotStart S s`; so
the support cutoff of slot `s' + 1`, and every later time used, is inside `[dutyWindowStart S s,
t]`. Three cases.

- `s' = s''`, or `e_v`'s block passes the slow test: both blocks are ancestors-or-equal of the
  two validators' saved confirmations of slot `s'` (Lemma 39 for `w`, and Lemma 39 or Lemma 37
  for `v`), saved by their updates of slot `s' + 1` (Lemma 39 or Lemma 40), which save compatible
  blocks (Lemma 31). Lemma 31's awake windows, from the support cutoff to the view freeze of slot
  `s'`, come from the duty test of those updates: a validator whose tick records that it has
  been awake since a time `τ`, and is awake and honest at that tick, has been awake at every time
  since `τ` (`awake_of_tickInput_awakeSince`), and `τ` is at most the duty window's start of slot
  `s' + 1`, which is at most the support cutoff of slot `s'`.
- `s' < s''` and `e_v`'s block is a fast block of `v`'s update: when `e_v`'s block is an ancestor
  of `w`'s finalized block before `t` or that block, `e_w`'s block, in `w`'s frame tree, descends
  from it. Otherwise `w`'s finalized block is an ancestor-or-equal of `e_v`'s block, and Lemma 34 at
  slot `s''` applies to the entries the two validators hold just after the update of slot `s''`
  (Lemma 39's tracking clause), with Lemma 42 for the revocation and
  `awakeSince_kept_of_awake_throughout` for its duty test.

## Why not Lemma 33

The brief's route took the first case through Lemma 33, whose hypothesis asks the two validators'
saved confirmations to be compatible at every slot from `s'' + 1 − k` to `s''`. A slot of that range
may be before `s₁`, where Lemma 31's synchrony hypothesis at a slot `s₀`,
`GST ≤ supportCutoff S s₀`, does not hold; and the brief's bound `s' ≥ s − k` (so that Lemma 31's
windows lie in `[dutyWindowStart S s, t]`) is off by one: a lock of slot `s − k − 1` is live at the
times from `slotStart S s` to before `voteTime S s`. The proof uses only the slot `s'`, as Lemma 45
does, and takes Lemma 31's awake windows from the updates' duty tests.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_succ_le_supportCutoff duty_window_start_mono one_le_Δ slotStart_cast slotStart_eq
  slotStart_mono slot_le_of_t_lt supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt
  t_lt_of_lt viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both
  compatible_of_compatible_ancestorEq compatible_symm')

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Times -/

/-! ## Blocks -/

/-! ## The ordered case -/

variable {S : Setup V} {Sched : Schedule V}

/-- Lemma 43 when `e_w`'s deadline is at most `e_v`'s: the two live lock entries are on compatible
blocks. The hypotheses are those of `lem43_live_locks_after_GST_compatible` without the
finalized-block condition at `v` (`hFvw`), which this case does not read.

The variables: those of `lem43_live_locks_after_GST_compatible`.

Roots name blocks until `t`: Lemma 31 and Lemma 42, which the proof calls at the slots of the
two entries, take blocks as held up to support cutoffs before `t`
(`lem39_lock_entry_provenance`). -/
theorem live_locks_compatible_of_deadline_le (x : AtomicExec (protocol S) Sched)
    (GST s₁ s t : ℕ) (v w : V) (e_v e_w : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s₁)
    (hst : slotStart S s ≤ t)
    (hv : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int))
    (hw : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (he_v : e_v ∈ (stateBefore x t v).A.lock_entries)
    (hd_v : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_v.d)
    (he_w : e_w ∈ (stateBefore x t w).A.lock_entries)
    (hlive_w : is_live (fg_to_ac (stateBefore x t w).S) (t : Int) e_w = true)
    (hd_w : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_w.d)
    (hFwv : (stateBefore x t w).S.F.compatible e_v.B = true)
    (hle : e_w.d ≤ e_v.d) :
    e_v.B.compatible e_w.B = true := by
  have hΔ := one_le_Δ S
  have hΔi : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have hk2 := S.C.k_ge_two
  -- the liveness of `e_w`
  have hlw : (t : Int) < e_w.d ∧ e_w.B ∈ (fg_to_ac (stateBefore x t w).S).tree := by
    exact (is_live_iff _ _ _).1 hlive_w
  -- Lemma 39 on both entries
  obtain ⟨s'', hdv, hcv, ⟨τv, hτv, hτvle⟩, A_v, hU_v, e₀v, he₀v, hd₀v, -, -, ⟨C₀v, hC₀v, hB₀v⟩,
      hFS_v, htrack_v⟩ :=
    GoldilocksCorrectness.Proofs.Executions.lem39_lock_entry_provenance S Sched x t v e_v hDiv he_v
  obtain ⟨s', hdw, hcw, ⟨τw, hτw, hτwle⟩, A_w, hU_w, e₀w, -, hd₀w, -, -, ⟨C₀w, hC₀w, hB₀w⟩,
      -, htrack_w⟩ :=
    GoldilocksCorrectness.Proofs.Executions.lem39_lock_entry_provenance S Sched x t w e_w hDiv he_w
  -- the deadlines and the liveness at `Int`, where `omega` reads them
  have hdv' : @Eq Int e_v.d (S.C.t_ (s'' + S.C.k) + 5 * S.C.Δ) := hdv
  have hdw' : @Eq Int e_w.d (S.C.t_ (s' + S.C.k) + 5 * S.C.Δ) := hdw
  have hle' : @LE.le Int _ e_w.d e_v.d := hle
  have hd_v' : @LE.le Int _ (S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ) e_v.d := hd_v
  have hd_w' : @LE.le Int _ (S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ) e_w.d := hd_w
  have hlw1 : @LT.lt Int _ (t : Int) e_w.d := hlw.1
  have hΔi' : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
  -- the slots
  have hbwv : s' ≤ s'' := by
    have h := slot_le_of_t_lt S (s := s' + S.C.k) (s' := s'' + S.C.k) (n := 0)
      (r := 4 * S.C.Δ) (by omega) (by omega)
    omega
  have hs₁v : s₁ ≤ s'' := by
    have h := slot_le_of_t_lt S (s := s₁ + S.C.k) (s' := s'' + S.C.k) (n := 0)
      (r := 4 * S.C.Δ) (by omega) (by omega)
    omega
  have hs₁w : s₁ ≤ s' := by
    have h := slot_le_of_t_lt S (s := s₁ + S.C.k) (s' := s' + S.C.k) (n := 0)
      (r := 4 * S.C.Δ) (by omega) (by omega)
    omega
  -- `s ≤ s' + k + 1`: `e_w` is live at `t ≥ slotStart S s`
  have hsw : s ≤ s' + S.C.k + 1 := by
    have h1 : @LE.le Int _ (S.C.t_ s) (t : Int) := by
      rw [← slotStart_cast]
      exact_mod_cast hst
    exact slot_le_of_t_lt S (s := s) (s' := s' + S.C.k) (n := 1) (r := 5 * S.C.Δ)
      (by omega) (by omega)
  -- `s'' + 1 ≤ s' + k`: `e_w` is live at `t`, after the support cutoff of slot `s'' + 1`
  have hvw : s'' + 1 ≤ s' + S.C.k := by
    have h1 : @LT.lt Int _ (S.C.t_ (s'' + 1) + 2 * S.C.Δ) (t : Int) := by
      rw [← supportCutoff_cast]
      exact_mod_cast hcv
    exact slot_le_of_t_lt S (s := s'' + 1) (s' := s' + S.C.k) (n := 0) (r := 3 * S.C.Δ)
      (by omega) (by omega)
  -- the times of slot `s'`, inside `[dutyWindowStart S s, t]`
  have hcw1 : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S _
  have hvw1 : voteTime S (s' + 1) = slotStart S (s' + 1) + Δ S := voteTime_eq S _
  have hssw : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S s', Nat.mul_add, Nat.mul_one]
  have hvwb : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hcwb : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
  have hfrw : viewFreeze S s' = slotStart S s' + 3 * Δ S := viewFreeze_eq S s'
  have hdcw : dutyWindowStart S s ≤ supportCutoff S (s' + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  have hGSTw : GST ≤ supportCutoff S s' := by
    have h := slotStart_mono S hs₁w
    rw [voteTime_eq S s₁] at hGST
    omega
  -- `v` and `w` are honest at every time up to `t`
  have hdt : dutyWindowStart S s ≤ t := by omega
  have hhon : ∀ u : V, (∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int)) →
      ∀ t' : ℕ, t' ≤ t → u ∉ Sched.adv (t' : Int) := fun u hu t' ht' h =>
    (hu t hdt le_rfl).2 (hMono _ _ (by exact_mod_cast ht') h)
  -- the awake window of Lemma 31 at slot `s'`, from the duty test of an update of slot `s' + 1`
  have hwin : ∀ u : V, (∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int)) →
      ∀ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s' + 1)))
        (supportCutoff S (s' + 1)) u).awakeSince = some τ →
      τ ≤ duty_window_start S.C (s' + 1) →
      ∀ t' : ℕ, supportCutoff S s' ≤ t' → t' ≤ viewFreeze S s' →
        u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int) := by
    intro u hu τ hτ hτle t' h1 h2
    have hc := hu (supportCutoff S (s' + 1)) hdcw (by omega)
    refine ⟨awake_of_tickInput_awakeSince x hDiv hMono (by omega) hτ hc.1 hc.2 t' ?_ (by omega),
      hhon u hu t' (by omega)⟩
    have h3 : duty_window_start S.C (s' + 1) ≤ ((dutyWindowStart S (s' + 1) : ℕ) : Int) :=
      duty_window_start_le_dutyWindowStart S (s' + 1)
    have h4 : dutyWindowStart S (s' + 1) ≤ supportCutoff S s' :=
      dutyWindowStart_succ_le_supportCutoff S (by omega)
    have h5 : ((supportCutoff S s' : ℕ) : Int) ≤ (t' : Int) := by exact_mod_cast h1
    have h6 : ((dutyWindowStart S (s' + 1) : ℕ) : Int) ≤ ((supportCutoff S s' : ℕ) : Int) := by
      exact_mod_cast h4
    exact Int.le_trans hτle (Int.le_trans h3 (Int.le_trans h6 h5))
  -- `e_w`'s block is `w`'s saved confirmation of slot `s'` or an ancestor of it
  obtain ⟨e₁w, -, -, hB₁w, hB₁₀w⟩ := htrack_w t hcw le_rfl
  have hBw : e_w.B.AncestorEq C₀w := ancestorEq_trans hB₁w (ancestorEq_trans hB₁₀w hB₀w)
  -- the comparison through slot `s'`, given `v`'s update of slot `s' + 1` saving `C₁`
  have key : ∀ (A₁ : ACState V) (C₁ : Block V) (τ₁ : Time),
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
          ((supportCutoff S (s' + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S)
        ((supportCutoff S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A₁ →
      A₁.saved_confirmation s' = some C₁ →
      (tickInputState x (stepBefore x (supportCutoff S (s' + 1)))
        (supportCutoff S (s' + 1)) v).awakeSince = some τ₁ →
      τ₁ ≤ duty_window_start S.C (s' + 1) →
      e_v.B.AncestorEq C₁ → e_v.B.compatible e_w.B = true := by
    intro A₁ C₁ τ₁ hU₁ hS₁ hτ₁ hτ₁le hB₁
    have hcomp := GoldilocksCorrectness.Proofs.Executions.lem31_saved_confirmations_compatible S
      Sched x GST s' v w A₁ A_w C₁ C₀w hDiv hMono hSync hCatch (hRoots.mono (by omega))
      hGSTw
      (hwin v hv τ₁ hτ₁ hτ₁le) (hwin w hw τw hτw hτwle) (hhon v hv _ (by omega))
      (hhon w hw _ (by omega)) hU₁ hS₁ hU_w hC₀w
    exact compatible_of_ancestorEq_both hB₁ hBw hcomp
  -- `e_v`'s block is an ancestor-or-equal of the block `v`'s update added
  obtain ⟨e₁v, -, -, hB₁v, hB₁₀v⟩ := htrack_v t hcv le_rfl
  have hBv₀ : e_v.B.AncestorEq e₀v.B := ancestorEq_trans hB₁v hB₁₀v
  rcases Nat.lt_or_ge s' s'' with hlt | hge
  · rcases hFS_v with hFast | hSlow
    · -- the fast case: through `w`'s revocation of slot `s'' + 1`
      have hFw := (compatible_iff _ _).1 hFwv
      rcases hFw with hFe | heF
      · -- `w`'s finalized block before `t` is an ancestor-or-equal of `e_v`'s block
        have hcv' : supportCutoff S (s'' + 1) + 1 ≤ t := hcv
        obtain ⟨e'v, he'v, hd'v, hB'v, hB'₀v⟩ := htrack_v (supportCutoff S (s'' + 1) + 1)
          (by omega) hcv'
        have hcwv : supportCutoff S (s' + 1) < supportCutoff S (s'' + 1) + 1 := by
          have := supportCutoff_lt_of_lt S (show s' + 1 < s'' + 1 by omega)
          omega
        obtain ⟨e'w, he'w, hd'w, hB'w, -⟩ := htrack_w (supportCutoff S (s'' + 1) + 1) hcwv hcv'
        -- the times of slot `s''`
        have hcv1 : supportCutoff S (s'' + 1) = voteTime S (s'' + 1) + Δ S :=
          supportCutoff_eq S _
        have hvv1 : voteTime S (s'' + 1) = slotStart S (s'' + 1) + Δ S := voteTime_eq S _
        have hssv : slotStart S (s'' + 1) = slotStart S s'' + 4 * Δ S := by
          rw [slotStart_eq, slotStart_eq S s'', Nat.mul_add, Nat.mul_one]
        have hvvb : voteTime S s'' = slotStart S s'' + Δ S := voteTime_eq S s''
        have hcvb : supportCutoff S s'' = voteTime S s'' + Δ S := supportCutoff_eq S s''
        have hfrv : viewFreeze S s'' = slotStart S s'' + 3 * Δ S := viewFreeze_eq S s''
        have hdcv : dutyWindowStart S s ≤ supportCutoff S s'' :=
          dutyWindowStart_le_supportCutoff S (by omega)
        have hGSTv : GST ≤ voteTime S s'' := by
          have h := slotStart_mono S hs₁v
          rw [voteTime_eq S s₁] at hGST
          omega
        have hcw_vt : supportCutoff S (s' + 1) ≤ voteTime S (s'' + 1) := by
          have := slotStart_mono S (show s' + 2 ≤ s'' + 1 by omega)
          have h2 : slotStart S (s' + 2) = slotStart S (s' + 1) + 4 * Δ S := by
            rw [slotStart_eq, slotStart_eq S (s' + 1), show s' + 2 = s' + 1 + 1 by omega,
              Nat.mul_add, Nat.mul_one]
          omega
        -- `w`'s finalized block before the vote time of slot `s'' + 1` is compatible with
        -- `e₀v`'s block
        have hF : (stateBefore x (voteTime S (s'' + 1)) w).S.F.compatible e₀v.B = true := by
          have hmono := F_ancestorEq_of_le x w
            (stepBefore_mono x hDiv (show voteTime S (s'' + 1) ≤ t by omega))
          exact (compatible_iff _ _).2
            (Or.inl (ancestorEq_trans hmono (ancestorEq_trans hFe hBv₀)))
        -- Lemma 42: `w`'s revocation of slot `s'' + 1` leaves only entries compatible with
        -- `e₀v`'s block
        have h42 := GoldilocksCorrectness.Proofs.Executions.lem42_fast_lock_clears_conflicting_locks
          S Sched x GST s'' e₀v.B v w A_v hDiv hMono hSync hCatch (hRoots.mono (by omega))
          hParent (by omega)
          (fun t' h1 h2 => hv t' (by omega) (by omega))
          (fun t' h1 h2 => hw t' (by omega) (by omega)) hU_v hFast hF
        -- the duty test of `w`'s revocation, kept from its update of slot `s' + 1`
        have hDuty : ∃ τ : Time, (tickInputState x (stepBefore x (voteTime S (s'' + 1)))
            (voteTime S (s'' + 1)) w).awakeSince = some τ ∧
            τ ≤ duty_window_start S.C (s'' + 1) :=
          ⟨τw, GoldilocksCorrectness.Proofs.Executions.awakeSince_kept_of_awake_throughout S Sched x
              _ _ w τw hDiv hcw_vt hτw
              (fun t' h1 h2 => (hw t' (by omega) (by omega)).1),
            le_trans hτwle (duty_window_start_mono S (by omega))⟩
        have hlive'w : ((supportCutoff S (s'' + 1) + 1 : ℕ) : Int) < e'w.d := by
          show @LT.lt Int _ _ _
          rw [hd'w]
          have : ((supportCutoff S (s'' + 1) + 1 : ℕ) : Int) ≤ (t : Int) := by exact_mod_cast hcv'
          omega
        have hOlder : e'w.d < e'v.d := by
          show @LT.lt Int _ _ _
          rw [hd'w, hd'v]
          have := t_lt_of_lt S (show s' + S.C.k < s'' + S.C.k by omega)
          omega
        have h34 := GoldilocksCorrectness.Proofs.Executions.lem34_fast_lock_compatible_of_revocation
          S Sched x s'' w e'v e'w hDiv (hd'v.trans hdv) he'w hlive'w hOlder
          (hw _ (by omega) (by omega)) hDuty
          (fun A'' hR e he _ => compatible_of_compatible_ancestorEq (h42 A'' hR e he) hB'₀v)
        exact compatible_of_ancestorEq_both hB'v hB'w h34
      · -- `e_v`'s block is an ancestor-or-equal of `w`'s finalized block, hence of `e_w`'s
        have hFe_w := ((mem_fg_to_ac_tree _ _).1 hlw.2).2
        exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heF hFe_w))
    · -- the slow case: `e₀v`'s block is `v`'s saved confirmation of slot `s'` or an ancestor
      obtain ⟨-, hj⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem37_slow_test_saved_confirmations S.C _ _ s''
          e₀v.B hSlow
      obtain ⟨Cj, hCj, -, hBj⟩ := hj s' (show s'' + 1 - S.C.k ≤ s' by omega) hlt
      have hCj' : (stateBefore x (supportCutoff S (s'' + 1)) v).A.saved_confirmation s' =
          some Cj := hCj
      obtain ⟨-, ⟨τ₁, hτ₁, hτ₁le⟩, ⟨A₁, hU₁, hS₁⟩, -⟩ :=
        GoldilocksCorrectness.Proofs.Executions.lem40_saved_confirmation_provenance S Sched x
          (supportCutoff S (s'' + 1)) v s' Cj hDiv hCj'
      exact key A₁ Cj τ₁ hU₁ hS₁ hτ₁ hτ₁le (ancestorEq_trans hBv₀ hBj)
  · -- the same slot
    have hbb : s' = s'' := le_antisymm hbwv hge
    subst hbb
    exact key A_v C₀v τv hU_v hC₀v hτv hτvle (ancestorEq_trans hBv₀ hB₀v)

/-- **Lemma 43, two live locks made after `GST` are compatible.** The proof; the audited
statement is in `Statements/Executions/HealingStatements.lean`.

Roots name blocks until `t`: `live_locks_compatible_of_deadline_le`, which the proof calls,
takes blocks as held up to `t`. -/
theorem lem43_live_locks_after_GST_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s₁ s t : ℕ) (v w : V) (e_v e_w : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s₁)
    (hst : slotStart S s ≤ t)
    (hv : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int))
    (hw : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (he_v : e_v ∈ (stateBefore x t v).A.lock_entries)
    (hlive_v : is_live (fg_to_ac (stateBefore x t v).S) (t : Int) e_v = true)
    (hd_v : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_v.d)
    (he_w : e_w ∈ (stateBefore x t w).A.lock_entries)
    (hlive_w : is_live (fg_to_ac (stateBefore x t w).S) (t : Int) e_w = true)
    (hd_w : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_w.d)
    (hFwv : (stateBefore x t w).S.F.compatible e_v.B = true)
    (hFvw : (stateBefore x t v).S.F.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true := by
  rcases le_total e_w.d e_v.d with hle | hle
  · exact live_locks_compatible_of_deadline_le x GST s₁ s t v w e_v e_w hDiv hMono hSync hCatch
      hRoots hParent hGST hst hv hw he_v hd_v he_w hlive_w hd_w hFwv hle
  · exact compatible_symm' (live_locks_compatible_of_deadline_le x GST s₁ s t w v e_w e_v hDiv
      hMono hSync hCatch hRoots hParent hGST hst hw hv he_w hd_w he_v hlive_v hd_v
      hFvw hle)

end GoldilocksCorrectness.Proofs.Executions
