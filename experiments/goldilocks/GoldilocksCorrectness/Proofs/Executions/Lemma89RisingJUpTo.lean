module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89RisingJ
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJUpTo

@[expose] public section

/-!
# `Lemma89RisingJ.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89RisingJ.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `floor_le_before_quiet`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slotStart_mono supportCutoff_eq
  supportCutoff_mono voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_height_mono)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **No honest `head_height_floor` reaches one more than a quiet opening's proposal before its
support cutoff.** In the climb's context, for the opening `i'` (`QuietCtx` with `s₀'`, `s₃`) whose
proposal `B₂` has chain-state height `h` with `h + 1` equal to `H₂` or `H₂ + 1`: every validator
honest at a time `t` from `T₁ + 1` to the support cutoff of slot `s₀' + 1` has its
`head_height_floor` before `t` at most `h`.

Why: at a member of the opening, at the vote time of its first slot, `head_height_floor` (the least chain-state height a viable block may have) is at most `B₂`'s
parent's height (the first clause), so at most `h`. A `head_height_floor` value of `h + 1` at an honest validator one
delay earlier reaches that member and stays (`ClimbCtx.spread_level_floor`,
`ClimbCtx.mono_level_floor`, or their `_succ` forms); later, up to the support cutoff, `head_height_floor`
does not rise (no fork-choice change in the opening's window).

The variables:
- `CC`: the climb's context; `C'`: the opening's context; `h`: the height; `B₂`: the proposal; `u`:
  the validator; `t`: the time.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo` `CC`; the bundle `QuietCtxUpTo` `C'` carries its own, `supportCutoff S s₃`. -/
theorem floor_le_before_quiet_upTo {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ}
    (CC : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂)
    (C' : QuietCtxUpTo S Sched x GST tGAT tAwakeEnd r m i' rs s₀' s₃)
    (hT₁ : T₁ + Δ S ≤ slotStart S (s₀' + 1 - S.C.k - 1))
    (h : ℕ) (hh : h + 1 = H₂ ∨ h = H₂) (B₂ : Block V) (hB₂ : ProposalAt S Sched x (s₀' + 1) B₂)
    (hB₂h : (chainStateOf S.C B₂).h = h) (u : V) (t : ℕ) (ht1 : T₁ + 1 ≤ t)
    (ht2 : t ≤ supportCutoff S (s₀' + 1)) (hu : u ∉ Sched.adv (t : Int)) :
    head_height_floor (stateBefore x t u).S ≤ h := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hw0 := C'.win (le_refl (s₀' + 1))
  have hsR := C'.sR
  have hEnd := C'.cut_end
  have hcut := C'.cut_le
  have hv1 := voteTime_eq S (s₀' + 1)
  have hc1 := supportCutoff_eq S (s₀' + 1)
  have hμ := voteTime_eq S (s₀' + 1 - S.C.k - 1)
  have hμs := slotStart_mono S (show s₀' + 1 - S.C.k - 1 ≤ s₀' + 1 by omega)
  have hμs' := slotStart_mono S (show s₀' + 1 - S.C.k - 1 ≤ s₀' by omega)
  have hss : slotStart S (s₀' + 1) = slotStart S s₀' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvtR : voteTime S (s₀' + 1) < aR S r := by
    have := supportCutoff_mono S (show s₀' + 1 ≤ s₃ by omega)
    omega
  -- a member of the opening, with its floor at most `h` at the vote time
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀' + 1 + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj := committee_majority_of_committeeSleepiness S Sched _ (s₀' + 1) C'.hCommittees hA2
  obtain ⟨w₀, hw₀⟩ : (S.P.committee (s₀' + 1) ∩ roundMembers S Sched (s₀' + 1 + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hw₀H : w₀ ∈ Hon S Sched (s₀' + 1) := (Finset.mem_inter.1 hw₀).2
  have hw₀b : w₀ ∉ Sched.adv ((supportCutoff S (s₀' + 1 + 1) : ℕ) : Int) :=
    (Finset.mem_sdiff.1 hw₀H).2
  have hw₀v : w₀ ∉ Sched.adv ((voteTime S (s₀' + 1) : ℕ) : Int) :=
    fun hh' => hw₀b (C'.hMono _ _ (by exact_mod_cast (le_trans (show voteTime S (s₀' + 1) ≤
      supportCutoff S (s₀' + 1) by omega) (supportCutoff_mono S (Nat.le_succ _)))) hh')
  obtain ⟨-, hfl₀⟩ := C'.clause1 B₂ hB₂ w₀ hw₀H
  obtain ⟨iB, hlB, hsentB⟩ := hB₂
  obtain ⟨-, hBne, hBpar?, -⟩ := proposal_parent_walk_end S Sched x s₀' iB B₂ _ hlB hsentB
  have hPB := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hBpar?
  have hpar := chainStateOf_height_mono S.C hPB
  have hfl₀' : head_height_floor (stateBefore x (voteTime S (s₀' + 1)) w₀).S ≤ h := by
    rw [← hB₂h]
    exact le_trans hfl₀ hpar
  -- the floor at a time one delay before the vote time
  have hearly : ∀ t' : ℕ, T₁ + 1 ≤ t' → t' + Δ S ≤ voteTime S (s₀' + 1) →
      u ∉ Sched.adv (t' : Int) → head_height_floor (stateBefore x t' u).S ≤ h := by
    intro t' h1 h2 hu'
    by_contra hgt
    push Not at hgt
    have hu'' : u ∉ Sched.adv ((t' - 1 : ℕ) : Int) :=
      fun hh' => hu' (C'.hMono _ _ (by exact_mod_cast (Nat.sub_le t' 1)) hh')
    have e1 : t' - 1 + 1 = t' := by omega
    rcases hh with hh | hh
    · have hL : H₂ ≤ head_height_floor (stateBefore x (t' - 1 + 1) u).S := by
        rw [e1]
        unfold Height at *
        omega
      have hsp := CC.spread_level_floor (τ := t' - 1) (t := voteTime S (s₀' + 1)) (by omega)
        hu'' hL (by omega) hvtR hw₀v
      have hm := CC.mono_level_floor (w := w₀) (t₂ := t' - 1 + 1 + Δ S)
        (t := voteTime S (s₀' + 1)) (by omega) (by omega) hvtR hw₀v hsp
      unfold Height at *
      omega
    · have hL : H₂ + 1 ≤ head_height_floor (stateBefore x (t' - 1 + 1) u).S := by
        rw [e1]
        unfold Height at *
        omega
      have hsp := CC.spread_level_floor_succ (τ := t' - 1) (t := voteTime S (s₀' + 1)) (by omega)
        hu'' hL (by omega) hvtR hw₀v
      have hm := CC.mono_level_floor_succ (w := w₀) (t₂ := t' - 1 + 1 + Δ S)
        (t := voteTime S (s₀' + 1)) (by omega) hvtR hw₀v hsp
      unfold Height at *
      omega
  by_cases htt : t + Δ S ≤ voteTime S (s₀' + 1)
  · exact hearly t ht1 htt hu
  · have hus : u ∉ Sched.adv ((voteTime S (s₀' + 1) - Δ S : ℕ) : Int) :=
      fun hh' => hu (C'.hMono _ _ (by exact_mod_cast (show voteTime S (s₀' + 1) - Δ S ≤ t by
        omega)) hh')
    have hfe := hearly (voteTime S (s₀' + 1) - Δ S) (by omega) (by omega) hus
    have hnc := floor_le_of_no_change S Sched x u (voteTime S (s₀' + 1) - Δ S) t (by omega)
      (C'.noChange u (by omega) (le_trans ht2 (supportCutoff_mono S (by omega))) hu)
    exact le_trans hnc hfe

end GoldilocksCorrectness.Proofs.Executions

