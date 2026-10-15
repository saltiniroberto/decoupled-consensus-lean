import Model.Sts.Spec2Claims.Claim13be
import Proofs.Claims.VocabularyAssumptionsLemmas
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_a

/-!
# The phase premises at an earlier phase end

The premises that mention the phase end hold at an earlier phase end `tE' ≤ tE` when they hold at
`tE`, provided `tGAT + 8RΔ ≤ tE'`. The file also holds the facts about validators inside the phase
and the window arithmetic they use.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Validators the adversary does not hold, inside the phase -/

/-- If corruption only grows, every validator the adversary does not hold at an instant of
    `[tGAT, tE]` is awake then, the window `[a, b]` lies inside `[tGAT, tE]`, and `v` is not held by
    the adversary at an instant `T ≥ b`, then `v` is awake at every instant of `[a, b]`. -/
theorem mem_awakeThroughout_of_notAdv_inPhase (Sched : Schedule V) (tGAT tE : Int)
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {a b T : Int} {v : V} (hlo : tGAT ≤ a) (hhi : b ≤ tE) (hT : b ≤ T)
    (hv : v ∉ Sched.adv T) :
    v ∈ Sched.awakeThroughout a b := by
  refine Finset.singleton_subset_iff.1 (Finset.le_inf ?_)
  intro t ht
  obtain ⟨h0, h1⟩ := Finset.mem_Icc.1 ht
  refine Finset.singleton_subset_iff.2 (hawake t (by linarith) (by linarith) v ?_)
  exact fun h => hv (hmono t T (by linarith) h)

/-- If the vote window of slot `s₀`, which ends at its vote instant, lies inside `[tGAT, tE]`, and
    `v` is not held by the adversary at an instant at or after that vote instant, then
    `v ∈ activeAtW S Sched s₀`. -/
theorem mem_activeAtW_of_notAdv_inPhase (S : Setup V) (Sched : Schedule V) (tGAT tE : Int)
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {s₀ : Slot} {T : Int} {v : V}
    (hlo : tGAT ≤ slotStart S.E.Δ s₀ + S.E.Δ - wVote S)
    (hhi : slotStart S.E.Δ s₀ + S.E.Δ ≤ tE) (hT : slotStart S.E.Δ s₀ + S.E.Δ ≤ T)
    (hv : v ∉ Sched.adv T) :
    v ∈ activeAtW S Sched s₀ :=
  mem_awakeThroughout_of_notAdv_inPhase Sched tGAT tE hmono hawake hlo hhi hT hv

/-! ## Window arithmetic -/

/-- Slot `s + tE.toNat` starts at or after `tE`. -/
theorem le_slotStart_add_toNat (S : Setup V) (s : Slot) (tE : Int) :
    tE ≤ slotStart S.E.Δ (s + tE.toNat) := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  rw [slotStart_closed]
  have hs : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg s
  have htn : tE ≤ ((tE.toNat : Nat) : Int) := Int.self_le_toNat tE
  have hn : (0 : Int) ≤ ((tE.toNat : Nat) : Int) := Int.natCast_nonneg _
  push_cast
  nlinarith

/-- If `tGAT + 8RΔ ≤ tE' ≤ slotStart s < tE` and `1 ≤ s`, then the window
    `[slotStart (s − 1) + Δ − wVote, slotStart (s − 1) + Δ]` lies inside `[tGAT, tE]`, and its end
    is at or before both `slotStart s + Δ` and `confirmation_time (s − 1)`. -/
theorem voteWindow_prev_inPhase (S : Setup V) (tGAT tE tE' : Int) {s : Slot}
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE') (hs1 : 1 ≤ s)
    (hs' : tE' ≤ slotStart S.E.Δ s) (hsE : slotStart S.E.Δ s < tE) :
    tGAT ≤ slotStart S.E.Δ (s - 1) + S.E.Δ - wVote S ∧
      slotStart S.E.Δ (s - 1) + S.E.Δ ≤ tE ∧
      slotStart S.E.Δ (s - 1) + S.E.Δ ≤ slotStart S.E.Δ s + S.E.Δ ∧
      slotStart S.E.Δ (s - 1) + S.E.Δ ≤ Protocol.confirmation_time S.E (s - 1) := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, (Nat.sub_add_cancel hs1).symm⟩
  simp only [Nat.add_sub_cancel] at *
  rw [confirmation_time_closed]
  simp only [slotStart_closed] at hs' hsE ⊢
  rw [show wVote S = (4 * (S.hc.R : Int) + 2) * S.E.Δ from rfl]
  push_cast at hs' hsE ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- If `tGAT + 8RΔ ≤ tE' ≤ opening r₀ < tE` and `1 ≤ r₀`, then the window
    `[a (r₀ − 1) − wAttest, a (r₀ − 1)]` lies inside `[tGAT, tE]`, and its end is at or before
    `opening (r₀ + 1)`. -/
theorem attestWindow_prev_inPhase (S : Setup V) (tGAT tE tE' : Int) {r₀ : Nat}
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE') (hr1 : 1 ≤ r₀)
    (hr' : tE' ≤ Protocol.opening S.E S.hc r₀) (hrE : Protocol.opening S.E S.hc r₀ < tE) :
    tGAT ≤ S.hc.a S.E.Δ (r₀ - 1) - wAttest S ∧
      S.hc.a S.E.Δ (r₀ - 1) ≤ tE ∧
      S.hc.a S.E.Δ (r₀ - 1) ≤ Protocol.opening S.E S.hc (r₀ + 1) := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  obtain ⟨r, rfl⟩ : ∃ r, r₀ = r + 1 := ⟨r₀ - 1, (Nat.sub_add_cancel hr1).symm⟩
  simp only [Nat.add_sub_cancel] at *
  rw [healA_closed]
  rw [opening_closed, opening_slot_closed] at hr' hrE ⊢
  rw [opening_slot_closed]
  rw [show wAttest S = 4 * (S.hc.R : Int) * S.E.Δ from rfl]
  push_cast at hr' hrE ⊢
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- Round `r + tE.toNat` opens at or after `tE`. -/
theorem le_opening_add_toNat (S : Setup V) (r : Nat) (tE : Int) :
    tE ≤ Protocol.opening S.E S.hc (r + tE.toNat) := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  rw [opening_closed, opening_slot_closed]
  have hr : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
  have htn : tE ≤ ((tE.toNat : Nat) : Int) := Int.self_le_toNat tE
  have hn : (0 : Int) ≤ ((tE.toNat : Nat) : Int) := Int.natCast_nonneg _
  push_cast
  have h1 : ((tE.toNat : Nat) : Int) ≤ ((r : Int) + ((tE.toNat : Nat) : Int)) * (S.hc.R : Int) := by
    nlinarith
  have h2 : (0 : Int) ≤ ((r : Int) + ((tE.toNat : Nat) : Int)) * (S.hc.R : Int) := by nlinarith
  have h3 : ((r : Int) + ((tE.toNat : Nat) : Int)) * (S.hc.R : Int) ≤
      4 * S.E.Δ * (((r : Int) + ((tE.toNat : Nat) : Int)) * (S.hc.R : Int)) := by nlinarith
  linarith

/-! ## The premises at an earlier phase end -/

/-- If corruption only grows, every validator the adversary does not hold at an instant of
    `[tGAT, tE]` is awake then, `tGAT + 8RΔ ≤ tE'`, and `sleepinessW` holds from `tE`, then
    `sleepinessW` holds from `tE'`. -/
theorem sleepinessW_of_later (S : Setup V) (Sched : Schedule V) (tGAT tE tE' : Int)
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE')
    (hsl : sleepinessW S Sched tE) :
    sleepinessW S Sched tE' := by
  intro s hs1 hs'
  by_cases hsE : tE ≤ slotStart S.E.Δ s
  · exact hsl s hs1 hsE
  push Not at hsE
  obtain ⟨hlo, hhi, hT, -⟩ := voteWindow_prev_inPhase S tGAT tE tE' hwin hs1 hs' hsE
  set T : Int := slotStart S.E.Δ s + S.E.Δ with hTdef
  have hact : ∀ v : V, v ∉ Sched.adv T → v ∈ activeAtW S Sched (s - 1) := fun v hv =>
    mem_activeAtW_of_notAdv_inPhase S Sched tGAT tE hmono hawake hlo hhi hT hv
  set s' : Slot := s + tE.toNat with hs'def
  have hs's : s ≤ s' := Nat.le_add_right _ _
  have hlater := hsl s' (le_trans hs1 hs's) (le_slotStart_add_toNat S s tE)
  set T' : Int := slotStart S.E.Δ s' + S.E.Δ with hT'def
  have hTT' : T ≤ T' := by
    have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
    have hss := slotStart_le_slotStart (le_trans (by decide) hΔ) hs's
    simp only [hTdef, hT'def]
    linarith
  have hsub : Sched.adv T ⊆ Sched.adv T' := hmono T T' hTT'
  have hkey : (Sched.adv T).card < (Finset.univ \ Sched.adv T).card := by
    have h1 : (Sched.adv T).card ≤ (Sched.adv T').card := Finset.card_le_card hsub
    have h2 : (Sched.adv T').card ≤ (Sched.adv T' ∪
        (votersAt S Sched (s' - 1) \
          (activeAtW S Sched (s' - 1) \ Sched.adv T'))).card :=
      Finset.card_le_card Finset.subset_union_left
    have h3 : (activeAtW S Sched (s' - 1) \ Sched.adv T').card ≤
        (Finset.univ \ Sched.adv T).card := by
      refine Finset.card_le_card ?_
      intro v hv
      obtain ⟨-, hv'⟩ := Finset.mem_sdiff.1 hv
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ v, fun h => hv' (hsub h)⟩
    have := hlater
    omega
  have hL : (Sched.adv T ∪
      (votersAt S Sched (s - 1) \ (activeAtW S Sched (s - 1) \ Sched.adv T))).card ≤
      (Sched.adv T).card := by
    refine Finset.card_le_card ?_
    intro v hv
    rcases Finset.mem_union.1 hv with h | h
    · exact h
    · obtain ⟨-, hn⟩ := Finset.mem_sdiff.1 h
      by_contra hvT
      exact hn (Finset.mem_sdiff.2 ⟨hact v hvT, hvT⟩)
  have hR : (Finset.univ \ Sched.adv T).card ≤
      (activeAtW S Sched (s - 1) \ Sched.adv T).card := by
    refine Finset.card_le_card ?_
    intro v hv
    obtain ⟨-, hvT⟩ := Finset.mem_sdiff.1 hv
    exact Finset.mem_sdiff.2 ⟨hact v hvT, hvT⟩
  show (Sched.adv T ∪
      (votersAt S Sched (s - 1) \ (activeAtW S Sched (s - 1) \ Sched.adv T))).card <
    (activeAtW S Sched (s - 1) \ Sched.adv T).card
  omega

/-- A bound of less than a third of the total weight on the adversary at every instant up to `tE`
    gives it at every instant up to `tE' ≤ tE`. -/
theorem third_of_later (S : Setup V) (Sched : Schedule V) (tE tE' : Int) (htE : tE' ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) :
    ∀ t : Int, t ≤ tE' →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
  fun t ht => hthird t (le_trans ht htE)

omit [DecidableEq V] [Fintype V] in
/-- If every validator the adversary does not hold at an instant of `[tGAT, tE]` is awake then, the
    same holds on `[tGAT, tE']` for `tE' ≤ tE`. -/
theorem awake_of_later (Sched : Schedule V) (tGAT tE tE' : Int) (htE : tE' ≤ tE)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) :
    ∀ t : Int, tGAT ≤ t → t ≤ tE' → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
  fun t h0 h1 => hawake t h0 (le_trans h1 htE)

end DecoupledConsensusModel.Sts
