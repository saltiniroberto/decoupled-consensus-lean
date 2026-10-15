import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettleEarlier

/-!
# Sleepiness conditions at an earlier phase end

That `roundSleepinessW`, `committeeSleepinessW` and `strongOpeningsRecurFrom` stated up to a phase
end `tE` also hold up to an earlier phase end `tE'`, with the round-timing facts they use, stated
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the attestation window of round `r` lies inside `[tGAT, tE]`, and `v` is not in the adversary
    set at a time at or after that round's action time, then `v ∈ activeRoundW S Sched r`. -/
theorem mem_activeRoundW_of_notAdv_inPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tGAT tE : Int)
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {r : Nat} {T : Int} {v : V}
    (hlo : tGAT ≤ (M.a S.hc S.E.Δ r) - wAttest S)
    (hhi : (M.a S.hc S.E.Δ r) ≤ tE) (hT : (M.a S.hc S.E.Δ r) ≤ T)
    (hv : v ∉ Sched.adv T) :
    v ∈ Restated.activeRoundW M S Sched r :=
  mem_awakeThroughout_of_notAdv_inPhase Sched tGAT tE hmono hawake hlo hhi hT hv

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `tGAT + 8RΔ ≤ tE' ≤ opening r₀ < tE` and `1 ≤ r₀`, then the attestation window of round
    `r₀ − 1` lies inside `[tGAT, tE]`, and its end is at or before `opening (r₀ + 1)`. -/
theorem attestWindow_prev_inPhase (facts : Record.Facts M) (S : Setup V) (tGAT tE tE' : Int) {r₀ : Nat}
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE') (hr1 : 1 ≤ r₀)
    (hr' : tE' ≤ M.opening S.E S.hc r₀) (hrE : M.opening S.E S.hc r₀ < tE) :
    tGAT ≤ (M.a S.hc S.E.Δ (r₀ - 1)) - wAttest S ∧
      (M.a S.hc S.E.Δ (r₀ - 1)) ≤ tE ∧
      (M.a S.hc S.E.Δ (r₀ - 1)) ≤ M.opening S.E S.hc (r₀ + 1) := by
  exact facts.gr.attestWindow_prev_inPhase S tGAT tE tE' hwin hr1 hr' hrE

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Round `r + tE.toNat` opens at or after `tE`. -/
theorem le_opening_add_toNat (facts : Record.Facts M) (S : Setup V) (r : Nat) (tE : Int) :
    tE ≤ M.opening S.E S.hc (r + tE.toNat) := by
  exact facts.gr.le_opening_add_toNat S r tE

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A later round opens later: if `r ≤ r'`, then `opening r ≤ opening r'`. -/
theorem opening_mono_c7 (facts : Record.Facts M) (S : Setup V) {r r' : Nat} (h : r ≤ r') :
    M.opening S.E S.hc r ≤ M.opening S.E S.hc r' := by
  exact facts.gr.Sts_opening_mono S h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If corruption only grows, every validator the adversary does not hold at a time of `[tGAT, tE]`
    is awake then, `tGAT + 8RΔ ≤ tE'`, and `roundSleepinessW` holds from `tE`, then
    `roundSleepinessW` holds from `tE'`. -/
theorem roundSleepinessW_of_later (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tGAT tE tE' : Int)
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE')
    (hrs : Restated.roundSleepinessW M S Sched tE) :
    Restated.roundSleepinessW M S Sched tE' := by
  intro r₀ hr1 hr'
  by_cases hrE : tE ≤ M.opening S.E S.hc r₀
  · exact hrs r₀ hr1 hrE
  push Not at hrE
  obtain ⟨hlo, hhi, hT⟩ := Restated.attestWindow_prev_inPhase facts S tGAT tE tE' hwin hr1 hr' hrE
  set T : Int := M.opening S.E S.hc (r₀ + 1) with hTdef
  have hact : ∀ v : V, v ∉ Sched.adv T → v ∈ Restated.activeRoundW M S Sched (r₀ - 1) := fun v hv =>
    Restated.mem_activeRoundW_of_notAdv_inPhase facts S Sched tGAT tE hmono hawake hlo hhi hT hv
  set r₁ : Nat := r₀ + tE.toNat with hr₁def
  have hr₀₁ : r₀ ≤ r₁ := Nat.le_add_right _ _
  have hlater := hrs r₁ (le_trans hr1 hr₀₁) (Restated.le_opening_add_toNat facts S r₀ tE)
  set T' : Int := M.opening S.E S.hc (r₁ + 1) with hT'def
  have hTT' : T ≤ T' := Restated.opening_mono_c7 facts S (Nat.succ_le_succ hr₀₁)
  have hsub : Sched.adv T ⊆ Sched.adv T' := hmono T T' hTT'
  have hkey : S.E.electorate.weightOf (Sched.adv T) <
      S.E.electorate.weightOf (Finset.univ \ Sched.adv T) := by
    have h1 := S.E.electorate.weightOf_mono hsub
    have h2 := S.E.electorate.weightOf_mono (Finset.subset_union_left (s₁ := Sched.adv T')
      (s₂ := Restated.attestersIn M S Sched (r₁ - S.hc.η_SG) (r₁ - 1) \
        (Restated.activeRoundW M S Sched (r₁ - 1) \ Sched.adv T')))
    have h3 : S.E.electorate.weightOf (Restated.activeRoundW M S Sched (r₁ - 1) \ Sched.adv T') ≤
        S.E.electorate.weightOf (Finset.univ \ Sched.adv T) := by
      refine S.E.electorate.weightOf_mono ?_
      intro v hv
      obtain ⟨-, hv'⟩ := Finset.mem_sdiff.1 hv
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ v, fun h => hv' (hsub h)⟩
    have := hlater
    omega
  have hL : S.E.electorate.weightOf (Sched.adv T ∪
      (Restated.attestersIn M S Sched (r₀ - S.hc.η_SG) (r₀ - 1) \
        (Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv T))) ≤
      S.E.electorate.weightOf (Sched.adv T) := by
    refine S.E.electorate.weightOf_mono ?_
    intro v hv
    rcases Finset.mem_union.1 hv with h | h
    · exact h
    · obtain ⟨-, hn⟩ := Finset.mem_sdiff.1 h
      by_contra hvT
      exact hn (Finset.mem_sdiff.2 ⟨hact v hvT, hvT⟩)
  have hR : S.E.electorate.weightOf (Finset.univ \ Sched.adv T) ≤
      S.E.electorate.weightOf (Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv T) := by
    refine S.E.electorate.weightOf_mono ?_
    intro v hv
    obtain ⟨-, hvT⟩ := Finset.mem_sdiff.1 hv
    exact Finset.mem_sdiff.2 ⟨hact v hvT, hvT⟩
  show S.E.electorate.weightOf (Sched.adv T ∪
      (Restated.attestersIn M S Sched (r₀ - S.hc.η_SG) (r₀ - 1) \
        (Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv T))) <
    S.E.electorate.weightOf (Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv T)
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If corruption only grows, every validator the adversary does not hold at a time of `[tGAT, tE]`
    is awake then, every committee has an honest majority through its slot's confirmation time,
    `tGAT + 8RΔ ≤ tE'`, and `committeeSleepinessW` holds from `tE`, then `committeeSleepinessW`
    holds from `tE'`. -/
theorem committeeSleepinessW_of_later (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tGAT tE tE' : Int)
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE')
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    Restated.committeeSleepinessW M S Sched tE' := by
  intro s hs1 hs'
  by_cases hsE : tE ≤ slotStart S.E.Δ s
  · exact hcs s hs1 hsE
  push Not at hsE
  obtain ⟨hlo, hhi, -, hT⟩ := facts.sch.voteWindow_prev_inPhase S tGAT tE tE' hwin hs1 hs' hsE
  set T : Int := M.confirmation_time S.E (s - 1) with hTdef
  set M : Finset V := S.E.committee (s - 1) with hMdef
  have hact : ∀ v : V, v ∉ Sched.adv T → v ∈ activeAtW S Sched (s - 1) := fun v hv =>
    mem_activeAtW_of_notAdv_inPhase S Sched tGAT tE hmono hawake hlo hhi hT hv
  have hmaj : M.card < 2 * (M ∩ honestThroughSet Sched T).card := hcom (s - 1)
  have hHT : (M ∩ honestThroughSet Sched T).card ≤ (M \ Sched.adv T).card := by
    refine Finset.card_le_card ?_
    intro v hv
    obtain ⟨hvM, hvH⟩ := Finset.mem_inter.1 hv
    exact Finset.mem_sdiff.2 ⟨hvM, (mem_honestThroughSet.1 hvH) T le_rfl⟩
  have hsplit := Finset.card_sdiff_add_card_inter M (Sched.adv T)
  have hL : (M \ (activeAtW S Sched (s - 1) \ Sched.adv T)).card ≤ (M ∩ Sched.adv T).card := by
    refine Finset.card_le_card ?_
    intro v hv
    obtain ⟨hvM, hn⟩ := Finset.mem_sdiff.1 hv
    refine Finset.mem_inter.2 ⟨hvM, ?_⟩
    by_contra hvT
    exact hn (Finset.mem_sdiff.2 ⟨hact v hvT, hvT⟩)
  have hR : (M \ Sched.adv T).card ≤
      ((activeAtW S Sched (s - 1) ∩ M) \ Sched.adv T).card := by
    refine Finset.card_le_card ?_
    intro v hv
    obtain ⟨hvM, hvT⟩ := Finset.mem_sdiff.1 hv
    exact Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨hact v hvT, hvM⟩, hvT⟩
  show (M \ (activeAtW S Sched (s - 1) \ Sched.adv T)).card <
    ((activeAtW S Sched (s - 1) ∩ M) \ Sched.adv T).card
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `strongOpeningsRecurFrom` up to `tE` gives it up to any `tE' ≤ tE`. -/
theorem strongOpeningsRecurFrom_of_later (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tGAT tE tE' : Int)
    (gap : Nat) (htE : tE' ≤ tE) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) :
    Restated.strongOpeningsRecurFrom M S Sched tGAT tE' gap :=
  fun t ht hle => hrec t ht (le_trans hle htE)

end

end DecoupledConsensusModel.Sts.Restated
