import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepCone
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# Committee sleepiness inside the phase

Inside `[tGAT, tE]` a committee member the adversary does not hold is counted in `HonSlot`, and
committee sleepiness holds from the slot after `s₀` on. Stated over a model `M : Record.Model V`.
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

/-- If slot `s`'s vote window lies inside `[tGAT, tE]`, every member of slot `s`'s committee that
    the adversary holds at no time up to slot `s`'s confirmation time is in `HonSlot S Sched s`. -/
theorem honSlot_of_honestThroughSet_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tE : Int} (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {s : Slot}
    (hlo : tGAT + wVote S ≤ slotStart S.E.Δ s + S.E.Δ)
    (hhi : slotStart S.E.Δ s + S.E.Δ ≤ tE) :
    (S.E.committee s) ∩ honestThroughSet Sched (M.confirmation_time S.E s)
      ⊆ Restated.HonSlot M S Sched s := by
  classical
  intro v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨hcomm, hhon⟩ := hv
  have hhon' : HonestThroughTime Sched (M.confirmation_time S.E s) v :=
    mem_honestThroughSet.mp hhon
  have hd := S.E.Δ_pos
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  refine (Restated.mem_HonSlot facts).mpr ⟨?_, hcomm, hhon' _ (le_refl _)⟩
  have hvote : v ∉ Sched.adv (slotStart S.E.Δ s + S.E.Δ) := hhon' _ (by rw [hct]; linarith)
  simp only [activeAtW]
  exact awakeThroughout_phase Sched hawake hmono (by linarith) hhi hvote

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From the start of slot `s₀ + 1` on, at every slot the members of the previous slot's committee
    that are awake throughout its vote window and not held by the adversary at its confirmation time
    are more than half of that committee. -/
theorem committeeSleepinessW_of_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tE : Int} (hmono : Sched.MonotoneCorruption)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hcsE : Restated.committeeSleepinessW M S Sched tE)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {s₀ : Slot} (hs₀ : 1 ≤ s₀)
    (hwin : tGAT + wVote S ≤ slotStart S.E.Δ s₀ + S.E.Δ) :
    Restated.committeeSleepinessW M S Sched (slotStart S.E.Δ (s₀ + 1)) := by
  classical
  intro s' hs' hanc
  have hd := S.E.Δ_pos
  by_cases hcase : tE ≤ slotStart S.E.Δ s'
  · exact hcsE s' hs' hcase
  · have hlt : slotStart S.E.Δ s' < tE := not_le.mp hcase
    -- the anchor condition, with the next slot's start written out
    have hsucc : slotStart S.E.Δ (s₀ + 1) = slotStart S.E.Δ s₀ + 4 * S.E.Δ :=
      slotStart_succ S.E.Δ s₀
    have hanc' : slotStart S.E.Δ s₀ + 4 * S.E.Δ ≤ slotStart S.E.Δ s' := by
      rw [← hsucc]; exact hanc
    have hle : s₀ + 1 ≤ s' := by
      rcases Nat.lt_or_ge s' (s₀ + 1) with hcon | hge
      · exfalso
        have h1 : s' ≤ s₀ := Nat.lt_succ_iff.mp hcon
        have h2 := slotStart_mono S h1
        linarith
      · exact hge
    have hsub : s₀ ≤ s' - 1 := Nat.le_pred_of_lt hle
    have hprev : slotStart S.E.Δ (s' - 1) = slotStart S.E.Δ s' - 4 * S.E.Δ := by
      have h1 := slotStart_succ S.E.Δ (s' - 1)
      rw [Nat.sub_add_cancel hs'] at h1
      linarith
    -- the two window conditions at `s' - 1`
    have hlo : tGAT + wVote S ≤ slotStart S.E.Δ (s' - 1) + S.E.Δ := by
      have hmo := slotStart_mono S hsub
      linarith
    have hhi : slotStart S.E.Δ (s' - 1) + S.E.Δ ≤ tE := by rw [hprev]; linarith
    have hT1 := Restated.honSlot_of_honestThroughSet_phase facts S Sched hmono hawake hlo hhi
    -- the committee majority at `s' - 1`, with the intersection replaced by `Restated.HonSlot M`
    have hcomm : (S.E.committee (s' - 1)).card <
        2 * ((S.E.committee (s' - 1)) ∩
          honestThroughSet Sched (M.confirmation_time S.E (s' - 1))).card :=
      hcom (s' - 1)
    have hcard : ((S.E.committee (s' - 1)) ∩
          honestThroughSet Sched (M.confirmation_time S.E (s' - 1))).card
        ≤ (Restated.HonSlot M S Sched (s' - 1)).card := Finset.card_le_card hT1
    have hmaj : (S.E.committee (s' - 1)).card < 2 * (Restated.HonSlot M S Sched (s' - 1)).card := by omega
    have hsubH : Restated.HonSlot M S Sched (s' - 1) ⊆ S.E.committee (s' - 1) :=
      Restated.HonSlot_subset_committee facts S Sched (s' - 1)
    have hfold : (activeAtW S Sched (s' - 1) ∩ S.E.committee (s' - 1)) \
        Sched.adv (M.confirmation_time S.E (s' - 1)) = Restated.HonSlot M S Sched (s' - 1) := rfl
    have heq : (S.E.committee (s' - 1)) \ (activeAtW S Sched (s' - 1) \
          Sched.adv (M.confirmation_time S.E (s' - 1)))
        = (S.E.committee (s' - 1)) \ Restated.HonSlot M S Sched (s' - 1) := by
      refine Finset.ext (fun v => ?_)
      simp only [Finset.mem_sdiff, Restated.HonSlot, Finset.mem_inter]
      tauto
    refine lt_of_le_of_lt (Finset.card_le_card
      (Finset.sdiff_subset_sdiff Finset.inter_subset_left (subset_refl _))) ?_
    rw [hfold, heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsubH]
    have hle2 : (Restated.HonSlot M S Sched (s' - 1)).card ≤ (S.E.committee (s' - 1)).card :=
      Finset.card_le_card hsubH
    omega

end

end DecoupledConsensusModel.Sts.Restated
