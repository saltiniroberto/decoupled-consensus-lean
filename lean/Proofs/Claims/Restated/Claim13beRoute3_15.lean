import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Internal_Legacy_Instance
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring

/-!
# The switch round inside the healing phase

The switch round's attester window lies inside `[tGAT, tE]`, and inside that interval a validator
the adversary does not hold at a round's action instant is an honest active attester of the round.
Stated over a model `M : Record.Model V`.
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

private theorem three_le_switchRound_target (r Fs Fd gap η : Nat) (hη : 1 ≤ η) :
    r + 3 ≤ r + Fs + Fd + gap + 2 + η := by omega

private theorem switchRound_target_ne_zero {n : Nat} (h : 3 ≤ n) : n ≠ 0 := by omega

/-- If `t_GST ≤ tGAT` and the healing phase `[tGAT, tE]` lasts at least `healingLengthη`, the whole
    attester window of the switch round, from `wAttest S` before its action instant through that
    instant, lies inside `[tGAT, tE]`. -/
theorem switchRound_window_in_phase (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) - wAttest S ∧ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ tE := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hper : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  -- the switch round is at least three rounds past the round at `tGAT`
  have hsw := Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen
  have h3 : Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 3 ≤ Restated.switchRound M S tE := by
    refine le_trans ?_ hsw
    exact three_le_switchRound_target _ _ _ _ _ S.hc.η_SG_ge_one
  -- its action instant is at least `tGAT + 3 * period`
  have hstep : (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 3))
      = (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT)) + (3 : Int) * (Restated.constants M S).period := by
    rw [Restated.action_add_eq_add_period_mul facts S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT) 3]
    norm_num
  have hlow : tGAT + 3 * (Restated.constants M S).period ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    have h1 : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT)) :=
      Restated.Vocabulary.Statements.roundAt_spec facts S tGAT
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 3)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) :=
      Restated.Vocabulary.Proofs.Assembly.a_mono facts S h3
    rw [hstep] at h2
    linarith
  have hwa : wAttest S = 4 * (S.hc.R : Int) * S.E.Δ := rfl
  refine ⟨by rw [hwa]; rw [hper] at hlow; nlinarith, ?_⟩
  -- the right end: the switch round's third slot is confirmed inside the phase
  have hne : Restated.switchRound M S tE ≠ 0 := by
    exact switchRound_target_ne_zero (le_trans (Nat.le_add_left 3 _) h3)
  exact le_trans (Restated.action_le_confirmation_third facts S (Restated.switchRound M S tE))
    (Restated.switchRound_spec facts S tE hne)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- When the whole attester window of round `r` lies inside `[tGAT, tE]`, every validator the
    adversary does not hold at `r`'s action instant is a member of `HonRound S Sched r`. -/
theorem nonAdv_mem_honRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tGAT tE : Int)
    (r : Round) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hlo : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) (hhi : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ tE)
    {v : V} (hv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r))) : v ∈ Restated.HonRound M S Sched r := by
  refine Finset.mem_sdiff.2 ⟨?_, hv⟩
  refine mem_awakeThroughout_of_forall Sched ?_
  intro t ht1 ht2
  have hnadv : v ∉ Sched.adv t := fun hmem => hv (hmono t ((Restated.Vocabulary.Execution.Setup.a M S r)) ht2 hmem)
  exact hawake t (by linarith) (by linarith) v hnadv

end

end DecoupledConsensusModel.Sts.Restated
