import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bHandover
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Constants
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bHandover
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Bounds after the asynchronous period

Instant bounds around the end of a phase and the asynchronous period, and the stable output of a
store as one of its bodies, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every instant `tE`, `tE < confirmedSettleTime S tE + 8Δ`. -/
theorem tAwakeEnd_lt_confirmedSettleTime_add (facts : Record.Facts M) (S : Setup V) (tE : Int) :
    tE < Restated.confirmedSettleTime M S tE + 8 * S.E.Δ := by
  have hnot : ¬ M.confirmation_time S.E
      ((M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2) ≤ tE := fun h =>
    absurd (Restated.switchRound_max facts S tE h) (Nat.not_succ_le_self _)
  rw [not_le, (pCR% confirmation_time_closed_cr) facts, (pCR% opening_slot_closed_cr) facts] at hnot
  have ha := (pCR% action_closed_cr) facts S (Restated.switchRound M S tE + 1)
  show tE < (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) + 8 * S.E.Δ
  rw [ha]
  push_cast at hnot ⊢
  nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `0 ≤ liveAgainAfterHealing S gap`. -/
theorem liveAgainAfterHealing_nonneg (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    0 ≤ Restated.liveAgainAfterHealing M S gap := by
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  unfold Restated.liveAgainAfterHealing Restated.finalityStartupDirect Restated.finalityPremisesContinueDirect
  have := Int.natCast_nonneg (2 * gap + S.cfg.timeoutDelay / S.hc.R + 3)
  have := Int.natCast_nonneg (3 * gap + S.cfg.timeoutDelay / S.hc.R)
  have := Int.natCast_nonneg (3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1)
  positivity

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If one delay after round `r + 2`'s action instant is at or before `b₀`, `b₀ ≤ b₁`,
    `b₁ + Δ ≤ tAgain`, `tAgain + (tHeal + liveAgainAfterHealing S gap) ≤ tSafe` and
    `healingLengthη S gap ≤ tHeal`, then round `r + η_SG + 2`'s action instant is at or before
    `tSafe`. -/
theorem action_le_tSafe_ofPage (facts : Record.Facts M) (S : Setup V) {b₀ b₁ tAgain tHeal tSafe : Int} {r gap : Nat}
    (hb₀ : Restated.periodAfterRound M S (r + 1) b₀) (hb : b₀ ≤ b₁) (hAgain : b₁ + S.E.Δ ≤ tAgain)
    (hSafe : tAgain + (tHeal + Restated.liveAgainAfterHealing M S gap) ≤ tSafe)
    (hheal : Restated.healingLengthη M S gap ≤ tHeal) :
    (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) ≤ tSafe := by
  unfold Restated.periodAfterRound at hb₀
  have hadd := Restated.action_add_eq_add_period_mul facts S (r + 2) S.hc.η_SG
  have heq : r + 2 + S.hc.η_SG = r + S.hc.η_SG + 2 := by omega
  rw [heq] at hadd
  have hL := Restated.healingLength_nonneg facts S gap
  have hlive := Restated.liveAgainAfterHealing_nonneg facts S gap
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hη : Restated.healingLengthη M S gap = Restated.healingLength M S gap + (S.hc.η_SG : Int) * (Restated.constants M S).period :=
    rfl
  have h2 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) = (M.a S.hc S.E.Δ (r + 1 + 1)) := rfl
  have h3 : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 2)) = (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) := rfl
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every step `T` and validator `v`, some body `C` of `v`'s store after `T` steps erases to
    `v`'s stable output there. -/
theorem get_stable_mem_bodies (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (T : Nat) (v : V) :
    ∃ C ∈ (x[T][v].st).st.bodies, C.erase = M.get_stable (x[T][v].st).st.core := by
  rcases facts.hd.get_stable_eq_or (x[T][v].st).st.core with h | h
  · have hmem := (Restated.records_mem_tree_sts facts S Sched x v T).1
    rw [Restated.bodies_image_eq_T facts S Sched x T v] at hmem
    obtain ⟨C, hC, hCe⟩ := Finset.mem_image.mp hmem
    exact ⟨C, hC, hCe.trans h.symm⟩
  · obtain ⟨Fb, hFb, hFbe, -⟩ := Restated.finalized_body_of_store facts S Sched x T v
    exact ⟨Fb, hFb, hFbe.trans h.symm⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `P` is an ancestor of `v`'s stable output after `T` steps, then `P` is an ancestor of the
    erasure of some body of `v`'s store after `T` steps. -/
theorem exists_body_preceq_of_read (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (T : Nat) (v : V) (P : Block V)
    (hP : Block.Preceq P (M.get_stable (x[T][v].st).st.core)) :
    ∃ C ∈ (x[T][v].st).st.bodies, Block.Preceq P C.erase := by
  obtain ⟨C, hC, hCe⟩ := Restated.get_stable_mem_bodies facts S Sched x T v
  exact ⟨C, hC, hCe ▸ hP⟩

end

end DecoupledConsensusModel.Sts.Restated
