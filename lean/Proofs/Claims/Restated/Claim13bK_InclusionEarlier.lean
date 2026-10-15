import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Restated.Claim13bK_InclusionExtends
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedIncludedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_InclusionEarlier

/-!
# Settle instants at an earlier phase end

Slot bounds and the confirmed-output extension carried from the settle instant of an earlier phase
end to a later one, stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

local macro "pS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- If `confirmedSettleTime S tE'` is at or before slot `s`'s proposal instant, then `s` is at least
    two slots after the opening slot of round `switchRound S tE' + 1`. -/
theorem slot_ge_of_settle_le (facts : Record.Facts M) (S : Setup V) {tE' : Int} {s : Slot}
    (h : Restated.confirmedSettleTime M S tE' ≤ M.proposal_time S.E s) :
    (M.opening_slot S.hc (Restated.switchRound M S tE' + 1)) + 2 ≤ s := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hps := (facts.sch.slot_instants_l55 S.E s).2.2.2.2.2
  have hcs := (pS% confirmation_time_closed_srs) facts S.E s
  have ha := (pS% action_closed_srs) facts S (Restated.switchRound M S tE' + 1)
  have hset : Restated.confirmedSettleTime M S tE' = (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE' + 1)) := rfl
  rw [hset, ha] at h
  rw [(pS% opening_slot_closed_srs) facts]
  by_contra hcon
  have hlt : (s : Int) + 1 ≤ ((Restated.switchRound M S tE' + 1 : Nat) : Int) * (S.hc.R : Int) + 2 := by
    have : s + 1 ≤ (Restated.switchRound M S tE' + 1) * S.hc.R + 2 := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
    exact_mod_cast this
  have hR : ((Restated.switchRound M S tE' + 1 : Nat) : Int) * (S.hc.R : Int)
      = ((Restated.switchRound M S tE' : Nat) : Int) * (S.hc.R : Int) + (S.hc.R : Int) := by
    push_cast; ring
  push_cast at h hlt
  nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- For a round `c ≥ 1`, the settle instant of the confirmation instant of round `c − 1`'s third
    slot is `S.a c`. -/
theorem confirmedSettleTime_third (facts : Record.Facts M) (S : Setup V) {c : Round} (hc : 1 ≤ c) :
    Restated.confirmedSettleTime M S
        (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2)) = (Restated.Vocabulary.Execution.Setup.a M S c) := by
  have hsw := Restated.switchRound_confirmation_third facts S (c - 1)
  have e : c - 1 + 1 = c := Nat.sub_add_cancel hc
  show (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S _ + 1)) = (Restated.Vocabulary.Execution.Setup.a M S c)
  rw [hsw, e]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- For a round `c ≥ 1` with `S.a c ≤ tE`, the settle instant of the confirmation instant of round
    `c − 1`'s third slot is at or before `tE`. -/
theorem confirmedSettleTime_third_le (facts : Record.Facts M) (S : Setup V) {c : Round} (hc : 1 ≤ c) {tE : Int}
    (hcE : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ tE) :
    Restated.confirmedSettleTime M S
        (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2)) ≤ tE := by
  rw [Restated.confirmedSettleTime_third facts S hc]; exact hcE

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- If `confirmedSettleTime S tE' ≤ tE` and slot `s`'s proposal instant is at or after `tE`, then
    `s` is at least two slots after the opening slot of round `switchRound S tE' + 1`. -/
theorem slot_ge_of_le_phaseEnd (facts : Record.Facts M) (S : Setup V) {tE' tE : Int} (hle : Restated.confirmedSettleTime M S tE' ≤ tE)
    {s : Slot} (hs : tE ≤ M.proposal_time S.E s) :
    (M.opening_slot S.hc (Restated.switchRound M S tE' + 1)) + 2 ≤ s :=
  Restated.slot_ge_of_settle_le facts S (le_trans hle hs)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- If every honest validator's confirmed output only extends from `confirmedSettleTime S tE'` on,
    and that instant is at or before `tE`, then it only extends from `tE` on. -/
theorem confirmedOnlyExtendsAfterHealing_of_settle_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE' tE : Int} (hle : Restated.confirmedSettleTime M S tE' ≤ tE)
    (h : Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x (Restated.confirmedSettleTime M S tE')) :
    Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x tE :=
  Restated.confirmedOnlyExtendsAfterHealing_of_le facts S Sched x hle h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- `healingLengthη S gap + (gap + 2) · period` is positive. -/
theorem healingLengthDevice_pos (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    0 < Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period := by
  have hper0 : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hη0 := Restated.healingLengthη_nonneg facts S gap
  have : (0 : Int) < ((gap : Int) + 2) * (Restated.constants M S).period :=
    mul_pos (by positivity) hper0
  linarith

end

end DecoupledConsensusModel.Sts.Restated
