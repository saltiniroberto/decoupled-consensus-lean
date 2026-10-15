import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKitFull
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsDerived
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Safety of confirmation after healing

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: monotonicity of the
switch round and the settle instant in the phase end, and `claimConfirmedAfterHealing_holds`, which
proves `Restated.claimConfirmedAfterHealingStatement M S Sched`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers by name to the private closed forms of the module
    `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle`. -/
local macro "pS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `tE' ≤ tE`, the switch round of `tE'` is at or before that of `tE`. -/
theorem switchRound_mono (facts : Record.Facts M) (S : Setup V) {tE' tE : Int} (h : tE' ≤ tE) :
    Restated.switchRound M S tE' ≤ Restated.switchRound M S tE := by
  by_cases h0 : Restated.switchRound M S tE' = 0
  · rw [h0]; exact Nat.zero_le _
  · exact Restated.switchRound_max facts S tE (le_trans (Restated.switchRound_spec facts S tE' h0) h)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `tE' ≤ tE`, then `confirmedSettleTime S tE' ≤ confirmedSettleTime S tE`. -/
theorem confirmedSettleTime_mono (facts : Record.Facts M) (S : Setup V) {tE' tE : Int} (h : tE' ≤ tE) :
    Restated.confirmedSettleTime M S tE' ≤ Restated.confirmedSettleTime M S tE :=
  Restated.action_mono facts S (Nat.succ_le_succ (Restated.switchRound_mono facts S h))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If confirmation agrees from `confirmedSettleTime S tE'` on and that instant is at or before
    `confirmedSettleTime S tE`, then it agrees from `confirmedSettleTime S tE` on. -/
theorem confirmedAgreeAfterHealing_of_earlier (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE' tE : Int}
    (hle : Restated.confirmedSettleTime M S tE' ≤ Restated.confirmedSettleTime M S tE)
    (h : Restated.ConfirmedAgreeAfterHealing M S Sched x tE') :
    Restated.ConfirmedAgreeAfterHealing M S Sched x tE :=
  fun v₁ v₂ i j hv₁ hv₂ hi hj ha₁ ha₂ =>
    h v₁ v₂ i j hv₁ hv₂ (le_trans hle hi) (le_trans hle hj) ha₁ ha₂

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If every validator's confirmed output only extends between two steps from
    `confirmedSettleTime S tE'` on and that instant is at or before `confirmedSettleTime S tE`, then
    the same holds from `confirmedSettleTime S tE` on. -/
theorem confirmedMonotoneAfterHealing_of_earlier (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE' tE : Int}
    (hle : Restated.confirmedSettleTime M S tE' ≤ Restated.confirmedSettleTime M S tE)
    (h : Restated.ConfirmedMonotoneAfterHealing M S Sched x tE') :
    Restated.ConfirmedMonotoneAfterHealing M S Sched x tE :=
  fun v i j hij hv hi ha₁ ha₂ => h v i j hij hv (le_trans hle hi) ha₁ ha₂

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- With `r = switchRound S T0 + 1` and `14Δ ≤ T0`, the confirmation instant of `o_r + 2` is after
    `T0`, and the opening of round `r` is at most `T0 + period − 14Δ`. -/
theorem round_after_switch_bounds (facts : Record.Facts M) (S : Setup V) {T0 : Int} (hT0 : 14 * S.E.Δ ≤ T0) :
    T0 < M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S T0 + 1)) + 2) ∧
      M.opening S.E S.hc (Restated.switchRound M S T0 + 1)
        ≤ T0 + (Restated.constants M S).period - 14 * S.E.Δ := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hper := Restated.period_eq facts S
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have := Restated.switchRound_max facts S T0 (not_lt.1 hcon)
    exact absurd this (Nat.not_succ_le_self _)
  · rw [hper, (pS% opening_closed_srs) facts S, (pS% opening_slot_closed_srs) facts S.hc]
    by_cases h0 : Restated.switchRound M S T0 = 0
    · rw [h0]
      push_cast
      linarith
    · have hspec := Restated.switchRound_spec facts S T0 h0
      rw [(pS% confirmation_time_closed_srs) facts S.E, (pS% opening_slot_closed_srs) facts S.hc] at hspec
      push_cast at hspec ⊢
      nlinarith

end


section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `claimConfirmedAfterHealing_holds` at the healing length
    `healingLengthη M S gap + (gap + 2) · period`. -/
theorem claimConfirmedAfterHealing_holds_at (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (gap : Nat) (hgap : gap + 2 ≤ S.cfg.K)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int)
    (hlen : tGAT + (Restated.healingLengthη M S gap
      + ((gap : Int) + 2) * (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWake M S x)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE)
    (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    Restated.ConfirmedAgreeAfterHealing M S Sched x tE ∧
      Restated.ConfirmedMonotoneAfterHealing M S Sched x tE := by
  have hper0 : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hη0 := Restated.healingLengthη_nonneg facts S gap
  have hcv := Restated.commonViewOfFinalizedDescendantsAt_of_catchUp facts S Sched x hexec hsync hcatch hmult
    htd hgst (tE := tE) (by have := Restated.delta_le_healingLengthη_add_gap_period facts S gap; linarith)
    hawake
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hper := Restated.period_eq facts S
  have hηp := Restated.period_le_healingLengthη facts S gap
  have hgst0 : (0 : Int) ≤ tGAT := le_trans S.E.t_GST_nonneg hgst
  set T0 : Int := tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) with hT0
  have hT0Δ : 14 * S.E.Δ ≤ T0 := by
    rw [hper] at hηp
    rw [hT0, hper]
    nlinarith
  set r : Round := Restated.switchRound M S T0 + 1 with hr
  obtain ⟨hTr, hopr⟩ := Restated.round_after_switch_bounds facts S hT0Δ
  rw [← hr] at hTr hopr
  have hstart : tGAT ≤ M.proposal_time S.E ((M.opening_slot S.hc r)) := by
    rw [← facts.gr.opening_eq_proposal_time]
    have h1 := hTr
    rw [(pS% confirmation_time_closed_srs) facts S.E] at h1
    rw [(pS% opening_closed_srs) facts S]
    push_cast at h1 ⊢
    rw [hper] at hηp
    nlinarith
  have hgapper : (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) = (gap : Int) * (Restated.constants M S).period := rfl
  have hwinr : M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0))
      ≤ tE := by
    rw [← facts.gr.opening_eq_proposal_time, hgapper]
    have : T0 + ((gap : Int) + 1) * (Restated.constants M S).period ≤ tE := by
      rw [hT0]; nlinarith
    nlinarith
  obtain ⟨c, hrc, hcg, hprops, hprev1, -⟩ := Restated.strongWindow_of_recurrence_l85d facts S Sched hrec hstart
    hwinr
  have hc2 : 2 ≤ c := le_trans (Nat.le_add_left 2 r) hrc
  have hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))) :=
    hprops 0 (by decide)
  obtain ⟨h12, h2a, -, -, hwin⟩ := Restated.settle_instants facts S hc2 tGAT gap
  have hlen₁ : T0 ≤ M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 2) := by
    have hrc2 : r ≤ c - 2 := Nat.le_sub_of_add_le hrc
    have hmono' := facts.sch.confirmation_time_mono S
      (Nat.add_le_add_right (facts.gr.opening_slot_mono S hrc2) 2)
    linarith
  have hcE : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ tE := by
    have hca : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + gap)) := Restated.action_mono facts S hcg
    have hrg : (Restated.Vocabulary.Execution.Setup.a M S (r + gap)) = M.opening S.E S.hc r + (gap : Int) * (Restated.constants M S).period
        + 6 * S.E.Δ := by
      rw [(pS% action_closed_srs) facts S, (pS% opening_closed_srs) facts S, (pS% opening_slot_closed_srs) facts S.hc, hper]
      push_cast
      ring
    have : T0 + ((gap : Int) + 1) * (Restated.constants M S).period ≤ tE := by
      rw [hT0]; nlinarith
    nlinarith
  obtain ⟨-, -, hwin8⟩ := hwin hlen₁
  set tE' : Int := M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2) with htE'
  have htE' : tE' ≤ tE := le_trans h2a hcE
  have hlen' : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE' :=
    le_trans hlen₁ (le_of_lt h12)
  have hwin' : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE' := le_trans hwin8 (le_of_lt h12)
  have hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE' :=
    Restated.recordsSettledAtSettleTick_atStrongRound facts S Sched x tGAT tE gap hgap hgst hmono hexec hsync
      hmult hcatch hcv htd hcom hthird hawake hrec hsl hrs hcs hc2 hlen₁ hcE
      hopening hprev1
  have hthird' := third_of_later S Sched tE tE' htE' hthird
  have hawake' := awake_of_later Sched tGAT tE tE' htE' hawake
  have hrec' := Restated.strongOpeningsRecurFrom_of_later facts S Sched tGAT tE tE' gap htE' hrec
  have hsl' := sleepinessW_of_later S Sched tGAT tE tE' hmono hawake hwin' hsl
  have hrs' := Restated.roundSleepinessW_of_later facts S Sched tGAT tE tE' hmono hawake hwin' hrs
  have hcs' := Restated.committeeSleepinessW_of_later facts S Sched tGAT tE tE' hmono hawake hcom hwin' hcs
  obtain ⟨hA, hM⟩ := Restated.claimConfirmedAfterHealing_conclusion_of_settleTick facts S Sched x tGAT tE' gap
    hgap hlen' hgst hmono hexec hsync hmult hcatch hcv htd hcom hthird' hawake'
    hrec' hsl' hrs' hcs' hsettle
  have hmonoS := Restated.confirmedSettleTime_mono facts S htE'
  exact ⟨Restated.confirmedAgreeAfterHealing_of_earlier facts S Sched x hmonoS hA,
    Restated.confirmedMonotoneAfterHealing_of_earlier facts S Sched x hmonoS hM⟩

/-- `Restated.claimConfirmedAfterHealingStatement M S Sched` holds: for every `gap` with
    `gap + 2 ≤ K` there is a nonnegative healing length such that in every execution satisfying the
    healing premises with a phase of at least that length, from one round after the phase's end, any
    two validators honest through their steps and awake throughout the vote window of their step's
    slot hold confirmed outputs on one chain, and each such validator's confirmed output only
    extends between two such steps. -/
theorem claimConfirmedAfterHealing_holds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
 :
    Restated.claimConfirmedAfterHealingStatement M S Sched := by
  intro gap hgap
  have hper0 : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hη0 := Restated.healingLengthη_nonneg facts S gap
  refine ⟨Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period, ?_, ?_⟩
  · have : (0 : Int) ≤ ((gap : Int) + 2) * (Restated.constants M S).period :=
      mul_nonneg (by positivity) (le_of_lt hper0)
    linarith
  exact fun x tGAT tE hlen hgst hmono hexec hsync hmult hcatch htd hcom hthird
    hawake hrec hsl hrs hcs =>
    Restated.claimConfirmedAfterHealing_holds_at facts S Sched gap hgap x tGAT tE hlen hgst hmono
      hexec hsync hmult hcatch htd hcom hthird hawake hrec hsl hrs hcs

end

end DecoupledConsensusModel.Sts.Restated
