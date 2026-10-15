import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedAgree
import Proofs.Claims.Restated.Claim13bK_JointBase
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_77
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
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
# The joint invariant at the switch round, and agreement after healing

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: from the healing
premises and `hlow`, the joint invariant at the switch round with its anchor, and agreement of
confirmed outputs from the settle instant on.
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
open DecoupledConsensusModel.Statements.Instantiation

/-- If, for the switch round's tick step `n_W` and every round-`rD'` anchor `T_D'`, every validator
    honest through a step `n₁ ≤ n_W` at or after one instant before the vote instant of `o_rW + 1`
    holds a justified height at least `h(T_D')`, then every validator honest through the switch
    round's tick step holds there a justified height at least that of every round-`rD'` anchor. -/
theorem baseJustifiedHighAtSwitchRoundW_of_hlow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat)
    (hlow : ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j) :
    Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap := by
  intro T_D' hAD' n_W hnW v hv
  have h1 := (Restated.tickStepAt_time facts x hnW).2
  have h2 := Restated.vote_time_succ_le_confirmation_time_l77 facts S ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  rw [Restated.a_eq_confirmation_opening_l58 facts] at h1
  exact hlow n_W hnW T_D' hAD' v n_W (by linarith) le_rfl hv

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- From the healing premises and `hlow`, there are a step `n_W` that is the tick at `S.a rW` and a
    round-`rW` anchor `T_W` such that every validator honest through a step `n₁ ≤ n_W` at or after
    one instant before the vote instant of `o_rW + 1` holds a latest justified checkpoint that is
    `T_W` or an ancestor of it, and the joint invariant holds at `rW` with tick step `n_W`, switch
    step `n_W` and anchor `T_W`. -/
theorem afterPhaseJointSwitchRound_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcatch : Restated.CatchUpOnWake M S x)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hlow : ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j) :
    ∃ (n_W : Nat) (T_W : NamedBlock V), Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) ∧
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W ∧
      (∀ (v : V) (n₁ : Nat),
        M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
          ≤ (x[n₁].time : Int) →
        n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) ∧
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T_W := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsync hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE gap hgst hmono
      hexec hsync hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE gap hlow
  obtain ⟨n_W, T_W, hnW, hAW, hbase⟩ := Restated.afterPhaseInvariantOverActiveSetsJoint_at_switchRound facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hwakes hsleeps hcv htd hcom hthird
    hawake hrec hsl hrs hcs hprev hclear hB'
  have hJswitch := Restated.justifiedAncestor_before_switchTick_of_justifiedHigh facts S Sched x tE hexec hmono
    htd tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcom hrec hprev hclear hnW hAW
    (hlow n_W hnW)
  exact ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- From the healing premises, `hlow` and `RecordsSettledAtActionTicks S Sched x tE`: from
    `confirmedSettleTime S tE` on, any two validators honest through their steps, each awake
    throughout the vote window of its step's slot, hold confirmed outputs on one chain. -/
theorem confirmedAgreeAfterHealing_of_joint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcatch : Restated.CatchUpOnWake M S x)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hlow : ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j)
    (hsettle : Restated.RecordsSettledAtActionTicks M S Sched x tE) :
    Restated.ConfirmedAgreeAfterHealing M S Sched x tE := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsync hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE gap hgst hmono
      hexec hsync hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE gap hlow
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises facts S Sched
    x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  exact Restated.confirmedAgreeAfterHealing_of_settle facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
    hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes hsleeps hrec hprev hclear hB' hnW hAW
    hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hsettle

end

end DecoupledConsensusModel.Sts.Restated
