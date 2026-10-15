import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedAgree
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedWake
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
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
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedIncludedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Extension of the confirmed output after the settle instant

Every honest validator's confirmed output only extends from the settle instant on, stated over a
model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- If `t ≤ t'` and every honest validator's confirmed output only extends from `t` on, then it only
    extends from `t'` on. -/
theorem confirmedOnlyExtendsAfterHealing_of_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {t t' : Int} (htt' : t ≤ t')
    (h : Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x t) :
    Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x t' :=
  fun v i j hij hvj hti => h v i j hij hvj (le_trans htt' hti)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- On the premises of `afterPhaseJointRound_of_premises`, if `RecordsSettledAtSettleTick` holds,
    then every honest validator's confirmed output only extends from `confirmedSettleTime S tE` on,
    whether or not it is awake. -/
theorem confirmedOnlyExtendsAfterHealing_of_settle (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE) :
    Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x (Restated.confirmedSettleTime M S tE) := by
  intro v i j hij hvj hti
  obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  have hts : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) ≤ (x[i].time : Int) := hti
  have hki : n_b + 1 ≤ i := by
    by_contra hcon
    have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
    linarith
  have hvk : ∀ k : Nat, k ≤ j → Restated.HonestThrough M Sched x k v := fun k hkj t' h =>
    hvj t' (le_trans h (Restated.time_mono_int facts S Sched x hkj))
  have hts' : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[i].time : Int) :=
    le_trans (Restated.action_mono facts S (Nat.le_succ _)) hts
  refine Restated.get_confirmed_preceq_of_records_along facts S Sched x htd hcs v hij (fun k hik hkj => ?_)
    (fun k hik hkj => ?_) (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew k τ u hl)
  · exact Restated.records_ancestorOfHonestHeads_after_settleTick facts S Sched x tE hexec hmono htd hcatch tGAT
      gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW
      hAW hJswitch hTW₀ hJ₀ hsettle hn_b v k (le_trans hki hik) (hvk k hkj)
  · exact Restated.finalized_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch le_rfl hTW₀ hJ₀ (le_trans hts' (Restated.time_mono_int facts S Sched x (le_of_lt hik)))
      (hvk k hkj)

end

end DecoupledConsensusModel.Sts.Restated
