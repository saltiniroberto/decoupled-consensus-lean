import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedGrowth
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Restated.Claim13bK_GradeForCatchUp
import Proofs.Claims.Restated.Claim13bK_InclusionEarlier
import Proofs.Claims.Restated.Claim13bK_InclusionExists
import Proofs.Claims.Restated.Claim13bK_StableRecord
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingHolds
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKit
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsDerived
import Proofs.Claims.Restated.Constants
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedWake
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
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedGrowsAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimStableLiveAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_preceq
import Proofs.Claims.Spec2Claims.Claim13bK_InclusionEarlier
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart

/-!
# Liveness of the stable output after healing

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: inclusion, extension
and growth of the stable output for one execution (`claimStableLiveAfterHealing_conclusion`), and
`claimStableLiveAfterHealing_holds`, which proves
`Restated.claimStableLiveAfterHealingStatement M S Sched`.
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

/-- Refers by name to a private helper of the module `Proofs.Claims.Restated.Claim13beRoute3_83`. -/
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- In an execution with a phase `tGAT + (healingLengthη S gap + (gap + 2) · period) ≤ tE`
    satisfying the healing premises: every block an honest proposer proposes from `tE` on is in the
    stable output of every honest active validator from two periods and four delays after its
    proposal instant on, and the proposer proposes one when awake from `M.proposal_wake_start S s`
    to its proposal instant; no honest validator's stable output retreats from `tE` on; and for
    every `gapP`, if honest awake proposers recur within `gapP` periods from `tE` on, the stable
    output of every honest active validator keeps growing. -/
theorem claimStableLiveAfterHealing_conclusion (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period) ≤ tE)
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
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    Restated.StableIncludedAfterHealing M S Sched x tE ∧
      Restated.StableOnlyExtendsAfterHealing M S Sched x tE ∧
      ∀ gapP : Nat, Restated.honestAwakeProposersRecurFrom M S Sched tE gapP →
        Restated.StableGrowsAfterHealing M S Sched x tE gapP := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hper0 : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
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
  have hc1 : 1 ≤ c := le_trans (by decide) hc2
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
      hmult hwakes hsleeps hcatch hcv htd hcom hthird hawake hrec hsl hrs hcs hc2 hlen₁ hcE
      hopening hprev1
  have hle : Restated.confirmedSettleTime M S tE' ≤ tE := Restated.confirmedSettleTime_third_le facts S hc1 hcE
  have hthird' := third_of_later S Sched tE tE' htE' hthird
  have hawake' := awake_of_later Sched tGAT tE tE' htE' hawake
  have hrec' := Restated.strongOpeningsRecurFrom_of_later facts S Sched tGAT tE tE' gap htE' hrec
  have hsl' := sleepinessW_of_later S Sched tGAT tE tE' hmono hawake hwin' hsl
  have hrs' := Restated.roundSleepinessW_of_later facts S Sched tGAT tE tE' hmono hawake hwin' hrs
  have hcs' := Restated.committeeSleepinessW_of_later facts S Sched tGAT tE tE' hmono hawake hcom hwin' hcs
  have hlen'' : tGAT + Restated.healingLengthη M S gap ≤ tE' := Restated.healingLength_le_of_kit_l76 facts S hlen'
  have hlow := Restated.hlow_of_premises_l85f facts S Sched x tGAT tE' gap hgap hlen' hgst hmono hexec hsync
    hmult hwakes hsleeps hcv htd hcom hthird' hawake' hrec' hsl' hrs' hcs'
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE' gap hlen' hgst
    hmono hexec hsync hmult hcv hcom hthird' hawake' hrec'
  have hclear := fun r (hrD' : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r)
      (hrW : r ≤ Restated.switchRound M S tE') =>
    Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE' gap hgst hmono
      hexec hsync hmult hcv hcom hthird' hawake' r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE' gap hlow
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises facts S Sched
    x tGAT tE' gap hgap hlen' hgst hmono hexec hsync hmult hwakes hsleeps hcatch hcv htd hcom
    hthird' hawake' hrec' hsl' hrs' hcs' hlow
  have htEpos : 0 < tE := pos_of_phase S hlen hgst (Restated.healingLengthDevice_pos facts S gap)
  have hincl : Restated.StableIncludedAfterHealing M S Sched x tE := by
    intro s hsE hhon
    refine ⟨Restated.confirmedIncludedExists_inclX facts S Sched x hexec htd htEpos s hsE hhon, ?_⟩
    intro k B hB hk
    exact Restated.stableIncluded_afterPhase facts S Sched x tE' hexec hmono htd hcatch tGAT gap hgst hlen''
      hsync hthird' hawake' hrs' hmult hcv hcs' hcom hwakes hsleeps hrec' hprev hclear hB' hnW
      hAW hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hsettle (Restated.slot_ge_of_le_phaseEnd facts S hle hsE) hhon hB
      hk
  refine ⟨hincl, ?_, ?_⟩
  ·
    have hext := Restated.stableOnlyExtendsAfterHealing_of_settle facts S Sched x tE' hexec hmono htd hcatch tGAT
      gap hgst hlen'' hsync hthird' hawake' hrs' hmult hcv hcs' hcom hwakes hsleeps hrec' hprev
      hclear hB' hnW hAW hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hsettle
    intro v i j hij hvj hti
    exact hext v i j hij hvj (le_trans hle hti)
  ·
    intro gapP hprop
    obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE')
    obtain ⟨-, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
    have hsettleE : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE' + 1)) ≤ tE := hle
    have hG : Restated.stableGrowthDelay M S gapP
        = (gapP : Int) * (Restated.constants M S).period + Restated.stableInclusionDelay M S := rfl
    intro t htE i hti
    obtain ⟨s, hts, hsP, hhon, hawP⟩ := hprop t htE
    have hsE : tE ≤ M.proposal_time S.E s := le_trans htE (le_of_lt hts)
    obtain ⟨k, B, hB, hk⟩ := Restated.confirmedIncludedExists_inclX facts S Sched x hexec htd htEpos s hsE hhon
      hawP
    have hkv : (x[k].time : Int) ≤ M.vote_time S.E s := by
      rw [hk]; exact (facts.sch.proposal_time_lt_vote_time S.E s).le
    refine ⟨s, k, B, hts, hhon, hB, hkv, ?_, ?_⟩
    ·
      intro v hv
      have hi : n_b + 1 ≤ i := by
        by_contra hcon
        have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
        linarith
      have hlt : (x[i].time : Int) < M.proposal_time S.E s := by rw [hti]; exact hts
      exact (Restated.prec_get_confirmed_of_honestProposal facts S Sched x tE' hexec hmono htd hcatch tGAT gap
        hgst hlen'' hsync hthird' hawake' hrs' hmult hcv hcs' hcom hwakes hsleeps hrec' hprev
        hclear hB' hnW hAW hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hsettle
        (Restated.slot_ge_of_le_phaseEnd facts S hle hsE) hhon hB hkv hn_b v hi hv hlt).2
    ·
      intro v j hv hj hact
      exact (hincl s hsE hhon).2 k B hB hkv v j hv (by rw [hG] at hj; linarith) hact

end


section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `claimStableLiveAfterHealing_holds` at the healing length
    `healingLengthη M S gap + (gap + 2) · period`. -/
theorem claimStableLiveAfterHealing_holds_at (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V)
    (gap : Nat) (hgap : gap + 2 ≤ S.cfg.K)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int)
    (hlen : tGAT + (Restated.healingLengthη M S gap
      + ((gap : Int) + 2) * (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched)
    (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
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
    Restated.StableIncludedAfterHealing M S Sched x tE ∧
      Restated.StableOnlyExtendsAfterHealing M S Sched x tE ∧
      ∀ gapP : Nat, Restated.honestAwakeProposersRecurFrom M S Sched tE gapP →
        Restated.StableGrowsAfterHealing M S Sched x tE gapP := by
  have hcv := Restated.commonViewOfFinalizedDescendantsAt_of_catchUp facts S Sched x hexec hsync hcatch hmult
    htd hgst (tE := tE) (by have := Restated.delta_le_healingLengthη_add_gap_period facts S gap; linarith)
    hawake
  exact Restated.claimStableLiveAfterHealing_conclusion facts S Sched x tGAT tE gap hgap hlen hgst hmono
    hexec hsync hmult hwakes hsleeps hcatch hcv htd hcom hthird hawake hrec hsl hrs hcs

/-- For every setup `S` and schedule `Sched`,
    `Restated.claimStableLiveAfterHealingStatement M S Sched` holds. -/
theorem claimStableLiveAfterHealing_holds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) :
    Restated.claimStableLiveAfterHealingStatement M S Sched := by
  intro gap hgap
  refine ⟨Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period,
    le_of_lt (Restated.healingLengthDevice_pos facts S gap), ?_⟩
  exact fun x tGAT tE hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird hawake
    hrec hsl hrs hcs =>
    Restated.claimStableLiveAfterHealing_holds_at facts S Sched gap hgap x tGAT tE hlen hgst hmono
      hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird hawake hrec hsl hrs hcs

end

end DecoupledConsensusModel.Sts.Restated
