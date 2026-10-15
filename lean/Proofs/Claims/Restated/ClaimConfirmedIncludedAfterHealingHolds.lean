import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Restated.Claim13bK_InclusionEarlier
import Proofs.Claims.Restated.Claim13bK_InclusionExists
import Proofs.Claims.Restated.Claim13bK_InclusionExtends
import Proofs.Claims.Restated.Claim13bK_InclusionReaders
import Proofs.Claims.Restated.Claim13bK_ProposalVotesAfterPhase
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
import Model.Conditions.Claim13bK_ConfirmedInclusion
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bK_InclusionReaders
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimConfirmedIncludedAfterHealingHolds
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
# Inclusion in confirmed outputs after healing

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: the inclusion
conclusions for one execution from `HonestProposalHeadsAtOwnSlotAfterPhase`, the statement
`Restated.claimConfirmedIncludedAfterHealingStatement M S Sched` from that fact, and the statement
with no further hypothesis (`claimConfirmedIncludedAfterHealing_holds`).
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

/-- Under `HonestProposalHeadsAtOwnSlotAfterPhase M S Sched`, in an execution with a phase
    `tGAT + (healingLengthη S gap + (gap + 2) · period) ≤ tE` satisfying the healing premises: from
    `tE` on, every honest proposer awake from `M.proposal_wake_start S s` to its proposal instant
    proposes, every block it proposes by its slot's vote instant is in the confirmed output of every
    honest active validator from six delays after its proposal on, and every honest validator's
    confirmed output only extends. -/
theorem claimConfirmedIncludedAfterHealing_conclusion_of_adoption (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hadoptP : Restated.HonestProposalHeadsAtOwnSlotAfterPhase M S Sched)
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
    Restated.ConfirmedIncludedAfterHealing M S Sched x tE ∧ Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x tE := by
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
  have hadopt := hadoptP x tE' hexec hmono htd hcatch tGAT gap hgst hlen'' hsync hthird' hawake'
    hrs' hmult hcv hcs' hcom hwakes hsleeps hrec' hprev hclear hB' hnW hAW hJswitch
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase
  have hincl := Restated.confirmedIncluded_of_ownSlotVotes facts S Sched x tE' hexec hmono htd hcatch tGAT gap
    hgst hlen'' hsync hthird' hawake' hrs' hmult hcv hcs' hcom hwakes hsleeps hrec' hprev hclear
    hB' hnW hAW hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hsettle hadopt
  have hext := Restated.confirmedOnlyExtendsAfterHealing_of_settle facts S Sched x tE' hexec hmono htd hcatch
    tGAT gap hgst hlen'' hsync hthird' hawake' hrs' hmult hcv hcs' hcom hwakes hsleeps hrec'
    hprev hclear hB' hnW hAW hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hsettle
  refine ⟨fun s hsE hhon => ⟨?_, ?_⟩,
    Restated.confirmedOnlyExtendsAfterHealing_of_settle_le facts S Sched x hle hext⟩
  ·
    have htEpos : 0 < tE := pos_of_phase S hlen hgst (Restated.healingLengthDevice_pos facts S gap)
    exact Restated.confirmedIncludedExists_inclX facts S Sched x hexec htd htEpos s hsE hhon
  · exact hincl s (Restated.slot_ge_of_le_phaseEnd facts S hle hsE) hhon

end


section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `claimConfirmedIncludedAfterHealing_of_adoption` at the healing length
    `healingLengthη M S gap + (gap + 2) · period`. -/
theorem claimConfirmedIncludedAfterHealing_of_adoption_at (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V)
    (hadoptP : Restated.HonestProposalHeadsAtOwnSlotAfterPhase M S Sched)
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
    Restated.ConfirmedIncludedAfterHealing M S Sched x tE ∧
      Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x tE := by
  have hcv := Restated.commonViewOfFinalizedDescendantsAt_of_catchUp facts S Sched x hexec hsync hcatch hmult
    htd hgst (tE := tE) (by have := Restated.delta_le_healingLengthη_add_gap_period facts S gap; linarith)
    hawake
  exact Restated.claimConfirmedIncludedAfterHealing_conclusion_of_adoption facts S Sched hadoptP x tGAT tE gap
    hgap hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch hcv htd hcom hthird hawake hrec
    hsl hrs hcs

/-- Under `HonestProposalHeadsAtOwnSlotAfterPhase M S Sched`,
    `Restated.claimConfirmedIncludedAfterHealingStatement M S Sched` holds: for every `gap` with
    `gap + 2 ≤ S.cfg.K` there is a nonnegative healing length such that in every execution
    satisfying the healing premises with a phase of at least that length, from the phase's end on,
    honest proposers awake before their proposal instant propose, their blocks are in every honest
    active validator's confirmed output from six delays after the proposal on, and every honest
    validator's confirmed output only extends. -/
theorem claimConfirmedIncludedAfterHealing_of_adoption (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hadoptP : Restated.HonestProposalHeadsAtOwnSlotAfterPhase M S Sched) :
    Restated.claimConfirmedIncludedAfterHealingStatement M S Sched := by
  intro gap hgap
  refine ⟨Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period,
    le_of_lt (Restated.healingLengthDevice_pos facts S gap), ?_⟩
  exact fun x tGAT tE hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird hawake
    hrec hsl hrs hcs =>
    Restated.claimConfirmedIncludedAfterHealing_of_adoption_at facts S Sched hadoptP gap hgap x tGAT
      tE hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird hawake hrec hsl hrs
      hcs

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `claimConfirmedIncludedAfterHealing_holds` at the healing length
    `healingLengthη M S gap + (gap + 2) · period`. -/
theorem claimConfirmedIncludedAfterHealing_holds_at (facts : Record.Facts M) (S : Setup V)
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
    Restated.ConfirmedIncludedAfterHealing M S Sched x tE ∧
      Restated.ConfirmedOnlyExtendsAfterHealing M S Sched x tE :=
  Restated.claimConfirmedIncludedAfterHealing_of_adoption_at facts S Sched
    (by
      intro x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs
        hcom hw hs hrec hprev hclear hB' n_W hnW T_W hAW hJswitch n₀ T₀ hTW₀ hJ₀ tHi
      exact Restated.honestProposalHeadsAtOwnSlot_afterPhase facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ tHi
        )
    gap hgap x tGAT tE hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird
    hawake hrec hsl hrs hcs

/-- For every setup `S` and schedule `Sched`,
    `Restated.claimConfirmedIncludedAfterHealingStatement M S Sched` holds. -/
theorem claimConfirmedIncludedAfterHealing_holds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) :
    Restated.claimConfirmedIncludedAfterHealingStatement M S Sched := by
  intro gap hgap
  refine ⟨Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period,
    le_of_lt (Restated.healingLengthDevice_pos facts S gap), ?_⟩
  exact fun x tGAT tE hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird hawake
    hrec hsl hrs hcs =>
    Restated.claimConfirmedIncludedAfterHealing_holds_at facts S Sched gap hgap x tGAT tE hlen hgst
      hmono hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird hawake hrec hsl hrs hcs

end

end DecoupledConsensusModel.Sts.Restated
