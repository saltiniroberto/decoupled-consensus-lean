import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Restated.Claim13bK_FinalityInclusion
import Proofs.Claims.Restated.Claim13bK_JointBase
import Proofs.Claims.Restated.Claim13bK_ProposalAdoption
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepKitStore
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Proofs.Claims.Restated.Claim13beRoute3_96
import Proofs.Claims.Restated.Claim13beRoute3_97
import Proofs.Claims.Restated.ClaimAsyncK_AfterFacts
import Proofs.Claims.Restated.ClaimAsyncK_FinalizedAbove
import Proofs.Claims.Restated.ClaimAsyncK_GstShift
import Proofs.Claims.Restated.Constants
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_GstShift
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_SecondHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1

/-!
# Finalized blocks after a phase of healing, and the stable output after `tSafe`

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: some block in play
becomes an ancestor of every honest finalized block and has chain-state height greater than every
earlier running maximum height (`finalizedAboveSeen_ofPhase_inLog`,
`finalizedAboveSeen_afterPeriod_inLog`), and the stable output keeps `P` as an ancestor after
`tSafe` (`stablePersists_afterSafe`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers by name to a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_85f`. -/
local macro "p85f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_85f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- On the premises of a phase `[tGAT, tE]` whose bounded premises continue to `tL`, at least
    `Restated.liveAgainAfterHealing M S gap` after `tE`, some named block `B` in play is an ancestor
    of the finalized block of every honest validator at every step from some time `t ≤ tL` on, and
    its chain-state height is greater than the running maximum height `h_max` of every store at
    every step up to the time `tGAT`. -/
theorem finalizedAboveSeen_ofPhase_inLog (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hlive : tE + Restated.liveAgainAfterHealing M S gap ≤ tL)
    (hrecvAll : ∀ r' : Round, Restated.switchRound M S tE ≤ r' → Restated.NextRoundReceipts M S Sched x r') :
    ∃ (B : NamedBlock V) (t : Int), t ≤ tL ∧
      (∀ (u : V) (i : Nat), (x[i].time : Int) ≤ tGAT →
        (x[i][u].st).st.core.h_max < (M.derive_named S.E S.cfg B).h) ∧
      (∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w → t ≤ (x[j].time : Int) →
        Block.Preceq B.erase (x[j][w].st).st.core.F) ∧
      Restated.blockInLog M S Sched x B := by
  classical
  have hthirdE : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t ht => hthird t (ht.trans hEL)
  have hphaseE : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h1 h2 => hawake t h1 (h2.trans hEL)
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hlenL' : tGAT + Restated.healingLengthη M S gap ≤ tL := hlen'.trans hEL
  -- Step 1: the anchor and the joint invariant.
  have hlow := Restated.hlow_of_premises_l85f facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult
     hcv htd hcom hthirdE hphaseE hrecE hsl hrs hcs
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsync hmult hcv hcom hthirdE hphaseE hrecE
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE gap hgst hmono
      hexec hsync hmult hcv hcom hthirdE hphaseE r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_phase facts S Sched x tGAT tE gap hgap hlen hgst hmono
    hexec hsync hmult hcv htd hcom hthirdE hphaseE hrecE hsl hrs hcs
  obtain ⟨n_W, T_W, hnW, hAW, hJ⟩ := Restated.afterPhaseInvariantOverActiveSetsJoint_at_switchRound facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hcv htd hcom hthirdE
    hphaseE hrecE hsl hrs hcs hprev hclear hB'
  have hJswitch := Restated.justifiedAncestor_before_switchTick_of_justifiedHigh facts S Sched x tE hexec hmono
    htd tGAT gap hgst hlen' hsync hthirdE hphaseE hrs hmult hcv hcom hrecE hprev hclear hnW hAW
    (hlow n_W hnW)
  -- Step 2: the running maximum heights up to `tGAT`.
  have hband := Restated.hMax_le_switchAnchor_of_le_tGAT facts S Sched x tGAT tE gap hexec hmono hgst hlen'
    hthirdE hphaseE hrs htd hJ
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hper : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  have hP12 : 12 * S.E.Δ ≤ (Restated.constants M S).period := by rw [hper]; nlinarith
  have hP0 : (0 : Int) ≤ (Restated.constants M S).period := by linarith
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  have hWne : Restated.switchRound M S tE ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos _) hrDrW)
  have hC : ∀ r d : Round, M.confirmation_time S.E ((M.opening_slot S.hc (r + d)) + 2)
      = M.confirmation_time S.E ((M.opening_slot S.hc r) + 2) + (d : Int) * (Restated.constants M S).period := by
    intro r d
    have h1 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + d)) + 2)
    have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc r) + 2)
    have h3 : (M.opening_slot S.hc (r + d)) + 2 = (M.opening_slot S.hc r) + 2 + d * S.hc.R := by
      rw [facts.gr.opening_slot_add]; exact Nat.add_right_comm _ _ _
    have h4 := slotStart_add S.E.Δ ((M.opening_slot S.hc r) + 2) (d * S.hc.R)
    rw [h3] at h1 ⊢
    rw [hper]
    push_cast at h4
    linarith
  have hWE : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) ≤ tE :=
    Restated.switchRound_spec facts S tE hWne
  have hWE1 : tE < M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2) := by
    by_contra hcon
    exact absurd (Restated.switchRound_max facts S tE (not_lt.mp hcon)) (Nat.not_succ_le_self _)
  have hliveEq : Restated.liveAgainAfterHealing M S gap =
      ((2 * gap + S.cfg.timeoutDelay / S.hc.R + 3 : Nat) : Int) * (Restated.constants M S).period +
        ((3 * gap + S.cfg.timeoutDelay / S.hc.R : Nat) : Int) * (Restated.constants M S).period +
        (((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) * (Restated.constants M S).period +
          14 * S.E.Δ) := rfl
  rw [hliveEq] at hlive
  have hWL : Restated.switchRound M S tE + (3 * gap + S.cfg.timeoutDelay / S.hc.R) ≤ Restated.switchRound M S tL := by
    apply Restated.switchRound_max facts
    rw [hC]
    have h1 : (0 : Int) ≤ ((2 * gap + S.cfg.timeoutDelay / S.hc.R + 3 : Nat) : Int) *
        (Restated.constants M S).period := mul_nonneg (Int.natCast_nonneg _) hP0
    have h2 : (0 : Int) ≤ ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) *
        (Restated.constants M S).period := mul_nonneg (Int.natCast_nonneg _) hP0
    linarith
  obtain ⟨-, hWg⟩ := nat_switch_fa _ _ _ gap (S.cfg.timeoutDelay / S.hc.R) hrDrW hWL
  obtain ⟨v₀, -⟩ := exists_not_adv_l76 S Sched (hthird tL le_rfl)
  obtain ⟨m₀, hm₀⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (Restated.switchRound M S tL))
  have hNeq : (x[m₀ + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) := (Restated.tickStepAt_time facts x hm₀).1
  have hrDW : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap rho₀ hgst hlenL')
  obtain ⟨-, hWLE⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlenL' hrDW le_rfl
  have hNW : (x[m₀ + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) := le_of_eq hNeq
  have hWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) ≤ (x[m₀ + 1].time : Int) := le_of_eq hNeq.symm
  have hN : (x[m₀ + 1].time : Int) ≤ tL := hNW.trans hWLE
  obtain ⟨T_D', hA⟩ := Restated.exists_anchorAtRound facts S Sched x hsync hmono hawake hgst hcv hexec hmult
    hthird hcom hrec hlenL' htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap)
    (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap rho₀ hgst hlenL')
  -- Step 3: the strong window `q₀` after the switch round, and its opening proposal `B'`.
  obtain ⟨q₀, hq₀lo, hq₀hi, hw₀, -, -⟩ := Restated.strongWindow_sharp_ofRound_f7 facts S Sched hrec hgst hlenL'
    hrDrW hWg
  obtain ⟨hg3, hrDq₀, hq₀WL, hq₀g⟩ := nat_firstWindow_fa _ _ _ _ gap
    (S.cfg.timeoutDelay / S.hc.R) hrDrW hWL hq₀lo hq₀hi
  have hopening₀ : S.E.proposer ((M.opening_slot S.hc q₀)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc q₀))) := by
    simpa only [Nat.add_zero] using hw₀ 0 (by decide)
  have hq₀W : (Restated.Vocabulary.Execution.Setup.a M S q₀) ≤ (x[m₀ + 1].time : Int) := by
    rw [hNeq]; exact (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hq₀WL
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ (m₀ + 1) hsync hmono hawake hgst
    hcv hexec hmult hthird hN
  obtain ⟨cpB, B', hcpB, hB'run⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc q₀)
  have hTB' := Restated.openingProposal_height_ge_anchorAtRound facts S Sched x v₀ (m₀ + 1) hsync hmono hawake
    hgst hcv hexec hmult hthird hN hcom hrec (le_trans (Nat.le_add_right _ 2) hrDrW) hAW hEL
    hq₀lo hrDq₀ hq₀W hopening₀ cpB hcpB hB'run
  have hconfq₀ : M.confirmation_time S.E ((M.opening_slot S.hc q₀)) = (Restated.Vocabulary.Execution.Setup.a M S q₀) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S q₀
  obtain ⟨hpos₀, hgat₀⟩ := Restated.openingBounds_afterDeadline_l85d facts S hrDq₀
  have hwinG1 : ∀ s : Slot, (M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap + 1)) ≤ s →
      tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ := by
    intro s hs
    have hround : Restated.deadlineRoundW M S tGAT gap + 1 ≤ M.round_of S.hc s := by
      have h := facts.gr.round_of_mono S.hc hs
      rwa [facts.gr.round_of_opening_slot_eq S.hc] at h
    have h0 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
      (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap) (Nat.lt_of_succ_le hround))
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (M.round_of S.hc s)
    have hΔ := S.E.Δ_pos
    linarith
  obtain ⟨k₀, hk₀t, hk₀sent, hk₀B⟩ := Restated.runProposal_sent_asItself facts S Sched x v₀ (m₀ + 1) hsync
    hmono hawake hgst hcv hexec hmult hthird hN hpos₀ hgat₀
    ((facts.sch.proposal_time_le_confirmation_time S.E _).trans (by rw [hconfq₀]; exact hq₀W))
    hopening₀
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (notHeldAt_anti hmono (facts.sch.proposal_time_le_confirmation_time S.E _) hopening₀)
      (hwinG1 _ (facts.gr.opening_slot_mono S (Nat.le_of_succ_le hrDq₀))))
    cpB hcpB hB'run
  have hB'log : Restated.blockInLog M S Sched x B' :=
    ⟨B', Or.inl ⟨k₀, _, hk₀sent, rfl⟩, Proofs.NamedAncestry.named_self B'⟩
  have hhon₀ : HonestThroughTime Sched (M.vote_time S.E ((M.opening_slot S.hc q₀)))
      (S.E.proposer ((M.opening_slot S.hc q₀))) :=
    fun t' ht' hadv => (mem_notHeldAt.mp hopening₀)
      (hmono _ _ (ht'.trans (facts.sch.Protocol_vote_time_le_confirmation_time S.E _)) hadv)
  have hs0₀ : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ (M.opening_slot S.hc q₀) := by
    have h1 := facts.gr.opening_slot_le_of_le S.hc hq₀lo
    rw [facts.gr.opening_slot_succ] at h1
    exact le_trans (Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _) h1
  have hheads₀ := Restated.honestProposal_ancestorOfHonestHeadsFrom_i1b (hrecvAll := hrecvAll) facts S Sched x tE hexec hmono htd tGAT
    gap hgst hlen' hsync hthirdE hphaseE hrs hmult hcv hcs hcom hrecE hprev hclear
    hB' hnW hAW hJswitch le_rfl (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hJ hawake hthird hrec hs0₀
    (by rw [hconfq₀]; exact hq₀W.trans hN) hhon₀ hk₀B
    (by rw [hk₀t]; exact (facts.sch.proposal_time_lt_vote_time S.E _).le)
  -- Step 4: the strong window `c₁` after `q₀`, and the second window.
  obtain ⟨c₁, hc₁lo, hc₁hi, hw₁, hw₁p, hw₁pp⟩ := Restated.strongWindow_sharp_ofRound_f7 facts S Sched hrec hgst
    hlenL' hrDq₀ hq₀g
  obtain ⟨hc₁W2, hq₀c₁, hc₁mg⟩ := nat_secondWindow_fa _ _ _ _ gap
    (S.cfg.timeoutDelay / S.hc.R) hWL hq₀lo hq₀hi hc₁lo hc₁hi
  obtain ⟨c₂, hc₁₂, hc₂hi, ⟨hw₂, -, -⟩, hall₂⟩ := Restated.secondWindowSharp_f7 facts S
    Sched x v₀ tGAT tE tL gap hgap hg3 hlen hEL hgst hmono hexec hsync hmult hcv htd hcom hthird
    hawake hrec hrs hcs hprev hclear hB' hnW hAW hJswitch le_rfl
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hJ hNW hN hWN hA hB'log (fun s' h _ => hheads₀ s' h) (facts.gr.opening_slot_mono S hq₀c₁) hc₁W2
    hc₁mg hw₁ hw₁p hw₁pp
  obtain ⟨cp₂, P₂, hcp₂, hP₂⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    ((M.opening_slot S.hc c₂) + 2)
  obtain ⟨P₂', hEq, hB'P₂, hltB, -⟩ := hall₂ cp₂ hcp₂ (some P₂) hP₂
  cases hEq
  obtain ⟨hrDc₂, hc₂W, hc₂1, hcount⟩ := nat_thirdWindow_fa _ _ _ _ _ _ gap
    (S.cfg.timeoutDelay / S.hc.R) hrDrW hWL hq₀lo hq₀hi hc₁lo hc₁hi hc₁₂ hc₂hi
  have hjlt : (M.derive_named S.E S.cfg P₂).h_j < (M.derive_named S.E S.cfg P₂).h :=
    ((facts.cs.chainOrder_derive_named S.E S.cfg P₂)).justified_below_height
  -- Step 5: `P₂` is a sent honest proposal of the slot `o_{c₂} + 2`, finalized.
  have hprop₂ : S.E.proposer ((M.opening_slot S.hc c₂) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₂) + 2)) :=
    hw₂ 2 (by decide)
  obtain ⟨-, hgat₂⟩ := Restated.openingBounds_afterDeadline_l85d facts S hrDc₂
  obtain ⟨-, hvA, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c₂
  have hhor₂ : M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2) ≤
      (x[m₀ + 1].time : Int) := by
    rw [hNeq]
    exact hpv.trans (hvA.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hc₂1))
  obtain ⟨k₂, hk₂t, hk₂sent, hk₂B⟩ := Restated.runProposal_sent_asItself facts S Sched x v₀ (m₀ + 1) hsync hmono
    hawake hgst hcv hexec hmult hthird hN (Nat.succ_pos _)
    (hgat₂.trans (facts.sch.proposal_time_mono S.E (Nat.le_add_right _ 2))) hhor₂ hprop₂
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (notHeldAt_anti hmono (facts.sch.proposal_time_le_confirmation_time S.E _) hprop₂)
      (hwinG1 _ ((facts.gr.opening_slot_mono S (Nat.le_of_succ_le hrDc₂)).trans (Nat.le_add_right _ 2))))
    cp₂ hcp₂ hP₂
  have hhon₂ : HonestThroughTime Sched (M.vote_time S.E ((M.opening_slot S.hc c₂) + 2))
      (S.E.proposer ((M.opening_slot S.hc c₂) + 2)) :=
    fun t' ht' hadv => (mem_notHeldAt.mp hprop₂)
      (hmono _ _ (ht'.trans (facts.sch.Protocol_vote_time_le_confirmation_time S.E _)) hadv)
  have hpt₂ := (facts.sch.slot_instants_l55 S.E ((M.opening_slot S.hc c₂) + 2)).2.2.2.2.2
  have hsE : tE ≤ M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2) := by
    have hC1 : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE + 2)) + 2)
        = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2) + ((1 : Nat) : Int) * (Restated.constants M S).period :=
      hC (Restated.switchRound M S tE + 1) 1
    have hmo := facts.sch.confirmation_time_mono S (Nat.add_le_add_right (facts.gr.opening_slot_mono S hc₂W) 2)
    push_cast at hC1
    linarith
  have hcontEq : Restated.finalityPremisesContinueDirect M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) * (Restated.constants M S).period +
        14 * S.E.Δ := rfl
  have hcont : M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2) +
      Restated.finalityPremisesContinueDirect M S gap ≤ tL := by
    rw [hcontEq]
    have hmo := facts.sch.confirmation_time_mono S (Nat.add_le_add_right (facts.gr.opening_slot_mono S hcount) 2)
    have e1 := hC c₂ (3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1)
    have e2 := hC (Restated.switchRound M S tE + (2 * gap + S.cfg.timeoutDelay / S.hc.R + 3) +
      (3 * gap + S.cfg.timeoutDelay / S.hc.R)) (3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1)
    have e3 := hC (Restated.switchRound M S tE + (2 * gap + S.cfg.timeoutDelay / S.hc.R + 3))
      (3 * gap + S.cfg.timeoutDelay / S.hc.R)
    have e4 := hC (Restated.switchRound M S tE) (2 * gap + S.cfg.timeoutDelay / S.hc.R + 3)
    linarith
  have hfin := Restated.finalizedAfterDeadline_of_premises_f3 facts S Sched x tGAT tE tL gap hgap hlen hEL hgst
    hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hsl hrs hcs hsE hcont
    hhon₂ hk₂B (by rw [hk₂t]; exact (facts.sch.proposal_time_lt_vote_time S.E _).le)
  have hdeadEq : Restated.finalityDeadlineDirect M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 : Nat) : Int) * (Restated.constants M S).period +
        9 * S.E.Δ := rfl
  refine ⟨P₂, M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2) + Restated.finalityDeadlineDirect M S gap,
    ?_, ?_, hfin, ⟨P₂, Or.inl ⟨k₂, _, hk₂sent, rfl⟩, Proofs.NamedAncestry.named_self P₂⟩⟩
  · have hK : ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) =
        ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 : Nat) : Int) + 1 := by push_cast; ring
    rw [hcontEq, hK] at hcont
    rw [hdeadEq]
    linarith
  · intro u i hi
    exact nat_heights_fa _ _ _ _ _ (hband u i hi) hTB' hltB hjlt

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- A block in play in the execution moved to the setup with GST `g` is in play in `x`. -/
theorem tr_back_blockInLog (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (A : NamedBlock V)
    (h : Restated.blockInLog M (setupWithGST S g hg) Sched
      (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) A) :
    Restated.blockInLog M S Sched x A := h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The healing-length bound `a + (healingLengthη + period) ≤ b` and `gap + 2 ≤ K` carry over from
    `S` to the setup with GST `g`. -/
theorem tr_length (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (gap : Nat)
    (a b : Int)
    (h : a + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ b ∧
      gap + 2 ≤ S.cfg.K) :
    a + (Restated.healingLengthη M (setupWithGST S g hg) gap +
        (Restated.constants M (setupWithGST S g hg)).period) ≤ b ∧
      gap + 2 ≤ (setupWithGST S g hg).cfg.K := by
  have hv : ∀ s : Slot, M.vote_time (setupWithGST S g hg).E s = M.vote_time S.E s := by
    intro s
    have h1 := (facts.sch.slot_instants_l55 (setupWithGST S g hg).E s).1
    have h2 := (facts.sch.slot_instants_l55 S.E s).1
    have h3 := facts.sch.proposal_time_eq_of_delta_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
    have h4 : (setupWithGST S g hg).E.Δ = S.E.Δ := rfl
    rw [h1, h2, h3, h4]
  have hhb : ∀ q : Round, Restated.healingBoundaryTime M (setupWithGST S g hg) q =
      Restated.healingBoundaryTime M S q := fun q => hv _
  have hfs : (Restated.constants M (setupWithGST S g hg)).finalityStartup gap =
      (Restated.constants M S).finalityStartup gap := by
    show Restated.healingBoundaryTime M (setupWithGST S g hg) _ - _ =
      Restated.healingBoundaryTime M S _ - _
    rw [hhb]
    rfl
  have hfd : (Restated.constants M (setupWithGST S g hg)).finalityDeadline gap =
      (Restated.constants M S).finalityDeadline gap := by
    show Restated.healingBoundaryTime M (setupWithGST S g hg) _ - _ + _ =
      Restated.healingBoundaryTime M S _ - _ + _
    rw [hhb]
    rfl
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  have e : Restated.healingLengthη M (setupWithGST S g hg) gap = Restated.healingLengthη M S gap := by
    simp only [Restated.healingLengthη, Restated.healingLength, hfs, hfd]
    rfl
  rw [e]
  exact h1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- On the premises after the period ending at `tAgain`, some named block `B` in play is, from some
    time at or before `tSafe` on, an ancestor of the finalized block of every honest validator at
    every step, and its chain-state height is greater than the running maximum height of every store
    at every step up to `tAgain`. -/
theorem finalizedAboveSeen_afterPeriod_inLog (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (gap : Nat) (hgap : gap + 2 ≤ S.cfg.K)
    {tE b₀ b₁ tAgain tSafe tHeal : Int}
    (hheal : Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period ≤ tHeal)
    (hb : b₀ ≤ b₁) (hg : S.E.t_GST ≤ b₁) (hAgain : b₁ + S.E.Δ ≤ tAgain)
    (hSafe : tAgain + (tHeal + Restated.liveAgainAfterHealing M S gap) ≤ tSafe)
    (htE : tE ≤ tAgain + tHeal)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hcvAgain : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tAgain)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hthird : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tAgain tSafe gap)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) :
    ∃ (B : NamedBlock V) (t : Int), t ≤ tSafe ∧
      (∀ (u : V) (i : Nat), (x[i].time : Int) ≤ tAgain →
        (x[i][u].st).st.core.h_max < (M.derive_named S.E S.cfg B).h) ∧
      (∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w → t ≤ (x[j].time : Int) →
        Block.Preceq B.erase (x[j][w].st).st.core.F) ∧
      Restated.blockInLog M S Sched x B := by
  have hb1 : (0 : Int) ≤ b₁ := le_trans S.E.t_GST_nonneg hg
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hperEq : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  have hη := Restated.healingLengthη_nonneg facts S gap
  have hlive := Restated.liveAgainAfterHealing_nonneg facts S gap
  have hgapI : (0 : Int) ≤ (gap : Int) := Int.natCast_nonneg gap
  have hgp : (0 : Int) ≤ (gap : Int) * (Restated.constants M S).period := mul_nonneg hgapI (le_of_lt hper)
  have hmulEq : ((gap : Int) + 2) * (Restated.constants M S).period =
      (gap : Int) * (Restated.constants M S).period + 2 * (Restated.constants M S).period := by ring
  have hlen : tAgain + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tAgain + tHeal := by
    linarith
  have hEL : tAgain + tHeal ≤ tSafe := by linarith
  have hliveE : tAgain + tHeal + Restated.liveAgainAfterHealing M S gap ≤ tSafe := by linarith
  have hgst' : b₁ ≤ tAgain := by linarith
  have hwin : tAgain + 8 * (S.hc.R : Int) * S.E.Δ ≤ tAgain + tHeal := by
    have h8 : 8 * (S.hc.R : Int) * S.E.Δ = 2 * (Restated.constants M S).period := by rw [hperEq]; ring
    linarith
  have hawakeE : ∀ t : Int, tAgain ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h1 h2 => hawake t h1 (by linarith)
  have hsl₂ := sleepinessW_of_later S Sched tAgain tE (tAgain + tHeal) hmono hawakeE hwin hsl
  have hrs₂ := Restated.roundSleepinessW_of_later facts S Sched tAgain tE (tAgain + tHeal) hmono hawakeE hwin hrs
  have hcs₂ := Restated.committeeSleepinessW_of_later facts S Sched tAgain tE (tAgain + tHeal) hmono hawakeE hcom
    hwin hcs
  have hs' := Restated.tr_SynchronyBy facts S b₁ hb1 Sched x (Restated.synchronyBy_of_outside facts S x hb hg hsync)
  have he' := Restated.tr_ExecutionValid facts S b₁ hb1 Sched x hexec
  have hcv' := Restated.tr_CommonViewOfFinalizedDescendantsAt facts S b₁ hb1 Sched x tAgain hcvAgain
  have htd' := Restated.tr_TimeDiverges facts S b₁ hb1 Sched x htd
  have hcom' := Restated.tr_HonestCommittees facts S b₁ hb1 Sched hcom
  have hrec' := Restated.tr_strongOpenings facts S b₁ hb1 Sched tAgain tSafe gap hrec
  have hslp' := Restated.tr_sleepiness facts S b₁ hb1 Sched (tAgain + tHeal) ⟨hsl₂, hrs₂, hcs₂⟩
  have hc' := Restated.tr_CatchUpBy facts S b₁ hb1 Sched x (Restated.catchUpBy_of_outside facts S x hb hg hcatch)
  have hlenT := (Restated.tr_length facts S b₁ hb1 gap tAgain (tAgain + tHeal) ⟨hlen, hgap⟩).1
  have hrecvAll' := fun (r' : Round) (hr' : Restated.switchRound M (setupWithGST S b₁ hb1) (tAgain + tHeal) ≤ r') =>
    Restated.nextRoundReceipts_of_catchUp facts (setupWithGST S b₁ hb1) Sched
      (Restated.toGST M S b₁ hb1 (Restated.protocol_setupWithGST facts S b₁ hb1) x) hs' hc'
      (Restated.gst_le_action_of_switchRound_le facts (setupWithGST S b₁ hb1) tAgain (tAgain + tHeal) gap hgst'
        (Restated.healingLength_le_of_kit_l76 facts (setupWithGST S b₁ hb1) hlenT) hr')
  obtain ⟨B, t, ht, hseen, hfin, hlog⟩ := Restated.finalizedAboveSeen_ofPhase_inLog (hrecvAll := hrecvAll') facts (setupWithGST S b₁ hb1)
    Sched (Restated.toGST M S b₁ hb1 (Restated.protocol_setupWithGST facts S b₁ hb1) x) tAgain (tAgain + tHeal) tSafe gap hgap (Restated.tr_length facts S b₁ hb1 gap tAgain (tAgain + tHeal) ⟨hlen, hgap⟩).1 hEL hgst' hmono he' hs'
    hmult hcv' htd' hcom' hthird hawake hrec' hslp'.1 hslp'.2.1 hslp'.2.2 hliveE
  refine ⟨B, t, ht, fun u i hi => ?_, fun w j hw htj => ?_,
    Restated.tr_back_blockInLog facts S b₁ hb1 Sched x B hlog⟩
  · have h := hseen u i hi
    have e : M.derive_named (setupWithGST S b₁ hb1).E (setupWithGST S b₁ hb1).cfg B =
        M.derive_named S.E S.cfg B := facts.csAdded.derive_named_setupWithGST S b₁ hb1 B
    rw [e] at h
    exact h
  · exact Restated.tr_back_Preceq_F facts S b₁ hb1 Sched x j w B.erase
      (hfin w j (Restated.tr_HonestThrough facts S b₁ hb1 Sched x j w hw) htj)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Let `B` be a named block in play that is an ancestor of every honest finalized block from a time
    `t ≤ tSafe` on, let every honest finalized block from `t` to `tSafe` be an ancestor or a
    descendant of `P`, and let some store, honest through its step, hold a body that has `P` as an
    ancestor while its running maximum height was less than `B`'s chain-state height. Then `P` is an
    ancestor of every honest validator's stable output at every step from `t` on. -/
theorem stablePersists_afterSafe (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tSafe t : Int) (P : Block V)
    (B : NamedBlock V) (ht : t ≤ tSafe) (htSafe : 0 ≤ tSafe)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hBlog : Restated.blockInLog M S Sched x B)
    (hfin : ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w → t ≤ (x[j].time : Int) →
      Block.Preceq B.erase (x[j][w].st).st.core.F)
    (hroots : ∀ (k : Nat), t ≤ (x[k].time : Int) → (x[k].time : Int) ≤ tSafe →
      ∀ w : V, Restated.HonestThrough M Sched x k w → Block.Compatible P (x[k][w].st).st.core.F)
    (hseen : ∃ (u : V) (i : Nat) (C : NamedBlock V), Restated.HonestThrough M Sched x i u ∧
      C ∈ (x[i][u].st).st.bodies ∧ Block.Preceq P C.erase ∧
      (x[i][u].st).st.core.h_max < (M.derive_named S.E S.cfg B).h) :
    ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w → t ≤ (x[j].time : Int) →
      Block.Preceq P (M.get_stable (x[j][w].st).st.core) := by
  -- Step 1: `B.erase ⪯ P` is impossible.
  have hnot : ¬ Block.Preceq B.erase P := by
    intro hBP
    obtain ⟨u, i, C, hu, hC, hPC, hlt⟩ := hseen
    have hBC : Block.Preceq B.erase C.erase := preceq_trans_Preceq hBP hPC
    have hnamed : NamedBlock.Preceq B C :=
      Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hBlog
        (Restated.blockInLog_of_mem_bodies facts S Sched hu hC) hBC
    have hmono := facts.cs.derive_height_mono S.E S.cfg hnamed
    have hcap := Restated.heights_le_hMax_sts facts S Sched x i u C hC
    exact absurd (lt_of_lt_of_le hlt (hmono.trans hcap)) (lt_irrefl _)
  -- Step 2: the validator `w` at step `j`.
  intro w j hw htj
  obtain ⟨j₀, hj₀j, htj₀, hj₀S⟩ : ∃ j₀ : Nat, j₀ ≤ j ∧ t ≤ (x[j₀].time : Int) ∧
      (x[j₀].time : Int) ≤ tSafe := by
    by_cases hj : (x[j].time : Int) ≤ tSafe
    · exact ⟨j, le_rfl, htj, hj⟩
    · obtain ⟨j₀, hj₀, hj₀t⟩ := Restated.exists_step_at_time facts S Sched x j (d := tSafe.toNat) (by omega)
      exact ⟨j₀, hj₀, by omega, by omega⟩
  have hw₀ : Restated.HonestThrough M Sched x j₀ w := fun t' ht' =>
    hw t' (ht'.trans (by exact_mod_cast Restated.time_mono facts S Sched x hj₀j))
  have hBF := hfin w j₀ hw₀ htj₀
  have hcomp := hroots j₀ htj₀ hj₀S w hw₀
  have hPF : Block.Preceq P (x[j₀][w].st).st.core.F := by
    rcases compatible_cases (compatible_iff_Compatible.mp hcomp) with h | h
    · exact h
    · exact absurd (preceq_trans_Preceq hBF h) hnot
  exact preceq_trans_Preceq (preceq_trans_Preceq hPF (Restated.F_mono facts S Sched x w hj₀j))
    (facts.hd.finalized_preceq_get_stable _)

end

end DecoupledConsensusModel.Sts.Restated
