import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ProposalVotesDelivery
import Proofs.Claims.Restated.Claim13bK_ProposalVotesWalk
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedInclusion
import Model.Conditions.Claim13bK_ProposalVotesPivot
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
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
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Honest proposals are voted after the phase

`HonestProposalHeadsAtOwnSlot` from the opening slot of the round after the switch round on, from
the confirmation premises alone, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pSCap% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bStepCone)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83ap% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the joint invariant at the switch round, at every slot from the opening slot of the round
    after the switch round whose proposer is not held up to the slot's vote instant, every honest
    active member of the slot's committee votes for the block that proposer sent by that vote
    instant. -/
theorem honestProposalHeadsAtOwnSlot_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    (tHi : Int) :
    Restated.HonestProposalHeadsAtOwnSlot M S Sched x ((M.opening_slot S.hc (Restated.switchRound M S tE + 1))) tHi := by
  intro s i B hsl _ hprop hB hi v m hv hm G hG
  have hpi : HonestThroughTime Sched (x[i].time : Int) (S.E.proposer s) :=
    fun t ht => hprop t (le_trans ht hi)
  obtain ⟨k, -, hk, B', hBe, hemit, hduty⟩ :=
    Restated.sentProposal_duty facts S Sched x hexec.toUnforgeability hpi hB
  have hawp := Restated.sentProposal_awake facts S Sched x hexec.toUnforgeability hpi hB
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (x[k][S.E.proposer s].st).st.core.toHealing
    (M.proposal_time S.E s) (x[k][S.E.proposer s].st).cache
  have hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢
      M.mkNode (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s))
        (x[k][S.E.proposer s].st).record c := by
    unfold Restated.proposalReadOf
    exact (pSCap% returns_map_intro_cone) _ _ c hc
  obtain ⟨D, hD⟩ : ∃ D : M.NS × Option (NamedBlock V), M.duties_propose_block_with
      (M.gradeContract (M.mkNode (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s))
        (x[k][S.E.proposer s].st).record c).cache) S.E S.hc S.cfg
      ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D := by
    obtain ⟨out₀, hout₀, hmem₀⟩ := id hemit
    have _hr_w := Record.reachedNode_wakeStage facts S Sched x k (S.E.proposer s) (M.proposal_time S.E s)
    have _hv_w := Record.runs_as_wakeStage facts S Sched x k (S.E.proposer s) (M.proposal_time S.E s)
    have hbm := facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) (S.E.proposer s) _
      (M.proposal_time S.E s) out₀ hout₀ hmem₀
    obtain ⟨D₀, hD₀⟩ := facts.dt.propose_block_with_nonempty (Setup.alwaysAwake S) (S.E.proposer s) _
      (M.proposal_time S.E s) out₀ hout₀ hbm.1.1 hbm.1.2.1 hbm.1.2.2
      (facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) (S.E.proposer s) _
        (M.proposal_time S.E s) out₀ hout₀ hmem₀) c
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc)
    rw [Record.wakeStage_st facts, ← facts.nd.gradeContract_eq_frameContract] at hD₀
    exact ⟨D₀, by rw [facts.nd.mkNode_cache]; exact hD₀⟩
  rw [Restated.voterHead_eq_proposal_afterPhase facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch hTW₀
    hJ₀ hsl hprop hawp hk hemit hn hD (hduty _ hn D hD) hv hm G hG, hBe]
  exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self B)

end

end DecoupledConsensusModel.Sts.Restated
