import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_FinalityDeadlineArith
import Proofs.Claims.Restated.Claim13bK_FinalityInclusion
import Proofs.Claims.Restated.Claim13bK_WindowProposalSent
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13beRoute3_85g
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Constants
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Finality grows

That no honest store finalizes a block of a slot before that slot's proposal time, and that, under
the phase premises, finalized blocks grow past a block proposed in every window, stated over a model
`M : Record.Model V`.
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
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Under the premises read for the run of the first steps, up to `tL`, with time diverging, for a
    slot `s > 0` whose proposal time is at or before `tL` and a block `B` that `s`'s proposer put in
    the sent log `x[k].sent` as its own block of slot `s`, at every step `i` whose time is strictly
    before `s`'s proposal time, `B` is not an ancestor of the finalized block of any validator `v`. -/
theorem not_preceq_finalized_before_proposal_f5 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) {tGAT tL : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (htd : Restated.TimeDiverges M x)
    {s : Slot} (hs : 0 < s) (hpt : M.proposal_time S.E s ≤ tL)
    {k : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x k s B)
    (v : V) {i : Nat} (hi : (x[i].time : Int) < M.proposal_time S.E s) :
    ¬ Block.Preceq B (x[i][v].st).st.core.F := by
  intro hpre
  have hpos : (0 : Int) < M.proposal_time S.E s :=
    lt_of_le_of_lt (Int.natCast_nonneg _) hi
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hm1, -⟩ := Restated.tickStepAt_time facts x hm
  have him : i ≤ m := by
    by_contra hcon
    have hle : (x[m + 1].time : Int) ≤ (x[i].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega : m + 1 ≤ i)
    omega
  have hBm : Block.Preceq B (x[m][v].st).st.core.F :=
    preceq_trans_Preceq hpre (Restated.F_mono facts S Sched x v him)
  have hn : (x[m + 1].time : Int) ≤ tL := by rw [hm1]; exact hpt
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv
    hvalid hawm hthird hn
  set rho : Record.Run V := { Restated.runAll M S Sched x v₀ (m + 1) with
    honest := notHeldAt Sched (x[m + 1].time : Int) } with hrho
  -- the world of the path the execution follows, before the events at `s`'s proposal instant
  have hst : Restated.runAllPath M S Sched x v₀ (m + 1)
      (strictEventIndex rho (M.proposal_time S.E s)) v = x[m][v].st :=
    Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hm (le_refl (m + 1)) v
  have hFT := Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBefore facts (Setup.alwaysAwake S) rho
    (strictEventIndex rho (M.proposal_time S.E s)) v _ (hf.onePath _).1
  have hFT' : (x[m][v].st).st.core.F ∈
      (Restated.runAllPath M S Sched x v₀ (m + 1)
        (strictEventIndex rho (M.proposal_time S.E s)) v).st.T := by
    rw [hst] at hFT ⊢; exact hFT
  have hBT := Restated.ancestor_mem_storeBeforeTimeOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hFT' hBm
  have hlt := Restated.block_slot_lt_of_mem_before_proposalOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hs hBT
  obtain ⟨B', -, hBe, hBs, -⟩ := hB
  rw [← hBe, Proofs.NamedWire.erase_slot, hBs] at hlt
  exact lt_irrefl _ hlt

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

/-- Under the phase premises with `gap + 2 ≤ K`, `tGAT + (healingLengthη S gap + period) ≤ tE` and
    `tE ≤ tL`: from every time `t` at or after the start with
    `t + (gap · period + finalityPremisesContinueDirect S gap) ≤ tL`, and every step `i` at `t`,
    there is a slot `s` proposed after `t` whose proposer is not held at any time up to its vote
    time, and a block `B` that proposer put in the sent log `x[k].sent` at a step `k` at or before
    that vote time, such that `B` is a strict descendant of the finalized block of every validator
    honest through step `i`, and an ancestor of the finalized block of every validator honest
    through any read at or after `t + finalityGrowthDelay S gap`. -/
theorem finalityGrows_of_premises_f5 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    Restated.FinalityGrowsAfterHealing M S Sched x tE tL gap := by
  intro t hstart htL i hit
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hstartup : (0 : Int) ≤ Restated.finalityStartupDirect M S gap :=
    mul_nonneg (Int.natCast_nonneg _) hper.le
  have hdl0 : (0 : Int) ≤ Restated.finalityDeadlineDirect M S gap := by
    have h : Restated.finalityDeadlineDirect M S gap =
        ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 : Nat) : Int) * (Restated.constants M S).period +
          9 * S.E.Δ := rfl
    rw [h]
    have := mul_nonneg (Int.natCast_nonneg (3 * gap + S.cfg.timeoutDelay / S.hc.R - 6)) hper.le
    linarith
  have hdlc := Restated.finalityDeadlineDirect_le_continue_f4 facts S gap
  have hgapP : (0 : Int) ≤ (gap : Int) * (Restated.constants M S).period :=
    mul_nonneg (Int.natCast_nonneg gap) hper.le
  have hheal := Restated.healingLengthη_nonneg facts S gap
  have hgrowth : Restated.finalityGrowthDelay M S gap =
      (gap : Int) * (Restated.constants M S).period + Restated.finalityDeadlineDirect M S gap := rfl
  have htE : tE ≤ t := by
    have h : Restated.finalityLiveStart M S tE gap = tE + Restated.finalityStartupDirect M S gap := rfl
    rw [h] at hstart
    linarith
  have hGt : tGAT ≤ t := by linarith
  have ht0 : (0 : Int) ≤ t := by rw [← hit]; exact Int.natCast_nonneg _
  -- the phase's premises at `tE`, read off the continued ones
  have hthirdE : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t ht => hthird t (ht.trans hEL)
  have hphaseE : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h1 h2 => hawake t h1 (h2.trans hEL)
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  -- the slot, from the recurrence at `t`
  obtain ⟨s, hs2, hsg, hmulti, -⟩ := hrec t hGt (by linarith)
  have hps2 : t + 2 * (Restated.constants M S).period ≤ M.proposal_time S.E s := hs2
  have hpsg : M.proposal_time S.E s ≤ t + (gap : Int) * (Restated.constants M S).period := hsg
  have hconf : HonestThroughTime Sched (M.confirmation_time S.E s) (S.E.proposer s) := by
    exact hmulti.2 0 (Restated.constants_holds facts S).proposerSlots_pos
  have hvote : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) :=
    fun t' ht' => hconf t' (ht'.trans (facts.sch.Sts_vote_time_le_confirmation_time S s))
  have hsE : tE ≤ M.proposal_time S.E s := by linarith
  have hpsL : M.proposal_time S.E s ≤ tL := by linarith
  have hcontS : M.proposal_time S.E s + Restated.finalityPremisesContinueDirect M S gap ≤ tL := by
    linarith
  -- the slot is after the opening slot of round `rD + 1`
  have hs0 := Restated.switchOpening_add_two_le_of_le_proposal_f3 facts S Sched hgst hlen' hrecE hsE
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrD : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  have hsW : (M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap + 1)) ≤ s :=
    (facts.gr.opening_slot_mono S
      (show Restated.deadlineRoundW M S tGAT gap + 1 ≤ Restated.switchRound M S tE from (Nat.le_succ _).trans hrD)).trans ((Nat.le_add_right _ 2).trans hs0)
  -- the proposer's block in the sent log, at the proposal instant
  have hpos : (0 : Int) < M.proposal_time S.E s := by linarith
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hm1, -⟩ := Restated.tickStepAt_time facts x hm
  -- one outcome of the proposer's cache update and one of its proposal duty, at the read of the
  -- proposal instant on the path the execution follows
  let R₁ : Record.Run V := { Restated.runAll M S Sched x (S.E.proposer s) (m + 1) with
    honest := notHeldAt Sched (x[m + 1].time : Int) }
  let wp := Restated.runAllPath M S Sched x (S.E.proposer s) (m + 1)
    (Restated.strictEventIndex R₁ (M.proposal_time S.E s)) (S.E.proposer s)
  obtain ⟨cp, hcp⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc wp.st.core.toHealing
    (M.proposal_time S.E s) wp.cache
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc ((Setup.alwaysAwake S).node (S.E.proposer s))
    (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) wp.record cp).st
  obtain ⟨P, -, -, ⟨k, hk, hkB⟩, -⟩ := Restated.windowSlotProposalSent_g1 facts S Sched x (S.E.proposer s)
    (m + 1) hsync hmono hawake hgst hcv hexec hmult hthird (by rw [hm1]; exact hpsL) hsW
    (le_of_eq hm1.symm) (mem_notHeldAt.mpr (hconf _ le_rfl)) cp hcp o ho
  have hki : (x[k].time : Int) ≤ M.vote_time S.E s := by
    rw [hk]; exact (facts.sch.proposal_time_lt_vote_time S.E s).le
  -- the inclusion of that block
  have hincl := Restated.finalizedAfterDeadline_of_premises_f3 facts S Sched x tGAT tE tL gap hgap hlen hEL hgst
    hmono hexec hsync hmult hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs hsE hcontS
    hvote hkB hki
  have hspos : 0 < s := (Restated.windowSlot_bounds_g1 facts S tGAT gap hsW).1
  refine ⟨s, k, P.erase, by linarith, hvote, hkB, hki, ?_, ?_⟩
  · -- strictness: comparability with a late honest reader, and no read before the proposal
    intro v hv
    have hgd : t + Restated.finalityGrowthDelay M S gap ≤ tL := by rw [hgrowth]; linarith
    have hTpos : (0 : Int) < t + Restated.finalityGrowthDelay M S gap := by rw [hgrowth]; linarith
    obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd hTpos
    obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn
    obtain ⟨v', hv'⟩ := exists_notHeld_f2c S Sched hthird hgd
    have hv'j : Restated.HonestThrough M Sched x (n + 1) v' := fun t' ht' =>
      mem_notHeldAt.mp (notHeldAt_anti hmono (by rw [hn1] at ht'; exact ht') hv')
    have hBj : Block.Preceq P.erase (x[n + 1][v'].st).st.core.F :=
      hincl v' (n + 1) hv'j (by rw [hn1, hgrowth]; linarith)
    have hlow := Restated.hlow_of_premises_l85f facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync
      hmult hwakes hsleeps hcv htd hcom hthirdE hphaseE hrecE hsl hrs hcs
    have hagree := Restated.claim13be_conclusion_of_joint_l85f facts S Sched x tGAT tE gap hgap hlen hgst hmono
      hexec hsync hmult hwakes hsleeps hcv htd hcom hthirdE hphaseE hrecE hsl hrs hcs hlow
      v' v (n + 1) i hv'j hv
    have hcomp : Block.Compatible (x[i][v].st).st.core.F P.erase :=
      compatible_iff_Compatible.mpr (Protocol.compatible_comm
        (Protocol.compatible_of_preceq_of_compatible hBj (compatible_iff_Compatible.mp hagree)))
    have hnot := Restated.not_preceq_finalized_before_proposal_f5 facts S Sched x (S.E.proposer s) hsync hmono
      hawake hgst hcv hexec hmult hthird htd hspos hpsL hkB v (i := i) (by rw [hit]; linarith)
    exact prec_of_compatible_of_not_preceq hcomp hnot
  · -- the last conjunct
    intro v j hv hj
    exact hincl v j hv (by rw [hgrowth] at hj; linarith)

end

end DecoupledConsensusModel.Sts.Restated
