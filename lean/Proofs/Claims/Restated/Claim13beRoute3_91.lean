import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_79
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryGenuineClearNextVote
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The clear FG source and the checkpoint

At every round from the deadline round to the switch round, an action FG source that is an ancestor
of the live confirmation is on one chain with the checkpoint of the regime of that round, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p69b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_69b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p70% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_70)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p78% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_78)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- At every round `r` from `Restated.deadlineRoundW M S tGAT gap` to `Restated.switchRound M S tE`,
    for a regime along the path of the first `N` steps of `x` with source round `r` and `n₀` the
    tick step at `S.a r`, `Restated.BaseClearFGSourceCompatibleWithAnchorAtRound` holds: every block
    an action FG source of round `r` can return, read from a node state after `n₀` steps, that is an
    ancestor of that read's live confirmation, is on one chain with the regime's checkpoint `T`. -/
theorem baseClearFGSource_atRound_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) :
    ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T := by
  intro r _hrD _hrW v N blocked first i a ta Cfg₀ T Tprev c0 n₀ hrN hn hreg harr hn₀ q hq n hnq Cfg
    hsrc hlc
  replace hlc : Block.Preceq Cfg n.st.core.live_confirmed := by
    rw [← facts.sto.toHealing_live_confirmed]
    exact hlc
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hlt
    have hmN := Restated.time_mono_int facts S Sched x (show N ≤ n₀ by omega)
    linarith
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hexec
    hmult hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨-, hloVote, hloPrevA, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hqA : q ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
    rw [mem_notHeldAt]
    exact (Finset.mem_sdiff.mp hq).2
  have hread : Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S r)) q = x[n₀][q].st :=
    Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N q
  have hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S r)) q) r := by
    rw [hread]
    exact hnq
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S r) = M.confirmation_time S.E ((M.opening_slot S.hc r)) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc r)) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [← hSc]
    exact hrN
  have hTCfg : Block.Preceq T.erase Cfg₀.erase := by
    rw [hreg.seed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg₀
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r)
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      q r _ hmemW n hnA with
    ⟨C, hgen, hCeq⟩ | ⟨Rt, hReq, hRlive⟩
  ·
    have hCfgC : Block.Preceq Cfg C := by rw [hCeq]; exact hlc
    have hoPos : 0 < (M.opening_slot S.hc r) := facts.gr.opening_slot_pos_of_round_pos S.hc (harr ▸ hapos)
    have hcut : M.support_cutoff S.E ((M.opening_slot S.hc r)) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
      rw [hSc]
      exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
    have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc r)) := by
      rw [← harr]
      exact hloVote
    have hmemWa := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)
    obtain ⟨na, hna⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)) a.val_index) a.round
    obtain ⟨oQ, hoQ⟩ := (p70% nodeQ2_nonempty₇₀w) facts (Setup.alwaysAwake S) na a.round
    obtain ⟨Q, hQeq⟩ := hreg.seed.exists_nodeQ2_l70 facts na hna oQ hoQ
    rw [hQeq] at hoQ
    obtain ⟨oB, hoB⟩ := (p63% actionFGSource_nonempty₆₃w) facts (Setup.alwaysAwake S) na
    rw [hreg.seed.exactFGSource na hna oB hoB] at hoB
    have hsplit := Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named facts
      (Setup.alwaysAwake S) _ a.val_index a.round _ hmemWa na hna hoQ hoB
    obtain ⟨c, hc, st, -, rfl⟩ := hnA
    rw [facts.nd.mkNode_cache] at hgen
    have hc' : M.onPhaseTick S.E S.hc
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S r)) q).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S r)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S r)) q).cache ⇢ c := hc
    replace hgen : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S r)) q).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))
        (M.opening_slot S.hc r) C := hgen
    rw [hSc] at hc' hgen
    have hwinR : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc r)) .g1 -
        S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc]
      have h0 := Restated.lo_le_early_g2_sub_delta_of_opening facts S hapos hlo harr.le
      have h1 := facts.gr.early_g2_add_delta_le_early_g1 S r
      have hΔ := S.E.Δ_pos
      linarith
    obtain ⟨y, hy, -, hCy⟩ :=
      Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hqA) hoPos hpostVote
        hconfHor c hc' hgen
        (fun z _ hz j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
          (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz) hwinR)
    have hyVote : y ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc r))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc r)))) y)
      ((M.opening_slot S.hc r))
    have hCH : Block.Preceq C H := hCy cc hcc Tr hTr L hL L' hL' H hH
    rcases hsplit with ⟨Ca, hCa, -, -, -, hCfgCa⟩ | hCfgQ
    ·
      have hsigner : a.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
        have h := hreg.seed.signerHonest
        rw [hreg.seed.actionTime_eq, harr] at h
        exact h
      have hpostProp : tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc r)) :=
        hloPrevA.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
            (by rw [← harr]; exact Nat.sub_lt hapos Nat.one_pos)))
      obtain ⟨ca, hca, sta, -, rfl⟩ := hna
      rw [facts.nd.mkNode_cache] at hCa
      have hca' : M.onPhaseTick S.E S.hc
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core.toHealing
          (Restated.Vocabulary.Execution.Setup.a M S a.round)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).cache ⇢ ca := hca
      have hCa' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract ca) S.E S.hc
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core
            (M.confirmation_time S.E (M.opening_slot S.hc a.round)))
          (M.opening_slot S.hc a.round) Ca := hCa
      rw [harr, hSc] at hca' hCa'
      have hcomp := Restated.sameSlot_genuine_compatible_after_gstOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hHs hHsXb
        (show q ∈ notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc r))) by
          rw [← hSc]; exact hqA)
        (show a.val_index ∈ notHeldAt Sched
            (M.confirmation_time S.E ((M.opening_slot S.hc r))) by
          rw [← hSc]; exact hsigner) hpostProp hconfHor c hc' hgen ca hca' hCa'
      have hTCa : Block.Preceq T.erase Ca := preceq_trans_Preceq hTCfg hCfgCa
      rcases compatible_cases hcomp with hCCa | hCaC
      · exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hCfgC hCCa) hTCa
      · exact compatible_of_preceq_common_Preceq hCfgC (preceq_trans_Preceq hTCa hCaC)
    ·
      rw [← hCfgQ] at hoQ
      have hyA : y ∈ notHeldAt Sched
          (M.vote_time S.E ((M.opening_slot S.hc a.round))) := by
        rw [harr]
        exact hyVote
      have hCfgy := hreg.seed.selectedSource_preceq_openingHead_of_namedFrame_history facts hf hHs
        hHsXb hX hXXb hreg.crossing hreg.frame hreg.ready hna hoQ hyA hlo
      rw [harr] at hCfgy
      have hCfgH : Block.Preceq Cfg₀.erase H := hCfgy cc hcc Tr hTr L hL L' hL' H hH
      exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hCfgC hCH)
        (preceq_trans_Preceq hTCfg hCfgH)
  ·
    have htk : Rt = M.get_fg_root (M.toHealing (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S r)) q).st.core).toFG := by
      rw [hReq]
      exact facts.fc.get_fg_root_set_clock_slot _ _ _
    have hlo' : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) ≤
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) := by
      rw [harr]
    have hhi : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) ≤
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (a.round + 1)) := by
      rw [harr]
      exact Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ _)
    have hRT : Block.Preceq Rt T.erase := by
      rw [htk]
      exact hreg.seed.fgRoot_preceq_before_nextAction_of_frame_run facts hf hHs hHsXb hX hXXb hcomOn
        hbelow hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev hreg.pred
        hreg.minimal hlo' hhi hqA hrN hlo
        (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
          hn k hk u j hj)
    rw [← hRlive] at hlc
    exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hlc hRT)
      (Proofs.ModelProperties.Preceq_self T.erase)

end

end DecoupledConsensusModel.Sts.Restated
