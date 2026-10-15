import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceWUpTo
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_JointBase
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitStore
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13beKitActiveSince
import Proofs.Claims.Restated.Claim13beKitActiveSinceUpTo
import Proofs.Claims.Restated.Claim13beRoute3_15
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_74
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_79
import Proofs.Claims.Restated.Claim13beRoute3_80
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_83UpTo
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86eUpTo
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_88UpTo
import Proofs.Claims.Restated.ClaimAsyncK_DeliveryUpTo
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_81
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
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
import Proofs.Claims.Restated.Claim13bK_GradeOld

/-!
# The joint invariant at the switch round, with synchrony up to a bound

The clauses `prevHeads`, `prevConfirmed` and `gradedUnderPrevSG` of the joint invariant at the
switch round, and the joint invariant there, with synchrony assumed only up to a bound, stated over
a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pKS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bStepKitStore)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p78% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_78)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pKAS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beKitActiveSince)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pJB% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_JointBase)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))


section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The clause `prevHeads` of the joint invariant at the switch round: if `n_prev` is the tick step
    at `S.a (rW − 1)`, then for every member `v_1` of `HonRound S Sched (rW − 1)` and every block
    `C` its store holds that its round-`(rW − 1)` attestation in the sent log right after `n_prev`
    names as confirmed, every honest active member of the committee of the switch round's opening
    slot votes there for a descendant of `C`; synchrony is assumed up to the phase end `tE` only. -/
theorem prevHeads_at_switchRound_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {n_prev : Nat} (hn_prev : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1)))) :
    ∀ v_1 ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE - 1), ∀ a : NamedAttestation V,
      a.round = Restated.switchRound M S tE - 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
  intro v_1 hv_1 a ha hav hsent C hC hconf
  obtain ⟨v, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  have hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched (Restated.runAll M S Sched x v 0) hgst hlen hrec).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v 0) hgst hlen)
  obtain ⟨c, hcW, hc, -, hr1⟩ := nat_round_split_l88 _ _ hr
  obtain ⟨N, hN, hNE, -, hrWN, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    (Restated.runAll M S Sched x v 0) hgst hlen htd
  obtain ⟨hnp1, -⟩ := Restated.tickStepAt_time facts x hn_prev
  have hprevlt : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1)) < (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) :=
    (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S) (pred_lt_of_two_le_jb _ _ hr)
  have hnpN : n_prev + 1 ≤ N := by
    by_contra hcon
    have hle := Restated.time_mono_int facts S Sched x (show N ≤ n_prev + 1 by omega)
    linarith
  have hv_1A : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) := (Finset.mem_sdiff.1 hv_1).2
  have hCeq := Restated.erase_eq_actionSGBlockAt_runAll_atRound facts S Sched x v hmono hexec hn_prev
    hnpN hv_1A ha hav hsent hC hconf
  intro w m hw hm H hH
  obtain ⟨hm1, -⟩ := Restated.tickStepAt_time facts x hm
  have hvc : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) + S.E.Δ ≤
      (x[N].time : Int) := by
    rw [hN]
    exact (facts.sch.vote_time_add_delta_le_confirmation_time S _).trans
      (facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2))
  have hmN : m + 1 ≤ N := by
    by_contra hcon
    have hle := Restated.time_mono_int facts S Sched x (show N ≤ m + 1 by omega)
    have hd := S.E.Δ_pos
    linarith
  have hwN : w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
    notHeldAt_anti hmono (facts.sch.Sts_vote_time_le_confirmation_time S _)
      (mem_notHeldAt.mpr ((Restated.mem_HonSlot facts).mp hw).2.2)
  rw [← Restated.stateBeforeTime_runAll_tick facts S Sched x v hm hmN w] at hH
  obtain ⟨cc, hcc, n, rfl, Tr, hTr, L, hL, L', hL', hHd⟩ :=
    ((p73% gfHeadFrom_returns_iff₇₃) facts S _ _ H).1 hH
  have e : Restated.switchRound M S tE - 1 = c + 1 := by rw [hcW]; exact hr1
  rw [e] at hCeq hv_1A
  have hv_1c : v_1 ∈ notHeldAt Sched
      ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c + 1))) :=
    mem_notHeldAt.mpr hv_1A
  have hd : (M.opening_slot S.hc (c + 1)) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) := by
    rw [hcW]
    exact facts.gr.opening_slot_succ_lt_l88 S c
  have hbound := Restated.actionSGBlock_preceq_voterHeadAt_runAll_notHeld_upTo facts S Sched x v N
    (Restated.SynchronyFromWakeBefore.mono hNE hsync) hmono hawake hgst hcv hexec hmult hthird hNE hcom hrec hc hd hvc hv_1c hwN
  obtain ⟨nu, hnu, A2, hA2, G, hG⟩ := (pJB% exists_actionSG_jb) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v_1) (c + 1)
  rw [hCeq nu hnu A2 hA2 G hG]
  exact hbound cc hcc Tr hTr L hL L' hL' H hHd nu hnu A2 hA2 G hG

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For a regime at `R_N` over the validators not held whose source round is at or before the switch
    round, with `S.a rW ≤ x[N].time ≤ tE`, some validator `w` not held at the vote instant of
    `o_rW + 1` is such that every head its vote read at that slot can compute, staged from the path
    of `R_N` that `x` follows, is a descendant of the regime's checkpoint `T` and of every block the
    SG vote selector can return at a round-`(rW − 1)` action read of a validator not held at
    `S.a (rW − 1)`; synchrony is assumed up to `x[N].time` only. -/
theorem anchor_and_prevSG_under_head_jb_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {N : Nat} (hsync : Restated.SynchronyFromWakeBefore M S x (x[N].time : Int)) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tE)
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v N
    let d : Slot := (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1
    ∃ w ∈ notHeldAt Sched (M.vote_time S.E d),
      ∀ cc : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex R (M.vote_time S.E d)) w).st.core.toHealing
          (M.vote_time S.E d)
          (W (strictEventIndex R (M.vote_time S.E d)) w).cache ⇢ cc →
        let nw := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex R (M.vote_time S.E d)) w).st (M.vote_time S.E d))
          (W (strictEventIndex R (M.vote_time S.E d)) w).record cc
        ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E nw.st.core nw.st.core.s ⇢ Tr →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore
            nw.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract nw.cache) S.E S.hc
            (M.toHealing nw.st.core) Tr L L' (nw.st.core.s - 1) ⇢ H →
          Block.Preceq T.erase H ∧
          ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))),
            ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
                (W (strictEventIndex R
                  (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
                (Restated.switchRound M S tE - 1),
            ∀ A2 : Option (Block V),
              M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
                (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
            ∀ G : Block V,
              M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
                (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
              Block.Preceq G H := by
  intro R W d
  have hd0 := S.E.Δ_pos
  have hvt1 : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) - S.E.Δ := by
    have h := Restated.vote_time_opening_slot_add facts S (Restated.switchRound M S tE) 1
    rw [h]; push_cast; ring
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hvt1]
    linarith
  have hvE : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) ≤ tE := by
    rw [hvt1]; linarith
  obtain ⟨w, hwA⟩ := exists_not_adv_l76 S Sched (hthird _ hvE)
  have hw : w ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) :=
    mem_notHeldAt.mpr hwA
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N hsync hmono hawake hgst hcv hexec
    hmult hthird hNhi
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hNhi
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 :=
    Nat.add_le_add_right (facts.gr.opening_slot_mono S harW) 1
  have hheads := hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo
    hhor hlo
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
      hNhi k hk u j hj)
  obtain ⟨v₀, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  have hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched (Restated.runAll M S Sched x v₀ 0) hgst hlen hrec).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen)
  obtain ⟨c, hcW, hc, -, hr1⟩ := nat_round_split_l88 _ _ hr
  have hd : (M.opening_slot S.hc (c + 1)) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 := by
    rw [hcW]
    exact (facts.gr.opening_slot_succ_lt_l88 S c).trans (Nat.le_succ _)
  have e : Restated.switchRound M S tE - 1 = c + 1 := by rw [hcW]; exact hr1
  refine ⟨w, hw, ?_⟩
  intro cc hcc nw Tr hTr L hL L' hL' H hH
  refine ⟨hheads w hw cc hcc Tr hTr L hL L' hL' H hH, ?_⟩
  rw [e]
  intro u hu nv hnv A2 hA2 G hG
  exact Restated.actionSGBlock_preceq_voterHeadAt_runAll_notHeld_upTo facts S Sched x v N hsync hmono
    hawake hgst hcv hexec hmult hthird hNhi hcom hrec hc hd hhor hu hw cc hcc Tr hTr L hL L' hL'
    H hH nv hnv A2 hA2 G hG

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The clause `prevConfirmed` of the joint invariant at the switch round: every round-`(rW − 1)` SG
    block of a member of `HonRound S Sched (rW − 1)` lies on one chain with the confirmed block of
    every honest active attester of the switch round at its round-`rW` action read; synchrony is
    assumed up to the phase end `tE` only. -/
theorem prevConfirmed_at_switchRound_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWakeBefore M S x tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_prev : Nat} (hn_prev : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
    {n_W : Nat} {T_W : NamedBlock V}
    (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n_W n_W T_W) :
    Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x (Restated.switchRound M S tE - 1) n_prev n_W := by
  have hnW := hinv.tick
  obtain ⟨v₀, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  have hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched (Restated.runAll M S Sched x v₀ 0) hgst hlen hrec).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen)
  obtain ⟨c, hcW, hc, -, hr1⟩ := nat_round_split_l88 _ _ hr
  have hsucc : Restated.switchRound M S tE - 1 + 1 = Restated.switchRound M S tE := (pred_facts_of_two_le_jb _ _ hr).2.1
  unfold Restated.ConfirmedCompatibleFreshSGOverHonRound
  rw [hsucc]
  intro q hq v_1 hv_1 a ha hav hsent C hC hconf hs hhs
  obtain ⟨nq, hnq, rfl⟩ := hhs
  beta_reduce
  rw [show (M.toHealing nq.st.core).live_confirmed = nq.st.core.live_confirmed from
    facts.sto.toHealing_live_confirmed nq.st.core]
  obtain ⟨v, N, n₀, blocked, first, i, a₀, ta, Cfg, Tprev, c0, hn₀, hNlo, hNhi, hreg, harW, -⟩ :=
    id hAW
  obtain rfl : n₀ = n_W := Restated.tickStepAt_unique facts x hn₀ hnW
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hcon
    have hle := Restated.time_mono_int facts S Sched x (show N ≤ n₀ by omega)
    linarith
  obtain ⟨hnp1, -⟩ := Restated.tickStepAt_time facts x hn_prev
  have hprevlt : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1)) < (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) :=
    (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S) (pred_lt_of_two_le_jb _ _ hr)
  have hnpN : n_prev + 1 ≤ N := by
    by_contra hcon
    have hle := Restated.time_mono_int facts S Sched x (show N ≤ n_prev + 1 by omega)
    linarith
  have hv_1A : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) := (Finset.mem_sdiff.1 hv_1).2
  have hCeq := Restated.erase_eq_actionSGBlockAt_runAll_atRound facts S Sched x v hmono hexec hn_prev
    hnpN hv_1A ha hav hsent hC hconf
  obtain ⟨nu, hnu, A2, hA2, G, hG⟩ := (pJB% exists_actionSG_jb) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) v_1)
    (Restated.switchRound M S tE - 1)
  rw [hCeq nu hnu A2 hA2 G hG]
  have hqA : q ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := (Finset.mem_sdiff.1 hq).2
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N q
  rw [← hread] at hnq
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hmemW := (p74% mem_stateBeforeTime_along₇₄) hsorted hP
    (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
  have e : Restated.switchRound M S tE - 1 = c + 1 := by rw [hcW]; exact hr1
  have hv_1c : v_1 ∈ notHeldAt Sched
      ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c + 1))) := by
    rw [mem_notHeldAt, ← e]; exact hv_1A
  have hnu' : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c + 1))) v_1) (c + 1) := by
    rw [← e]; exact hnu
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N (Restated.SynchronyFromWakeBefore.mono hNhi hsync) hmono hphase hgst hcv hexec
    hmult hthird hNhi
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hrW1 : 1 ≤ Restated.switchRound M S tE := (pred_facts_of_two_le_jb _ _ hr).2.2
  have hloW : tGAT + 1 ≤ M.opening S.E S.hc (Restated.switchRound M S tE - S.hc.η_SG) :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right harW _))
  obtain ⟨-, hpostVote, -, -⟩ := Restated.loBounds_l70 facts S (lt_of_lt_of_le Nat.zero_lt_one hrW1) hloW
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      q (Restated.switchRound M S tE) _ hmemW nq hnq with
    ⟨Lc, hgen, hLeq⟩ | ⟨Rt, hReq, hRlive⟩
  · -- a confirmation `Lc` of `o_rW`
    rw [← hLeq]
    have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) := by
      exact facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le Nat.zero_lt_one hrW1)
    have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
      rw [hSc]
      exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
    have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).horizon := by
      show _ ≤ (x[N].time : Int)
      rw [← hSc]
      exact hNlo
    obtain ⟨cq, hcq, stq, -, rfl⟩ := hnq
    rw [facts.nd.mkNode_cache] at hgen
    have hcq' : M.onPhaseTick S.E S.hc
        (Restated.runAllPath M S Sched x v N
          (strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) q).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
        (Restated.runAllPath M S Sched x v N
          (strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) q).cache ⇢ cq := hcq
    rw [hSc] at hcq' hgen
    have hwinW : tGAT + 1 ≤ M.early S.E S.hc
        (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc]
      have h0 := Restated.lo_le_early_g2_sub_delta_of_opening facts S
        (lt_of_lt_of_le Nat.zero_lt_one hrW1) hloW (le_refl _)
      have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (Restated.switchRound M S tE)
      have hΔ := S.E.Δ_pos
      linarith
    obtain ⟨y, hy, -, hLy⟩ :=
      Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn
        (hHs _ _ hcut (mem_notHeldAt.mpr hqA)) hoPos hpostVote hconfHor cq hcq' hgen
        (fun z _ hz j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
          (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz) hwinW)
    have hyVote : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
    have hd : (M.opening_slot S.hc (c + 1)) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) := by
      rw [hcW]
      exact facts.gr.opening_slot_succ_lt_l88 S c
    have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) + S.E.Δ ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).horizon :=
      (facts.sch.vote_time_add_delta_le_confirmation_time S _).trans hconfHor
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
      ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    have hLH : Block.Preceq Lc H := hLy cc hcc Tr hTr L hL L' hL' H hH
    have hb : Block.Preceq G H :=
      Restated.actionSGBlock_preceq_voterHeadAt_runAll_notHeld_upTo facts S Sched x v N
        (Restated.SynchronyFromWakeBefore.mono hNhi hsync) hmono hphase hgst hcv hexec hmult hthird hNhi hcom hrec hc hd hhor hv_1c hyVote cc hcc Tr hTr L hL L' hL'
        H hH nu hnu' A2 hA2 G hG
    exact Block.compatible_of_preceq_common (preceq_eq_true_iff_Preceq.mpr hb)
      (preceq_eq_true_iff_Preceq.mpr hLH)
  · -- the FG root
    rw [← hRlive]
    have hfg1 := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_openingConfStore facts
      (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      q (Restated.switchRound M S tE) _ hmemW nq hnq
    have hfg2 := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts
      (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      q (Restated.switchRound M S tE) _ hmemW nq hnq
    have hqn : Restated.HonestThrough M Sched x n₀ q := by
      intro t' ht' hmem'
      exact hqA (hmono t' _ (by linarith) hmem')
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
    have hRT : Block.Preceq Rt T_W.erase := by
      rw [hReq, ← hfg1, hfg2, hread, Restated.get_fg_root_eq_ite_l78 facts]
      split
      · exact Restated.justified_preceq_anchor_after_switchW_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst
          hlen hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB'
          hAW hn₀ le_rfl hinv (Proofs.ModelProperties.Preceq_self _) hn' q n₀ le_rfl
          ((Nat.le_succ n₀).trans (Nat.succ_le_succ
            (Restated.tick_le_of_round_le facts S Sched x hn₀ hn' (Nat.le_succ _)))) hqn
      · exact hinv.fin q n₀ (Nat.le_succ _) hqn
    obtain ⟨y, -, hy⟩ := Restated.anchor_and_prevSG_under_head_jb_upTo facts S Sched x v hlen hgst hmono hexec
      (Restated.SynchronyFromWakeBefore.mono hNhi hsync) hmult hcv hcom hthird hphase hrec hNlo hNhi hreg harW
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts S
      (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) y)
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
    obtain ⟨hTy, hSGy⟩ := hy cc hcc Tr hTr L hL L' hL' H hH
    exact Block.compatible_of_preceq_common
      (preceq_eq_true_iff_Preceq.mpr (hSGy v_1 (mem_notHeldAt.mpr hv_1A) nu hnu A2 hA2 G hG))
      (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hRT hTy))

end

-- Folded in from the former module `Claim13bK_JointBaseUpToNotHeld.lean` (wake switch, lane S).
/-!
# The gradedUnderPrevSG clause at the switch round, for every validator not held at the domain instant, with synchrony up to a cutoff

`gradedUnderPrevSG_at_switchRound_upTo` of `Claim13bK_JointBaseUpTo.lean` with the honest active attesters of
the switch round replaced by every validator the adversary does not hold at the domain instant of
the grade read: the proof never used the reader's awake window.
-/



section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The clause `gradedUnderPrevSG` of the joint invariant at the switch round: every block that a
    validator not held at the domain instant of the grade read can grade at least 1 for the switch
    round is an ancestor of
    the block that the round-`(rW − 1)` attestation of some member of `HonRound S Sched (rW − 1)`,
    in the sent log right after `n_prev`, names as confirmed; synchrony is assumed up to the phase
    end `tE` only. -/
theorem gradedUnderPrevSG_at_switchRound_upTo_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (htd : Restated.TimeDiverges M x)
    {n_prev : Nat} (hn_prev : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
    {n_W : Nat} {T_W : NamedBlock V}
    (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n_W n_W T_W) :
    ∀ v : V, ∀ p : Protocol.Phase,
      M.domain S.E S.hc (Restated.switchRound M S tE) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) →
      v ∉ Sched.adv (M.domain S.E S.hc (Restated.switchRound M S tE) p) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (Restated.switchRound M S tE) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (Restated.switchRound M S tE)
          (M.early S.E S.hc (Restated.switchRound M S tE) p)
          (M.late S.E S.hc (Restated.switchRound M S tE) p) B ⇢ true →
      ∃ v_1 ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE - 1), ∃ a : NamedAttestation V,
        a.round = Restated.switchRound M S tE - 1 ∧ a.val_index = v_1 ∧
        (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent ∧
        ∃ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
          Block.Preceq B C.erase := by
  intro w p hdom hw m hm B hB
  obtain ⟨v, N, n₀, blocked, first, i, a, ta, Cfg, Tprev, c0, hn₀, hNlo, hNhi, hreg, harW, -⟩ :=
    hAW
  have hnW := hinv.tick
  obtain rfl : n₀ = n_W := Restated.tickStepAt_unique facts x hn₀ hnW
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hcon
    have hle := Restated.time_mono_int facts S Sched x (show N ≤ n₀ by omega)
    linarith
  obtain ⟨v₀, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  have hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched (Restated.runAll M S Sched x v₀ 0) hgst hlen hrec).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen)
  have hrW1 : 1 ≤ Restated.switchRound M S tE := (pred_facts_of_two_le_jb _ _ hr).2.2
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N (Restated.SynchronyFromWakeBefore.mono hNhi hsync) hmono hawake hgst hcv hexec
    hmult hthird hNhi
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hNhi
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hloW : tGAT + 1 ≤ M.opening S.E S.hc (Restated.switchRound M S tE - S.hc.η_SG) :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right harW _))
  obtain ⟨-, -, hpost, -⟩ := Restated.loBounds_l70 facts S (lt_of_lt_of_le Nat.zero_lt_one hrW1) hloW
  have hmn₀ : m ≤ n₀ := by
    by_contra hcon
    have hlt := hm.1 n₀ (Nat.lt_of_not_le hcon)
    linarith
  have hmN : m + 1 ≤ N := (Nat.succ_le_succ hmn₀).trans hn₀N
  have hread := Restated.stateBeforeTime_runAll_stepBefore facts S Sched x v hm hmN w
  have hmtime : (x[m].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    have hle := Restated.time_mono_int facts S Sched x hmn₀
    linarith
  have hthr : Restated.HonestThrough M Sched x m w := by
    intro t' ht' hmem'
    have hm' : Restated.stepBeforeInstant M x m
        (M.domain S.E S.hc ((Restated.switchRound M S tE - 1) + 1) p) := by
      rwa [Nat.sub_add_cancel hrW1]
    have hmd := Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm'
    rw [Nat.sub_add_cancel hrW1] at hmd
    exact hw (hmono t' _ (ht'.trans (le_of_lt hmd)) hmem')
  have hwdom : w ∈ notHeldAt Sched (M.domain S.E S.hc (Restated.switchRound M S tE) p) :=
    mem_notHeldAt.mpr hw
  have hdomainHor : M.domain S.E S.hc (Restated.switchRound M S tE) p ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    exact hdom.trans hNlo
  have hFT : Block.Preceq
      (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) w).st.core.F T_W.erase := by
    rw [hread]
    exact hinv.fin w m (hmn₀.trans (Nat.le_succ _)) hthr
  have hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) w).st.core))
      (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) w).st.core.F
      S.hc.η_SG (Restated.switchRound M S tE) (M.early S.E S.hc (Restated.switchRound M S tE) p)
        (M.late S.E S.hc (Restated.switchRound M S tE) p) B ⇢ true := by
    rw [hread]
    exact hB
  obtain ⟨y, -, hy⟩ := Restated.anchor_and_prevSG_under_head_jb_upTo facts S Sched x v hlen hgst hmono hexec
    (Restated.SynchronyFromWakeBefore.mono hNhi hsync) hmult hcv hcom hthird hawake hrec hNlo hNhi hreg harW
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts S
    (Restated.runAllPath M S Sched x v N
      (strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) y)
    ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
  obtain ⟨hTy, hSGy⟩ := hy cc hcc Tr hTr L hL L' hL' H hH
  have hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) (Restated.switchRound M S tE - 1) T_W.erase := by
    intro u hu nu hnu D hD _ gc st k A2 hA2 G hG
    exact compatible_of_preceq_common_Preceq (hSGy u hu nu hnu A2 hA2 G hG) hTy
  have hkPrev : tGAT + 1 ≤ M.early S.E S.hc (Restated.switchRound M S tE - 1) .g2 - S.E.Δ := by
    have hr0 := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    have hη := S.hc.η_SG_ge_one
    have h1 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤
        (Restated.roundAt M S tGAT : Nat) + S.hc.η_SG + 2 :=
      Nat.add_le_add_right (Nat.add_le_add_left hη _) 2
    have h2 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤ (Restated.switchRound M S tE : Nat) :=
      h1.trans (hr0.trans harW)
    have hA1 : tGAT + 1 ≤
        Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
      Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
        (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
    exact Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hA1
      (Restated.lt_pred_of_add_two_le_l54 h2)
  obtain ⟨u, hu, hall⟩ := Restated.phaseGrade_preceq_previousSGBlock_l80 facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hrW1 hpost hdomainHor hwdom hFT hsg hgrade
    (fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
      hNhi (Restated.switchRound M S tE - 1) hkPrev u j hj)
  obtain ⟨nu, hnu, A2, hA2, G, hG⟩ := (pJB% exists_actionSG_jb) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE - 1))) u)
    (Restated.switchRound M S tE - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nu.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node u) nu.st nu.record
  obtain ⟨hemit, hBu⟩ := hall nu hnu D hD
  have hBG : Block.Preceq B G := hBu A2 hA2 G hG
  have hrD1 : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE - 1 :=
    (pred_facts_of_two_le_jb _ _ hr).1
  obtain ⟨hwin, hwinE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen hrD1 (Nat.sub_le _ 1)
  have huA : u ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) := mem_notHeldAt.mp hu
  have huR : u ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE - 1) :=
    Restated.nonAdv_mem_honRound facts S Sched tGAT tE _ hmono hawake hwin hwinE huA
  obtain ⟨k, hkN, hk, hksent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hemit
  have hkp : k = n_prev := Restated.tickStepAt_unique facts x hk hn_prev
  rw [hkp] at hksent
  have hnpN : n_prev + 1 ≤ N := by rw [← hkp]; exact Nat.succ_le_of_lt hkN
  have hreadP := Restated.stateBeforeTime_runAll_tick facts S Sched x v hn_prev hnpN u
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hmemW := (p74% mem_stateBeforeTime_along₇₄) hsorted hP
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE - 1))
  obtain ⟨hDval, hDround, hDconf⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      u (Restated.switchRound M S tE - 1) nu ⟨_, hmemW, hnu⟩ D hD A2 hA2 G hG
  have hmemT := Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts
    (Setup.alwaysAwake S) _ u (Restated.switchRound M S tE - 1) _ hmemW nu hnu A2 hA2 G hG
  have hmemT' : G ∈ (x[n_prev][u].st).st.core.T := by
    rw [← hreadP]
    exact hmemT
  obtain ⟨Cn, hCnMem, hCnErase⟩ := Restated.exists_named_of_mem_tree facts S Sched x n_prev u hmemT'
  refine ⟨u, huR, D.2.2, hDround, hDval, hksent, Cn,
    Restated.bodies_mono_sts_jb facts S Sched x u (Nat.le_succ n_prev) hCnMem, ?_, ?_⟩
  · rw [hDconf, ← hCnErase, Proofs.NamedWire.erase_root Cn]
  · rw [hCnErase]
    exact hBG

end


section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `T_W` is a switch-round anchor and the invariant with the target clause since the switch
    round holds at the switch round with tick step `n_W`, switch step `n_W` and anchor `T_W`, then
    the joint invariant holds there with the same steps and anchor; synchrony is assumed up to the
    phase end `tE` only. -/
theorem afterPhaseInvariantOverActiveSetsJoint_at_switchRound_of_since_upTo (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWakeBefore M S x tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} {T_W : NamedBlock V}
    (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n_W n_W T_W) :
    Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T_W := by
  obtain ⟨n_prev, hn_prev⟩ := Restated.exists_tickStepAt facts x htd
    (Restated.action_pos facts S (Restated.switchRound M S tE - 1))
  have hG := Restated.gradedUnderPrevSG_at_switchRound_upTo_notHeld facts S Sched x tGAT tE gap hlen hgst hmono hexec
    hsync hmult hcv hcom hthird hphase hrec htd hn_prev hAW hinv
  exact (pJB% joint_of_prevTick_jointBase) facts hinv hn_prev
    (Restated.prevHeads_at_switchRound_upTo facts S Sched x tGAT tE gap hlen hgst hmono hexec hsync hmult hcv
      htd hcom hthird hphase hrec hn_prev)
    (Restated.prevConfirmed_at_switchRound_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
      hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hn_prev hAW hinv)
    (fun w hw p hp m hm B b hb hbt => hG w p hp (fun h => (Finset.mem_sdiff.1 hw).2 (hmono _ _ hp h)) m hm B
      (hbt ▸ hb))
    (fun w hw m hm B b hb hbt => hG w .g1 (facts.gr.domain_le_action S _ .g1) (Finset.mem_sdiff.1 hw).2 m hm B
      (hbt ▸ hb))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- There are a step `n_W` that is the tick step at the switch round's action instant and a
    switch-round anchor `T_W` at which the joint invariant holds at the switch round with tick step
    `n_W` and switch step `n_W`; synchrony is assumed up to the phase end `tE` only. -/
theorem afterPhaseInvariantOverActiveSetsJoint_at_switchRound_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmult : AwakeAtMultiples S Sched)
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
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) :
    ∃ (n_W : Nat) (T_W : NamedBlock V), Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) ∧
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W ∧
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T_W := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  obtain ⟨v₀, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  have hcE : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) ≤ tE := by
    obtain ⟨Ns, hNs, hNsE, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
      (Restated.runAll M S Sched x v₀ 0) hgst hlen' htd
    rw [← hNs]; exact hNsE
  have hrDW' : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hclearW : ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (x[N].time : Int)
        = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = Restated.switchRound M S tE →
      Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      Restated.BaseClearFGSourceCompatibleWithAnchor M S Sched x tE n₀ T := by
    intro v N blocked first i a ta Cfg T Tprev c0 n₀ hN hreg heq hn₀
    obtain ⟨N', hN', hN'E, -, hrWN', -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
      (Restated.runAll M S Sched x v 0) hgst hlen' htd
    have hNeq : (x[N].time : Int) = (x[N'].time : Int) := hN.trans hN'.symm
    rw [Restated.baseClearFGSource_atRound_switchRound facts]
    exact hclear (Restated.switchRound M S tE) hrDW' le_rfl v N blocked first i a ta Cfg T Tprev c0 n₀
      (by rw [hNeq]; exact hrWN') (by rw [hNeq]; exact hN'E) hreg heq hn₀
  obtain ⟨n_W, T_W, hnW, hAW, hinv⟩ :=
    Restated.claim13beBaseOverActiveSetsSince_anchored_of_premises_upTo facts S Sched x tGAT tE gap hgap hlen hgst
      hmono hexec (Restated.SynchronyFromWakeBefore.mono hcE hsync) hmult hcv htd hcom hthird hawake hrec hsl hrs hcs
      (Restated.basePreviousRoundSGBelowOpeningVotes_atSwitch_upTo facts S Sched x tGAT tE gap hlen hgst hmono
        hexec (Restated.SynchronyFromWakeBefore.mono hcE hsync) hmult hcv htd hcom hthird hawake hrec)
      hclearW
  exact ⟨n_W, T_W, hnW, hAW,
    Restated.afterPhaseInvariantOverActiveSetsJoint_at_switchRound_of_since_upTo facts S Sched x tE hexec hmono
      htd tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcom hrec hprev hclear hB' hAW hinv⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `T_W` is a switch-round anchor, `n_W` the switch round's tick step, and every validator
    honest through a step from one before the vote instant of `o_rW + 1` up to `n_W` holds there a
    justified height at least that of every round-`rD'` anchor (`hlow`), then at every such step the
    justified block of a validator honest through it is an ancestor of `T_W`; synchrony is assumed
    up to the phase end `tE` only. -/
theorem justifiedAncestor_before_switchTick_of_justifiedHigh_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWakeBefore M S x tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hlow : ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j) :
    ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase := by
  classical
  intro v n₁ hlo₁ hn₁ hv
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  have hWn' : n_W ≤ n' := Restated.tick_le_of_round_le facts S Sched x hnW hn' (Nat.le_succ _)
  have hrsW' := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono
    hthird hphase hrsW
  have htE' := Restated.switchOpening_le_opening facts S (Nat.le_succ (Restated.switchRound M S tE))
  rcases Restated.justified_honest_vote_before_succ_tick facts S Sched x hexec hmono hrsW' hn' htE'
      ((hn₁.trans hWn').trans (Nat.le_succ _)) hv with
    hgen | ⟨Jn, v', a, k, hJnmem, hJne, -, hktick, hround, hqhon, hidx, hsent, hpair⟩
  · rw [hgen]
    exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)
  · rw [← hJne]
    have hJnlog : Restated.blockInLog M S Sched x Jn := Restated.blockInLog_of_mem_bodies facts S Sched hv hJnmem
    have hkW : k ≤ n_W := Restated.tick_le_of_round_le facts S Sched x hktick hnW hround
    have hqk : Restated.HonestThrough M Sched x (k + 1) v' := fun t ht =>
      hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_succ (hkW.trans hWn'))))
    have hrDW' : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
      Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v 0) hgst hlen
    obtain ⟨T_D', hAD'⟩ := Restated.exists_anchorAtRound_upTo facts S Sched x hsync hmono hphase hgst hcv hexec
      hmult hthird hcom hrec hlen htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW'
    exact Restated.honestVotes_onAnchorChain_since_roundW_upTo facts S Sched x hsync hmono hphase hgst hcv hexec
      hmult hthird hcom hrec hlen htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW' hprev
      hclear hAD' hAW hnW v' (k + 1) a _ Jn.root false (Nat.succ_le_succ hkW) hqk hidx hsent hpair
      (hlow T_D' hAD' v n₁ hlo₁ hn₁ hv) Jn hJnlog rfl

end

end DecoupledConsensusModel.Sts.Restated
