import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The previous round's SG blocks and the opening's parent

In the run of the first `n` steps of an execution `x`, after the progress deadline, every SG block
of the round before an opening is an ancestor of the opening proposal's parent, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_64b` by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_58` by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_71` by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- In the run `R` of the first `n` steps of the execution `x`, along the path
    `W = Restated.runAllPath M S Sched x v n`, for a round `q` at least two rounds after the
    progress deadline whose opening slot's vote instant is at or before `x[n].time` and whose
    opening proposer is not held at its confirmation instant: every block the SG vote selector can
    return at a round-`(q − 1)` action read of a validator not held at `S.a (q − 1)` is an ancestor
    of the parent of every proposal input of the opening proposer's read. -/
theorem actionSGBlock_preceq_proposedParent_runAll_notHeld_afterDeadline (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {q : Round} (hq : Restated.deadlineRoundW M S tGAT gap + 2 ≤ q)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc q)) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc q)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q))) pn.st ⇢ some P →
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q - 1))),
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (W (strictEventIndex R
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q - 1))) u) (q - 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q)))
          (M.toHealing pn.st.core) ⇢ I →
        Block.Preceq G I.parent := by
  intro R W wp cp hcp pn hP u hu nv hnv A2 hA2 G hG I hI
  have hex : ∀ w : V, ∃ H : Block V, ∃ cw : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc q) - 1))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).cache ⇢ cw ∧
      let nw := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record cw
      ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E nw.st.core nw.st.core.s ⇢ T ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore
          nw.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract nw.cache) S.E S.hc
        (M.toHealing nw.st.core) T L L' (nw.st.core.s - 1) ⇢ H := by
    intro w
    obtain ⟨cw, hcw⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st.core.toHealing
      (M.vote_time S.E ((M.opening_slot S.hc q) - 1))
      (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).cache
    obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
      (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record cw).st.core
      (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record cw).st.core.s
    obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record
        cw).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record cw).st.core.s
    obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record
        cw).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record cw).st.core.s
    obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record cw).cache)
      S.E S.hc
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record cw).st.core)
      T L L'
      ((M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1)))
        (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc q) - 1))) w).record
        cw).st.core.s - 1)
    exact ⟨H, cw, hcw, T, hT, L, hL, L', hL', hH⟩
  choose head hheadAll using hex
  obtain ⟨E, -, -, -, hsg, hpar, -, -⟩ :=
    Restated.openingPivot_runAll_notHeld facts S Sched x v n hsync hmono hawake hgst hcv hvalid
      hawm hthird hn hcom hrec hq hvoteHor hopening cp hcp hP head (fun w _ => hheadAll w)
  exact preceq_trans_Preceq (hsg u hu nv hnv A2 hA2 G hG) (hpar I hI)

end

end DecoupledConsensusModel.Sts.Restated
