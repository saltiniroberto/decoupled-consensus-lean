import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
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
# The pivot of an opening with synchrony up to a step

The pivot of an opening after the progress deadline in the run of the first `n` steps of an
execution `x`, with synchrony assumed only up to `x[n].time`, over a model `M : Record.Model V`.
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
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_86c` by name. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- With synchrony only up to `x[n].time`, in the run `R` of the first `n` steps of the execution
    `x`, along the path `W = Restated.runAllPath M S Sched x v₀ n`, for a round `c` at least two
    rounds after the progress deadline whose opening proposer is not held at its confirmation
    instant: some run block `E` is the greatest common ancestor of the heads of the validators not
    held at the previous slot, every round-`(c − 1)` SG block of a validator not held is an ancestor
    of `E`, `E` is an ancestor of the parent of every proposal input, the proposer's anchor is an
    ancestor of `E`, and `E`'s stored height is at least the proposer's `h_max − 1`. -/
theorem openingPivot_runAll_notHeld_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int)) (hmono : Sched.MonotoneCorruption)
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
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hhor : M.vote_time S.E ((M.opening_slot S.hc c)) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ head : V → Block V,
      (∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) - 1)), ∃ cw : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).st.core.toHealing
          (M.vote_time S.E ((M.opening_slot S.hc c) - 1))
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).cache ⇢ cw ∧
        let nw := M.mkNode
          (M.ns_setClock S.E
            (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).st
            (M.vote_time S.E ((M.opening_slot S.hc c) - 1)))
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).record cw
        ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E nw.st.core nw.st.core.s ⇢ T ∧
        ∃ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s ⇢ L ∧
        ∃ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore
            nw.st.core.s ⇢ L' ∧
        M.get_head_in_tree_with_layer (M.gradeContract nw.cache) S.E S.hc
          (M.toHealing nw.st.core) T L L' (nw.st.core.s - 1) ⇢ head w) →
    ∃ E : NamedBlock V,
      Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ E ∧
      (∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) - 1)),
        Block.Preceq E.erase (head w)) ∧
      (∀ B : Block V,
        (∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) - 1)),
          Block.Preceq B (head w)) →
        Block.Preceq B E.erase) ∧
      (∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1))),
        ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
            (W (strictEventIndex R
              (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1))) u) (c - 1),
        ∀ A2 : Option (Block V),
          M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
        ∀ G : Block V,
          M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
          Block.Preceq G E.erase) ∧
      (∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c)))
          (M.toHealing pn.st.core) ⇢ I →
        Block.Preceq E.erase I.parent) ∧
      (∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) pn
          (M.round_of S.hc pn.st.core.s) ⇢ A0 →
        Block.Preceq A0 E.erase) ∧
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S) wp.st.core
          (M.proposal_time S.E (M.opening_slot S.hc c))).h_max - 1 ≤
        ((Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S) wp.st.core
          (M.proposal_time S.E (M.opening_slot S.hc c))).σ E.erase).h := by
  intro R W wp cp hcp pn hP head hhead
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.openingPivot_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst
      hcv hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj) head hhead

end

end DecoupledConsensusModel.Sts.Restated
