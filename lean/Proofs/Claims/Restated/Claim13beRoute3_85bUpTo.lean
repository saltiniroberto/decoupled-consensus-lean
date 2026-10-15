import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The opening proposal after the deadline, with synchrony up to step `n`

The theorems of `Claim13beRoute3_85b.lean` along the path an execution follows, with synchrony
assumed only up to `x[n].time`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_64b.lean`, by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_58.lean`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_71.lean`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
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

/-- With synchrony assumed only up to `x[n].time`, in the run `R` of the execution `x` up to step
    `n`, along its path `W`, for a round `c` with `deadlineRoundW S tGAT gap + 2 ≤ c` within the
    horizon whose opening proposer is not held at the opening slot's confirmation instant and
    proposed `P` on `W`: every block the SG vote selector can return at a round-`c` action read on
    `W` of a validator not held at `S.a c`, with any grade-2 candidate, is `P`. -/
theorem sgBlock_eq_openingProposal_runAll_notHeld_upTo (facts : Record.Facts M)
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
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
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
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) A2 ⇢ G →
        G = P.erase := by
  intro R W wp cp hcp pn hP
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.sgBlock_eq_openingProposal_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)

/-- With synchrony assumed only up to `x[n].time`, in the run `R` of the execution `x` up to step
    `n`, along its path `W`, for a round `c` with `deadlineRoundW S tGAT gap + 2 ≤ c` within the
    horizon whose opening proposer is not held at the opening slot's confirmation instant and
    proposed `P` on `W`: if the FG source at a round-`c` action read on `W` of a validator not held
    at `S.a c` can return `some X`, then `X` is `P`. -/
theorem fgSource_eq_openingProposal_of_some_runAll_notHeld_upTo (facts : Record.Facts M)
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
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
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
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ X : Block V,
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nu ⇢ some X →
        X = P.erase := by
  intro R W wp cp hcp pn hP
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.fgSource_eq_openingProposal_of_some_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)

/-- With synchrony assumed only up to `x[n].time`, in the run `R` of the execution `x` up to step
    `n`, along its path `W`, for a round `c` with `deadlineRoundW S tGAT gap + 3 ≤ c` within the
    horizon whose opening proposers of `c` and `c − 1` are not held at their opening slots'
    confirmation instants and proposed `P` and `P'` on `W`: `P'` is an ancestor of the parent of
    every proposal input of the round-`c` opening proposer's read on `W`. -/
theorem prevOpeningProposal_preceq_proposedParent_runAll_notHeld_upTo (facts : Record.Facts M)
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
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c)))
        (M.toHealing pn.st.core) ⇢ I →
      Block.Preceq P'.erase I.parent := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.prevOpeningProposal_preceq_proposedParent_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
        exact (Nat.le_succ _).trans hc3)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc3)
    hopeningPrev cp' hcp' hP'

/-- With synchrony assumed only up to `x[n].time`, in the run `R` of the execution `x` up to step
    `n`, along its path `W`, for a round `c` with `deadlineRoundW S tGAT gap + 3 ≤ c` within the
    horizon whose opening proposers of `c` and `c − 1` are not held at their opening slots'
    confirmation instants and proposed `P` and `P'` on `W`: every validator not held at the
    round-`c` grade-2 domain instant has `P'` in the filtered tree of its node state in the world of
    `W` strictly before that instant, and every outcome of its round-`c` grade-2 store grade for
    `P'` there is `true`. -/
theorem namedGradeFormsAt_prevOpeningProposal_runAll_notHeld_upTo (facts : Record.Facts M)
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
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    Restated.NamedGradeFormsAtOn M (Setup.alwaysAwake S) R (notHeldAt Sched) c P'.erase
      (W (strictEventIndex R (M.domain S.E S.hc c Phase.g2))) := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.namedGradeFormsAt_prevOpeningProposal_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
        exact (Nat.le_succ _).trans hc3)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc3)
    hopeningPrev cp' hcp' hP'

/-- With synchrony assumed only up to `x[n].time`, in the run `R` of the execution `x` up to step
    `n`, along its path `W`, for a round `c` with `deadlineRoundW S tGAT gap + 3 ≤ c` within the
    horizon whose opening proposers of `c` and `c − 1` are not held at their opening slots'
    confirmation instants and proposed `P` and `P'` on `W`: every outcome of the FG source at every
    round-`c` action read on `W` of a validator not held at `S.a c` is `some P`. -/
theorem fgSource_eq_openingProposal_runAll_notHeld_upTo (facts : Record.Facts M)
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
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ o : Option (Block V),
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nu ⇢ o →
        o = some P.erase := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.fgSource_eq_openingProposal_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
        exact (Nat.le_succ _).trans hc3)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc3)
    hopeningPrev cp' hcp' hP'

end

end DecoupledConsensusModel.Sts.Restated
