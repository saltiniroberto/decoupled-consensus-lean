import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13beRoute3_15
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85e
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_SeedActionRowCarriage
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.Claim13beRoute3_92
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ChainState_W4FKChainJustification
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The justification of a window over an execution

Theorems over a model `M : Record.Model V` about the run of the first `n` steps of an execution `x`,
read along the path it follows: the window justifies the opening proposal's height, an opening
round's honest rows are planned or every honest store already justifies that height, and the
recurrence's windows fit the interval.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_58` by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_71` by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_85f` by name. -/
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

/-- In an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ n`, for a round `c` at least four rounds after the
    deadline round whose relevant opening proposers are not held: if `P`'s `nj` bit is clear, every
    round-`c` row of a validator not held at `S.a c` is `vote h(P) T_h(P) false`, and, when
    `h(P') = h(P)` and `P'`'s `nj` bit is clear, every round-`(c − 1)` row of a validator not held
    at `S.a (c − 1)` is `vote h(P') T_h(P') false`, then `h(P) ≤ h_j(P₂)` and `P ⪯ P₂` for the
    proposals `P`, `P₂`, `P'`, `P''` of `o_c`, `o_c + 2`, `o_{c − 1}`, `o_{c − 2}`. -/
theorem windowJustified_exec_l92 (facts : Record.Facts M) 
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {c : Round} (hc4 : Restated.deadlineRoundW M S tGAT gap + 4 ≤ c)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hprops : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k)))
    (hopeningPrev : S.E.proposer (M.opening_slot S.hc (c - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c - 1))))
    (hopeningPrev2 : S.E.proposer (M.opening_slot S.hc (c - 2)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c - 2))))
    {P P₂ P' P'' : NamedBlock V}
    (hnj : (M.derive_named S.E S.cfg P).nj = false)
    (hplannedC : ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root false)
    (hplannedM : (M.derive_named S.E S.cfg P').h = (M.derive_named S.E S.cfg P).h →
      ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)),
      (M.derive_named S.E S.cfg P').nj = false →
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1))) u) (c - 1),
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P').h
          (M.derive_named S.E S.cfg P').T_h.root false) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c) + 2))) (S.E.proposer ((M.opening_slot S.hc c) + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c) + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c) + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c) + 2))) pn₂.st ⇢ some P₂ →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    let wp'' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 2)))) (S.E.proposer (M.opening_slot S.hc (c - 2)))
    ∀ cp'' : M.Cache,
      M.onPhaseTick S.E S.hc wp''.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c - 2))) wp''.cache ⇢ cp'' →
      let pn'' := M.mkNode (M.ns_setClock S.E wp''.st (M.proposal_time S.E (M.opening_slot S.hc (c - 2)))) wp''.record cp''
      M.proposal_with (M.gradeContract cp'') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 2)))) pn''.st ⇢ some P'' →
    (M.derive_named S.E S.cfg P).h ≤ (M.derive_named S.E S.cfg P₂).h_j ∧
      NamedBlock.Preceq P P₂ := by
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂ wp' cp' hcp' pn' hP' wp'' cp'' hcp'' pn'' hP''
  have hopening : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c)) := by
    simpa only [Nat.add_zero] using hprops 0 (by decide)
  have hprop2 := hprops 2 (by decide)
  obtain ⟨hAc, -, -, -, hAcDelta, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤ (x[n].time : Int) := hAc.trans (hpv.trans hvoteHor)
  obtain ⟨hc2, hc3, hc1, hc3', hsub⟩ := nat_window_rounds_l85f _ _ hc4
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨hP₂ne, hPQ, hQslot2, hsl⟩ := Restated.windowParent_l85d facts S Sched x v₀ n hsync hmono hawake hgst
    hcv hvalid hawm hthird hn hcom hrec hc2 hvoteHor hopening hprop2 cp hcp hP cp₂ hcp₂ hP₂
  obtain ⟨hPne, hPm⟩ := Restated.prevOpening_namedPreceq_parent_l85f facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hc3 hAcHor hopening hopeningPrev
    cp hcp hP cp' hcp' hP'
  have hPmslot : P'.slot = (M.opening_slot S.hc (c - 1)) :=
    (p85f% proposal_slot₈₅f) facts hf.sorted hf.onePath _ cp' hcp' hP'
  obtain ⟨hAmDelta, hpropA, hoc⟩ := Restated.openingInstants_l85f facts S hc1
  have hQslot : P₂.parent.slot + 1 ≤ (M.opening_slot S.hc (c - 1)) + S.cfg.timeoutDelay := by
    exact nat_slot_budget_l85f _ _ _ _ _ hQslot2 hoc S.hc.R_ge_three S.timeout_rounds.2
  have hpropHor : M.proposal_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int) :=
    hpv.trans hvoteHor
  have hprop2' : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ) :=
    notHeldAt_anti hmono (hAcDelta.trans (facts.sch.proposal_time_le_confirmation_time S.E _))
      hprop2
  have hp₂read : pn₂ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R ((M.opening_slot S.hc c) + 2) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R (M.opening_slot S.hc c) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hcov2 : (M.derive_named S.E S.cfg P₂.parent).h =
        (M.derive_named S.E S.cfg P).h →
      (M.derive_named S.E S.cfg P₂.parent).T_h =
        (M.derive_named S.E S.cfg P).T_h →
      Restated.Vocabulary.Proofs.HealingSurface.NamedTargetQuorumCoveredByChild M S.E
        (M.derive_named S.E S.cfg P₂.parent) P₂ := fun hQH hT =>
    Restated.targetQuorumCovered_of_plannedRows_l85f facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
      hawm hthird hn hcom hrec hc3 hAcHor hopening hopeningPrev (P := P) (P' := P')
      (s := (M.opening_slot S.hc c) + 2) (B := P₂) hPQ hQH hT hprop2'
      hpropHor hAcDelta hplannedC cp hcp hP cp' hcp' hP' cp₂ hcp₂ hP₂
      (Restated.Vocabulary.Proofs.HealingSurface.inWindow_round_at_plusTwo facts (Setup.alwaysAwake S) R c pn₂ hp₂read)
  have hAmHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)) ≤ (x[n].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c 1)).trans hAcHor
  have hpropP : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)) + S.E.Δ) :=
    notHeldAt_anti hmono (hAmDelta.trans (facts.sch.proposal_time_le_confirmation_time S.E _))
      hopening
  have hpropHorP : M.proposal_time S.E (M.opening_slot S.hc c) ≤ (x[n].time : Int) :=
    hpropA.trans hAcHor
  have hP'P : NamedBlock.Preceq P' P := namedPreceq_trans_l85 hPm (parent_namedPreceq_l85 P)
  have hcovc : (M.derive_named S.E S.cfg P').h = (M.derive_named S.E S.cfg P).h →
      (M.derive_named S.E S.cfg P.parent).h = (M.derive_named S.E S.cfg P).h →
      (M.derive_named S.E S.cfg P.parent).T_h = (M.derive_named S.E S.cfg P').T_h →
      Restated.Vocabulary.Proofs.HealingSurface.NamedTargetQuorumCoveredByChild M S.E
        (M.derive_named S.E S.cfg P.parent) P := fun hPmH hparH hTpar => by
    have hnj' : (M.derive_named S.E S.cfg P').nj = false := by
      rw [facts.csAdded.nj_eq_on_plateau_l85 S.E S.cfg hP'P hPmH]; exact hnj
    have key := Restated.targetQuorumCovered_of_plannedRows_l85f facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn hcom hrec (c := c - 1) hc3' hAmHor hopeningPrev
      (by rw [hsub]; exact hopeningPrev2) (P := P') (P' := P'') (s := (M.opening_slot S.hc c)) (B := P) hPm
      (hparH.trans hPmH.symm) hTpar hpropP hpropHorP hAmDelta
      (fun u hu => hplannedM hPmH u hu hnj')
    rw [hsub] at key
    exact key cp' hcp' hP' cp'' hcp'' hP'' cp hcp hP
      (Restated.inWindow_prevRound_at_opening_l85f facts (Setup.alwaysAwake S) R c pn hpread)
  exact ⟨facts.csAdded.windowJustified_l85d S.E S.cfg hsl hPne hP₂ne hnj hPm hPmslot hPQ hQslot hcov2 hcovc,
    namedPreceq_trans_l85 hPQ (parent_namedPreceq_l85 P₂)⟩

/-- In an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ N`, for an opening round `q` with
    `S.a q ≤ x[N].time ≤ tL` proposing `P`: either every validator not held at `S.a q` has every
    round-`q` row it can sign equal to `vote h(P) T_h(P) b`, with `b = false` when `nj(P) = false`,
    or some tick step `m` at `S.a q` with `m + 1 ≤ N` leaves every validator not held at `S.a q`
    with justified height at least `h(P)`. -/
theorem plannedRows_or_heightBound_l92 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (N : Nat)
    {tGAT tL : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[N].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL))) (hn : (x[N].time : Int) ≤ tL)
    {q : Round} (hq' : Restated.rebasedDeadlineRoundW M S tGAT gap + 1 ≤ q)
    (hq3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ q)
    (hqhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q) ≤ (x[N].time : Int))
    (hopening : S.E.proposer (M.opening_slot S.hc q) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc q)))
    (hopeningPrev : S.E.proposer (M.opening_slot S.hc (q - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (q - 1))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc q))) (S.E.proposer (M.opening_slot S.hc q))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q))) pn.st ⇢ some P →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (q - 1)))) (S.E.proposer (M.opening_slot S.hc (q - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (q - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (q - 1)))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (q - 1)))) pn'.st ⇢ some P' →
    Restated.OpeningRowsPlanned M S Sched x v₀ N q P ∨
    ∃ m : Nat, Restated.tickStepAt M x m ((Restated.Vocabulary.Execution.Setup.a M S q)) ∧ m + 1 ≤ N ∧
      ∀ v₁ ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S q)),
        (M.derive_named S.E S.cfg P).h ≤ (x[m][v₁].st).st.core.h_j := by
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP'
  have htop := Restated.openingProposal_height_ge_rebasedAnchor_l85d facts S Sched x v₀ N hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hA hq' hqhor hopening cp hcp hP
  rcases Restated.honestRow_atOpening_planned_runAll_l85e facts S Sched x v₀ N hsync hmono hawake hgst hcv hvalid
      hawm hthird hcom hrec hlen htd hA hnW hq3 hqhor hopening hopeningPrev htop
      cp hcp hP cp' hcp' hP' with
    hpl | hst
  · exact Or.inl hpl
  · right
    obtain ⟨mq, hmq⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S q)
    have hmqN : mq + 1 ≤ N := by
      by_contra hcon
      have hle : x[N].time ≤ x[mq].time := Restated.time_mono facts S Sched x (by omega)
      have hle' : (x[N].time : Int) ≤ (x[mq].time : Int) := by exact_mod_cast hle
      have h0 := (Restated.tickStepAt_time facts x hmq).2
      have hq : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q) = (Restated.Vocabulary.Execution.Setup.a M S q) := rfl
      linarith
    refine ⟨mq, hmq, hmqN, fun v₁ hv₁ => ?_⟩
    have h := hst v₁ hv₁
    have hstep := Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hmq hmqN v₁
    exact h.trans (le_of_eq (congrArg (fun z => z.st.core.h_j) hstep))

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη S gap ≤ tL`, `deadlineRoundW ≤ r` and
    `r + gap ≤ switchRound S tL`, then `tGAT ≤ proposal_time o_r` and
    `proposal_time o_r + gap · (S.a 1 − S.a 0) ≤ tL`. -/
theorem recurrenceWindow_fits_l92 (facts : Record.Facts M) (S : Setup V) {tGAT tL : Int} {gap : Nat}
    (hgst : S.E.t_GST ≤ tGAT) (hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL) {r : Round}
    (hr : Restated.deadlineRoundW M S tGAT gap ≤ r) (hrg : r + gap ≤ Restated.switchRound M S tL) :
    tGAT ≤ M.proposal_time S.E ((M.opening_slot S.hc r)) ∧
      M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) ≤ tL := by
  have hΔ := S.E.Δ_pos
  have hR3 : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hrDW : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL := hr.trans ((Nat.le_add_right _ _).trans hrg)
  obtain ⟨hlo0, -⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlen' le_rfl hrDW
  obtain ⟨-, hWE⟩ := Restated.switchRound_window_in_phase facts S tGAT tL gap hgst hlen'
  have hwa : wAttest S = 4 * (S.hc.R : Int) * S.E.Δ := rfl
  have hper1 : (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) = 4 * S.E.Δ * (S.hc.R : Int) := by
    rw [Restated.action_eq_l85d facts, Restated.action_eq_l85d facts]; push_cast; ring
  rw [Restated.proposal_time_opening_eq_l85d facts, hper1]
  rw [Restated.action_eq_l85d facts, hwa] at hlo0
  rw [Restated.action_eq_l85d facts] at hWE
  have hr' : ((Restated.deadlineRoundW M S tGAT gap : Nat) : Int) ≤ (r : Int) := by exact_mod_cast hr
  have hrg' : (r : Int) + (gap : Int) ≤ ((Restated.switchRound M S tL : Nat) : Int) := by
    exact_mod_cast hrg
  have hR3' : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast hR3
  have hP : (0 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by positivity
  constructor
  · nlinarith
  · nlinarith

end

end DecoupledConsensusModel.Sts.Restated
