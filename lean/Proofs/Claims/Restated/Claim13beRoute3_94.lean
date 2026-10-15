import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedInclusion
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_HjMono
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_41
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_92
import Proofs.Claims.Restated.Claim13beRoute3_93
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.Claim13beRoute3_92
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ChainState_W4FKChainJustification
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_94

/-!
# The window step after the joint invariant's round

Theorems over a model `M : Record.Model V` about the run of the first `N` steps of an execution `x`,
read along the path it follows: a height whose `nj` bit is set is never a descendant's justified
height, the previous opening proposal has a smaller height, the rows of every honest opening round
are planned, and the window step from the honest heads.
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
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_83` by name. -/
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
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

/-- If `X ⪯ Y` and the `nj` bit of `X`'s chain state is set, then the justified height of `Y`'s
    chain state is not the height of `X`. -/
theorem h_j_ne_of_nj_f2c (facts : Record.Facts M) (E : Env V) (cfg : Protocol.HeightConfig) {X Y : NamedBlock V}
    (hXY : NamedBlock.Preceq X Y) (hnj : (M.derive_named E cfg X).nj = true) :
    (M.derive_named E cfg Y).h_j ≠ (M.derive_named E cfg X).h := by
  induction Y with
  | genesis =>
    rw [namedPreceq_genesis_iff_l85] at hXY
    subst hXY
    exact Nat.ne_of_lt
      (facts.cs.chainOrder_derive_named E cfg _).justified_below_height
  | node p s root votes support rows proposer ih =>
    rcases namedPreceq_node_iff_l85.mp hXY with rfl | hXp
    · exact Nat.ne_of_lt
        (facts.cs.chainOrder_derive_named E cfg _).justified_below_height
    · rcases facts.cs.derive_named_h_j_step_cases E cfg p s root votes support rows proposer with
        h | ⟨h, hnjp⟩
      · rw [h]
        exact ih hXp
      · rw [h]
        intro heq
        have hsame := facts.csAdded.nj_eq_on_plateau_l85 E cfg hXp heq.symm
        rw [hnj, hnjp] at hsame
        exact Bool.noConfusion hsame

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

/-- In an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ n`, for a round `c` at least four rounds after the
    deadline round whose openings `o_c`, `o_{c − 1}`, `o_{c − 2}` have proposers not held, proposing
    `P`, `P'`, `P''`: if `P`'s `nj` bit is clear and, when `P'`'s `nj` bit is clear, every
    round-`(c − 1)` row of a validator not held at `S.a (c − 1)` is `vote h(P') T_h(P') false`, then
    `h(P') < h(P)`. -/
theorem prevOpening_height_lt_f2c (facts : Record.Facts M)
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
    (hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    (hopeningPrev2 : S.E.proposer ((M.opening_slot S.hc (c - 2))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)))))
    {P P' P'' : NamedBlock V}
    (hnj : (M.derive_named S.E S.cfg P).nj = false)
    (hplannedM : ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)),
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
    (M.derive_named S.E S.cfg P').h < (M.derive_named S.E S.cfg P).h := by
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP' wp'' cp'' hcp'' pn'' hP''
  obtain ⟨-, hc3, hc1, hc3', hsub⟩ := nat_window_rounds_l85f _ _ hc4
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R (M.opening_slot S.hc c) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  obtain ⟨hPne, hPm⟩ := Restated.prevOpening_namedPreceq_parent_l85f facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hc3 hAcHor hopening hopeningPrev
    cp hcp hP cp' hcp' hP'
  obtain ⟨hAmDelta, hpropA, -⟩ := Restated.openingInstants_l85f facts S hc1
  have hAmHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)) ≤ (x[n].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c 1)).trans hAcHor
  have hpropP : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)) + S.E.Δ) :=
    notHeldAt_anti hmono (hAmDelta.trans (facts.sch.proposal_time_le_confirmation_time S.E _))
      hopening
  have hpropHorP : M.proposal_time S.E ((M.opening_slot S.hc c)) ≤ (x[n].time : Int) :=
    hpropA.trans hAcHor
  have hParP : NamedBlock.Preceq P.parent P := parent_namedPreceq_l85 P
  have hP'P : NamedBlock.Preceq P' P := namedPreceq_trans_l85 hPm hParP
  have hle := facts.cs.derive_height_mono S.E S.cfg hP'P
  by_contra hnlt
  have hPmH : (M.derive_named S.E S.cfg P').h = (M.derive_named S.E S.cfg P).h :=
    Nat.le_antisymm hle (Nat.le_of_not_lt hnlt)
  have h2 := facts.cs.derive_height_mono S.E S.cfg hPm
  have h3 := facts.cs.derive_height_mono S.E S.cfg hParP
  have hparH : (M.derive_named S.E S.cfg P.parent).h =
      (M.derive_named S.E S.cfg P).h :=
    Nat.le_antisymm h3 (hPmH ▸ h2)
  have hTpar : (M.derive_named S.E S.cfg P.parent).T_h =
      (M.derive_named S.E S.cfg P').T_h :=
    (facts.cs.entry_eq_on_plateau S.E S.cfg hPm (hPmH.trans hparH.symm)).symm
  have hnj' : (M.derive_named S.E S.cfg P').nj = false := by
    rw [facts.csAdded.nj_eq_on_plateau_l85 S.E S.cfg hP'P hPmH]; exact hnj
  have key := Restated.targetQuorumCovered_of_plannedRows_l85f facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn hcom hrec (c := c - 1) hc3' hAmHor hopeningPrev
    (by rw [hsub]; exact hopeningPrev2) (P := P') (P' := P'') (s := (M.opening_slot S.hc c)) (B := P) hPm
    (hparH.trans hPmH.symm) hTpar hpropP hpropHorP hAmDelta
    (fun u hu => hplannedM u hu hnj')
  rw [hsub] at key
  have hcov := key cp' hcp' hP' cp'' hcp'' hP'' cp hcp hP
    (Restated.inWindow_prevRound_at_opening_l85f facts (Setup.alwaysAwake S) R c pn hpread)
  have hnjpar : (M.derive_named S.E S.cfg P.parent).nj = false := by
    rw [facts.csAdded.nj_eq_on_plateau_l85 S.E S.cfg hParP hparH]; exact hnj
  have hJc := facts.csAdded.namedJustifiedAt_of_targetQuorumCoveredByChild S.E S.cfg hPne hcov
    hnjpar
  have hup := hJc.2
  rw [hparH] at hup
  exact absurd hup (Nat.succ_ne_self _).symm

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ N`, with the joint invariant at a round `r₀` at or
    after the switch round and a round `q` with `r₀ + 1 ≤ q` and `S.a q ≤ x[N].time`, whose openings
    `q` and `q − 1` are honest and propose `P` and `P'`: every validator not held at `S.a q` has
    every round-`q` attestation it can sign carrying `vote h(P) T_h(P) b`, with `b = false` when
    `nj(P) = false`. -/
theorem openingRowsPlanned_f2c (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
    (tGAT tE tL : Int) (gap : Nat)
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
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
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
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {N : Nat} (hNW : (x[N].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    (hN : (x[N].time : Int) ≤ tL)
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {q : Round} (hq : r₀ + 1 ≤ q) (hqA : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[N].time : Int))
    (hopeningM : S.E.proposer ((M.opening_slot S.hc q)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hopeningMM : S.E.proposer ((M.opening_slot S.hc (q - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (q - 1)))))
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
    Restated.OpeningRowsPlanned M S Sched x v₀ N q P := by
  classical
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP'
  have hthirdE : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t ht => hthird t (ht.trans hEL)
  have hphaseE : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h1 h2 => hawake t h1 (h2.trans hEL)
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL := hlen.trans hEL
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  have hrD'rW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen'
  obtain ⟨hq1, hq', hq3, hrk, hrW1, hq11, hqd, hrWq⟩ := nat_rowsPlanned_f2c
    (Restated.deadlineRoundW M S tGAT gap) (Restated.rebasedDeadlineRoundW M S tGAT gap) (Restated.switchRound M S tE) r₀ q
    hrDrW hrD'rW hr₀ hq
  rcases Restated.plannedRows_or_heightBound_l92 facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec hmult
      hthird hcom hrec hlenL htd hA hNW hN hq' hq3 hqA hopeningM hopeningMM
      cp hcp hP cp' hcp' hP' with
    hC | ⟨mq, hmq, hmqN, hb⟩
  · exact hC
  obtain ⟨w, hwq⟩ := exists_notHeld_f2c S Sched hthird (hqA.trans hN)
  have hwM := hb w hwq
  have hstep := Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hmq hmqN w
  obtain ⟨n_k, T_k, hJk, -, hWk⟩ := Restated.exists_anchor_chain_withoutCatchUp_i1 facts S Sched x tE hexec hmono
    htd tGAT gap hgst hlen' hsync hthirdE hphaseE hrsW hmult hcv hcs hcom hw hs hrecE hprev hclear
    hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ (q - 1 - r₀)
  rw [hrk] at hJk
  have hmq' : Restated.tickStepAt M x mq ((Restated.Vocabulary.Execution.Setup.a M S (q - 1 + 1))) := by
    rw [hq11]; exact hmq
  obtain ⟨hmq1, hmq0⟩ := Restated.tickStepAt_time facts x hmq
  have hwHon : Restated.HonestThrough M Sched x mq w := by
    intro t ht hadv
    have hlt : t ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
      have : (x[mq].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by linarith
      exact ht.trans this
    exact (mem_notHeldAt.mp hwq) (hmono t _ hlt hadv)
  have hWmq : n_W ≤ mq := by
    by_contra hcon
    have hle : (x[mq + 1].time : Int) ≤ (x[n_W].time : Int) := Restated.time_mono_int facts S Sched x (by omega)
    have hW0 := (Restated.tickStepAt_time facts x hnW).2
    have hsw : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
      (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hrWq
    linarith
  have hJT : Block.Preceq (x[mq][w].st).st.core.J T_k.erase :=
    Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen' hsync hthirdE
      hphaseE hrsW hmult hcv hcom hrecE hprev hclear hB' hnW hAW hrW1 hWk hJk hmq' w mq hWmq
      (Nat.le_succ mq) hwHon
  have hTheads := Restated.anchor_ancestorOfHonestHeadsFrom_withoutCatchUp_i1 facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen' hsync hthirdE hphaseE hrsW hmult hcv hcs hcom hw hs hrecE hprev hclear hB'
    hnW hAW hJswitch hrW1 hWk hJk
  obtain ⟨t', -, ht's, -, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen' hphaseE hcs hrW1
  have hoM : (M.opening_slot S.hc q) = (M.opening_slot S.hc (q - 1)) + S.hc.R :=
    (Restated.openingInstants_l85f facts S hq1).2.2
  obtain ⟨hoo1, hoo⟩ := nat_openings_f2b _ _ _ hoM S.hc.R_ge_three
  have hcsC : t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc q) + 1) :=
    ht's.trans (slotStart_mono S hoo1)
  have hTM : Block.Preceq T_k.erase P.erase :=
    Restated.preceq_openingProposal_of_heads_f2b facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec hmult
      hthird hN hcom hrec htd hcs' hqd hcsC hqA hopeningM hTheads hoo cp hcp hP
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hbelow := Restated.belowOneThird_runAll_notHeld_inPhase facts S Sched x N tL hthird hN
  have hhjR : (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) w).st.h_j
      = (x[mq][w].st).st.core.h_j :=
    congrArg (fun z => z.st.core.h_j) hstep
  have hJR : (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) w).st.J
      = (x[mq][w].st).st.core.J :=
    congrArg (fun z => z.st.core.J) hstep
  have hHne : (M.derive_named S.E S.cfg P).h ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (facts.cs.one_le_derive_named_h S.E S.cfg P)
  have hnz : (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) w).st.h_j
      ≠ 0 := by
    rw [hhjR]
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.pos_iff_ne_zero.mpr hHne) hwM)
  obtain ⟨⟨E₀, hE₀run, hE₀J, hE₀h, hE₀T⟩, -⟩ := Restated.storeJustified_runEntry_f2b facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs (fun _ => Finset.subset_univ _)
    hbelow (Finset.mem_univ w) _ hnz
  rw [hJR] at hE₀J
  rw [hhjR] at hE₀h
  have hE₀h' : (M.derive_named S.E S.cfg E₀).h = (x[mq][w].st).st.core.h_j := hE₀h
  have hE₀T' : (M.derive_named S.E S.cfg E₀).T_h = E₀.erase := hE₀T
  obtain ⟨hPrun, -, -⟩ := Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ N hsync hmono hawake
    hgst hcv hexec hmult hthird hN hqd hqA hopeningM cp hcp hP
  have hE₀P : NamedBlock.Preceq E₀ P := by
    refine Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hE₀run hPrun ?_
    rw [hE₀J]
    exact preceq_trans_Preceq hJT hTM
  have hE₀le := facts.cs.derive_height_mono S.E S.cfg hE₀P
  have hwh : (x[mq][w].st).st.core.h_j = (M.derive_named S.E S.cfg P).h :=
    le_antisymm (hE₀h' ▸ hE₀le) hwM
  have hE₀hP : (M.derive_named S.E S.cfg E₀).h = (M.derive_named S.E S.cfg P).h :=
    hE₀h'.trans hwh
  have hTE : (M.derive_named S.E S.cfg E₀).T_h = (M.derive_named S.E S.cfg P).T_h :=
    facts.cs.entry_eq_on_plateau S.E S.cfg hE₀P hE₀hP
  have hroot : (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) w).st.J.root =
      (M.derive_named S.E S.cfg P).T_h.root := by
    rw [hJR, ← hE₀J, ← hE₀T', hTE]
  have htop := Restated.openingProposal_height_ge_rebasedAnchor_l85d facts S Sched x v₀ N hsync hmono hawake hgst
    hcv hexec hmult hthird hN hcom hrec hA hq' hqA hopeningM cp hcp hP
  have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q) ≤
      ({ Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := hqA
  exact Restated.openingRowsPlanned_of_justifiedEntry_f2b facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hcom hrec hlenL htd hA hNW hq3 hhor hopeningM hopeningMM htop (w := w)
    (hhjR.trans hwh) hroot cp hcp hP cp' hcp' hP'

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The window step: in an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ N`, with the joint invariant at a round `r₀` at or
    after the switch round and a round `c` with `r₀ + 2 ≤ c` whose openings and slots `o_c + 1`,
    `o_c + 2` have proposers not held, proposing `P` at `o_c` and `P₂` at `o_c + 2`: if `B'`'s
    erasure is an ancestor of the honest heads of every slot from `s ≤ o_{c − 1}` on, then `B' ⪯ P`,
    `P ⪯ P₂`, and either `h(B') < h_j(P₂)`, or `nj(P)` is set and `h(B') ≤ h(P)`. -/
theorem windowStep_ofHeads_f2c (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
    (tGAT tE tL : Int) (gap : Nat)
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
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
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
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
{N : Nat} (hNW : (x[N].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    (hN : (x[N].time : Int) ≤ tL)
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {c : Round} (hc : r₀ + 2 ≤ c)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[N].time : Int))
    (hprops : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k)))
    (hopeningM : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    (hopeningMM : S.E.proposer ((M.opening_slot S.hc (c - 2))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)))))
    {P P₂ P' P'' : NamedBlock V}
    {B' : NamedBlock V} (hB'log : Restated.blockInLog M S Sched x B') {s : Slot}
    (hheads : Restated.AncestorOfHonestHeadsFrom M S Sched x B'.erase s)
    (hsM : s ≤ (M.opening_slot S.hc (c - 1))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
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
    NamedBlock.Preceq B' P ∧ NamedBlock.Preceq P P₂ ∧
      ((M.derive_named S.E S.cfg B').h < (M.derive_named S.E S.cfg P₂).h_j ∨
        ((M.derive_named S.E S.cfg P).nj = true ∧
          (M.derive_named S.E S.cfg B').h ≤ (M.derive_named S.E S.cfg P).h)) := by
  classical
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂ wp' cp' hcp' pn' hP' wp'' cp'' hcp'' pn'' hP''
  have hthirdE : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t ht => hthird t (ht.trans hEL)
  have hphaseE : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h1 h2 => hawake t h1 (h2.trans hEL)
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  obtain ⟨hc4, hc1r, hcm1r, hsub, hcd, hcd', hrWc1, hrWc2, hc1, hc11⟩ := nat_windowStep_f2c
    (Restated.deadlineRoundW M S tGAT gap) (Restated.switchRound M S tE) r₀ c hrDrW hr₀ hc
  have hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))) := by
    simpa only [Nat.add_zero] using hprops 0 (by decide)
  have hprop2 := hprops 2 (by decide)
  obtain ⟨hAc, -, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[N].time : Int) := hAc.trans (hpv.trans hvoteHor)
  have hAcmN : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (x[N].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c 1)).trans hAcN
  have hCc := Restated.openingRowsPlanned_f2c facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
    hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hNW hN hA hc1r hAcN hopening hopeningM cp hcp hP cp' hcp' hP'
  have keym := Restated.openingRowsPlanned_f2c facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
    hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hNW hN hA (q := c - 1) hcm1r hAcmN hopeningM (by rw [hsub]; exact hopeningMM)
    (P := P') (P' := P'')
  rw [hsub] at keym
  have hCm := keym cp' hcp' hP' cp'' hcp'' hP''
  have hoP : (M.opening_slot S.hc c) = (M.opening_slot S.hc (c - 1)) + S.hc.R :=
    (Restated.openingInstants_l85f facts S hc1).2.2
  have hoM : (M.opening_slot S.hc (c - 1)) = (M.opening_slot S.hc (c - 2)) + S.hc.R := by
    have h := (Restated.openingInstants_l85f facts S (c := c - 1) hc11).2.2
    rw [hsub] at h
    exact h
  obtain ⟨hoP1, -⟩ := nat_openings_f2b _ _ _ hoP S.hc.R_ge_three
  obtain ⟨hoM1, -⟩ := nat_openings_f2b _ _ _ hoM S.hc.R_ge_three
  obtain ⟨t₁, -, ht₁s, -, hcs₁⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen' hphaseE hcs hrWc1
  obtain ⟨t₂, -, ht₂s, -, hcs₂⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen' hphaseE hcs hrWc2
  have hsP : s ≤ (M.opening_slot S.hc c) := hsM.trans (facts.gr.opening_slot_mono S (Nat.sub_le c 1))
  have hBP : Block.Preceq B'.erase P.erase :=
    Restated.preceq_openingProposal_of_heads_f2b facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
      hmult hthird hN hcom hrec htd hcs₁ hcd (ht₁s.trans (slotStart_mono S hoP1)) hAcN hopening
      hheads hsP cp hcp hP
  have hBM : Block.Preceq B'.erase P'.erase :=
    Restated.preceq_openingProposal_of_heads_f2b facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
      hmult hthird hN hcom hrec htd hcs₂ hcd' (ht₂s.trans (slotStart_mono S hoM1)) hAcmN
      hopeningM hheads hsM cp' hcp' hP'
  have hzero : ∃ u : V, u ∉ Sched.adv 0 :=
    exists_notHeld_zero S Sched hthird (le_trans (Int.natCast_nonneg _) hN)
  obtain ⟨hPrun, -, -⟩ := Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ N hsync hmono
    hawake hgst hcv hexec hmult hthird hN hcd hAcN hopening cp hcp hP
  obtain ⟨hMrun, -, -⟩ := Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ N hsync hmono
    hawake hgst hcv hexec hmult hthird hN hcd' hAcmN hopeningM cp' hcp' hP'
  have hPlog := Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v₀ _ N hmono hzero hPrun
  have hMlog := Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v₀ _ N hmono hzero hMrun
  have hB'P : NamedBlock.Preceq B' P :=
    Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hB'log hPlog hBP
  have hB'M : NamedBlock.Preceq B' P' :=
    Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hB'log hMlog hBM
  obtain ⟨-, hPQ, -, -⟩ := Restated.windowParent_l85d facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN hcom hrec hcd hvoteHor hopening hprop2 cp hcp hP cp₂ hcp₂ hP₂
  have hPP₂ : NamedBlock.Preceq P P₂ := namedPreceq_trans_l85 hPQ (parent_namedPreceq_l85 P₂)
  refine ⟨hB'P, hPP₂, ?_⟩
  by_cases hnj : (M.derive_named S.E S.cfg P).nj = true
  · exact Or.inr ⟨hnj, facts.cs.derive_height_mono S.E S.cfg hB'P⟩
  · have hnjf : (M.derive_named S.E S.cfg P).nj = false := by
      simpa only [Bool.not_eq_true] using hnj
    left
    have hwin := (Restated.windowJustified_exec_l92 facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
      hmult hthird hN hcom hrec hc4 hvoteHor hprops hopeningM hopeningMM hnjf
      (fun u hu nu hnu D hD => (hCc u hu nu hnu D hD).2 hnjf)
      (fun _ u hu hnjM nu hnu D hD => (hCm u hu nu hnu D hD).2 hnjM)
      cp hcp hP cp₂ hcp₂ hP₂ cp' hcp' hP' cp'' hcp'' hP'').1
    have hlt := Restated.prevOpening_height_lt_f2c facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec hmult
      hthird hN hcom hrec hc4 hAcN hopening hopeningM hopeningMM hnjf
      (fun u hu hnjM nu hnu D hD => (hCm u hu nu hnu D hD).2 hnjM)
      cp hcp hP cp' hcp' hP' cp'' hcp'' hP''
    exact lt_of_le_of_lt (facts.cs.derive_height_mono S.E S.cfg hB'M)
      (lt_of_lt_of_le hlt hwin)

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The window after a timeout: in an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ N`, for a round `c ≥ r₀` whose opening proposal `P` has
    its `nj` bit set and a later round `c'` with `c + tD / R ≤ c' ≤ c + tD / R + gap` whose opening,
    slots `o_{c'} + 1`, `o_{c'} + 2` and two previous openings have proposers not held, with `P'`
    and `P₂` the proposals of `o_{c'}` and `o_{c'} + 2`: `P ⪯ P'`, `P' ⪯ P₂` and `h(P) < h_j(P₂)`. -/
theorem windowAfterTimeout_f2c (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
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
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
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
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
{N : Nat} (hNW : (x[N].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    (hN : (x[N].time : Int) ≤ tL)
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {c c' : Round} (hc : r₀ ≤ c)
    (hlo : c + S.cfg.timeoutDelay / S.hc.R ≤ c')
    (hhi : c' ≤ c + S.cfg.timeoutDelay / S.hc.R + gap)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c') + 2) ≤ (x[N].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hprops : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c') + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c') + k)))
    (hopeningM : S.E.proposer ((M.opening_slot S.hc (c' - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c' - 1)))))
    (hopeningMM : S.E.proposer ((M.opening_slot S.hc (c' - 2))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c' - 2)))))
    {P P' P₂ Pm Pmm : NamedBlock V}
    (hnj : (M.derive_named S.E S.cfg P).nj = true) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c'))) (S.E.proposer (M.opening_slot S.hc c'))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c')) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc c'))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c'))) pn'.st ⇢ some P' →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c') + 2))) (S.E.proposer ((M.opening_slot S.hc c') + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c') + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c') + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c') + 2))) pn₂.st ⇢ some P₂ →
    let wpm := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c' - 1)))) (S.E.proposer (M.opening_slot S.hc (c' - 1)))
    ∀ cpm : M.Cache,
      M.onPhaseTick S.E S.hc wpm.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c' - 1))) wpm.cache ⇢ cpm →
      let pnm := M.mkNode (M.ns_setClock S.E wpm.st (M.proposal_time S.E (M.opening_slot S.hc (c' - 1)))) wpm.record cpm
      M.proposal_with (M.gradeContract cpm) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c' - 1)))) pnm.st ⇢ some Pm →
    let wpmm := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c' - 2)))) (S.E.proposer (M.opening_slot S.hc (c' - 2)))
    ∀ cpmm : M.Cache,
      M.onPhaseTick S.E S.hc wpmm.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c' - 2))) wpmm.cache ⇢ cpmm →
      let pnmm := M.mkNode (M.ns_setClock S.E wpmm.st (M.proposal_time S.E (M.opening_slot S.hc (c' - 2)))) wpmm.record cpmm
      M.proposal_with (M.gradeContract cpmm) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c' - 2)))) pnmm.st ⇢ some Pmm →
    NamedBlock.Preceq P P' ∧ NamedBlock.Preceq P' P₂ ∧
      (M.derive_named S.E S.cfg P).h < (M.derive_named S.E S.cfg P₂).h_j := by
  classical
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP' wp₂ cp₂ hcp₂ pn₂ hP₂ wpm cpm hcpm pnm hPm
    wpmm cpmm hcpmm pnmm hPmm
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
  have hm2 : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).mpr (by simpa only [Nat.mul_comm] using S.timeout_rounds.2)
  obtain ⟨hcd, hc4, hcc, hc1r, hcm1r, hsub, hcd'⟩ := nat_afterTimeout_f2c (Restated.deadlineRoundW M S tGAT gap)
    (Restated.switchRound M S tE) r₀ c c' (S.cfg.timeoutDelay / S.hc.R) hrDrW hr₀ hc hm2 hlo
  have hopening' : S.E.proposer ((M.opening_slot S.hc c')) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c'))) := by
    simpa only [Nat.add_zero] using hprops 0 (by decide)
  have hprop2 := hprops 2 (by decide)
  obtain ⟨hAc, -, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c'
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c') ≤ (x[N].time : Int) := hAc.trans (hpv.trans hvoteHor)
  have hAcmN : (Restated.Vocabulary.Execution.Setup.a M S (c' - 1)) ≤ (x[N].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c' 1)).trans hAcN
  have hPP' : NamedBlock.Preceq P P' := Restated.openingProposal_namedPreceq_later_l85f facts S Sched x v₀ N
    hsync hmono hawake hgst hcv hexec hmult hthird hN hcom hrec hcd hcc hAcN hopening hopening'
    cp hcp hP cp' hcp' hP'
  obtain ⟨-, hP'Q, -, -⟩ := Restated.windowParent_l85d facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN hcom hrec hcd' hvoteHor hopening' hprop2 cp' hcp' hP' cp₂ hcp₂ hP₂
  have hP'P₂ : NamedBlock.Preceq P' P₂ := namedPreceq_trans_l85 hP'Q (parent_namedPreceq_l85 P₂)
  have hCc := Restated.openingRowsPlanned_f2c facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
    hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hNW hN hA hc1r hAcN hopening' hopeningM cp' hcp' hP' cpm hcpm hPm
  have keym := Restated.openingRowsPlanned_f2c facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
    hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hNW hN hA (q := c' - 1) hcm1r hAcmN hopeningM (by rw [hsub]; exact hopeningMM)
    (P := Pm) (P' := Pmm)
  rw [hsub] at keym
  have hCm := keym cpm hcpm hPm cpmm hcpmm hPmm
  refine ⟨hPP', hP'P₂, ?_⟩
  by_cases hnj' : (M.derive_named S.E S.cfg P').nj = true
  ·
    have hcl := Restated.climb_excluded_l85f facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec hmult hthird
      hN hcom hrec hgap hcd hc4 hlo hhi hvoteHor hopening hprops hopeningM hopeningMM hnj hnj'
      (fun u hu nu hnu D hD => (hCm u hu nu hnu D hD).1)
      cp hcp hP cp' hcp' hP' cp₂ hcp₂ hP₂ cpm hcpm hPm cpmm hcpmm hPmm
    have hne := Restated.h_j_ne_of_nj_f2c facts S.E S.cfg hPP' hnj
    exact lt_of_lt_of_le (lt_of_le_of_ne hcl (Ne.symm hne)) (Restated.h_j_mono_chain facts S hP'P₂)
  ·
    have hnjf' : (M.derive_named S.E S.cfg P').nj = false := by
      simpa only [Bool.not_eq_true] using hnj'
    have hlt : (M.derive_named S.E S.cfg P).h < (M.derive_named S.E S.cfg P').h := by
      refine lt_of_le_of_ne (facts.cs.derive_height_mono S.E S.cfg hPP') ?_
      intro heq
      have hsame := facts.csAdded.nj_eq_on_plateau_l85 S.E S.cfg hPP' heq
      rw [hnj, hnjf'] at hsame
      exact Bool.noConfusion hsame
    have hwin := (Restated.windowJustified_exec_l92 facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
      hmult hthird hN hcom hrec hc4 hvoteHor hprops hopeningM hopeningMM hnjf'
      (fun u hu nu hnu D hD => (hCc u hu nu hnu D hD).2 hnjf')
      (fun _ u hu hnjM nu hnu D hD => (hCm u hu nu hnu D hD).2 hnjM)
      cp' hcp' hP' cp₂ hcp₂ hP₂ cpm hcpm hPm cpmm hcpmm hPmm).1
    exact lt_of_lt_of_le hlt hwin

end

end DecoupledConsensusModel.Sts.Restated
