import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FinalityStepWindow
import Proofs.Claims.Restated.Claim13bK_ProposalAdoption
import Proofs.Claims.Restated.Claim13bK_WindowProposalSent
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_92
import Proofs.Claims.Restated.Claim13beRoute3_93
import Proofs.Claims.Restated.Claim13beRoute3_94
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
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
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_95
import Proofs.Claims.Restated.Claim13bK_ProposalAdoptionBounded

/-!
# The anchor's height and the chain of windows

Theorems over a model `M : Record.Model V` about the run of the first `N` steps of an execution `x`,
read along the path it follows: at a window whose opening proposal has its `nj` bit clear the
anchor's height is at most the third proposal's justified height, and the third proposal of a window
is an ancestor of the middle proposal of a later window.
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

/-- If `c + 1 ≤ W` and `S.a W ≤ t`, then `vote_time (o_c + 2) ≤ t`. -/
theorem voteHor_f2d (facts : Record.Facts M) (S : Setup V) {c W : Round} {t : Int} (hc : c + 1 ≤ W)
    (hWt : (Restated.Vocabulary.Execution.Setup.a M S W) ≤ t) : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ t :=
  (Restated.interiorInstants_l85d facts S c).2.1.trans (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hc).trans hWt)

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

/-- Along the path `W = Restated.runAllPath M S Sched x v₀ N`, for a round `c` with `r₀ + 2 ≤ c` and
    `c + 1 ≤ W` whose openings `o_c`, `o_{c − 1}`, `o_{c − 2}` and slot `o_c + 2` propose `P`, `P'`,
    `P''` and `P₂`: if `nj(P)` is clear, then the height of `T_D'` is at most `h_j(P₂)`. -/
theorem secondWindowClear_f2d (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hN : (x[N].time : Int) ≤ tL) (hWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) ≤ (x[N].time : Int))
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {c : Round} (hc : r₀ + 2 ≤ c) (hcW : c + 1 ≤ Restated.switchRound M S tL)
    (hprops : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k)))
    (hopeningM : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    (hopeningMM : S.E.proposer ((M.opening_slot S.hc (c - 2))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)))))
    {P P₂ P' P'' : NamedBlock V}
    (hnjf : (M.derive_named S.E S.cfg P).nj = false) :
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
    (M.derive_named S.E S.cfg T_D').h ≤ (M.derive_named S.E S.cfg P₂).h_j := by
  classical
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂ wp' cp' hcp' pn' hP' wp'' cp'' hcp'' pn'' hP''
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  have hrD'rW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen'
  obtain ⟨hc4, hc1r, hcm1r, hsub, -, -, -, -, -, -⟩ := nat_windowStep_f2c
    (Restated.deadlineRoundW M S tGAT gap) (Restated.switchRound M S tE) r₀ c hrDrW hr₀ hc
  have hq := nat_anchorRound_f2d _ _ _ _ hrD'rW hr₀ hc
  have hvoteHor := Restated.voteHor_f2d facts S hcW hWN
  have hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))) := by
    simpa only [Nat.add_zero] using hprops 0 (by decide)
  obtain ⟨hAc, -, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[N].time : Int) := hAc.trans (hpv.trans hvoteHor)
  have hAcmN : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (x[N].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c 1)).trans hAcN
  have hCc := Restated.openingRowsPlanned_f2c facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
    hmult hcv htd hcom hthird hawake hrec hrsW hcs hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hNW hN hA hc1r hAcN hopening hopeningM cp hcp hP cp' hcp' hP'
  have keym := Restated.openingRowsPlanned_f2c facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
    hmult hcv htd hcom hthird hawake hrec hrsW hcs hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hNW hN hA (q := c - 1) hcm1r hAcmN hopeningM (by rw [hsub]; exact hopeningMM)
    (P := P') (P' := P'')
  rw [hsub] at keym
  have hCm := keym cp' hcp' hP' cp'' hcp'' hP''
  have hwin := (Restated.windowJustified_exec_l92 facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN hcom hrec hc4 hvoteHor hprops hopeningM hopeningMM hnjf
    (fun u hu nu hnu D hD => (hCc u hu nu hnu D hD).2 hnjf)
    (fun _ u hu hnjM nu hnu D hD => (hCm u hu nu hnu D hD).2 hnjM)
    cp hcp hP cp₂ hcp₂ hP₂ cp' hcp' hP' cp'' hcp'' hP'').1
  have htop := Restated.openingProposal_height_ge_rebasedAnchor_l85d facts S Sched x v₀ N hsync hmono hawake hgst
    hcv hexec hmult hthird hN hcom hrec hA hq hAcN hopening cp hcp hP
  exact htop.trans hwin

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

/-- Along the path `W = Restated.runAllPath M S Sched x v₀ N`, for a round `c₂ ≥ r₀` whose slot
    `o_{c₂} + 2` has its proposer not held and a round `c₃` with `c₂ + 1 ≤ c₃` and `c₃ + 1 ≤ W`
    whose slots `o_{c₃}`, `o_{c₃} + 1`, `o_{c₃} + 2` have proposers not held: the proposal `P₂` of
    `o_{c₂} + 2` is an ancestor of the proposal `P₃₁` of `o_{c₃} + 1`. -/
theorem thirdWindowParent_f2d (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {N : Nat} (hN : (x[N].time : Int) ≤ tL) (hWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) ≤ (x[N].time : Int))
    {c₂ c₃ : Round} (hr₀c₂ : r₀ ≤ c₂) (hc₂₃ : c₂ + 1 ≤ c₃) (hc₃W : c₃ + 1 ≤ Restated.switchRound M S tL)
    (hprop₂ : S.E.proposer ((M.opening_slot S.hc c₂) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₂) + 2)))
    (hprops₃ : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c₃) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₃) + k)))
    {P₂ P₃₁ : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) (S.E.proposer ((M.opening_slot S.hc c₂) + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c₂) + 2))) pn₂.st ⇢ some P₂ →
    let wp₃₁ := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c₃) + 1))) (S.E.proposer ((M.opening_slot S.hc c₃) + 1))
    ∀ cp₃₁ : M.Cache,
      M.onPhaseTick S.E S.hc wp₃₁.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c₃) + 1)) wp₃₁.cache ⇢ cp₃₁ →
      let pn₃₁ := M.mkNode (M.ns_setClock S.E wp₃₁.st (M.proposal_time S.E ((M.opening_slot S.hc c₃) + 1))) wp₃₁.record cp₃₁
      M.proposal_with (M.gradeContract cp₃₁) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c₃) + 1))) pn₃₁.st ⇢ some P₃₁ →
    NamedBlock.Preceq P₂ P₃₁ := by
  classical
  intro R W wp₂ cp₂ hcp₂ pn₂ hP₂ wp₃₁ cp₃₁ hcp₃₁ pn₃₁ hP₃₁
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
  obtain ⟨hd₂, hd₃, hrW₃, hc₃1, hc₂₃', hc₂W, hc₂W', hW0⟩ := nat_thirdParent_f2d
    (Restated.deadlineRoundW M S tGAT gap) (Restated.switchRound M S tE) r₀ c₂ c₃ (Restated.switchRound M S tL) hrDrW hr₀ hr₀c₂
    hc₂₃ hc₃W
  have hhor₂ : M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2) ≤ (x[N].time : Int) :=
    (Restated.interiorInstants_l85d facts S c₂).2.2.2.2.2.trans (Restated.voteHor_f2d facts S hc₂W hWN)
  obtain ⟨Q, hQ, -, ⟨j, hj, hjB⟩, -⟩ := Restated.windowOpeningProposalSent_g1 facts S Sched x v₀ N hsync hmono
    hawake hgst hcv hexec hmult hthird hN hd₂ 2 hhor₂ hprop₂ cp₂ hcp₂ (some P₂) hP₂
  have hQP : Q = P₂ := (Option.some.inj hQ).symm
  rw [hQP] at hjB
  have hs0 : (M.opening_slot S.hc r₀) + 2 ≤ (M.opening_slot S.hc c₂) + 2 :=
    Nat.add_le_add_right (facts.gr.opening_slot_mono S hr₀c₂) 2
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc c₂) + 2) ≤ tL :=
    (facts.sch.confirmation_time_mono S (Nat.add_le_add_right (facts.gr.opening_slot_mono S hc₂W') 2)).trans
      (Restated.switchRound_spec facts S tL hW0)
  have hpropT : HonestThroughTime Sched (M.vote_time S.E ((M.opening_slot S.hc c₂) + 2))
      (S.E.proposer ((M.opening_slot S.hc c₂) + 2)) := fun t' ht' hadv =>
    (mem_notHeldAt.mp hprop₂) (hmono t' _ (ht'.trans (facts.sch.Sts_vote_time_le_confirmation_time S _)) hadv)
  have hi : (x[j].time : Int) ≤ M.vote_time S.E ((M.opening_slot S.hc c₂) + 2) := by
    rw [hj]; exact (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hHeads := Restated.honestProposal_ancestorOfHonestHeadsFrom_fromSwitch_bounded facts S Sched x tE hexec
    hmono htd tGAT gap hgst hlen' hsync hthirdE hphaseE tL hEL hawake hrsW hmult hcv hcs hcom hrecE hprev hclear
    hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hthird hrec hs0 hct hpropT hjB hi
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN
  obtain ⟨hspos, hlo⟩ := Restated.windowSlot_bounds_g1 facts S tGAT gap (s := (M.opening_slot S.hc c₂) + 2)
    ((facts.gr.opening_slot_mono S hd₂).trans (Nat.le_add_right _ _))
  have hP₂clock : M.proposal_with (M.gradeContract cp₂)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c₂) + 2)))
      (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) ⇢ some P₂ := by
    have h := hP₂
    rewrite [show pn₂.st = M.store_with_cache
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) cp₂
      from facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hround₂ : Restated.deadlineRoundW M S tGAT gap + 1 ≤ M.round_of S.hc ((M.opening_slot S.hc c₂) + 2) := by
    have h := facts.gr.round_of_mono S.hc ((facts.gr.opening_slot_mono S hd₂).trans (Nat.le_add_right _ 2))
    rwa [facts.gr.round_of_opening_slot_eq S.hc] at h
  have hwin₂ : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc ((M.opening_slot S.hc c₂) + 2)) .g1 - S.E.Δ := by
    have h0 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
      (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (Nat.lt_of_succ_le hround₂))
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (M.round_of S.hc ((M.opening_slot S.hc c₂) + 2))
    have hΔ := S.E.Δ_pos
    linarith
  have hP₂run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _) hspos hprop₂ hhor₂ hlo
    (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (notHeldAt_anti hmono (facts.sch.proposal_time_le_confirmation_time S.E _) hprop₂) hwin₂)
    cp₂ hcp₂ hP₂clock
  have hzero : ∃ u : V, u ∉ Sched.adv 0 :=
    exists_notHeld_zero S Sched hthird (le_trans (Int.natCast_nonneg _) hN)
  have hP₂log := Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v₀ _ N hmono hzero hP₂run
  obtain ⟨cp₃, P₃, hcp₃, hP₃⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc c₃)
  obtain ⟨cp₃₂, P₃₂, hcp₃₂, hP₃₂⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    ((M.opening_slot S.hc c₃) + 2)
  have hopening₃ : S.E.proposer ((M.opening_slot S.hc c₃)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₃))) := by
    simpa only [Nat.add_zero] using hprops₃ 0 (by decide)
  have hvoteHor₃ := Restated.voteHor_f2d facts S hc₃W hWN
  obtain ⟨hAc₃, -, -, -, -, hpv₃⟩ := Restated.interiorInstants_l85d facts S c₃
  have hAc₃N : (Restated.Vocabulary.Execution.Setup.a M S c₃) ≤ (x[N].time : Int) := hAc₃.trans (hpv₃.trans hvoteHor₃)
  obtain ⟨t₁, -, ht₁s, -, hcs₁⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen' hphaseE hcs hrW₃
  have hoP : (M.opening_slot S.hc c₃) = (M.opening_slot S.hc (c₃ - 1)) + S.hc.R :=
    (Restated.openingInstants_l85f facts S hc₃1).2.2
  obtain ⟨hoP1, hoP2⟩ := nat_openings_f2b _ _ _ hoP S.hc.R_ge_three
  have hs₀ : (M.opening_slot S.hc c₂) + 2 ≤ (M.opening_slot S.hc c₃) :=
    (Nat.add_le_add_right (facts.gr.opening_slot_mono S hc₂₃') 2).trans hoP2
  have hBP : Block.Preceq P₂.erase P₃.erase :=
    Restated.preceq_openingProposal_of_heads_f2b facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
      hmult hthird hN hcom hrec htd hcs₁ hd₃ (ht₁s.trans (slotStart_mono S hoP1)) hAc₃N hopening₃
      (hHeads _ hs₀ (by rw [facts.gr.round_of_opening_slot_eq]; have := Restated.action_switchRound_add_delta_le_b facts S tGAT tL gap hgst (le_trans hlen' hEL); have := Restated.action_mono facts S (Nat.le_of_succ_le hc₃W); linarith)) cp₃ hcp₃ hP₃
  obtain ⟨hP₃run, -, -⟩ := Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ N hsync hmono
    hawake hgst hcv hexec hmult hthird hN hd₃ hAc₃N hopening₃ cp₃ hcp₃ hP₃
  have hP₃log := Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v₀ _ N hmono hzero hP₃run
  have hP₂P₃ : NamedBlock.Preceq P₂ P₃ :=
    Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hP₂log hP₃log hBP
  obtain ⟨-, hPQ, -, -⟩ := Restated.windowParent_l85d facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN hcom hrec hd₃ hvoteHor₃ hopening₃ (hprops₃ 2 (by decide))
    cp₃ hcp₃ hP₃ cp₃₂ hcp₃₂ hP₃₂
  obtain ⟨-, hpar⟩ := Restated.windowMiddleParent_f1b1 facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN hcom hrec hd₃ hvoteHor₃ hopening₃ (hprops₃ 1 (by decide))
    (hprops₃ 2 (by decide)) cp₃ hcp₃ hP₃ cp₃₁ hcp₃₁ hP₃₁ cp₃₂ hcp₃₂ hP₃₂
  rw [hpar] at hPQ
  exact namedPreceq_trans_l85 hP₂P₃ hPQ

end

end DecoupledConsensusModel.Sts.Restated
