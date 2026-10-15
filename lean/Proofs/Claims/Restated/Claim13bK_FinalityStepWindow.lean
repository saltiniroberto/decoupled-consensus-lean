import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ActionHeads
import Proofs.Claims.Restated.Claim13bK_FinalityStep
import Proofs.Claims.Restated.Claim13bK_ProposalAdoption
import Proofs.Claims.Restated.Claim13beRoute3_41
import Proofs.Claims.Restated.Claim13beRoute3_42
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_49b
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_57b
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_67b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85e
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Proofs.Claims.Restated.Claim13beRoute3_86g
import Proofs.Claims.Restated.Claim13beRoute3_87b
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_W4FKChainAdvanceFold
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_CheckpointAlgebra
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_NamedNjGap
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_W4FKChainFinalityWrite
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ActionHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
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
import Model.Conditions.Vocabulary_Execution_W4FKChainAdvanceFold
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Assumptions_Weight
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Admissible
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_Store
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_FinalityPairCore
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Certificates
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_FinalityStepWindow
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# The finality step over a strong window

Facts about justification, lock checks, action attestations and the proposals of a window's slots,
and the finality step over a strong window, read along the bundle's path `W`
(`Restated.AdmissibleFieldsOn M S rho W Hs Xb lo`) or along the path the execution follows,
`Restated.runAllPath M S Sched x v₀ n`. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of `Claim13beRoute3_46`, by name. -/
local macro "p46% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_46)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_51`, by name. -/
local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_53b`, by name. -/
local macro "p53b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_53b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_57b`, by name. -/
local macro "p57b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_57b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_58`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_64b`, by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_67b`, by name. -/
local macro "p67b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_67b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_71`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_85c`, by name. -/
local macro "p85c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_85c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_85f`, by name. -/
local macro "p85f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_85f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_86g`, by name. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_86f`, by name. -/
local macro "p86f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_60`, by name. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_56`, by name. -/
local macro "p56% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_56)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_44`, by name. -/
local macro "p44% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_44)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_50`, by name. -/
local macro "p50% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_50)
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

/-- If `B ⪯ P` and `h(B) < h_j(P)`, then `B` is an ancestor of `P`'s justified block `J(P)`. -/
theorem preceq_justified_of_height_lt_f1b1 (facts : Record.Facts M) (E : Env V) (cfg : HeightConfig)
    {B P : NamedBlock V} (hBP : NamedBlock.Preceq B P)
    (hlt : (M.derive_named E cfg B).h < (M.derive_named E cfg P).h_j) :
    Block.Preceq B.erase (M.derive_named E cfg P).J := by
  obtain ⟨⟨J, hJP, hJerase, -, hJh⟩, -⟩ := facts.cs.derive_named_checkpoint_entries E cfg P
  rcases hJh with ⟨h0, -⟩ | hJh
  · rw [h0] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  rcases namedPreceq_total_l85 hBP hJP with hBJ | hJB
  · rw [← hJerase]
    exact Proofs.NamedWire.erase_preceq hBJ
  · have hle := facts.cs.derive_height_mono E cfg hJB
    rw [hJh] at hle
    exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

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

/-- Under the phase premises, if `D` is a run block of `R_n` along
    `W := Restated.runAllPath M S Sched x v₀ n` with `h_j(D) ≠ 0` and `h(T_0) ≤ h_j(D)`, then the
    record of every validator's node state in `W`'s world strictly before any time locks at `h_j(D)`
    nothing or `J(D)`, and for every validator `v` not held at a time `t` the record of `v`'s node
    state in `W`'s world strictly before `t` has, at `h_j(D)`, the target nothing or `J(D)` and the
    timeout bit clear. -/
theorem finalityRecord_clear_ofRunBlock_f1b1 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE tL : Int} {gap : Nat}
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
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
    (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    {D : NamedBlock V}
    (hDrun : Restated.RunBlockOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ n) Finset.univ D)
    (hH0 : (M.derive_named S.E S.cfg D).h_j ≠ 0)
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg D).h_j) :
    (∀ (v : V) (t : Int) (L : BlockId),
      (Restated.runAllPath M S Sched x v₀ n (strictEventIndex
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        t) v).record.legacy.lock (M.derive_named S.E S.cfg D).h_j = some L →
      L = (M.derive_named S.E S.cfg D).J.root) ∧
    (∀ (v : V) (t : Int), v ∈ notHeldAt Sched t →
      (∀ T : BlockId,
        (Restated.runAllPath M S Sched x v₀ n (strictEventIndex
          ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
          t) v).record.legacy.target (M.derive_named S.E S.cfg D).h_j = some T →
        T = (M.derive_named S.E S.cfg D).J.root) ∧
      (Restated.runAllPath M S Sched x v₀ n (strictEventIndex
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        t) v).record.legacy.timeout (M.derive_named S.E S.cfg D).h_j = false) := by
  classical
  -- the run, its path, its bundle, and the weight bound at its horizon
  set rho : Record.Run V :=
    ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
    with hrho
  set W := Restated.runAllPath M S Sched x v₀ n with hWdef
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL := hlen.trans hEL
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL := Restated.healingLength_le_of_kit_l76 facts S hlenL
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tL := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hfb := Restated.belowOneThird_runAll_notHeld_inPhase facts S Sched x n tL hthird hn
  set H : Height := (M.derive_named S.E S.cfg D).h_j with hHdef
  set J : Block V := (M.derive_named S.E S.cfg D).J with hJdef
  -- the justification of `D`: its certificate and a vote by a signer not held
  have hcertJ : Restated.CertificateOn M (Setup.alwaysAwake S) rho W Finset.univ H J.root :=
    Restated.certificate_of_justifiedRunBlock_l1On facts (Setup.alwaysAwake S) Finset.univ hDrun ⟨rfl, rfl⟩ hH0
  obtain ⟨z, tz, az, hemz, hzt, hpz⟩ := Restated.certificateOn_emittedVote_l85e facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hfb hcertJ
  -- one entry at `H`
  have hagree := Restated.honestVotes_oneEntry_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hrec hlenL htd hA0 hnW htop
  have hone : ∀ (w : V) (t : Int) (a : NamedAttestation V) (e' : BlockId) (b' : Bool),
      (Restated.Vocabulary.Execution.Run.emits M (Setup.alwaysAwake S) rho W w (Object.attest a) t) → w ∈ notHeldAt Sched t →
      a.height_pair = .vote H e' b' → e' = J.root :=
    fun w t a e' b' hem hw hp => hagree w z t tz a az e' J.root b' false hem hw hp hemz hzt hpz
  refine ⟨?_, ?_⟩
  · -- the lock: two certificates at one height
    intro v t L hl
    have hcertL := Restated.recordLock_certificateOn_f1 facts (Setup.alwaysAwake S) (notHeldAt Sched)
      Finset.univ hf (Finset.mem_univ v) t hH0 hl
    exact Restated.certificateTarget_uniqueOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs
      hfb H L J.root hcertL hcertJ
  intro v t hv
  refine ⟨?_, ?_⟩
  · -- the target: the validator's own vote names the one entry
    intro T hT
    obtain ⟨t', a, hlt, hem, hp⟩ := Restated.recordTarget_emits_before_l85c facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf v t hT
    exact hone v t' a T false hem (hHs t' t hlt.le hv) hp
  · -- the timeout: the justified entry's `nj` bit is clear
    have hpos : 0 < (M.derive_named S.E S.cfg D).h_j := Nat.pos_of_ne_zero hH0
    obtain ⟨P, hPD, hPe, hPh, hPT, hPnj⟩ :=
      Restated.Vocabulary.Proofs.NamedCheckpointAlgebra.namedJustification_ancestor_data facts S.E S.cfg D hpos
    have hPrun : Restated.RunBlockOn M (Setup.alwaysAwake S) rho W Finset.univ P :=
      Restated.runBlock_ancestorOn_FixedHeightRootCore facts hDrun hPD
    have hPh' : (M.derive_named S.E S.cfg P).h = H := hPh
    have hProot : (M.derive_named S.E S.cfg P).T_h.root = J.root := by
      rw [hPT, hPe]
    have hone' : ∀ (w : V) (t : Int) (a : NamedAttestation V) (e' : BlockId) (b' : Bool),
        (Restated.Vocabulary.Execution.Run.emits M (Setup.alwaysAwake S) rho W w (Object.attest a) t) → w ∈ notHeldAt Sched t →
        a.height_pair = .vote (M.derive_named S.E S.cfg P).h e' b' → e' = J.root := by
      intro w t a e' b' hem hw hp
      rw [hPh'] at hp
      exact hone w t a e' b' hem hw hp
    have hno := Restated.noTimeoutVote_l85c facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs
      (fun _ => Finset.subset_univ _) hPrun hPnj hProot hone' v
    cases htmo : (W (strictEventIndex rho t) v).record.legacy.timeout H with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨t', a, e, hlt, hem, hp⟩ := Restated.recordTimeout_emits_before_l85c facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf v t htmo
      rw [← hPh'] at hp
      exact hno a.round a t' rfl hem (hHs t' t hlt.le hv) e hp

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

/-- Under the bundle along its path `W`, if `v ∈ Xb`, `P` is a run block along `W` with
    `h_j(P) = hJ`, `J(P) = J`, `h_F(P) < hJ`, and the record of `v`'s node state in `W`'s world
    strictly before `S.a r` has at `hJ` the target nothing or `J`, the timeout bit clear, and the
    lock nothing or `J`, then for every node state `n` of `v`'s round-`r` action read on which the
    action head can return `P`'s erasure, every attestation the attestation duty can return on `n`
    has the finality pair `(hJ, J)`. -/
theorem actionAttestation_finality_pairOn_f1b1 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {P : NamedBlock V}
    (hPrun : Restated.RunBlockOn M S rho W Xb P)
    {hJ : Height} {J : Block V}
    (hhj : (M.derive_named S.E S.cfg P).h_j = hJ)
    (hJeq : (M.derive_named S.E S.cfg P).J = J)
    (hdebt : (M.derive_named S.E S.cfg P).h_F < hJ)
    (htarget : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy.target hJ = none ∨
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy.target hJ = some J.root)
    (htimeout : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy.timeout hJ = false)
    (hlock : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy.lock hJ = none ∨
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy.lock hJ = some J.root) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) ⇢ P.erase →
      ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
        D.2.2.finality_pair = some ⟨hJ, J.root⟩ := by
  intro n hn hhead D hD
  have hmem := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hheadMem : P.erase ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith_mem_storeBeforeTime facts S v r _ hmem n hn _ hhead
  have hbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts S Hs Xb hf hv hheadMem hPrun
  have hbody' : P ∈ n.st.bodies := by
    rw [(p57b% actionReadFrom_bodies₅₇b) facts S _ r n hn]
    exact hbody
  have hagree := Restated.derivedStateAgrees_actionStoreAtOn facts S Hs Xb hf v r n hn P hbody'
  have hsigma : (M.toHealing n.st.core).σ P.erase = M.derive_named S.E S.cfg P := by
    rw [Record.Model.HS.σ, facts.sto.Sts_toHealing_σ]
    exact hagree
  have hrecord : n.record = (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record :=
    (p46% actionReadFrom_record₄₆) facts S _ r n hn
  obtain ⟨res, hres, hHd⟩ := hhead
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  rw [facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA]
  exact facts.dt.namedRoundAction_finality_pair_of_record_guard
    (M.gradeContract n.cache) S.E S.hc (S.node v) (M.toHealing n.st.core) n.record
    (by rw [hrecord]; exact htarget)
    (by rw [hrecord]; exact htimeout)
    (by rw [hrecord]; exact hlock)
    A hA res hres P.erase hHd
    (by rw [hsigma]; exact hhj)
    (by rw [hsigma, hJeq])
    (by rw [hsigma]; exact hdebt)

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
open DecoupledConsensusModel.Statements.Instantiation
open Proofs.HealingLemmas

/-- Under the bundle along its path `W`, if the slot-`s` proposer is in the set for `S.a r + Δ`,
    `lo ≤ S.a r`, `S.a r + Δ ≤ proposal_time s ≤ horizon`, the proposal duty of slot `s`'s proposer
    can return `B` on its read along `W`, `v` is in the set for `proposal_time s`, holds `B`'s
    parent in `W`'s world strictly before `S.a r` and is flagged awake for `r`, and round `r` is in
    the proposal read's row window, then every round-`r` attestation `v`'s attestation duty can
    return on a node state of its action read along `W` is among `B`'s own attestations. -/
theorem actionAttestationAt_mem_proposal_of_parentHeldOn_f1b1 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {r : Round} {s : Slot} {B : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c) .poolAndCarried
      S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B)
    (hprop : S.E.proposer s ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E s)
    {v : V} (hv : v ∈ Hs (M.proposal_time S.E s))
    (hpre : B.parent ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.bodies)
    (hinWindow : M.inWindow S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)).core r = true)
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ ast ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract ast.cache) S.E S.hc (S.node v) ast.st ast.record ⇢ D →
      D.2.2 ∈ B.attestations := by
  intro ast hast D hD
  have hFchain := facts.dt.chainRows_iff_named_chain
  have hW := hf.onePath
  have hwmem := (p51% mem_stateBeforeTime_along₅₁) hf.sorted hW
    (Restated.Vocabulary.Execution.Setup.a M S r)
  set a := D.2.2 with ha
  set pr := M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
    (M.proposal_time S.E s) with hpr
  have hmem : ast ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)), hwmem, hast⟩
  have hdelayLe : (Restated.Vocabulary.Execution.Setup.a M S r) ≤
      (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ :=
    le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hvDelta : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ hdelay hv
  have hvA : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) := hHs _ _ hdelayLe hvDelta
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    hdelayLe.trans (hdelay.trans hhor)
  have hemitV : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a)
      (Restated.Vocabulary.Execution.Setup.a M S r) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf r hvA hactionHor hpost hA
      (fun j hj => hf.tick_outcome j _ _ hj) ast hast D hD
  have haVal : a.val_index = v :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemitV).1
  have haRound : a.round = r := by
    obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract ast.cache) S.E S.hc
      (M.toHealing ast.st.core) (M.round_of S.hc (M.toHealing ast.st.core).s)
    obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract ast.cache) S.E S.hc
      (M.toHealing ast.st.core) (M.round_of S.hc (M.toHealing ast.st.core).s) g2
    exact (Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho v r ast hmem
      D hD g2 hg2 G hG).2.1
  have hemit : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index
      (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [haVal, haRound]
    exact hemitV
  have hemitAtR : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index
      (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
    rw [haVal]
    exact hemitV
  have hnotC := Restated.emittedAttestation_not_mem_named_chain_beforeOn facts
    S Hs Xb hf hHs hvA hemitV hpre
  have hprocessed := Restated.honestAttestation_mem_processedAtProposal_after_gstOn facts
    S Hs Xb hf hHs hhor (by rw [haVal]; exact hvDelta) hprop hemitAtR hpost hdelay
  have haProcessed := Restated.exactRow_mem_namedProcessedOn facts
    S Hs Xb hf hHs (by rw [haVal]; exact hv) hemit hprocessed
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc pr
  have haSelected : a ∈ L :=
    facts.dt.mem_select_of_processed_inWindow .poolAndCarried S.hc _ haProcessed
      (by rw [haRound]; exact hinWindow) L hL
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing pr.core)
  have _hr_s1 : M.reachedStore pr := facts.sto.reachedStore_setClock S.E _ (M.proposal_time S.E s) (facts.nd.reachedStore_of_node _ (facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (M.proposal_time S.E s)) (W (strictEventIndex rho (M.proposal_time S.E s))) (hf.onePath _).1 (S.E.proposer s)))
  have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts
    (M.gradeContract c) .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) pr B hB input hinput L hL
  by_cases hchain : a ∈ M.chainRows B.parent
  · exact absurd ((hFchain B.parent a).mp hchain) hnotC
  · rw [hpay.2.2.2.2.2.2.1]
    apply facts.dt.mem_proposalRows_of_unique B.parent _ a haSelected hchain
    intro b hb hval hround
    exact Restated.honest_selected_row_uniqueOn facts S Hs Xb hf hHs s L hL haSelected hb
      (by rw [haVal]; exact hv) hval hround

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
open DecoupledConsensusModel.Internal.PhaseGrades

/-- Under the phase premises, if `rD + 2 ≤ c`,
    `vote_time (o_c + 2) ≤ x[n].time ≤ tE`, the proposers of `o_c`, `o_c + 1` and `o_c + 2` are not
    held at their confirmation times, and `P`, `P₁` and `P₂` are proposals of their reads on the
    path the execution follows, `W = Restated.runAllPath M S Sched x v₀ n`, then `P₂` is not genesis
    and its parent is `P₁`. -/
theorem windowMiddleParent_f1b1 (facts : Record.Facts M)
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
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopening₁ : S.E.proposer ((M.opening_slot S.hc c) + 1) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1)))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {P P₁ P₂ : NamedBlock V} :
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
    let wp₁ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 1)))
      (S.E.proposer (M.opening_slot S.hc c + 1))
    ∀ cp₁ : M.Cache,
      M.onPhaseTick S.E S.hc wp₁.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 1)) wp₁.cache ⇢ cp₁ →
      let pn₁ := M.mkNode
        (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (M.opening_slot S.hc c + 1))) wp₁.record cp₁
      M.proposal_with (M.gradeContract cp₁) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 1))) pn₁.st ⇢ some P₁ →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2)))
      (S.E.proposer (M.opening_slot S.hc c + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2))) pn₂.st ⇢ some P₂ →
    P₂ ≠ .genesis ∧ P₂.parent = P₁ := by
  intro R W wp cp hcp pn hP wp₁ cp₁ hcp₁ pn₁ hP₁ wp₂ cp₂ hcp₂ pn₂ hP₂
  classical
  -- `windowParent_l85d`: the parent's slot, and slots along `P₂`'s chain
  obtain ⟨hP₂ne, -, hQslot, hsl⟩ := Restated.windowParent_l85d facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hvoteHor hopening hprop2 cp hcp hP
    cp₂ hcp₂ hP₂
  obtain ⟨q, rfl⟩ : ∃ q : Round, c = q + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by
      intro h0; rw [h0] at hc; exact absurd hc (Nat.not_succ_le_zero _ ∘ fun h =>
        (Nat.le_add_left 1 _).trans ((Nat.le_succ _).trans h)))
  set o := (M.opening_slot S.hc (q + 1)) with ho
  obtain ⟨hAc, hvoteNext, hpconf, hsupp, hAcDelta, hpv⟩ :=
    Restated.interiorInstants_l85d facts S (q + 1)
  have hΔ := S.E.Δ_pos
  have hpropHor : M.proposal_time S.E (o + 2) ≤ R.horizon := hpv.trans hvoteHor
  obtain ⟨hv1, hs1, -, -, -, -⟩ := facts.sch.slot_instants_l55 S.E (o + 1)
  have hvs : M.vote_time S.E (o + 1) ≤ M.support_cutoff S.E (o + 1) := by linarith
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) ≤
      (x[n].time : Int) := hAc.trans hpropHor
  -- the family at `R_n`
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
  have hrecOn := Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hloPost := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
  -- the grade-2 awake test at every action tick whose round's window start is after `tGAT`
  have hA : ∀ k : Round, tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
      R.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) u (W j u) k :=
    fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj
  have hDq : Restated.deadlineRoundW M S tGAT gap ≤ q :=
    Nat.le_of_succ_le_succ ((Nat.le_succ _).trans hc)
  have hD : Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
      (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds =
      Restated.deadlineRoundW M S tGAT gap :=
    Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts S R tGAT gap
  obtain ⟨hopos, hgatO⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
  have hconfA : M.confirmation_time S.E o = (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (q + 1)
  have hp0 : S.E.proposer o ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) := by
    rw [← hconfA]; exact hopening
  -- the proposers' reads of `o`, `o + 1` and `o + 2`
  have hpnst : pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E o)) cp :=
    facts.nd.mkNode_st _ _ _
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R o :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hPn : M.proposal_with (M.gradeContract pn.cache) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o)) pn.st ⇢ some P := by
    rw [hpncache]
    exact hP
  have hpn₁st : pn₁.st = M.store_with_cache (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (o + 1))) cp₁ :=
    facts.nd.mkNode_st _ _ _
  have hP₁clock : M.proposal_with (M.gradeContract cp₁)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 1)))
      (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (o + 1))) ⇢ some P₁ := by
    have h := hP₁
    rw [hpn₁st, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hpn₂st : pn₂.st = M.store_with_cache (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (o + 2))) cp₂ :=
    facts.nd.mkNode_st _ _ _
  have hpn₂cache : pn₂.cache = cp₂ := facts.nd.mkNode_cache _ _ _
  have hp₂read : pn₂ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R (o + 2) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂
  have hP₂n : M.proposal_with (M.gradeContract pn₂.cache) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) pn₂.st ⇢ some P₂ := by
    rw [hpn₂cache]
    exact hP₂
  have hP₂clock : M.proposal_with (M.gradeContract cp₂)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2)))
      (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (o + 2))) ⇢ some P₂ := by
    have h := hP₂
    rw [hpn₂st, facts.dt.proposal_with_store_with_cache] at h
    exact h
  -- the SG block of round `q + 1` is `P`: one such block of `P`'s own proposer
  have hsg := Restated.sgBlock_eq_openingProposal_runAll_notHeld facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp hP
  obtain ⟨nv0, hnv0, g0, hg0, G0, hG0⟩ := (p56% exists_actionSG₅₆) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
      (S.E.proposer o)) (q + 1)
  have hG0P : G0 = P.erase := hsg _ hp0 nv0 hnv0 g0 hg0 G0 hG0
  -- every head a member can vote at `o + 1` is a descendant of `P`; first the window-start bound of
  -- round `q + 1`
  have hkq : tGAT + 1 ≤ M.early S.E S.hc (q + 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (Nat.lt_succ_of_le ((Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap).trans hDq))
  have hfirst := fun (w : V) (hw : w ∈ notHeldAt Sched (M.vote_time S.E (o + 1))) =>
    Restated.actionSGBlock_preceq_firstInteriorHead_after_GST_namedOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost (by rw [hD]; exact hDq) hAcHor hp0
      (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
        (q + 1) hkq _ j hj) hw hloPost
      hloOpen ht₀ hA
  -- the grade-1 awake test at the duty ticks of slot `o + 1`
  have hround1 : M.round_of S.hc (o + 1) = q + 1 := facts.gr.HealingLemmas_round_of_opening_succ S.hc _
  have hwin1 : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 1)) .g1 - S.E.Δ := by
    rw [hround1]
    have h2 := facts.gr.q10_early_g2_le_early_g1 S (q + 1)
    linarith
  have hvote1Hor : M.vote_time S.E (o + 1) ≤ R.horizon :=
    (hvs.trans hsupp).trans hpropHor
  have hlo1 : tGAT + 1 ≤ M.vote_time S.E (o + 1) :=
    hgatO.trans ((facts.sch.proposal_time_mono S.E (Nat.le_succ o)).trans
      (facts.sch.proposal_time_lt_vote_time S.E (o + 1)).le)
  -- every head a member can vote at `o + 1` is `P₁`, and `P ⪯ P₁`
  have hstart : (M.opening_slot S.hc) (Restated.fgSafetyProgressDeadline
      (Setup.alwaysAwake S) R (Restated.roundAt M S tGAT + S.hc.η_SG) gap
      (Setup.alwaysAwake S).extraRounds + 2) ≤ o + 1 := by
    rw [hD]
    exact (facts.gr.opening_slot_mono S hc).trans (Nat.le_succ _)
  have hstores := Restated.slotProposal_voteStoreExtends_afterDeadlineOn_i1b facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
    (Setup.timeoutDelayBound _) hpost hstart hvote1Hor hopening₁ cp₁ hcp₁ hP₁ hloPost hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
  obtain ⟨I₁, hI₁⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp₁) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (o + 1))) (M.toHealing pn₁.st.core)
  have hp1Vote : S.E.proposer (o + 1) ∈ notHeldAt Sched (M.vote_time S.E (o + 1)) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E (o + 1)) hopening₁
  have hPP₁ : Block.Preceq P.erase P₁.erase := by
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) (S.E.proposer (o + 1)))
        (M.vote_time S.E (o + 1))
    have hHP₁ : H = P₁.erase :=
      (hstores _ hp1Vote cw hcw Tr hTr I₁ hI₁).head Tr hTr L hL L' hL' H hH
    have h := hfirst _ hp1Vote cw hcw Tr hTr L hL L' hL' H hH nv0 hnv0 g0 hg0 G0 hG0
    rw [hG0P, hHP₁] at h
    exact h
  -- the cone at `o + 1`, with target `P₁`
  have hcone : Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S) R W (notHeldAt Sched)
      Finset.univ (o + 1) (fun X => Block.Preceq P₁.erase X) := by
    intro w hw hcomm
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) w) (M.vote_time S.E (o + 1))
    obtain ⟨X, hXerase, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHsXb hw (Nat.succ_pos o) hcomm
      hvote1Hor hlo1 cw hcw (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin1)
      Tr hTr L hL L' hL' H hH
    have hHP₁ : H = P₁.erase :=
      (hstores w hw cw hcw Tr hTr I₁ hI₁).head Tr hTr L hL L' hL' H hH
    exact ⟨X, by rw [hXerase, hHP₁]; exact Proofs.ModelProperties.Preceq_self _, hXrun, hXemit⟩
  -- the proposer of `o + 2` and its read
  have huRead : S.E.proposer (o + 2) ∈ notHeldAt Sched (M.proposal_time S.E (o + 2)) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop2
  have huVote1 : S.E.proposer (o + 2) ∈ notHeldAt Sched (M.vote_time S.E (o + 1)) :=
    hHs _ _ (hvs.trans hsupp) huRead
  have hheadsO := (Restated.openingAdoption_at_strongWindow_afterDeadline facts S Sched x v₀ n
    hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp
    hP).1
  have hsource := Restated.fgSource_eq_openingProposal_of_some_runAll_notHeld facts S Sched x v₀
    n hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp hP
  have hroot : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st.core).toFG)
      P.erase :=
    Restated.fgRoot_preceq_openingProposal_at_read_afterDeadlineOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost (by rw [hD]; exact hc) hheadsO hsource
      hAc (hpv.trans hvoteNext) hpropHor huRead hloPost hloOpen ht₀ hA
  have hprop1Hor : M.proposal_time S.E (o + 1) ≤ R.horizon :=
    (facts.sch.proposal_time_lt_vote_time S.E (o + 1)).le.trans hvote1Hor
  have hgat1 : tGAT + 1 ≤ M.proposal_time S.E (o + 1) :=
    hgatO.trans (facts.sch.proposal_time_mono S.E (Nat.le_succ o))
  have hP₁run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb (Nat.succ_pos o) hopening₁ hprop1Hor hgat1
    (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening₁) hwin1) cp₁ hcp₁
    hP₁clock
  have hP₁slot : P₁.slot = o + 1 :=
    Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts (Setup.alwaysAwake S) R (o + 1)
      (some P₁) ((p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf (o + 1) cp₁ hcp₁
        hP₁clock) rfl
  -- `P₁` is active at the proposer's read
  have hactiveStore : P₁.erase ∈ M.get_filtered_block_tree
      (M.toHealing
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st.core).toFG := by
    have hDread : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) ≤
        M.proposal_time S.E (o + 2) := by
      rw [hD]
      exact ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
        (hDq.trans (Nat.le_succ q))).trans hAc
    have hslotD : (M.opening_slot S.hc) (Restated.fgSafetyProgressDeadline
        (Setup.alwaysAwake S) R (Restated.roundAt M S tGAT + S.hc.η_SG) gap
        (Setup.alwaysAwake S).extraRounds) + 1 ≤ o + 1 := by
      rw [hD]
      exact Nat.succ_le_succ (facts.gr.opening_slot_mono S (hDq.trans (Nat.le_succ q)))
    have hshor1 : M.vote_time S.E (o + 1) + S.E.Δ ≤ R.horizon := by
      refine le_trans ?_ hpropHor
      linarith
    obtain ⟨T, hTrun, hTband, hTheads⟩ :=
      (p86f% exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f) facts
        (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
        (Setup.timeoutDelayBound _) hpost hDread hpropHor hslotD hpconf hshor1 huRead hloPost
        hloOpen ht₀ hA
    -- one head the proposer of `o + 2` can vote at `o + 1`: it is `P₁`
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) (S.E.proposer (o + 2)))
        (M.vote_time S.E (o + 1))
    have hHP₁ : H = P₁.erase :=
      (hstores _ huVote1 cw hcw Tr hTr I₁ hI₁).head Tr hTr L hL L' hL' H hH
    have hTH : Block.Preceq T.erase H :=
      hTheads _ huVote1 cw hcw Tr hTr L hL L' hL' H hH
    have hheadVote := Restated.voteDutyHead_mem_voteDutyStoreOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (S.E.proposer (o + 2)) (o + 1) cw hcw Tr hTr L hL L' hL' H hH
    have hHvoteT : H ∈ (W (strictEventIndex R (M.vote_time S.E (o + 1)))
        (S.E.proposer (o + 2))).st.core.T := by
      have h := hheadVote
      rw [(p60% voteStore_eq₆₀s) facts, facts.hd.Sts_setClock_core_T] at h
      exact h
    have hheadRead : H ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
        (S.E.proposer (o + 2))).st.core.T :=
      Restated.seedStore_T_subsetOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
        (S.E.proposer (o + 2)) (hvs.trans hsupp) hHvoteT
    have hmemRead := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
      (M.proposal_time S.E (o + 2))
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts
      (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
    have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      facts (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
    have hP₁read : P₁.erase ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
        (S.E.proposer (o + 2))).st.core.T := by
      rw [← hHP₁]
      exact hheadRead
    have hTP₁ : Block.Preceq T.erase P₁.erase := by
      rw [← hHP₁]
      exact hTH
    have hTP₁n := Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched)
      Finset.univ hf hTrun hP₁run hTP₁
    have hP₁body := Restated.namedBody_of_mem_storeBeforeTime_l86f facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (Finset.mem_univ (S.E.proposer (o + 2))) hP₁read hP₁run
    have hP₁view := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts
      (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
      P₁ hP₁body
    have hband : (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
          (S.E.proposer (o + 2))).st.core.h_max - 1 ≤
        ((W (strictEventIndex R (M.proposal_time S.E (o + 2)))
          (S.E.proposer (o + 2))).st.core.σ P₁.erase).h := by
      rw [hP₁view]
      exact hTband.trans (facts.cs.derive_height_mono S.E S.cfg hTP₁n)
    exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq
      facts hpc hFJ (preceq_trans_Preceq hroot hPP₁) hP₁read hband
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  have hactive : P₁.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.proposal_time S.E (o + 1 + 1)))
          (S.E.proposer (o + 1 + 1))).st.core
        (M.proposal_time S.E (o + 1 + 1)))).toFG := by
    rw [(p86f% tickStore_eq₈₆f) facts, (p60% setClock_filtered₆₀) facts]
    exact hactiveStore
  -- the proposer's anchor is an ancestor of `P`, hence compatible with `P₁`
  have hupper := Restated.actionSGBlock_preceq_proposedParent_runAll_notHeld_afterDeadline facts S
    Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc
    ((facts.sch.Protocol_vote_time_le_confirmation_time S.E o).trans (by rw [hconfA]; exact hAcHor))
    hopening cp hcp hP
  simp only [Nat.add_sub_cancel] at hupper
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer o)) (M.toHealing pn.st.core)
  have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn.cache) S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o)) (M.toHealing pn.st.core) ⇢ I := by
    rw [hpncache]
    exact hI
  obtain ⟨-, hIP⟩ := (p58% parent_preceq_of_proposal₅₈s) facts (Setup.alwaysAwake S) R o pn hpread
    hPn I hI'
  have hupperP : ∀ v ∈ notHeldAt Sched
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)),
      ∀ nq ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core)
          (M.round_of S.hc (M.toHealing nq.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core)
          (M.round_of S.hc (M.toHealing nq.st.core).s) g ⇢ B →
        Block.Preceq B P.erase := by
    intro v hv nq hnq g hg B hB
    exact preceq_trans_Preceq (hupper v hv nq hnq g hg B hB I hI) hIP
  have hrootProp : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st
        (M.proposal_time S.E (o + 2)))
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).record
        cp₂).st.core).toFG) P.erase := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(p60% setClock_fgRoot₆₀) facts]
    exact hroot
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ R.horizon := by
    have h1 := facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E (q + 1)]
    linarith
  have hpostQ : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (by
      unfold Restated.deadlineRoundW at hDq
      exact (Nat.le_succ _).trans ((Nat.le_add_right _ _).trans hDq)))
  have hgatG1 : tGAT + 1 ≤ M.domain S.E S.hc (q + 1) .g1 := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact hgatO
  have hslo : (M.opening_slot S.hc (q + 1)) + 1 ≤ o + 2 := Nat.succ_le_succ (Nat.le_succ o)
  have hshi : o + 2 < (M.opening_slot S.hc (q + 1 + 1)) := by
    have hR := S.hc.R_ge_three
    rw [ho, facts.gr.opening_slot_succ S.hc (q + 1)]
    exact Nat.add_lt_add_left (lt_of_lt_of_le (by decide) hR) _
  have hanchor := Restated.interiorProposalAnchor_preceq_of_previousCarriersOn_l85d facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hpostQ hcut hslo
    hshi hpropHor hupperP huRead cp₂ hcp₂ hrootProp
    (fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn q
      (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
        (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
          (Nat.lt_of_succ_le (Nat.le_of_succ_le_succ hc)))) u j hj) hgatG1
  have hround2 : M.round_of S.hc pn₂.st.core.s = q + 1 := by
    rw [hpn₂st, facts.nd.store_with_cache_core_s, facts.hd.Sts_setClock_core_s,
      facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  obtain ⟨A0, hA0⟩ := (p58% nodeAnchor_outcome₅₈) facts (Setup.alwaysAwake S) pn₂
    (M.round_of S.hc pn₂.st.core.s)
  have hA0' : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) pn₂
      (q + 1) ⇢ A0 := by
    have h := hA0
    rw [hround2] at h
    exact h
  have hcompat : Block.compatible A0 P₁.erase = true :=
    compatible_of_preceq_common_Preceq (preceq_trans_Preceq (hanchor A0 hA0') hPP₁)
      (Proofs.ModelProperties.Preceq_self P₁.erase)
  have hconeT := Restated.coneTarget_preceq_nextProposedParent_namedOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (Nat.succ_pos o) hlo1
    (hsupp.trans hpropHor) (hHs _ _ (hsupp.trans (facts.sch.proposal_time_le_confirmation_time
      S.E _)) hprop2) hcone hactive cp₂ hcp₂ A0 hA0 hcompat
  -- the named form, and the slots
  obtain ⟨I₂, hI₂⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp₂) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) (M.toHealing pn₂.st.core)
  have hI₂' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn₂.cache) S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) (M.toHealing pn₂.st.core) ⇢ I₂ := by
    rw [hpn₂cache]
    exact hI₂
  obtain ⟨Q, hQ, hQerase⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts
    (Setup.alwaysAwake S) R (o + 2) pn₂ hp₂read hP₂n I₂ hI₂'
  have hP₂par : P₂.parent = Q := by
    cases P₂ with
    | genesis => cases hQ
    | node p sl rt vs sp rows proposer =>
        simp only [NamedBlock.parent?] at hQ
        rw [namedBlock_parent_node]
        exact Option.some.inj hQ
  have hP₂run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb (Nat.succ_pos _) hprop2 hpropHor
    (hgatO.trans (facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)))
    (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop2)
      (by
        show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 2)) .g1 - S.E.Δ
        rw [ho, facts.gr.round_of_opening_slot_add S.hc (q + 1) (j := 2)
          (by have := S.hc.R_ge_three; omega)]
        have h2 := facts.gr.q10_early_g2_le_early_g1 S (q + 1)
        linarith)) cp₂ hcp₂
    hP₂clock
  have hQrun : Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ Q :=
    Restated.blockInRun_of_ancestorOn facts (Setup.alwaysAwake S) R W Finset.univ hP₂run
      (by rw [← hP₂par]; exact parent_namedPreceq_l85 P₂)
  have hP₁Q : NamedBlock.Preceq P₁ Q :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hP₁run
      hQrun (by rw [hQerase]; exact hconeT I₂ hI₂')
  have hQP₂ : NamedBlock.Preceq Q P₂ := by rw [← hP₂par]; exact parent_namedPreceq_l85 P₂
  refine ⟨hP₂ne, ?_⟩
  rw [hP₂par]
  by_contra hne
  have hlt := (slot_le_of_namedPreceq_l85 hsl hP₁Q hQP₂).2 (fun h => hne h.symm)
  rw [hP₂par] at hQslot
  rw [hP₁slot] at hlt
  exact absurd (lt_of_lt_of_le hlt (Nat.le_of_succ_le_succ hQslot)) (lt_irrefl _)

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

/-- For every path `W` of `rho`, if no two blocks of `rho` held by any validator along `W` collide
    on a root or carry slashable weight between their chains, then for every `i`, every body `D`
    that `v` holds in `W i` has its chain state's finalized block an ancestor of the finalized block
    of `v`'s store in `W i`. -/
theorem finalityAdvance_stateBefore_f1b1 (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.SlashableBoundOn M S rho W Finset.univ)
    (hcf : Restated.RootCollisionFreeOn M S rho W Finset.univ)
    (v : V) : ∀ i : Nat, Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S (W i v).st := by
  set rho' : Record.Run V := { rho with honest := Finset.univ } with hrho'
  have hW' : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho' W := hW
  have hsb' : Restated.Vocabulary.Execution.SlashableBound M S rho' W := hsb
  have hcf' : Restated.Vocabulary.Execution.RootCollisionFree M S rho' W := ⟨hcf.root_injective⟩
  have hRun : ∀ (i : Nat) (D : NamedBlock V), D ∈ (W i v).st.bodies →
      Restated.Vocabulary.Execution.RunBlock M S rho' W D :=
    fun i D hD => Restated.runBlock_of_stateBefore_memOn facts S W Finset.univ (Finset.mem_univ v) hD
  intro i
  induction i with
  | zero =>
      intro D hD
      have hDg : D = NamedBlock.genesis :=
        facts.ndRun.stateBefore_zero_body_eq_genesis S rho v (W 0) (hW 0).1 hD
      subst hDg
      rw [facts.csAdded.derive_named_genesis_F]
      exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)
  | succ i ih =>
      rcases (p85c% path_step₈₅c) hW i with ⟨-, hEq⟩ | ⟨e, hev, hstep⟩
      · rw [hEq]
        exact ih
      · have hcohBase : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W i v).st :=
          (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v (W i) (hW i).1).1.1.1
        have _hr : M.reachedNode (W i v) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 v
        have hmaxBase := Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBefore facts S rho i v
          (W i) (hW i).1
        have hprovBase := Restated.Vocabulary.Proofs.Bridges.namedProvenance_stateBefore facts S rho i v
          (W i) (hW i).1
        cases e with
        | wake u tt =>
            simp only [Record.worldStepOf, Set.mem_singleton_iff] at hstep
            by_cases hvu : v = u
            · subst hvu
              have hv1 : (W (i + 1) v).st = (W i v).st := by
                rw [hstep, Function.update_self]
                exact (facts.nd.wake_st_record _).1
              rw [hv1]
              exact ih
            · have hv1 : W (i + 1) v = W i v := by rw [hstep, Function.update_of_ne hvu]
              rw [hv1]
              exact ih
        | tick u tt =>
            simp only [Record.worldStepOf, Set.mem_setOf_eq] at hstep
            rcases hstep with ⟨out, hout, hEq⟩ | ⟨-, hEq⟩
            · by_cases hvu : v = u
              · subst hvu
                have hv1 : W (i + 1) v = out.1 := by rw [hEq, Function.update_self]
                rw [hv1]
                -- `advance_node_tick` covers a tick that fails the grade-1
                -- awake test itself (`facts.nd.tick_frame_of_not_awake_for_grade1`)
                refine Restated.Vocabulary.Proofs.HealingSurface.advance_node_tick facts S hW' hsb' hcf' v (W i v) tt
                  (facts.hd.coherent_clock S.E S.cfg _ tt hcohBase)
                  (by rw [facts.hd.Sts_setClock_bodies, facts.hd.setClock_core_h_max]; exact hmaxBase)
                  ((p53b% namedProvenance_setClock₅₃b) facts S _ tt hprovBase)
                  (fun D hD => hRun i D (by rw [facts.hd.Sts_setClock_bodies] at hD; exact hD)) ih
                  out hout ?_ (facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 v)
                intro D hD
                exact hRun (i + 1) D (by rw [hv1]; exact hD)
              · have hv1 : W (i + 1) v = W i v := by rw [hEq, Function.update_of_ne hvu]
                rw [hv1]
                exact ih
            · rw [hEq]
              exact ih
        | deliver u o tt =>
            simp only [Record.worldStepOf, Set.mem_setOf_eq] at hstep
            rcases hstep with ⟨n', hn', hEq⟩ | ⟨-, hEq⟩
            · by_cases hvu : v = u
              · subst hvu
                have hv1 : W (i + 1) v = n' := by rw [hEq, Function.update_self]
                rw [hv1]
                refine Restated.Vocabulary.Proofs.HealingSurface.advance_node_process facts S hW' hsb' hcf' (W i v) o
                  hcohBase hmaxBase hprovBase (hRun i) ih n' hn' ?_
                intro D hD
                exact hRun (i + 1) D (by rw [hv1]; exact hD)
              · have hv1 : W (i + 1) v = W i v := by rw [hEq, Function.update_of_ne hvu]
                rw [hv1]
                exact ih
            · rw [hEq]
              exact ih

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

/-- Under the premises read up to `tL`, if `x[N].time ≤ tL`, step `m` is the tick at a time `t` and
    `m + 1 ≤ N`, then for every validator `w` and every body `D` that `w` holds after `m` steps, the
    finalized block of `D`'s chain state is an ancestor of `w`'s finalized block after `m` steps. -/
theorem finalityAdvance_atTick_f1b1 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (N : Nat)
    {tGAT tL : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hN : (x[N].time : Int) ≤ tL)
    {m : Nat} {t : Int} (hm : Restated.tickStepAt M x m t) (hmN : m + 1 ≤ N) (w : V)
    {D : NamedBlock V} (hD : D ∈ (x[m][w].st).st.bodies) :
    Block.Preceq (M.derive_named S.E S.cfg D).F (x[m][w].st).st.core.F := by
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ N hsync hmono hawake hgst hcv hvalid
    hawm hthird hN
  have hstep := Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hm hmN w
  have hadv := Restated.finalityAdvance_stateBefore_f1b1 facts (Setup.alwaysAwake S) hf.onePath
    hf.slashableBound hf.rootCollisionFree w
    (strictEventIndex
      ({ Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t)
  rw [hstep] at hadv
  exact hadv D hD

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

/-- If `m ≤ n` and `t ≤ x[m + 1].time`, the world of `runAllPath` of the first `n` steps strictly
    before `t` is the world of `runAllPath` of the first `m` steps strictly before `t`. -/
private theorem runAllPath_strict_of_le_fsw (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat}
    (h : m ≤ n) (X X' : Finset V) {t : Int} (ht : t ≤ (x[m + 1].time : Int)) :
    Restated.runAllPath M S Sched x v n
        (strictEventIndex ({ Restated.runAll M S Sched x v n with honest := X' } : Record.Run V) t) =
      Restated.runAllPath M S Sched x v m
        (strictEventIndex ({ Restated.runAll M S Sched x v m with honest := X } : Record.Run V) t) := by
  obtain ⟨l, hl, hlate⟩ := Restated.runEvents_append_late facts S Sched x h
  have hf2 : l.filter (fun e => decide (Record.Event.time e < t)) = [] := by
    refine List.filter_eq_nil_iff.2 (fun e he => ?_)
    have hge := hlate e he
    simp only [decide_eq_true_eq, not_lt]
    rw [namedEvent_time_eq]
    exact le_trans ht hge
  have hidx : strictEventIndex ({ Restated.runAll M S Sched x v n with honest := X' } : Record.Run V) t =
      strictEventIndex ({ Restated.runAll M S Sched x v m with honest := X } : Record.Run V) t := by
    show ((Restated.runEvents M S Sched x n).filter (fun e => decide (Record.Event.time e < t))).length =
      ((Restated.runEvents M S Sched x m).filter (fun e => decide (Record.Event.time e < t))).length
    rw [hl, List.filter_append, hf2, List.append_nil]
  rw [hidx]
  have hle : strictEventIndex ({ Restated.runAll M S Sched x v m with honest := X } : Record.Run V) t ≤
      (Restated.runEvents M S Sched x m).length :=
    List.length_filter_le _ _
  exact ((p44% runAllPath_le) facts S Sched x v h hle).symm

/-- Under the premises of `finalityStepWindow_f1b1`, for every proposal `P₁` of the proposer of
    `o_c + 1` at its read on the path with `h(T_0) ≤ h_j(P₁)`, if every choice of one round-`c`
    action head on the path for each validator not held at `S.a c` gives `P₁`'s block, then for
    every proposal `P` of `o_c` and `P₂` of `o_c + 2` at their proposers' reads on the path, `J(P₁)`
    is an ancestor of `F(P₂)`. -/
private theorem finalityStep_justified_preceq_finalized_fsw (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V)
    {tGAT tE tL : Int} {gap : Nat}
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
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
    (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopening₁ : S.E.proposer ((M.opening_slot S.hc c) + 1) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1)))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {n : Nat} (hvoteN : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    {P₁ : NamedBlock V}
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P₁).h_j) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp₁ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 1)))
      (S.E.proposer (M.opening_slot S.hc c + 1))
    ∀ cp₁ : M.Cache,
      M.onPhaseTick S.E S.hc wp₁.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 1)) wp₁.cache ⇢ cp₁ →
      let pn₁ := M.mkNode
        (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (M.opening_slot S.hc c + 1))) wp₁.record cp₁
      M.proposal_with (M.gradeContract cp₁) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 1))) pn₁.st ⇢ some P₁ →
    (∀ head : V → Block V,
      (∀ v ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M S c),
        ∃ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c,
        Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract nv.cache)
          S.E S.hc (M.toHealing nv.st.core) ⇢ head v) →
      Restated.HonestActionHeadsAtStrongWindow M S Sched x v₀ n c (some P₁) head) →
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).cache ⇢ cp →
    ∀ P : NamedBlock V,
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c)))
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).st (M.proposal_time S.E (M.opening_slot S.hc c)))
          (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).record cp).st ⇢ some P →
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 2)) (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).cache ⇢ cp₂ →
    ∀ P₂ : NamedBlock V,
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2)))
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).st (M.proposal_time S.E (M.opening_slot S.hc c + 2)))
          (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).record cp₂).st ⇢ some P₂ →
    Block.Preceq (M.derive_named S.E S.cfg P₁).J (M.derive_named S.E S.cfg P₂).F := by
  intro R W wp₁ cp₁ hcp₁ pn₁ hP₁ hheads cp hcp P hP cp₂ hcp₂ P₂ hP₂
  classical
  set o := (M.opening_slot S.hc c) with ho
  -- the horizon of `R_n` is inside `[tGAT, tL]`
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL :=
    hlen.trans hEL
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL :=
    Restated.healingLength_le_of_kit_l76 facts S hlenL
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap
      (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tL := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  obtain ⟨hAc, -, -, -, hAcDelta, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hpropHor : M.proposal_time S.E (o + 2) ≤ R.horizon := hpv.trans hvoteN
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[n].time : Int) := hAc.trans hpropHor
  obtain ⟨hopos, hgatO⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
  have hconfA : M.confirmation_time S.E o = (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S c
  have hP₂clock := hP₂
  rewrite [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache] at hP₂clock
  have hB₂mem := (p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf (o + 2) cp₂ hcp₂
    hP₂clock
  have hP₁clock : M.proposal_with (M.gradeContract cp₁)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 1)))
      (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (o + 1))) ⇢ some P₁ := by
    have h := hP₁
    rewrite [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache] at h
    exact h
  -- `P₂`'s parent is `P₁`
  obtain ⟨hP₂ne, hpar⟩ := Restated.windowMiddleParent_f1b1 facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hvoteN hopening hopening₁ hprop2
    cp hcp hP cp₁ hcp₁ hP₁ cp₂ hcp₂ hP₂
  -- `J(P₁) ⪯ F(P₂)`
  by_cases hdebt : (M.derive_named S.E S.cfg P₁).h_F <
      (M.derive_named S.E S.cfg P₁).h_j
  · -- the finality pairs, carried by `P₂`
    have hH0 : (M.derive_named S.E S.cfg P₁).h_j ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hdebt)
    have hprop1Hor : M.proposal_time S.E (o + 1) ≤ R.horizon :=
      (facts.sch.proposal_time_mono S.E (Nat.le_succ (o + 1))).trans hpropHor
    have hgat1 : tGAT + 1 ≤ M.proposal_time S.E (o + 1) :=
      hgatO.trans (facts.sch.proposal_time_mono S.E (Nat.le_succ o))
    -- the grade-1 awake test of the proposer of `o + 1`
    have hwinC : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 1)) .g1 - S.E.Δ := by
      rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc c]
      have hk := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
        (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
        (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
          (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_succ _).trans hc)))
      have h2 := facts.gr.q10_early_g2_le_early_g1 S c
      linarith
    have hP₁run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
      Finset.univ hf hHs hHsXb (Nat.succ_pos o) hopening₁ hprop1Hor hgat1
      (fun j hj => hf.tick_outcome j _ _ hj)
      (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
        (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening₁) hwinC) cp₁ hcp₁
      hP₁clock
    obtain ⟨hlock, hclear⟩ := Restated.finalityRecord_clear_ofRunBlock_f1b1 facts S Sched x v₀
      n hlen hEL hsync hmono hawake hgst hcv hvalid hawm hthird hcom hrec htd hA0 hnW hP₁run hH0
      htop
    have hbot := Restated.belowOneThird_runAll_notHeld_inPhase facts S Sched x n tL hthird hn
    have hvA : ∀ v ∈ R.honest,
        v ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S c)) :=
      fun v hv => hHs _ _ hAcN hv
    have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)
    -- for every validator: one node state of its action read on the path, one action head
    -- and one attestation computed on it
    have hex : ∀ v : V,
        ∃ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c,
        ∃ H : Block V,
          Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract nv.cache)
            S.E S.hc (M.toHealing nv.st.core) ⇢ H ∧
          ∃ D, M.duties_attest_with (M.gradeContract nv.cache) S.E S.hc
            ((Setup.alwaysAwake S).node v) nv.st nv.record ⇢ D := by
      intro v
      obtain ⟨nv, hnv, -⟩ := (p56% exists_actionSG₅₆) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c
      obtain ⟨H, hH⟩ := (p50% actionHeadWith_nonempty₅₀) facts (M.gradeContract nv.cache) S.E S.hc
        (M.toHealing nv.st.core)
      obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc
        ((Setup.alwaysAwake S).node v) nv.st nv.record
      exact ⟨nv, hnv, H, hH, D, hD⟩
    choose nvf hnvf Hf hHf Df hDf using hex
    have hheadEq : ∀ v ∈ R.honest, Hf v = P₁.erase :=
      fun v hv => hheads Hf (fun u _ => ⟨nvf u, hnvf u, hHf u⟩) P₁ rfl v (hvA v hv)
    -- the finality pairs
    have hfinality : ∀ v ∈ R.honest,
        (Df v).2.2.finality_pair =
          some ⟨(M.derive_named S.E S.cfg P₁).h_j,
            (M.derive_named S.E S.cfg P₁).J.root⟩ := by
      intro v hv
      obtain ⟨htgt, htmo⟩ := hclear v
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) (hvA v hv)
      refine Restated.actionAttestation_finality_pairOn_f1b1 facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf (Finset.mem_univ v) hP₁run rfl rfl hdebt ?_ htmo ?_
        (nvf v) (hnvf v) (by rw [← hheadEq v hv]; exact hHf v) (Df v) (hDf v)
      · refine (Option.eq_none_or_eq_some _).imp id ?_
        rintro ⟨T, h⟩
        rw [h]
        exact congrArg some (htgt T h)
      · refine (Option.eq_none_or_eq_some _).imp id ?_
        rintro ⟨L, h⟩
        rw [h]
        exact congrArg some (hlock v _ L h)
    -- the rows are carried by `P₂`
    have hRpos : 2 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
    have hslo : (M.opening_slot S.hc c) + 1 ≤ o + 2 := Nat.succ_le_succ (Nat.le_succ o)
    have hshi : o + 2 < (M.opening_slot S.hc (c + 1)) := by
      rw [facts.gr.opening_slot_succ]
      exact Nat.add_lt_add_left hRpos _
    have hinWindow : M.inWindow S.hc
        (M.ns_setClock S.E
          (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st
          (M.proposal_time S.E (o + 2))).core c = true := by
      rw [facts.dt.inWindow_iff, facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time,
        facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi]
      exact ⟨Nat.sub_le c _, le_rfl⟩
    have hprop' : S.E.proposer (o + 2) ∈
        notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ) :=
      hHs _ _ (hAcDelta.trans (facts.sch.proposal_time_le_confirmation_time S.E _)) hprop2
    have hpostA : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
      hgatO.trans ((facts.sch.proposal_time_le_confirmation_time S.E o).trans (le_of_eq hconfA))
    have hcoverage : ∀ v ∈ R.honest,
        let a := (Df v).2.2
        (a ∈ Protocol.named_chain_attestations P₂.parent ∧
            v ∈ M.finalize (M.derive_named S.E S.cfg P₂.parent)) ∨
          a ∈ P₂.attestations := by
      intro v hv
      refine Or.inr ?_
      have hvProp : v ∈ notHeldAt Sched (M.proposal_time S.E (o + 2)) :=
        hHs _ _ hpropHor hv
      have hpre : P₂.parent ∈
          (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c))
            v).st.bodies := by
        rw [hpar]
        have hmem := Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith_mem_storeBeforeTime
          facts (Setup.alwaysAwake S) v c _ hmemA (nvf v) (hnvf v) _ (hHf v)
        rw [hheadEq v hv] at hmem
        exact Restated.namedBody_of_mem_storeBeforeTime_l86f facts (Setup.alwaysAwake S)
          (notHeldAt Sched) Finset.univ hf (Finset.mem_univ v) hmem hP₁run
      exact Restated.actionAttestationAt_mem_proposal_of_parentHeldOn_f1b1 facts
        (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs cp₂ hcp₂ hP₂clock hprop'
        hpropHor hpostA hAcDelta hvProp hpre hinWindow
        (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn c
          (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
            (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
            (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
              (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_succ _).trans hc)))) v j hj)
        (nvf v) (hnvf v) (Df v) (hDf v)
    -- the finality write
    have hrows : ∀ v ∈ R.honest, (Df v).2.2 ∈
        Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt M (Setup.alwaysAwake S) R v c :=
      fun v _ => ⟨nvf v, ⟨_, hmemA, hnvf v⟩, (Df v).1, (Df v).2.1, hDf v⟩
    have hfinAt := Restated.Vocabulary.Proofs.HealingSurface.namedFinalizedAt_of_actionRows facts
      (Setup.alwaysAwake S) hbot (r := c) (s := o + 2)
      (hJ := (M.derive_named S.E S.cfg P₁).h_j)
      (TJ := (M.derive_named S.E S.cfg P₁).J.root)
      (J := (M.derive_named S.E S.cfg P₁).J) hB₂mem (fun v => (Df v).2.2) hrows hcoverage
      (by rw [hpar]; rfl) (by rw [hpar]; rfl) rfl (by rw [hpar]; exact hdebt) hfinality
    have hF₂ : (M.derive_named S.E S.cfg P₂).F =
        (M.derive_named S.E S.cfg P₁).J := hfinAt.1
    rw [hF₂]
    exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · -- no finality pair: `J(P₁) ⪯ F(P₁)`, and `F(P₂)` is `F(P₁)` or `J(P₁)`
    have hJF₁ := facts.csAdded.justified_preceq_finalized_of_le_f1b1 S.E S.cfg P₁
      (Nat.le_of_not_lt hdebt)
    rcases facts.csAdded.derive_named_F_cases S.E S.cfg hP₂ne with h | h
    · rw [h, hpar]; exact hJF₁
    · rw [h, hpar]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)

/-- Under the premises of `finalityStepWindow_f1b1` that name no proposal of `o_c + 1`, for every
    proposal `P` of `o_c` and `P₂` of `o_c + 2` at their proposers' reads on the path with `P` an
    ancestor of `P₂`: after every step `j` with `vote_time (o_c + 2) ≤ x[j].time`, every validator
    not held at `vote_time (o_c + 2)` has `F(P₂)` as an ancestor of its finalized block. -/
private theorem finalityStep_afterTick_fsw (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V)
    {tGAT tE tL : Int} {gap : Nat}
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
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
    (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopening₁ : S.E.proposer ((M.opening_slot S.hc c) + 1) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1)))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {n : Nat} (hvoteN : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).cache ⇢ cp →
    ∀ P : NamedBlock V,
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c)))
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).st (M.proposal_time S.E (M.opening_slot S.hc c)))
          (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))).record cp).st ⇢ some P →
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 2)) (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).cache ⇢ cp₂ →
    ∀ P₂ : NamedBlock V,
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2)))
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).st (M.proposal_time S.E (M.opening_slot S.hc c + 2)))
          (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2))) (S.E.proposer (M.opening_slot S.hc c + 2))).record cp₂).st ⇢ some P₂ →
    NamedBlock.Preceq P P₂ →
    ∀ j : Nat, M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[j].time : Int) →
      ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) + 2)),
        Block.Preceq (M.derive_named S.E S.cfg P₂).F (x[j][w].st).st.core.F := by
  intro R W cp hcp P hP cp₂ hcp₂ P₂ hP₂ hPP₂ j hj w hw
  classical
  set o := (M.opening_slot S.hc c) with ho
  -- the horizon of `R_n` is inside `[tGAT, tL]`
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL :=
    hlen.trans hEL
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL :=
    Restated.healingLength_le_of_kit_l76 facts S hlenL
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap
      (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tL := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  obtain ⟨hAc, -, -, -, hAcDelta, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hpropHor : M.proposal_time S.E (o + 2) ≤ R.horizon := hpv.trans hvoteN
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[n].time : Int) := hAc.trans hpropHor
  obtain ⟨hopos, hgatO⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
  have hconfA : M.confirmation_time S.E o = (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S c
  -- the tick at `M.vote_time (o + 2)`
  have hvpos : 0 < M.vote_time S.E (o + 2) := by
    have hg0 := S.E.t_GST_nonneg
    have := hgatO.trans ((facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)).trans hpv)
    linarith
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd hvpos
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  have hmn : m + 1 ≤ n := by
    by_contra hlt
    have hle := Restated.time_mono facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hlt))
    have hle' : (x[n].time : Int) ≤ (x[m].time : Int) := by exact_mod_cast hle
    linarith
  have hmj : m ≤ j := by
    by_contra hlt
    have hle := Restated.time_mono facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hlt))
    have hle' : (x[j].time : Int) ≤ (x[m].time : Int) := by exact_mod_cast hle
    linarith
  -- the worlds of the path of `R_{m + 1}` before the two proposal instants are those of `W`
  have hm2 : M.vote_time S.E (o + 2) ≤ (x[m + 1 + 1].time : Int) := by
    have hle := Restated.time_mono facts S Sched x (Nat.le_succ (m + 1))
    have hle' : (x[m + 1].time : Int) ≤ (x[m + 1 + 1].time : Int) := Int.ofNat_le.mpr hle
    rw [hm1] at hle'
    exact hle'
  have e0 : W (strictEventIndex R (M.proposal_time S.E o)) = _ :=
    runAllPath_strict_of_le_fsw facts S Sched x v₀ hmn (notHeldAt Sched (x[m + 1].time : Int)) _
      (((facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)).trans hpv).trans hm2)
  have e2 : W (strictEventIndex R (M.proposal_time S.E (o + 2))) = _ :=
    runAllPath_strict_of_le_fsw facts S Sched x v₀ hmn (notHeldAt Sched (x[m + 1].time : Int)) _
      (hpv.trans hm2)
  have hcp' := hcp
  have hP' := hP
  have hcp₂' := hcp₂
  have hP₂' := hP₂
  rw [e0] at hcp' hP'
  rw [e2] at hcp₂' hP₂'
  obtain ⟨hbody, -⟩ := Restated.windowProposal_held_atTick_l85d facts S Sched x v₀ hsync hmono
    hawake hgst hcv hvalid hawm hthird hcom hrec hc hm le_rfl (hvoteN.trans hn) hopening hprop2
    hPP₂ hw cp hcp' hP' cp₂ hcp₂' hP₂'
  have hadv := Restated.finalityAdvance_atTick_f1b1 facts S Sched x v₀ n hsync hmono hawake hgst
    hcv hvalid hawm hthird hn hm hmn w hbody
  exact preceq_trans_Preceq hadv (Restated.F_mono facts S Sched x w hmj)

/-- Under the phase premises, for a round `c` with `rD + 2 ≤ c` whose
    proposers of `o_c`, `o_c + 1` and `o_c + 2` are not held at their slots' confirmation times, and
    for every proposal `P₁` of the proposer of `o_c + 1` at its read on the path the execution
    follows with `h(T_0) ≤ h_j(P₁)`: if, for every choice of one round-`c` action head on that path
    for each validator not held at `S.a c`, each chosen head is `P₁`'s block, then after every step
    `j` with `vote_time (o_c + 2) ≤ x[j].time`, every validator not held at `vote_time (o_c + 2)`
    has `J(P₁)` as an ancestor of its finalized block. -/
theorem finalityStepWindow_f1b1 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V)
    {tGAT tE tL : Int} {gap : Nat}
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
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
    (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopening₁ : S.E.proposer ((M.opening_slot S.hc c) + 1) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1)))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {n : Nat} (hvoteN : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    {P₁ : NamedBlock V}
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P₁).h_j) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp₁ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 1)))
      (S.E.proposer (M.opening_slot S.hc c + 1))
    ∀ cp₁ : M.Cache,
      M.onPhaseTick S.E S.hc wp₁.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 1)) wp₁.cache ⇢ cp₁ →
      let pn₁ := M.mkNode
        (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (M.opening_slot S.hc c + 1))) wp₁.record cp₁
      M.proposal_with (M.gradeContract cp₁) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 1))) pn₁.st ⇢ some P₁ →
    (∀ head : V → Block V,
      (∀ v ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M S c),
        ∃ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c,
        Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract nv.cache)
          S.E S.hc (M.toHealing nv.st.core) ⇢ head v) →
      Restated.HonestActionHeadsAtStrongWindow M S Sched x v₀ n c (some P₁) head) →
    ∀ j : Nat, M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[j].time : Int) →
      ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) + 2)),
        Block.Preceq (M.derive_named S.E S.cfg P₁).J (x[j][w].st).st.core.F := by
  intro R W wp₁ cp₁ hcp₁ pn₁ hP₁ hheads j hj w hw
  classical
  set o := (M.opening_slot S.hc c) with ho
  -- the horizon of `R_n` is inside `[tGAT, tL]`
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL :=
    hlen.trans hEL
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL :=
    Restated.healingLength_le_of_kit_l76 facts S hlenL
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap
      (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tL := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  obtain ⟨hAc, -, -, -, hAcDelta, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hpropHor : M.proposal_time S.E (o + 2) ≤ R.horizon := hpv.trans hvoteN
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[n].time : Int) := hAc.trans hpropHor
  obtain ⟨hopos, hgatO⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
  have hconfA : M.confirmation_time S.E o = (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S c
  -- one proposal `P` of the opening slot and one proposal `P₂` of `o + 2` on the path
  obtain ⟨cp, hcp⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).st.core.toHealing
    (M.proposal_time S.E o)
    (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).cache
  obtain ⟨p0, hPclock⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer o))
    (M.ns_setClock S.E (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).st
      (M.proposal_time S.E o))
  obtain ⟨P, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts
    (Setup.alwaysAwake S) R o p0
    ((p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf o cp hcp hPclock)
  have hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).st
        (M.proposal_time S.E o))
        (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).record cp).st ⇢ some P := by
    rewrite [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
    exact hPclock
  obtain ⟨cp₂, hcp₂⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st.core.toHealing
    (M.proposal_time S.E (o + 2))
    (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).cache
  obtain ⟨p2, hP₂clock⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp₂)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (o + 2)))
    (M.ns_setClock S.E
      (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st
      (M.proposal_time S.E (o + 2)))
  have hB₂mem := (p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf (o + 2) cp₂ hcp₂
    hP₂clock
  obtain ⟨P₂, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts
    (Setup.alwaysAwake S) R (o + 2) p2 hB₂mem
  have hP₂ : M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st
        (M.proposal_time S.E (o + 2)))
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).record
        cp₂).st ⇢ some P₂ := by
    rewrite [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
    exact hP₂clock
  have hPP₂ : NamedBlock.Preceq P P₂ :=
    namedPreceq_trans_l85 (Restated.windowParent_l85d facts S Sched x v₀ n hsync hmono hawake
      hgst hcv hvalid hawm hthird hn hcom hrec hc hvoteN hopening hprop2 cp hcp hP cp₂ hcp₂
      hP₂).2.1 (parent_namedPreceq_l85 P₂)
  exact preceq_trans_Preceq
    (finalityStep_justified_preceq_finalized_fsw facts S Sched x v₀ hlen hEL hsync hmono hawake hgst hcv
      hvalid hawm hthird hcom hrec htd hA0 hc hopening hopening₁ hprop2 hvoteN hnW htop
      cp₁ hcp₁ hP₁ hheads cp hcp P hP cp₂ hcp₂ P₂ hP₂)
    (finalityStep_afterTick_fsw facts S Sched x v₀ hlen hEL hsync hmono hawake hgst hcv
      hvalid hawm hthird hcom hrec htd hA0 hc hopening hopening₁ hprop2 hvoteN hnW
      cp hcp P hP cp₂ hcp₂ P₂ hP₂ hPP₂ j hj w hw)

/-- Under the premises of `finalityStepWindow_f1b1` without the condition on action heads, for every
    proposal `P₁` of the proposer of `o_c + 1` at its read on the path the execution follows with
    `h(T_0) ≤ h_j(P₁)`: after every step `j` with `vote_time (o_c + 2) ≤ x[j].time`, every validator
    not held at `vote_time (o_c + 2)` has `J(P₁)` as an ancestor of its finalized block. -/
theorem finalityStepWindow_joined_f1b1 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V)
    {tGAT tE tL : Int} {gap : Nat}
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
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
    (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopening₁ : S.E.proposer ((M.opening_slot S.hc c) + 1) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1)))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {n : Nat} (hvoteN : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    {P₁ : NamedBlock V}
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P₁).h_j) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp₁ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 1)))
      (S.E.proposer (M.opening_slot S.hc c + 1))
    ∀ cp₁ : M.Cache,
      M.onPhaseTick S.E S.hc wp₁.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 1)) wp₁.cache ⇢ cp₁ →
      let pn₁ := M.mkNode
        (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (M.opening_slot S.hc c + 1))) wp₁.record cp₁
      M.proposal_with (M.gradeContract cp₁) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 1))) pn₁.st ⇢ some P₁ →
    ∀ j : Nat, M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[j].time : Int) →
      ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) + 2)),
        Block.Preceq (M.derive_named S.E S.cfg P₁).J (x[j][w].st).st.core.F := by
  intro R W wp₁ cp₁ hcp₁ pn₁ hP₁
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL :=
    hlen.trans hEL
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL :=
    Restated.healingLength_le_of_kit_l76 facts S hlenL
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap
      (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tL := hnW.trans hWE
  obtain ⟨hAc, -, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[n].time : Int) :=
    hAc.trans (hpv.trans hvoteN)
  exact Restated.finalityStepWindow_f1b1 facts S Sched x v₀ hlen hEL hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hrec htd hA0 hc hopening hopening₁ hprop2 hvoteN hnW htop
    cp₁ hcp₁ hP₁
    (Restated.honestActionHeadsAtStrongWindow_f1b2 facts S Sched x v₀ n hsync hmono hawake hgst
      hcv hvalid hawm hthird hn hcom hrec hc hAcN hopening hopening₁ cp₁ hcp₁ (some P₁) hP₁)

end

end DecoupledConsensusModel.Sts.Restated
