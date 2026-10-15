import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_77
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_78UpTo
import Proofs.Claims.Restated.Claim13beRoute3_79
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryGenuineClearNextVote
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_79
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The second-slot cone over an honest SG block, with synchrony up to the third slot

Each theorem here is the theorem of the same name without `_upTo`, stated over a model
`M : Record.Model V` and its facts, with synchrony assumed only up to the confirmation instant of
the switch round's third slot.
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
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p77% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_77)
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`, source
    round `rW`, and synchrony assumed only up to `x[N].time`, the confirmation instant of slot
    `opening_slot rW + 2`: for a validator `v'` in `notHeldAt Sched` at `S.a rW`, a node state `n`
    of its round-`rW` action read whose live confirmation satisfies `GenuineConfirmation` for the
    opening slot, and a block `G` the SG vote selector can return at `n` that is an ancestor of that
    live confirmation, `T` and `G` are on one chain. -/
theorem checkpoint_compatible_clearSG_at_sourceRound_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round = Restated.switchRound M S tE)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    (hlive : ∃ C : Block V,
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
        ((M.opening_slot S.hc (Restated.switchRound M S tE))) C ∧
      C = n.live_confirmed)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hclear : Block.Preceq G n.live_confirmed) :
    Block.compatible T.erase G = true := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨-, hloVote, hloPrevA, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW.le)
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [← harW]
    exact hloVote
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
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
  obtain ⟨C, hgen, hCeq⟩ := hlive
  obtain ⟨c, hc, st, -, rfl⟩ := hnA
  rw [facts.nd.mkNode_cache] at hgen
  have hc' : M.onPhaseTick S.E S.hc
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core.toHealing
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').cache ⇢ c := hc
  rw [hSc] at hc' hgen
  have hwinW : tGAT + 1 ≤ M.early S.E S.hc
      (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc]
    have h0 := Restated.lo_le_early_g2_sub_delta_of_opening facts S hapos hlo harW.le
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (Restated.switchRound M S tE)
    have hΔ := S.E.Δ_pos
    linarith
  obtain ⟨y, hy, -, hCy⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hv') hoPos hpostVote
      hconfHor c hc' hgen
      (fun z _ hz j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
        (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz) hwinW)
  have hyVote : y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
    ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  have hCH : Block.Preceq C H := hCy cc hcc Tr hTr L hL L' hL' H hH
  have hSGC : Block.Preceq G C := by
    rw [hCeq]
    exact hclear
  have hTCfg : Block.Preceq T.erase Cfg.erase := by
    rw [hreg.seed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  rcases hsplit with ⟨Ca, hCa, -, -, -, hCfgCa⟩ | hCfgQ
  · -- case: `Cfg` is a clear block, an ancestor of the confirmation `Ca` (satisfying `GenuineConfirmation`)
    have hsigner : a.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := by
      have h := hreg.seed.signerHonest
      rw [hreg.seed.actionTime_eq, harW] at h
      exact h
    have hpostProp : tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
      hloPrevA.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
        (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
          (by rw [← harW]; exact Nat.sub_lt hapos Nat.one_pos)))
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
    rw [harW, hSc] at hca' hCa'
    have hcomp := Restated.sameSlot_genuine_compatible_after_gstOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb
      (show v' ∈ notHeldAt Sched
          (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) by
        rw [← hSc]; exact hv')
      (show a.val_index ∈ notHeldAt Sched
          (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) by
        rw [← hSc]; exact hsigner) hpostProp hconfHor c hc' hgen ca hca' hCa'
    have hTCa : Block.Preceq T.erase Ca := preceq_trans_Preceq hTCfg hCfgCa
    rcases compatible_cases hcomp with hCCa | hCaC
    · exact compatible_of_preceq_common_Preceq hTCa (preceq_trans_Preceq hSGC hCCa)
    · exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hTCa hCaC) hSGC
  · -- case: `Cfg` is the selected grade-2 block
    rw [← hCfgQ] at hoQ
    have hyA : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc a.round))) := by
      rw [harW]
      exact hyVote
    have hCfgy := hreg.seed.selectedSource_preceq_openingHead_of_namedFrame_history facts hf hHs
      hHsXb hX hXXb hreg.crossing hreg.frame hreg.ready hna hoQ hyA hlo
    rw [harW] at hCfgy
    have hCfgH : Block.Preceq Cfg.erase H := hCfgy cc hcc Tr hTr L hL L' hL' H hH
    exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hTCfg hCfgH)
      (preceq_trans_Preceq hSGC hCH)

end

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`, a
    source round at or before `rW`, `topHonestRow` at the tick step `n₀` of `S.a rW` at most `T`'s
    height, and synchrony assumed only up to `x[N].time`: for a validator `v'` in `notHeldAt Sched`
    at `S.a rW`, a node state `n` of its round-`rW` action read whose live confirmation satisfies
    `GenuineConfirmation` for the opening slot, and a block `G` the SG vote selector can return at
    `n` that is an ancestor of that live confirmation, `T` and `G` are on one chain. -/
theorem checkpoint_compatible_clearSG_at_switchRound_le_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    (hlive : ∃ C : Block V,
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
        ((M.opening_slot S.hc (Restated.switchRound M S tE))) C ∧
      C = n.live_confirmed)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hclear : Block.Preceq G n.live_confirmed) :
    Block.compatible T.erase G = true := by
  rcases Nat.lt_or_ge a.round (Restated.switchRound M S tE) with hlt | hge
  · exact Restated.checkpoint_compatible_clearSG_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv
      hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop (Nat.succ_le_of_lt hlt) hv' hnA hlive
      hA2 hG hclear
  · exact Restated.checkpoint_compatible_clearSG_at_sourceRound_upTo facts S Sched x v hsync hmono hawake hgst hcv
      hvalid hawm hthird hcom hlen htd hN hreg (le_antisymm harW hge) hv' hnA hlive hA2 hG hclear

end

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and
    synchrony assumed only up to `x[N].time`: for a node state `n` of `v'`'s round-`rW` action read
    with `T ⪯ n.live_confirmed` and a block `G` the SG vote selector can return at `n`, for every
    validator `u` in `notHeldAt Sched` at the vote instant of slot `opening_slot rW` and every run
    block `Hn` erasing to a head `u`'s vote read can compute and descending from `n.live_confirmed`,
    every validator `w` in `notHeldAt Sched` at the next slot's vote instant whose FG root at its
    vote store is an ancestor of `G` has `h_max ≤ h(Hn) + 1` at that store. -/
theorem hmax_at_secondSlot_of_checkpointPreceqLive_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    {v' : V}
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hTlive : Block.Preceq T.erase n.live_confirmed) :
    ∀ u ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))),
      ∀ cu : M.Cache, M.onPhaseTick S.E S.hc
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) u).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) u).cache ⇢ cu →
      let nu := M.mkNode
        (M.ns_setClock S.E
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) u).st
          (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE))))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) u).record cu
      ∀ Tu : Finset (Block V), M.voter_filtered_block_tree S.E nu.st.core nu.st.core.s ⇢ Tu →
      ∀ Lu : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore nu.st.core.s ⇢ Lu →
      ∀ Lu' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore nu.st.core.s ⇢ Lu' →
      ∀ Hu : Block V, M.get_head_in_tree_with_layer (M.gradeContract nu.cache) S.E S.hc
          (M.toHealing nu.st.core) Tu Lu Lu' (nu.st.core.s - 1) ⇢ Hu →
      ∀ Hn : NamedBlock V,
      Hn.erase = Hu →
      Restated.RunBlockOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) Finset.univ Hn →
      Block.Preceq n.live_confirmed Hn.erase →
      ∀ w ∈ notHeldAt Sched
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
        Block.Preceq (M.get_fg_root
            (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
              ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))).toFG) G →
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
              ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)).h_max ≤
            (M.derive_named S.E S.cfg Hn).h + 1 := by
  intro u hu cu hcu nu Tu hTu Lu hLu Lu' hLu' Hu hHu Hn hHerase hHrun hLH w hw _
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  have hTrun := (hreg.checkpoint_runBlock facts hf hHsXb).1
  have hTH : Block.Preceq T.erase Hn.erase := preceq_trans_Preceq hTlive hLH
  have hTHh : (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg Hn).h :=
    facts.cs.derive_height_mono S.E S.cfg
      (Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hTrun hHrun hTH)
  have hvote := Restated.vote_time_openingSucc_lt_action_l78 facts S (Restated.switchRound M S tE)
  have hthor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact le_trans (le_of_lt (Int.lt_add_of_pos_right _ S.E.Δ_pos))
      (Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_succ _))
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hrow : (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.h_max ≤
      Restated.topHonestRow M S Sched x n₀ + 1 := by
    by_cases hlarge : 1 < (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.h_max
    · obtain ⟨b, tb, hb, hemit, htb, hrowb, -⟩ :=
        Restated.frontier_confirmationWitnessOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
          hHs hHsXb (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hthor hlarge
      obtain ⟨k, -, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hemit
      obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hk
      have hkn : k + 1 ≤ n₀ + 1 := by
        by_contra hcon
        have hmono' : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[k + 1].time : Nat) : Int) := by
          exact_mod_cast Restated.time_mono facts S Sched x (by omega)
        have : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ tb := by
          rw [← hn₀1, ← hk1]; exact hmono'
        linarith
      have hbk : b.val_index ∈ Finset.univ \ Sched.adv (x[k + 1].time : Int) := by
        rw [hk1]
        exact hHs _ _ htb.le hb
      have hhon : Restated.HonestThrough M Sched x (k + 1) b.val_index :=
        Restated.honestThrough_of_mem_notHeld facts S Sched x (k + 1) hmono _ hbk
      obtain ⟨entry, tmo, hpair⟩ := heightPair_vote_of_height_l72 hrowb
      have hle := Restated.honestRow_le_topHonestRow facts S Sched x hvalid.toUnforgeability
        ⟨b.val_index, k + 1, b, entry, tmo, hkn, hhon, rfl, hsent, hpair⟩
      exact Nat.sub_le_iff_le_add.mp hle
    · exact (Nat.le_of_not_lt hlarge).trans (Nat.le_add_left 1 _)
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, (p77% tickStore_h_max₇₇) facts]
  exact hrow.trans (Nat.add_le_add_right (htop.trans hTHh) 1)

end

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`,
    synchrony assumed only up to `x[N].time`, and the round-`(rW − 1)` SG blocks ancestors of the
    opening-slot votes of `rW` (`hP`): for a validator `v'` in `notHeldAt Sched` at `S.a rW`, a node
    state `n` of its round-`rW` action read whose live confirmation satisfies `GenuineConfirmation`
    for the opening slot, and a block `G` the SG vote selector can return at `n` that is an ancestor
    of that live confirmation and a descendant of `T`, every anchor of the vote read at slot
    `opening_slot rW + 1` of every validator in `notHeldAt Sched` at that slot's vote instant is on
    one chain with `G`. -/
theorem anchor_compatible_clearSG_at_secondSlot_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    (hlive : ∃ C : Block V,
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
        ((M.opening_slot S.hc (Restated.switchRound M S tE))) C ∧
      C = n.live_confirmed)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hclear : Block.Preceq G n.live_confirmed)
    (hTC : Block.Preceq T.erase G) :
    ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.toHealing
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).cache ⇢ cw →
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S)
          (M.mkNode
            (M.ns_setClock S.E
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw).st.core.s) ⇢ A →
        Block.compatible A G = true := by
  intro w hw cw hcw A hA
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
  obtain ⟨-, hloVote, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW)
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    hloVote.trans (facts.sch.vote_time_mono_slots S.E (facts.gr.opening_slot_mono S harW))
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  obtain ⟨C, hgen, hCeq⟩ := hlive
  obtain ⟨c, hc, st, -, rfl⟩ := hnA
  rw [facts.nd.mkNode_cache] at hgen
  have hc' : M.onPhaseTick S.E S.hc
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core.toHealing
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').cache ⇢ c := hc
  rw [hSc] at hc' hgen
  have hwinW : tGAT + 1 ≤ M.early S.E S.hc
      (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc]
    have h0 := Restated.lo_le_early_g2_sub_delta_of_opening facts S hapos hlo harW
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (Restated.switchRound M S tE)
    have hΔ := S.E.Δ_pos
    linarith
  obtain ⟨y, hy, hycomm, hCy⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hv') hoPos hpostVote
      hconfHor c hc' hgen
      (fun z _ hz j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
        (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz) hwinW)
  have hyVote : y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
    ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  have hSGy : Block.Preceq G H := by
    refine preceq_trans_Preceq ?_ (hCy cc hcc Tr hTr L hL L' hL' H hH)
    rw [hCeq]
    exact hclear
  obtain ⟨Hy, hHyErase, hHyRun⟩ := Restated.seedVoteDutyHead_runBlockOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf (hHsXb _ hyVote) ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    cc hcc Tr hTr L hL L' hL' H hH
  have hvoteHorO : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hHyEmit := Restated.seedVoteDutyHead_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    hf hyVote hoPos hycomm hvoteHorO hpostVote cc hcc
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hyVote hwinW) Tr hTr L hL L' hL' H hH
  have hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) (Restated.switchRound M S tE - 1) G := by
    intro u hu nu hnu D hD hemit gc stu k A2' hA2' G' hG'
    have hne : ∀ u' : V, ∃ m : M.N,
        m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u')
          (Restated.switchRound M S tE - 1) :=
      fun u' => (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S) _ _
    obtain ⟨nprev, hnprev, hnprevu⟩ : ∃ nprev : V → M.N,
        (∀ u' : V, nprev u' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u')
          (Restated.switchRound M S tE - 1)) ∧ nprev u = nu := by
      classical
      refine ⟨fun u' => if u' = u then nu else Classical.choose (hne u'), fun u' => ?_, if_pos rfl⟩
      by_cases hu' : u' = u
      · subst hu'
        beta_reduce
        rw [if_pos rfl]
        exact hnu
      · beta_reduce
        rw [if_neg hu']
        exact Classical.choose_spec (hne u')
    have hPu := hP nprev hnprev u hu
    rw [hnprevu] at hPu
    obtain ⟨X, hXu, hXrun, hXemit⟩ := hPu D hD hemit A2' hA2' G' hG' y hyVote hycomm
    have hXH : X.erase = Hy.erase :=
      Restated.runBlock_eq_of_root_eqOn facts _ Finset.univ hf.rootCollisionFree hXrun hHyRun (by
        rw [hHyErase]
        exact congrArg GoldfishVote.head
          (Restated.emits_gfVote_uniqueOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hXemit
            hHyEmit rfl))
    rw [hXH, hHyErase] at hXu
    exact compatible_of_preceq_common_Preceq hXu hSGy
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (M.vote_time (Setup.alwaysAwake S).E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
  have hroot : Block.compatible
      (M.get_fg_root (M.toHealing (M.mkNode
        (M.ns_setClock S.E
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw).st.core).toFG)
      G = true := by
    refine (congrArg (fun R => Block.compatible R G)
      (Restated.fgRoot_voteDutyRead_eq_l78 facts (Setup.alwaysAwake S) _ w _ _ hmemW cw hcw)).trans ?_
    exact compatible_of_preceq_common_Preceq
      (preceq_trans_Preceq
        (Restated.fgRoot_comparable_anchor_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
          hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw) hTC)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  have hr := Restated.round_of_openingSucc_l78 facts S (Restated.switchRound M S tE)
  have hwdom : w ∈ notHeldAt Sched (M.domain S.E S.hc
      ((M.round_of S.hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) .g1) := by
    rw [hr]
    exact hHs _ _ (Restated.domain_g1_le_vote_openingSucc_l78 facts S (Restated.switchRound M S tE)) hw
  have hr' : (M.round_of (Setup.alwaysAwake S).hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) =
      Restated.switchRound M S tE := hr
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
  exact Restated.voterAnchorAt_compatible_of_previousSGHistory_namedOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hconfHor (by rw [hr']; exact hrW1)
    (by rw [hr']; exact hsg) (by rw [hr']; exact hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle))
    hwdom cw hcw hroot
    (by
      rw [hr']
      exact fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
        hn (Restated.switchRound M S tE - 1) hkPrev u j hj) A hA

end

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`,
    synchrony assumed only up to `x[N].time`, and the round-`(rW − 1)` SG blocks ancestors of the
    opening-slot votes of `rW` (`hP`): for a validator `v'` in `notHeldAt Sched` at `S.a rW`, a node
    state `n` of its round-`rW` action read, and a block `G` the SG vote selector can return at `n`
    that is an ancestor of `n.live_confirmed`, every committee member of slot `opening_slot rW + 1`
    in `notHeldAt Sched` at its vote instant votes there, along the path, a run block descending
    from `G`. -/
theorem clearTier_cone_at_secondSlot_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hclear : Block.Preceq G n.live_confirmed) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (notHeldAt Sched) Finset.univ ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      (fun X => Block.Preceq G X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      v' (Restated.switchRound M S tE) _ hmemW n hnA with
    ⟨C, hgen, hCeq⟩ | ⟨Rt, hReq, hRlive⟩
  · have hlive : ∃ C : Block V,
        Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache) S.E S.hc
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core
            (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
          ((M.opening_slot S.hc (Restated.switchRound M S tE))) C ∧
        C = n.live_confirmed := ⟨C, hgen, hCeq⟩
    have hcomp := Restated.checkpoint_compatible_clearSG_at_switchRound_le_upTo facts S Sched x v hsync hmono hawake
      hgst hcv hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop hv' hnA hlive hA2 hG hclear
    rcases compatible_cases hcomp with hTC | hCT
    · -- case `T ⪯ G`
      have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
        fun _ _ h => notHeldAt_anti hmono h
      have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
        fun _ => Finset.subset_univ _
      have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
      obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
      have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
      have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
      obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
      obtain ⟨-, -, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
      exact Restated.secondSlotCone_of_clearGenuine_atBaseOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
        Finset.univ hf hHs hHsXb hcomOn hrW1
        (hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)) hrWN hv'
        hnA hA2 hG hlive
        (fun w hw => Or.inl (preceq_trans_Preceq
          (Restated.fgRoot_comparable_anchor_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
            hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw) hTC))
        (Restated.hmax_at_secondSlot_of_checkpointPreceqLive_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
          hawm hthird hcom hlen htd hN hreg harW hn₀ htop hnA hA2 hG
          (preceq_trans_Preceq hTC hclear))
        (Restated.anchor_compatible_clearSG_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
          hawm hthird hcom hlen htd hN hreg harW hn₀ htop hP hv' hnA hlive hA2 hG hclear hTC)
        hclear
    · -- case `G ⪯ T`: the cone over the checkpoint
      exact Restated.namedHonestVotesConeOn_of_preceq_l78 facts hCT
        (Restated.checkpointCone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
          hawm hthird hcom hlen htd hN hreg harW)
  · -- case: the live confirmation is the FG root of the confirmation store
    refine Restated.fgRootTier_cone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
      hawm hthird hcom hlen htd hN hreg harW hn₀ htop hv' hnA hA2 hG ?_
    have hfg : M.get_fg_root (M.toHealing n.st.core).toFG =
        M.get_fg_root (M.toHealing (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core).toFG :=
      Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts
        (Setup.alwaysAwake S) _ v' (Restated.switchRound M S tE) _ hmemW n hnA
    have htk : Rt = M.get_fg_root (M.toHealing (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core).toFG := by
      rw [hReq]
      exact facts.fc.get_fg_root_set_clock_slot _ _ _
    rw [hfg, ← htk, hRlive]
    exact hclear

end

end DecoupledConsensusModel.Sts.Restated
