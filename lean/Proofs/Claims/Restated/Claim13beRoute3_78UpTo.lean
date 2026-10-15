import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_74
import Proofs.Claims.Restated.Claim13beRoute3_75UpTo
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_79
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The checkpoint and the switch round's second slot, with synchrony up to the third slot

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
local macro "p65% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_65)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p69b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_69b)
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
    height, and synchrony assumed only up to `x[N].time`, the confirmation instant of slot
    `opening_slot rW + 2`: every validator `w` in `notHeldAt Sched` at the vote instant of slot
    `opening_slot rW + 1` has, at its vote store of that slot computed in the path's world before
    that instant, an FG root that is an ancestor of `T`. -/
theorem fgRoot_comparable_anchor_at_secondSlot_upTo (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
      Block.Preceq (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
          ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))).toFG) T.erase := by
  intro w hw
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid hawm hthird hn
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
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 :=
    Nat.add_le_add_right (facts.gr.opening_slot_mono S harW) 1
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_succ _)
  have hTw := hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo hhor hlo
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj) w hw
  obtain ⟨m, hm⟩ : ∃ m : Nat,
      Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) :=
    Restated.exists_tickStepAt facts x htd
      (facts.sch.vote_time_pos S (Nat.succ_pos ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hvA := Restated.vote_time_openingSucc_lt_action_l78 facts S (Restated.switchRound M S tE)
  have hmn₀ : m + 1 ≤ n₀ + 1 := by
    by_contra hcon
    have hle : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[m + 1].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hn₀N := Restated.succ_le_of_tick_switchRound_l74 facts S Sched x hn₀ hN
  have hmN : m + 1 ≤ N := by omega
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hm hmN w
  have hwA : w ∉ Sched.adv
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) :=
    mem_notHeldAt.mp hw
  have hmtime : (x[m].time : Int) ≤
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) := by
    linarith
  have hwm : Restated.HonestThrough M Sched x m w := by
    intro t' ht' hmem'
    exact hwA (hmono t' _ (ht'.trans hmtime) hmem')
  have hmE : (x[m].time : Int) ≤ tE := by
    have hle : ((x[m].time : Nat) : Int) ≤ ((x[N].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hrootEq : M.get_fg_root
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
        ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))).toFG =
      M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG := by
    rw [hread]
    exact facts.fc.get_fg_root_toHealing_clock _ _ _
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (M.vote_time (Setup.alwaysAwake S).E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
  obtain ⟨cc, hcc⟩ := facts.gr.onPhaseTick_nonempty (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.toHealing
    (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).cache
  obtain ⟨nd, hnd⟩ : ∃ nd : M.N, nd = M.mkNode
      (M.ns_setClock S.E (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cc :=
    ⟨_, rfl⟩
  have hndmem : nd ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      w ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) :=
    ⟨_, hmemW, cc, hcc, hnd⟩
  obtain ⟨Tr, hTr⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nd.st.core nd.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing nd.st.core).toFG.toSG.toGoldfishStore nd.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing nd.st.core).toFG.toSG.toGoldfishStore nd.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract nd.cache) S.E S.hc
    (M.toHealing nd.st.core) Tr L L' (nd.st.core.s - 1)
  have hRH := Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts (Setup.alwaysAwake S)
    _ w _ nd hndmem Tr hTr L hL L' hL' H hH
  have hTH : Block.Preceq T.erase H := by
    subst hnd
    exact hTw cc hcc Tr hTr L hL L' hL' H hH
  have hrootNd : M.get_fg_root (M.toHealing nd.st.core).toFG =
      M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG := by
    rw [hnd, ((p65% dutyNode_parts₆₅) facts S _ _ cc).2.2.2.2.2, hread]
  have hcomp : Block.compatible
      (M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG) T.erase = true := by
    rw [← hrootNd]
    exact compatible_of_preceq_common_Preceq hRH hTH
  have hF := Restated.fin_at_switchRound_of_regime_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hlen htd hN hreg hn₀ htop w m (by omega) hwm
  rw [hrootEq]
  exact Restated.fgRoot_preceq_checkpoint_of_compatible_l78 facts S Sched x hvalid hmono (n₀ := n₀) (by omega)
    (hthird _ hmE) hwm (Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg)
    (Restated.heightCeiling_of_topHonestRow facts S Sched x hvalid.toUnforgeability htop)
    (Restated.targetsTop_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
      hlen htd hN hreg hn₀) hF hcomp

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
    source round before `rW`, and synchrony assumed only up to `x[N].time`, the confirmation instant
    of slot `opening_slot rW + 2`: for every validator `u` in `notHeldAt Sched` at the vote instant
    of slot `opening_slot rW`, every head `u`'s vote duty of that slot can return, staged from the
    path's world before that instant, descends from `T`. -/
theorem headsAtOpening_of_regime_l78_upTo (facts : Record.Facts M)
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
    (hbefore : a.round + 1 ≤ Restated.switchRound M S tE) :
    ∀ u ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))),
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).st
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T.erase H := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid hawm hthird hn
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
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    (facts.gr.opening_slot_succ_le_l78 S a.round).trans (facts.gr.opening_slot_mono S hbefore)
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_add_right _ 2)
  exact hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo hhor hlo
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)

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
    source round at or before `rW`, and synchrony assumed only up to `x[N].time`, the confirmation
    instant of slot `opening_slot rW + 2`: every committee member of slot `opening_slot rW + 1` in
    `notHeldAt Sched` at its vote instant votes there, along that path, a run block descending from
    `T`. -/
theorem checkpointCone_at_secondSlot_upTo (facts : Record.Facts M)
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
    (harW : a.round ≤ Restated.switchRound M S tE) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (notHeldAt Sched) Finset.univ ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      (fun X => Block.Preceq T.erase X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid hawm hthird hn
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
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_succ _)
  rcases Nat.lt_or_ge a.round (Restated.switchRound M S tE) with hlt | hge
  · have hr : (M.round_of (Setup.alwaysAwake S).hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) =
        Restated.switchRound M S tE := Restated.round_of_openingSucc_l78 facts S (Restated.switchRound M S tE)
    exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow
      (Nat.succ_le_of_lt hlt) hlo (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)).1 _ hr hhor).2
  · have heq : a.round = Restated.switchRound M S tE := le_antisymm harW hge
    have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 := by
      rw [heq]
    have hdhi : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 < (M.opening_slot S.hc (a.round + 1)) := by
      rw [heq]
      exact facts.gr.opening_slot_succ_lt_l78 S _
    exact (hreg.seed.checkpointProtection_sourceRound_of_frame_run facts hf hHs hHsXb hX hXXb hcomOn
      hbelow hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev hreg.pred
      hreg.minimal hdlo hdhi hhor hlo (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)).2

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
    synchrony assumed only up to `x[N].time`, the confirmation instant of slot
    `opening_slot rW + 2`: for every validator `v'` in `notHeldAt Sched` at `S.a rW`, every node
    state of its round-`rW` action read staged from the path's world before `S.a rW` has an FG root
    that is an ancestor of `T`. -/
theorem actionFgRoot_preceq_checkpoint_at_switchRound_upTo (facts : Record.Facts M)
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
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE),
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) T.erase := by
  intro v' hv' nd hnd
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid hawm hthird hn
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
  have hreadHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := hrWN
  have hcompRead : Block.compatible (M.get_fg_root
      (M.toHealing (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core).toFG)
      T.erase = true := by
    refine hreg.seed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run facts hf hHs hHsXb hX
      hXXb hcomOn hbelow hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev
      hreg.pred hreg.minimal (Restated.Vocabulary.Proofs.Assembly.a_mono facts S harW) ?_ hv' hreadHor hlo
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)
    intro r hr hrlt u hu B hB
    have hrHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).horizon := le_trans (le_of_lt hrlt) hrWN
    obtain ⟨nr, hnr⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r)) u) r
    obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts (Setup.alwaysAwake S) nr
    exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow hr hlo
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)).2 hrHor).2 u hu nr hnr B (hB nr hnr o ho)
  have hn₀N := Restated.succ_le_of_tick_switchRound_l74 facts S Sched x hn₀ hN
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N v'
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  have hrootNd : M.get_fg_root (M.toHealing nd.st.core).toFG =
      M.get_fg_root (M.toHealing (x[n₀][v'].st).st.core).toFG := by
    rw [← hread]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts
      (Setup.alwaysAwake S) _ v' (Restated.switchRound M S tE) _ hmemW nd hnd
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hvA : v' ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := mem_notHeldAt.mp hv'
  have hn₀time : (x[n₀].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by linarith
  have hv'n₀ : Restated.HonestThrough M Sched x n₀ v' := by
    intro t' ht' hmem'
    exact hvA (hmono t' _ (ht'.trans hn₀time) hmem')
  have hn₀E : (x[n₀].time : Int) ≤ tE := hn₀time.trans (hrWN.trans hn)
  rw [hrootNd]
  rw [hread] at hcompRead
  exact Restated.fgRoot_preceq_checkpoint_of_compatible_l78 facts S Sched x hvalid hmono (n₀ := n₀)
    (Nat.le_succ n₀) (hthird _ hn₀E) hv'n₀ (Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg)
    (Restated.heightCeiling_of_topHonestRow facts S Sched x hvalid.toUnforgeability htop)
    (Restated.targetsTop_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
      hlen htd hN hreg hn₀)
    (Restated.fin_at_switchRound_of_regime_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird
      hcom hlen htd hN hreg hn₀ htop v' n₀ (Nat.le_succ n₀) hv'n₀)
    hcompRead

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
    synchrony assumed only up to `x[N].time`, the confirmation instant of slot
    `opening_slot rW + 2`: for a validator `v'` in `notHeldAt Sched` at `S.a rW`, a node state `n`
    of its round-`rW` action read staged from the path's world, and a block `G` the SG vote selector
    can return at `n`, if `G` is an ancestor of the FG root of `n`'s store, then every committee
    member of slot `opening_slot rW + 1` in `notHeldAt Sched` at its vote instant votes there, along
    the path, a run block descending from `G`. -/
theorem fgRootTier_cone_at_secondSlot_upTo (facts : Record.Facts M)
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
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hroot : Block.Preceq G (M.get_fg_root (M.toHealing n.st.core).toFG)) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (notHeldAt Sched) Finset.univ ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      (fun X => Block.Preceq G X) :=
  Restated.namedHonestVotesConeOn_of_preceq_l78 facts
    (preceq_trans_Preceq hroot
      (Restated.actionFgRoot_preceq_checkpoint_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv
        hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop v' hv' n hnA))
    (Restated.checkpointCone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
      hlen htd hN hreg harW)

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
    source round before `rW`, and synchrony assumed only up to `x[N].time`, the confirmation instant
    of slot `opening_slot rW + 2`: for a validator `v'` in `notHeldAt Sched` at `S.a rW`, a node
    state `n` of its round-`rW` action read whose live confirmation satisfies `GenuineConfirmation`
    for the opening slot, and a block `G` the SG vote selector can return at `n` that is an ancestor
    of that live confirmation, `T` and `G` are on one chain. -/
theorem checkpoint_compatible_clearSG_at_switchRound_upTo (facts : Record.Facts M)
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
    (hbefore : a.round + 1 ≤ Restated.switchRound M S tE)
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
    hmono hawake hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨-, hloVote, -, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW)
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hpostVote : _ ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
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
  obtain ⟨y, hy, -, hCy⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hv') hoPos hpostVote
      hconfHor c hc' hgen
      (fun z _ hz j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
        (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz) hwinW)
  have hyVote : y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
  have hTy := Restated.headsAtOpening_of_regime_l78_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hlen htd hN hreg hbefore y hyVote
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
    ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  have hTH : Block.Preceq T.erase H := hTy cc hcc Tr hTr L hL L' hL' H hH
  have hCH : Block.Preceq C H := hCy cc hcc Tr hTr L hL L' hL' H hH
  have hSGH : Block.Preceq G H := by
    refine preceq_trans_Preceq ?_ hCH
    rw [hCeq]
    exact hclear
  exact compatible_of_preceq_common_Preceq hTH hSGH

end

end DecoupledConsensusModel.Sts.Restated
