import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecoveryTimeout
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Filtered-tree membership at a fixed root and the height of a proposal

Theorems read along the path `W` of a run satisfying `AdmissibleFieldsOn`, over a model
`M : Record.Model V` and its facts: a block that is a descendant of an exact fixed root is in the
filtered tree, and an accepted proposal's derived height is at most the largest `h_max` over the set
for its proposal time.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ### Helpers about paths -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₂p (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, the world `W (strictEventIndex rho t)` of a path `W` is a world strictly
    before `t`. -/
private theorem mem_stateBeforeTime_along₅₂p {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₂p S rho hsorted]
  exact (hW _).1

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₂p {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (m : Nat) :
    ∀ k : Nat, W (m + k) ∈ ((rho.events.drop m).take k).foldlM (Record.worldStepOf M S) (W m) := by
  intro k
  induction k with
  | zero => exact Set.mem_singleton _
  | succ k ih =>
    have hstep := (hW (m + k)).2
    rw [Nat.add_sub_cancel_left] at hstep
    rw [List.take_add, List.foldlM_append, Set.bind_def, List.drop_drop]
    refine Set.mem_iUnion₂.mpr ⟨W (m + k), ih, ?_⟩
    rw [← Nat.add_assoc]
    exact hstep

/-- Along a path `W` of `rho`, for `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` lead
    to from `W m`. -/
private theorem onePath_slice₅₂p {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₂p W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

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
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `w ∈ Xb`, `B` is a run block whose erasure is in `w`'s core store in
    `W (strictEventIndex rho target)`, `u`'s justified block in `W (strictEventIndex rho read0)` is
    an ancestor of `B`'s erasure, `H − 1` is at most `B`'s height, and `w`'s store has that
    justified block as FG root and `H` as `h_max`, then `B`'s erasure is in that store's filtered
    tree. -/
theorem fixedRootGrade_mem_filtered_of_exactRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {H : Height} {u w : V} {read0 target : Time} {B : NamedBlock V}
    (hw : w ∈ Xb)
    (hBRun : Restated.RunBlockOn M S rho W Xb B)
    (hprocessed : B.erase ∈ (W (strictEventIndex rho target) w).st.core.T)
    (hJB : Block.Preceq (W (strictEventIndex rho read0) u).st.J B.erase)
    (hBheight : H - 1 ≤ (M.derive_named S.E S.cfg B).h)
    (hroot : M.get_fg_root
      (M.toHealing (W (strictEventIndex rho target) w).st.core).toFG =
        (W (strictEventIndex rho read0) u).st.J)
    (hmax : (W (strictEventIndex rho target) w).st.core.h_max = H) :
    B.erase ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho target) w).st.core).toFG := by
  have hwd := mem_stateBeforeTime_along₅₂p hf.sorted hf.onePath (S := S) target
  let st := (W (strictEventIndex rho target) w).st
  obtain ⟨D, hDbody, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts
      S rho target w _ hwd hprocessed
  have hDRun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hDbody
  have hrootEq : D.root = B.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDerase]
  have hDB : D = B :=
    hf.rootCollisionFree.root_injective D B hDRun hBRun D B
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hrootEq
  have hBbody : B ∈ st.bodies := by
    rw [← hDB]
    exact hDbody
  have hview : st.core.σ B.erase = M.derive_named S.E S.cfg B :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho target w _ hwd
      B hBbody
  have hFJ : Block.Preceq st.core.F st.core.J :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho target w _ hwd
  have hFroot : Block.Preceq st.core.F
      (M.get_fg_root (M.toHealing st.core).toFG) := by
    rcases facts.fc.get_fg_root_eq_J_or_F st.core with h | h
    · rw [h]
      exact hFJ
    · rw [h]
      exact Proofs.ModelProperties.Preceq_self _
  have hrootB : Block.Preceq
      (M.get_fg_root (M.toHealing st.core).toFG) B.erase := by
    rw [show M.get_fg_root (M.toHealing st.core).toFG =
        (W (strictEventIndex rho read0) u).st.J from hroot]
    exact hJB
  have hFB : Block.Preceq st.core.F B.erase :=
    preceq_trans_Preceq hFroot hrootB
  have hσ : st.core.h_max - 1 ≤ (st.core.σ B.erase).h := by
    rw [show st.core.h_max = H from hmax, hview]
    exact hBheight
  have hT : B.erase ∈ (M.toHealing st.core).toFG.toSG.toGoldfishStore.T := by
    rw [facts.sto.toHealing_T]
    exact hprocessed
  exact facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing st.core) hT
    (by rw [facts.sto.Sts_toHealing_F]; exact hFB) hT (Proofs.ModelProperties.Preceq_self _)
    (by rw [facts.sto.Sts_toHealing_h_max, facts.sto.Sts_toHealing_σ]; exact hσ) hrootB

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

/-- For `0 < s` and `lo ≤ proposal_time s`, if the proposer of `s` is in the set for
    `confirmation_time s`, its tick at the proposal time has an outcome from a node state passing
    the grade-1 awake test, and the proposal duty on its staged store can return `some B`, then
    `B`'s derived height is at most the largest `h_max` of the members of the set for
    `proposal_time s` in `W (inclusiveEventIndex rho (proposal_time s))`. -/
theorem honestProposedBlock_height_le_honestHMaxAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s)) :
    (M.derive_named S.E S.cfg B).h ≤
      (Hs (M.proposal_time S.E s)).sup fun u =>
        (W (inclusiveEventIndex rho (M.proposal_time S.E s)) u).st.core.h_max := by
  obtain ⟨i, hacc⟩ :=
    Restated.acceptsAt_proposedBlockOn facts S Hs Xb hf hHs hs hprop hhor hgat hneTick hrun c hc hB
  have hpropP : S.E.proposer s ∈ Hs (M.proposal_time S.E s) :=
    hHs _ _ ((le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)).trans
      (facts.sch.Protocol_vote_time_le_confirmation_time S.E s)) hprop
  have hBmem : B ∈ (W (i + 1) (S.E.proposer s)).st.bodies :=
    of_decide_eq_true hacc.2.2
  have hheightLe :
      (M.derive_named S.E S.cfg B).h ≤ (W (i + 1) (S.E.proposer s)).st.core.h_max :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho (i + 1)
      (S.E.proposer s) _ (hf.onePath (i + 1)).1 B hBmem
  obtain ⟨_, e, hie, _, hetime⟩ := hacc.1
  have hi : i < inclusiveEventIndex rho (M.proposal_time S.E s) := by
    unfold inclusiveEventIndex
    exact Restated.index_lt_stateAt_lengthOn facts S Hs Xb hf hie (le_of_eq hetime)
  have hmono : (W (i + 1) (S.E.proposer s)).st.core.h_max ≤
      (W (inclusiveEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.h_max :=
    Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho (S.E.proposer s)
      (Nat.succ_le_iff.mpr hi) _ (hf.onePath (i + 1)).1 _
      (onePath_slice₅₂p W hf.onePath (Nat.succ_le_iff.mpr hi))
  exact hheightLe.trans (hmono.trans (Finset.le_sup (f := fun u =>
    (W (inclusiveEventIndex rho (M.proposal_time S.E s)) u).st.core.h_max) hpropP))

end

end DecoupledConsensusModel.Sts.Restated
