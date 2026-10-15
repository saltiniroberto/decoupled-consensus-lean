import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_SeedCommonRootComplement
import Proofs.Claims.Restated.Vocabulary_Execution_StoreFinalityCore
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalityMonotoneCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Anchors, heads and SG compatibility along a path

Theorems over a model `M : Record.Model V` and its facts, read along a path `W` of a run with the
admissible fields `hf`. They show that a member's prepared vote-duty anchor and vote-duty head reach
a run block of height at least `Mh − 1`, that a run block of that height becomes visible and stamped
after one delay, and that phase grades, voter anchors, action SG emissions and FG confirmation
witnesses stay compatible with a block `T` that the previous round's SG emissions protect.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before the time `t` are the worlds before the event
    of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₅ (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world of a path `W` before the event of index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₆₅ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₅ S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₅ {S : Setup V} {rho : Record.Run V}
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

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₆₅ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₅ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W`, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an ancestor
    of the one in `W n`. -/
private theorem F_mono_along₆₅ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₆₅ W hW hjn)

/-- `strictEventIndex rho t` does not decrease with `t`. -/
private theorem strictEventIndex_mono₆₅ (rho : Record.Run V) {d t : Time} (hdt : d ≤ t) :
    strictEventIndex rho d ≤ strictEventIndex rho t :=
  (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_lt_of_le he hdt)).length_le

/-- In a run sorted by key, every event of index less than `strictEventIndex rho t` is strictly
    before `t`. -/
private theorem time_lt_of_lt_strict₆₅ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho t → rho.events[j]? = some e →
      e.time < t := by
  intro j e hj he
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j <(rho.events.filter (fun e => decide (e.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  have hp := (List.mem_filter.mp hmem).2
  simpa only [decide_eq_true_eq] using hp

/-- Every node state of the round-`r` action read from `before` holds the bodies `before` holds. -/
private theorem actionReadFrom_bodies₆₅ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read and the
    SG vote selector each can return a value. -/
private theorem exists_actionSG₆₅ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, ?_⟩
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s) g
  exact ⟨g, hg, B, hB⟩

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₅ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- The anchor of a node state `n` at a round `r` has an outcome. -/
private theorem nodeAnchor_nonempty₆₅ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  refine ⟨G.anchor, ?_⟩
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₅ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hG

/-- If every outcome of a store grade is `true`, the store grade can return `true`. -/
private theorem storeGrade_true_of_all₆₅ (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) (B : Block V)
    (h : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ b → b = true) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ true := by
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty E (M.gradeView (M.toHealing st.core)) st.core.F
    hc.η_SG r (M.early E hc r p) (M.late E hc r p) B
  have hbt : b = true := h b hb
  subst hbt
  exact hb

/-- The node state staged from `b` with its clock set to slot `d`'s vote time and the cache `cv` has
    `b`'s tree, block stamps, `h_max`, finalized block and FG root, and its slot is `d`. -/
private theorem dutyNode_parts₆₅ (facts : Record.Facts M) (S : Setup V) (b : M.N) (d : Slot)
    (cv : M.Cache) :
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core.T = b.st.core.T ∧
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core.timestamp_block =
      b.st.core.timestamp_block ∧
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core.s = d ∧
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core.h_max =
      b.st.core.h_max ∧
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core.F = b.st.core.F ∧
    M.get_fg_root (M.toHealing
        (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core).toFG =
      M.get_fg_root (M.toHealing b.st.core).toFG := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_T]
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_timestamp_block]
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_h_max]
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_F]
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s]
    exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- The view-freeze time of a slot is at or before the view-freeze time of a later slot. -/
private theorem view_freeze_mono₆₅ (facts : Record.Facts M) (E : Env V) {k k' : Slot}
    (h : k ≤ k') : M.view_freeze E k ≤ M.view_freeze E k' := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · rw [heq]
  · exact (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ E k)).trans
      ((facts.sch.vote_time_mono_slots E (Nat.succ_le_of_lt hlt)).trans
        (facts.sch.vote_time_le_view_freeze E k'))

/-- The vote time of a slot is at or before the proposal time of the next slot. -/
private theorem vote_time_le_proposal_time_succ₆₅ (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.vote_time E s ≤ M.proposal_time E (s + 1) := by
  have h1 := facts.sch.vote_time_le_view_freeze E s
  have h2 := facts.sch.view_freeze_add_delta_le_proposal_time_succ E s
  have hΔ := E.Δ_pos
  linarith

/-- For `1 ≤ c`, `S.a (c − 1) + Δ` is at or before the view-freeze time of every slot `k` with
    `opening_slot c ≤ k + 1`. -/
private theorem prevAction_add_delta_le_view_freeze₆₅ (facts : Record.Facts M) (S : Setup V)
    {c : Round} (hc : 1 ≤ c) {k : Slot} (hk : M.opening_slot S.hc c ≤ k + 1) :
    Restated.Vocabulary.Execution.Setup.a M S (c - 1) + S.E.Δ ≤ M.view_freeze S.E k := by
  have hslots : M.opening_slot S.hc (c - 1) + 1 ≤ k := by
    have h := facts.gr.opening_slot_add S.hc (c - 1) 1
    rw [Nat.sub_add_cancel hc] at h
    have hR := S.hc.R_ge_two
    have h2 : M.opening_slot S.hc (c - 1) + 2 ≤ M.opening_slot S.hc c := by
      rw [h, Nat.one_mul]
      exact Nat.add_le_add_left hR _
    exact Nat.le_of_succ_le_succ (h2.trans hk)
  have h := facts.sch.a_add_delta_eq_view_freeze S (c - 1)
  show M.a S.hc S.E.Δ (c - 1) + S.E.Δ ≤ M.view_freeze S.E k
  rw [h]
  exact view_freeze_mono₆₅ facts S.E hslots

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

/-- Along the path `W` with the admissible fields `hf`, two run blocks `A` and `D` read through `Xb`
    with `A.erase = D.erase` are equal. -/
theorem runBlock_unique_of_erase_eqOn_SeedCanonicalAnchor (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A D : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hD : Restated.RunBlockOn M S rho W Xb D)
    (herase : A.erase = D.erase) : A = D :=
  hf.rootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

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

/-- Along the path `W` with the admissible fields `hf`, if `freeze ≤ read` and `Wb` is genesis or
    admitted at `w` before `freeze`, then `Wb` is in `w`'s tree in `W (strictEventIndex rho read)`
    and stamped there before `freeze`. -/
theorem seedCanonicalRelayedWitness_mem_and_stampOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {Wb : Block V} {freeze read : Time} (hle : freeze ≤ read)
    (h : Wb = Block.genesis ∨ Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w Wb freeze) :
    Wb ∈ (W (strictEventIndex rho read) w).st.T ∧
      stampedBefore (W (strictEventIndex rho read) w).st.timestamp_block freeze Wb = true := by
  rcases h with hgen | hadmit
  · rw [hgen]
    exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w read freeze
  · exact Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hle

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

/-- Along the path `W` with the admissible fields `hf`, if `cut ≤ read`, the finalized block of
    `w`'s store in `W (strictEventIndex rho read)` is an ancestor of `P`, and `P` is an ancestor of
    `C`'s erasure, then for every `i` up to the number of events before `cut` the finalized block of
    `w`'s store in `W i` is an ancestor of `C`'s erasure. -/
theorem finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {P : Block V} {C : NamedBlock V} {cut read : Time}
    (hcut : cut ≤ read)
    (hFP : Block.Preceq (W (strictEventIndex rho read) w).st.core.F P)
    (hPC : Block.Preceq P C.erase) :
    ∀ i : Nat, i ≤ (rho.events.filter (fun e => decide (e.time < cut))).length →
      Block.Preceq (W i w).st.core.F C.erase := by
  intro i hi
  have hiN : i ≤ strictEventIndex rho read := Nat.le_trans hi (strictEventIndex_mono₆₅ rho hcut)
  exact preceq_trans_Preceq (F_mono_along₆₅ facts S hf.onePath w hiN)
    (preceq_trans_Preceq hFP hPC)

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

/-- Along the path `W` with the admissible fields `hf`: if every member of the set for each time
    from `S.a (c − 1)` to `S.a (c + 1)` has `h_j + 2 ≤ Mh` and `h_max = Mh` there (`hframe`), `w` is
    in the set for `vote_time d`, `v` is in the set for `S.a c`, `d` is a slot of round `c` from its
    opening slot to the last slot before the next opening, and `cv` is an outcome of `w`'s cache
    update at `vote_time d`, then every anchor `A0` of the node state staged with `cv` is compatible
    with every block `v`'s round-`c` action can select, or is the active prefix of round `c`'s saved
    grade-one root at that node state. -/
theorem preparedAnchor_compatible_carrier_or_activePrefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (_hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {w v : V} {d : Slot} (hw : w ∈ Hs (M.vote_time S.E d))
    (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hd1 : (M.opening_slot S.hc c) ≤ d)
    (hd2 : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)
    (hround : (M.round_of S.hc d) = c)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core)
      (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cv
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A0 →
    ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
        (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2 →
    ∀ B : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
        (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ B →
    Block.compatible A0 B = true ∨
      ∃ root A : Block V,
        (M.readFrame n.cache (M.toHealing n.st.core) c).g1 = some (some root) ∧
        M.activePrefix (M.get_filtered_block_tree (M.toHealing n.st.core).toFG) root = some A ∧
        A0 = A := by
  intro n A0 hA0 na hna A2 hA2 B hB
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haPredC : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hvoteLo : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E d := by
    have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S hpredLt
    exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((facts.sch.proposal_time_mono S.E hd1).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d)))
  have hdNext : d ≤ (M.opening_slot S.hc (c + 1)) := by
    unfold Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot at hd2
    exact hd2.trans (Nat.sub_le _ _)
  have hvoteHi : M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    have h1 := facts.sch.vote_time_mono_slots S.E hdNext
    have h2 := facts.sch.Protocol_vote_time_le_confirmation_time S.E (M.opening_slot S.hc (c + 1))
    have h3 := facts.sch.a_eq_confirmation_time S.hc S.E (c + 1)
    show M.vote_time S.E d ≤ M.a S.hc S.E.Δ (c + 1)
    rw [h3]
    exact h1.trans h2
  obtain ⟨hgateRead, hfrontierRead⟩ := hframe (M.vote_time S.E d) hvoteLo hvoteHi w hw
  have hparts := dutyNode_parts₆₅ facts S (W (strictEventIndex rho (M.vote_time S.E d)) w) d cv
  have hnS : n.st.core.s = d := hparts.2.2.1
  have hnRoot : M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core).toFG :=
    hparts.2.2.2.2.2
  have hrootEq : M.get_fg_root
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core).toFG =
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F :=
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts
      (st := (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core) hgateRead hfrontierRead
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath _, cv, hcv, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w d n hnmem A0 hA0 with
    hfgAnchor | ⟨root, A, hframeG1, hactivePrefix, hanchorEq⟩
  · left
    have hfrontierV : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))
        v).st.core.h_max = Mh :=
      (hframe ((Restated.Vocabulary.Execution.Setup.a M S c)) haPredC haCSucc v hv).2
    obtain ⟨Wn, hWbody, hcarrierW, hWh⟩ :=
      Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf hfrontierV na hna A2 hA2 B hB
    have hWpre : Wn ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))
        v).st.bodies := by
      rw [← actionReadFrom_bodies₆₅ facts S _ _ na hna]
      exact hWbody
    have hWrun : Restated.RunBlockOn M S rho W Xb Wn :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hWpre
    have hFW : Block.Preceq (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F Wn.erase :=
      Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw hgateRead hWrun hWh
    rw [hfgAnchor, hnRoot, hrootEq]
    exact compatible_of_preceq_common_Preceq hFW hcarrierW
  · right
    have hroundRead : M.round_of S.hc n.st.core.s = c := by
      rw [hnS]
      exact hround
    rw [hroundRead] at hframeG1
    exact ⟨root, A, hframeG1, hactivePrefix, hanchorEq⟩

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

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if the frame
    `hframe` holds from `S.a (c − 1)` to `S.a (c + 1)`, `lo ≤ S.a (c − 1)`, `S.a (c + 1)` is in the
    horizon, `w` is in the set for `vote_time d`, `d` is a slot of round `c` from its opening slot
    to the last slot before the next opening, every member of the set for `S.a (c − 1) + Δ` is awake
    at `c − 1`, and `cv` is an outcome of `w`'s cache update at `vote_time d`, then for every anchor
    `A0` of the node state `n` staged with `cv` and every outcome `P` of the voter-processed tree at
    `n`, some run block along `W` descends from `A0`, has its erasure in `P`, and has height at
    least `n`'s `h_max` less one. -/
theorem voteDutyPreparedAnchor_bandDescendant_processedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {w : V} {d : Slot} (hw : w ∈ Hs (M.vote_time S.E d))
    (hd1 : (M.opening_slot S.hc c) ≤ d)
    (hd2 : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)
    (hround : (M.round_of S.hc d) = c)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core)
      (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cv
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A0 →
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s ⇢ P →
    ∃ C : NamedBlock V,
      Block.Preceq A0 C.erase ∧
      Restated.RunBlockOn M S rho W Xb C ∧
      C.erase ∈ P ∧
      n.st.core.h_max ≤ (M.derive_named S.E S.cfg C).h + 1 := by
  intro n A0 hA0 P hP
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hpredSucc : c - 1 + 1 = c := Nat.sub_add_cancel hc
  have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
  have haPredC : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hoPos : 0 < (M.opening_slot S.hc c) := facts.gr.opening_slot_pos_of_round_pos S.hc hcPos
  have hdPos : 0 < d := lt_of_lt_of_le hoPos hd1
  have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel hdPos
  have hprevOpen :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S hpredLt
  have hprevΔVote : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤
      M.vote_time S.E d :=
    hprevOpen.trans ((facts.sch.proposal_time_mono S.E hd1).trans
      (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d)))
  have hvoteLo : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E d :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hprevΔVote
  have hdNext : d ≤ (M.opening_slot S.hc (c + 1)) := by
    have h := hd2
    unfold Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot at h
    exact h.trans (Nat.sub_le _ _)
  have hvoteHi : M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    have h1 := facts.sch.vote_time_mono_slots S.E hdNext
    have h2 := facts.sch.Protocol_vote_time_le_confirmation_time S.E (M.opening_slot S.hc (c + 1))
    have h3 := facts.sch.a_eq_confirmation_time S.hc S.E (c + 1)
    show M.vote_time S.E d ≤ M.a S.hc S.E.Δ (c + 1)
    rw [h3]
    exact h1.trans h2
  have hvoteHor : M.vote_time S.E d ≤ rho.horizon := hvoteHi.trans hhorNext
  have hfreezeLe : M.view_freeze S.E (d - 1) ≤ M.vote_time S.E d := by
    have h := facts.sch.view_freeze_lt_vote_time_succ S.E (d - 1)
    rw [hdSucc] at h
    exact le_of_lt h
  have hprevΔFreeze : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤
      M.view_freeze S.E (d - 1) :=
    prevAction_add_delta_le_view_freeze₆₅ facts S hc (by rw [hdSucc]; exact hd1)
  have hprevLeFreeze : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
      M.view_freeze S.E (d - 1) :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hprevΔFreeze
  have hfreezeHor : M.view_freeze S.E (d - 1) ≤ rho.horizon := hfreezeLe.trans hvoteHor
  have hwPrev : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) := hHs _ _ hvoteLo hw
  have hwPrevΔ : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ) :=
    hHs _ _ hprevΔVote hw
  obtain ⟨hgateRead, hfrontierRead⟩ := hframe (M.vote_time S.E d) hvoteLo hvoteHi w hw
  have hparts := dutyNode_parts₆₅ facts S (W (strictEventIndex rho (M.vote_time S.E d)) w) d cv
  have hnT : n.st.core.T = (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.T := hparts.1
  have hnStamp : n.st.core.timestamp_block =
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.timestamp_block := hparts.2.1
  have hnS : n.st.core.s = d := hparts.2.2.1
  have hnMax : n.st.core.h_max = (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.h_max :=
    hparts.2.2.2.1
  have hnRoot : M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core).toFG :=
    hparts.2.2.2.2.2
  have hrootEq : M.get_fg_root
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core).toFG =
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F :=
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts
      (st := (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core) hgateRead hfrontierRead
  have hslotH : (M.toHealing n.st.core).s = d := by
    show (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = d
    rw [facts.sto.toHealing_gs_s]
    exact hnS
  -- A block of `w`'s tree before the vote time stamped before the previous view freeze is in the
  -- voter-processed tree.
  have hprocessed : ∀ X : Block V,
      X ∈ (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.T →
      stampedBefore (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.timestamp_block
        (M.view_freeze S.E (d - 1)) X = true → X ∈ P := by
    intro X hXT hXst
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T, hnT]
      exact hXT
    · rw [facts.sto.toHealing_gs_timestamp_block, hnStamp, hslotH]
      exact hXst
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath _, cv, hcv, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w d n hnmem A0 hA0 with
    hfgAnchor | ⟨root, A, hframeG1, hactivePrefix, hanchorEq⟩
  · -- Case: the prepared anchor is the read's FG root, which the frame identifies with the finalized block.
    have hmemPrev := mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath
      (Restated.Vocabulary.Execution.Setup.a M S (c - 1))
    obtain ⟨X, hXbody, hXmax⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime facts S rho
        ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) w _ hmemPrev
    have hprevFrontier : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
        w).st.core.h_max = Mh :=
      (hframe ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) le_rfl
        (haPredC.trans haCSucc) w hwPrev).2
    have hXheight : (M.derive_named S.E S.cfg X).h = Mh := hXmax.trans hprevFrontier
    have hXband : Mh - 1 ≤ (M.derive_named S.E S.cfg X).h := by
      rw [hXheight]
      exact Nat.sub_le Mh 1
    have hXcore : X.erase ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
        w).st.core.T := by
      have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) w _ hmemPrev).1.1.1
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hXbody
    have hXrun : Restated.RunBlockOn M S rho W Xb X :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hw) hXbody
    have hFX : Block.Preceq (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F X.erase :=
      Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw hgateRead hXrun hXband
    have hXrelay : X.erase = Block.genesis ∨
        Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w X.erase
          (M.view_freeze S.E (d - 1)) := by
      rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts
          S Hs Xb hf w ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) hXcore with
        hgen | ⟨D, i, t, hDerase, hacc, ht⟩
      · exact Or.inl hgen
      · exact Or.inr ⟨D, hDerase, i, t, hacc, lt_of_lt_of_le ht hprevLeFreeze⟩
    have hvisible := Restated.seedCanonicalRelayedWitness_mem_and_stampOn facts
      S Hs Xb hf hfreezeLe hXrelay
    refine ⟨X, ?_, hXrun, hprocessed X.erase hvisible.1 hvisible.2, ?_⟩
    · rw [hfgAnchor, hnRoot, hrootEq]
      exact hFX
    · rw [hnMax, hfrontierRead, hXheight]
      exact Nat.le_add_right Mh 1
  · -- Case: the prepared anchor is the active prefix of the round's saved grade-one root.
    have hroundRead : M.round_of S.hc n.st.core.s = c := by
      rw [hnS]
      exact hround
    rw [hroundRead] at hframeG1
    have hnextOpening : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1) := by
      have hlt : d < (M.opening_slot S.hc (c + 1)) := by
        have hpos : 0 < (M.opening_slot S.hc (c + 1)) :=
          facts.gr.opening_slot_pos_of_round_pos S.hc (Nat.succ_pos c)
        have h := hd2
        unfold Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot at h
        exact lt_of_le_of_lt h (Nat.sub_lt hpos Nat.zero_lt_one)
      rw [facts.gr.opening_eq_proposal_time]
      exact (vote_time_le_proposal_time_succ₆₅ facts S.E d).trans
        (facts.sch.proposal_time_mono S.E (Nat.succ_le_of_lt hlt))
    have hdomainG1Eq : M.domain S.E S.hc c .g1 = M.proposal_time S.E ((M.opening_slot S.hc c)) :=
      (facts.gr.Sts_domain_g1_eq_opening S c).trans (facts.gr.opening_eq_proposal_time _ _ _)
    have hdomainG1Vote : M.domain S.E S.hc c .g1 ≤ M.vote_time S.E d := by
      rw [hdomainG1Eq]
      exact (facts.sch.proposal_time_mono S.E hd1).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d))
    have hprevG1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤
        M.domain S.E S.hc c .g1 := by
      rw [hdomainG1Eq]
      exact hprevOpen
    have hprevLeG1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g1 :=
      (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hprevG1
    have hG1LeNext : M.domain S.E S.hc c .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
      hdomainG1Vote.trans hvoteHi
    have hwG1 : w ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ hdomainG1Vote hw
    have hloG1 : lo ≤ M.domain S.E S.hc c .g1 := hpost.trans hprevLeG1
    have hdomainG1Hor : M.domain S.E S.hc c .g1 ≤ rho.horizon := hdomainG1Vote.trans hvoteHor
    obtain ⟨-, hAGrade⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
      S Hs Xb hf hcPos hd1 hround hnextOpening hvoteHor hwG1 cv hcv hframeG1 hactivePrefix
      hloG1
    have hwindow :=
      Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hcPos
        (p := .g1) (Mh := Mh) hpost
        (fun u hu => (hframe ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) le_rfl
          (haPredC.trans haCSucc) u hu).2)
        (fun u hu => (hframe _ hprevLeG1 hG1LeNext u hu).2)
        (fun u hu => (hframe _ hprevLeG1 hG1LeNext u hu).1)
        hdomainG1Hor hA
    have hmajorityC : Restated.GradeFormingMajorityOn M S rho W Hs
        (Hs (M.domain S.E S.hc c .g1)) c :=
      Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb
        hcPos hprevG1 hdomainG1Hor hpost hA
    have hgradeC : M.gradeBool S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F
        S.hc.η_SG c (M.early S.E S.hc c .g1) (M.late S.E S.hc c .g1) A ⇢ true :=
      storeGrade_true_of_all₆₅ facts S.E S.hc _ c .g1 A hAGrade
    obtain ⟨u, hu, hAcarrier⟩ :=
      Restated.relativeGrade_has_roundCarrierOn facts (r := c - 1) (p := .g1)
        S Hs Xb (Hs (M.domain S.E S.hc c .g1)) hf hHs hwindow
        (by simpa only [hpredSucc] using hmajorityC)
        (by rw [hpredSucc])
        (by simpa only [hpredSucc] using hwG1)
        (by simpa only [hpredSucc] using hgradeC)
    have huHon : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) :=
      ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u (c - 1)).mp hu).1
    have hprevFrontier : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
        u).st.core.h_max = Mh :=
      (hframe ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) le_rfl
        (haPredC.trans haCSucc) u huHon).2
    obtain ⟨na, hna, A2, hA2, Bk, hBk⟩ := exists_actionSG₆₅ facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u) (c - 1)
    obtain ⟨Wn, hWbody, hcarrierW, hWh⟩ :=
      Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf hprevFrontier na hna A2 hA2 Bk hBk
    have hABk : Block.Preceq A Bk := hAcarrier na hna A2 hA2 Bk hBk
    have hWpre : Wn ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
        u).st.bodies := by
      rw [← actionReadFrom_bodies₆₅ facts S _ _ na hna]
      exact hWbody
    have hmemPrev := mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath
      (Restated.Vocabulary.Execution.Setup.a M S (c - 1))
    have hWcore : Wn.erase ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
        u).st.core.T := by
      have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u _ hmemPrev).1.1.1
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hWpre
    have hWrun : Restated.RunBlockOn M S rho W Xb Wn :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ huHon) hWpre
    have hAW : Block.Preceq A Wn.erase := preceq_trans_Preceq hABk hcarrierW
    have hFW : Block.Preceq (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F Wn.erase :=
      Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw hgateRead hWrun hWh
    have hFhist := Restated.finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterReadOn facts
      S Hs Xb hf (C := Wn) hprevΔVote hFW (Proofs.ModelProperties.Preceq_self Wn.erase)
    have hrelay : Wn.erase = Block.genesis ∨
        Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w Wn.erase
          (M.view_freeze S.E (d - 1)) := by
      rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts
          S Hs Xb hf u ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) hWcore with
        hgen | ⟨D, i, t, hDerase, hacc, ht⟩
      · exact Or.inl hgen
      · right
        have hDbody : D ∈ (W (i + 1) u).st.bodies := of_decide_eq_true hacc.2.2
        have hDrun : Restated.RunBlockOn M S rho W Xb D :=
          Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ huHon) hDbody
        have hDW : D = Wn :=
          Restated.runBlock_unique_of_erase_eqOn_SeedCanonicalAnchor facts hf hDrun hWrun hDerase
        have hDpos : 0 < D.slot := by
          rw [← Proofs.NamedWire.erase_slot D]
          exact Nat.zero_lt_of_lt
            (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
        have huSrc : u ∈ Hs (max t lo) := hHs _ _ (max_le ht.le hpost) huHon
        have hFhistD : ∀ j : Nat,
            j ≤ (rho.events.filter (fun e => decide (e.time <
              (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ))).length →
            Block.Preceq (W j w).st.core.F D.erase := by
          rw [hDW]
          exact hFhist
        obtain ⟨C, hCerase, j, t', hacc', hlt'⟩ :=
          Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
            S Hs Xb hf hHs hHsXb huSrc hwPrevΔ hDpos hacc ht hpost rfl
            (hprevΔFreeze.trans hfreezeHor) hFhistD
        rw [← hDW]
        exact ⟨C, hCerase, j, t', hacc', lt_of_lt_of_le hlt' hprevΔFreeze⟩
    have hvisible := Restated.seedCanonicalRelayedWitness_mem_and_stampOn facts
      S Hs Xb hf hfreezeLe hrelay
    refine ⟨Wn, ?_, hWrun, hprocessed Wn.erase hvisible.1 hvisible.2, ?_⟩
    · rw [hanchorEq]
      exact hAW
    · rw [hnMax, hfrontierRead]
      exact Nat.sub_le_iff_le_add.mp hWh

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

/-- Under the hypotheses of `voteDutyPreparedAnchor_bandDescendant_processedOn`, every head the head
    computation can return at the node state staged with `cv` is the erasure of some run block along
    `W` of height at least `Mh − 1`. -/
theorem voteDutyHead_band_at_dutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {w : V} {d : Slot} (hw : w ∈ Hs (M.vote_time S.E d))
    (hd1 : (M.opening_slot S.hc c) ≤ d)
    (hd2 : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)
    (hround : (M.round_of S.hc d) = c)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core)
      (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cv
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ Vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Vv →
    ∀ Uv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Uv →
    ∀ X : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T Vv Uv (n.st.core.s - 1) ⇢ X →
    ∃ Hn : NamedBlock V,
      Hn.erase = X ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hoPos : 0 < (M.opening_slot S.hc c) := facts.gr.opening_slot_pos_of_round_pos S.hc hcPos
  have hdPos : 0 < d := lt_of_lt_of_le hoPos hd1
  obtain ⟨s, rfl⟩ : ∃ s, d = s + 1 := ⟨d - 1, (Nat.sub_add_cancel hdPos).symm⟩
  intro n T hT Vv hVv Uv hUv X hX
  have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
  have hprevOpen :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S hpredLt
  have hvoteLo : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E (s + 1) :=
    ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hprevOpen).trans
      ((facts.sch.proposal_time_mono S.E hd1).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E (s + 1))))
  have hdNext : s + 1 ≤ (M.opening_slot S.hc (c + 1)) := by
    have h := hd2
    unfold Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot at h
    exact h.trans (Nat.sub_le _ _)
  have hvoteHi : M.vote_time S.E (s + 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    have h1 := facts.sch.vote_time_mono_slots S.E hdNext
    have h2 := facts.sch.Protocol_vote_time_le_confirmation_time S.E (M.opening_slot S.hc (c + 1))
    have h3 := facts.sch.a_eq_confirmation_time S.hc S.E (c + 1)
    show M.vote_time S.E (s + 1) ≤ M.a S.hc S.E.Δ (c + 1)
    rw [h3]
    exact h1.trans h2
  have hfreezeLe : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
    le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)
  have hprevLeFreeze : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.view_freeze S.E s :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (prevAction_add_delta_le_view_freeze₆₅ facts S hc hd1)
  obtain ⟨-, hfrontierRead⟩ := hframe (M.vote_time S.E (s + 1)) hvoteLo hvoteHi w hw
  have hMaxEq : (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cv).st.core.h_max = Mh :=
    (dutyNode_parts₆₅ facts S (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w) (s + 1)
      cv).2.2.2.1.trans hfrontierRead
  obtain ⟨A0, hA0⟩ := nodeAnchor_nonempty₆₅ facts S n (M.round_of S.hc n.st.core.s)
  obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s
  obtain ⟨C, hAC, hCrun, hCP, hCh⟩ :=
    Restated.voteDutyPreparedAnchor_bandDescendant_processedOn facts
      S Hs Xb hf hHs hHsXb hfb hc hframe hpost hhorNext hw hd1 hd2 hround hA cv hcv
      A0 hA0 P hP
  obtain ⟨Hn, hErase, hRun, hband⟩ :=
    Restated.voteDutyHead_height_ge_frontier_sub_one_of_anchorDescendantOn facts
      S Hs Xb hf hHsXb s (hHs _ _ hfreezeLe hw) cv hcv
      ⟨C, ⟨A0, hA0, hAC⟩, hCrun, ⟨P, hP, hCP⟩, hCh⟩ (hpost.trans hprevLeFreeze)
      T hT Vv hVv Uv hUv X hX
  refine ⟨Hn, hErase, hRun, ?_⟩
  rw [← hMaxEq]
  exact hband

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

/-- Along the path `W` with the admissible fields `hf` and the slashable bound `hsb`, if `Wb` is a
    run block along `W` of height at least `Mh − 1`, `w ∈ Xb`, and `w`'s store in
    `W (strictEventIndex rho cut)` has `h_max = Mh` and `h_j + 2 ≤ Mh`, then for every `i` up to the
    number of events before `cut` the finalized block of `w`'s store in `W i` is an ancestor of
    `Wb`'s erasure. -/
theorem seedBase_thinBlock_finalizedBelowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {Wb : NamedBlock V}
    (hWrun : Restated.RunBlockOn M S rho W Xb Wb)
    (hWthin : Mh - 1 ≤ (M.derive_named S.E S.cfg Wb).h)
    {w : V} (hw : w ∈ Xb) {cut : Time}
    (hfrontier : (W (strictEventIndex rho cut) w).st.h_max = Mh)
    (hgate : (W (strictEventIndex rho cut) w).st.h_j + 2 ≤ Mh) :
    ∀ i : Nat, i ≤ (rho.events.filter (fun e => decide (e.time < cut))).length →
      Block.Preceq (W i w).st.core.F Wb.erase := by
  intro i hi
  have hroot := Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb hw
    (X := Wb.erase) (Xn := Wb) rfl hWrun hWthin hfrontier hgate
  have hrootEq : M.get_fg_root (M.toHealing (W (strictEventIndex rho cut) w).st.core).toFG =
      (W (strictEventIndex rho cut) w).st.core.F :=
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts
      (st := (W (strictEventIndex rho cut) w).st.core) hgate hfrontier
  have hcutRoot : Block.Preceq (W (strictEventIndex rho cut) w).st.core.F Wb.erase := by
    rw [← hrootEq]
    exact hroot
  exact preceq_trans_Preceq
    (F_mono_along₆₅ facts S hf.onePath w (n := strictEventIndex rho cut) hi) hcutRoot

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

/-- Along the path `W` with the admissible fields `hf` and the slashable bound `hsb`: if a holder in
    the set for `source` holds `Wb` in `W (strictEventIndex rho source)`, `w` is in the set for
    `cut`, `Wb` is a run block of height at least `Mh − 1`, `lo ≤ source`, `source + Δ = cut`,
    `cut ≤ read`, `cut` is in the horizon, and `w`'s store in `W (strictEventIndex rho cut)` has
    `h_max = Mh` and `h_j + 2 ≤ Mh`, then `Wb`'s erasure is in the tree of `w`'s store in
    `W (strictEventIndex rho read)`, and is genesis or stamped there before `cut`. -/
theorem thinBlock_visible_and_stamped_after_oneDelayOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {Wb : NamedBlock V} {holder w : V}
    {source cut read : Time}
    (hholder : holder ∈ Hs source) (hw : w ∈ Hs cut)
    (hsource : Wb ∈ (W (strictEventIndex rho source) holder).st.bodies)
    (hWrun : Restated.RunBlockOn M S rho W Xb Wb)
    (hWthin : Mh - 1 ≤ (M.derive_named S.E S.cfg Wb).h)
    (hpost : lo ≤ source)
    (hhop : source + S.E.Δ = cut)
    (hcutRead : cut ≤ read)
    (hhor : cut ≤ rho.horizon)
    (hfrontier : (W (strictEventIndex rho cut) w).st.h_max = Mh)
    (hgate : (W (strictEventIndex rho cut) w).st.h_j + 2 ≤ Mh) :
    Wb.erase ∈ (W (strictEventIndex rho read) w).st.T ∧
      (Wb.erase = Block.genesis ∨
        stampedBefore (W (strictEventIndex rho read) w).st.timestamp_block cut Wb.erase = true) := by
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho source) holder).st (.block Wb) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hsource
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts
      S rho holder W hf.onePath (strictEventIndex rho source) Wb hprocessed with
    hgen | ⟨i, hi, ta, hacc⟩
  · refine ⟨?_, Or.inl ?_⟩
    · rw [hgen, erase_named_genesis]
      exact (Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w read read).1
    · rw [hgen, erase_named_genesis]
  · have hta : ta < source := by
      obtain ⟨-, e, he, -, het⟩ := hacc.1
      rw [← het]
      exact time_lt_of_lt_strict₆₅ hf.sorted source i e hi he
    have hWpos : 0 < Wb.slot := by
      rw [← Proofs.NamedWire.erase_slot Wb]
      exact Nat.zero_lt_of_lt
        (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
    have hFhist := Restated.seedBase_thinBlock_finalizedBelowOn facts S Hs Xb hf hsb hWrun hWthin
      (hHsXb _ hw) hfrontier hgate
    have hholderSrc : holder ∈ Hs (max ta lo) := hHs _ _ (max_le hta.le hpost) hholder
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w Wb.erase cut :=
      Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hholderSrc hw hWpos hacc hta hpost hhop hhor hFhist
    have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hcutRead
    exact ⟨hvisible.1, Or.inr hvisible.2⟩

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
local macro "rah% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Execution.RecoveryInitialSourceNamedActionHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hbelow`: if
    `lo ≤ S.a (c − 1)`, `domain c p` is in the horizon, `w` is in the set for `domain c p`, the
    finalized block of `w`'s store in `W` before `domain c p` is an ancestor of `T`, every
    round-`(c − 1)` action emission of a member of the set for `S.a (c − 1)` selects only blocks
    compatible with `T` (`hsg`), the relative phase-`p` grade test of round `c` for `B` at that
    store can return `true`, and every member of the set for `S.a (c − 1) + Δ` is awake at `c − 1`,
    then `B` is compatible with `T`. It is stated before
    `voterAnchorAt_compatible_of_previousSGHistory_namedOn`, which uses it. -/
theorem phaseGrade_compatible_previousSGHistory_l65 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : BelowOneThirdOn S rho Hs)
    {c : Round} (hc : 1 ≤ c) {p : DecoupledConsensusModel.Protocol.Phase}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hdomainHor : M.domain S.E S.hc c p ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc c p))
    {T B : Block V}
    (hFT : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core.F T)
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1) T)
    (hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core.F
      S.hc.η_SG c (M.early S.E S.hc c p) (M.late S.E S.hc c p) B ⇢ true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    Block.compatible B T = true := by
  obtain ⟨q, rfl⟩ : ∃ q, c = q + 1 := ⟨c - 1, (Nat.sub_add_cancel hc).symm⟩
  simp only [Nat.add_sub_cancel] at hpost hsg hA
  have hW := hf.onePath
  have hlatest : q ∈ M.latest_window S.hc.η_SG (q + 1) := by
    simpa only [Nat.add_sub_cancel] using
      facts.fc.pred_mem_latest_window S.hc.η_SG (q + 1) S.hc.η_SG_ge_one (Nat.succ_pos q)
  have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
      M.early S.E S.hc (q + 1) p := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self q)
    have h2 := facts.gr.early_g2_add_delta_le_early_g1 S (q + 1)
    have h3 := facts.gr.early_g1_add_delta_le_early_g0 S (q + 1)
    have hΔ := S.E.Δ_pos
    show M.a S.hc S.E.Δ q + S.E.Δ ≤ M.early S.E S.hc (q + 1) p
    cases p <;> linarith
  have hearlyDomain : M.early S.E S.hc (q + 1) p ≤ M.domain S.E S.hc (q + 1) p := by
    have h := facts.gr.early_add_two_delta_le_domain S (q + 1) p
    linarith [S.E.Δ_pos]
  have hearlyHor : M.early S.E S.hc (q + 1) p ≤ rho.horizon := hearlyDomain.trans hdomainHor
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hactionDeadline.trans hearlyHor)
  have hwE : w ∈ Hs (M.early S.E S.hc (q + 1) p) := hHs _ _ hearlyDomain hw
  have hmemE : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p), v ∈ Hs (M.early S.E S.hc (q + 1) p) :=
    fun v hv => hHs _ _ hearlyDomain hv
  have hmemAD : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p),
      v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ) :=
    fun v hv => hHs _ _ (hactionDeadline.trans hearlyDomain) hv
  have hmemA : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p),
      v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q) :=
    fun v hv => hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) (hmemAD v hv)
  -- Every member of the set for the domain time emitted a round-`q` action vote compatible with `T`
  -- that is an interpreted input of `w`'s grade read.
  have hvoteIn : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) p),
      ∃ (a : NamedAttestation V) (Bk : Block V) (Bn : NamedBlock V),
        a.val_index = v ∧ a.round = q ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a)
          (Restated.Vocabulary.Execution.Setup.a M S q) ∧
        a.confirmed = some Bk.root ∧ Bn.erase = Bk ∧ Restated.RunBlockOn M S rho W Xb Bn ∧
        Block.compatible Bk T = true ∧
        ∀ Y, M.interpretedInputs
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
          S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v ⇢ Y → M.sgVote a.erase ∈ Y := by
    intro v hv
    have hvA := hmemA v hv
    obtain ⟨nv, hnv, g, hg, Bk, hBk⟩ := exists_actionSG₆₅ facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc (S.node v)
      nv.st nv.record
    have hem := Restated.honest_emits_actionAttestationAtOn facts S Hs Xb hf q hvA hactionHor hpost
      (hA v (hmemAD v hv)) (fun j hj => hf.tick_outcome j _ _ hj) nv hnv D hD
    have hsgv := hem.2 g hg Bk hBk
    have haval : D.2.2.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hsgv
      rw [facts.sto.sgVote_val_index_eq_val_index, namedAttestation_erase_val_index] at h
      exact h
    have haround : D.2.2.round = q := by
      have h := congrArg Protocol.SGVote.round hsgv
      rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round] at h
      exact h
    have haconf : D.2.2.confirmed = some Bk.root := by
      have h := congrArg Protocol.SGVote.confirmed hsgv
      rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed] at h
      exact h
    obtain ⟨i, hi, -, -, -, -, hall⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hW hem.1
    obtain ⟨ni, hni, -⟩ := exists_actionSG₆₅ facts S (W i v) D.2.2.round
    obtain ⟨H, hH, hHconf⟩ := hall ni hni
    have hHbody : H ∈ (W i v).st.bodies := by
      rw [← actionReadFrom_bodies₆₅ facts S _ _ ni hni]
      exact hH
    have hHrun : Restated.RunBlockOn M S rho W Xb H :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hHbody
    have hamem := mem_stateBeforeTime_along₆₅ hf.sorted hW
      (Restated.Vocabulary.Execution.Setup.a M S q)
    have hBmem : Bk ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T :=
      Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v q _
        hamem nv hnv g hg Bk hBk
    obtain ⟨Bn, hBnerase, hBnrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb
      hf (hHsXb _ hv) (Restated.Vocabulary.Execution.Setup.a M S q) hBmem
    have hrootEq : H.erase.root = Bn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hBnerase]
      exact Option.some.inj (hHconf.symm.trans haconf)
    have hHB : H.erase = Bn.erase :=
      Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHrun hBnrun hrootEq
    have hHerase : H.erase = Bk := hHB.trans hBnerase
    have hBT : Block.compatible Bk T = true :=
      hsg v hvA nv hnv D hD hem.1 g hg Bk hBk
    have hmem : ∀ Y, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
        S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v ⇢ Y → M.sgVote D.2.2.erase ∈ Y := by
      rcases compatible_cases hBT with hBkT | hTBk
      · exact Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
          S Hs Xb hf hHs hHsXb p hlatest (hmemE v hv) hwE
          ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩
          (by rw [hHerase]; exact hBkT) hFT
          (by rw [haround]; exact hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
      · exact Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
          S Hs Xb hf hHs hHsXb p hlatest (hmemE v hv) hwE
          ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩
          (Proofs.ModelProperties.Preceq_self H.erase)
          (preceq_trans_Preceq hFT (by rw [hHerase]; exact hTBk))
          (by rw [haround]; exact hpost)
          (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
          hearlyDomain hearlyHor
    exact ⟨D.2.2, Bk, Bn, haval, haround, hem.1, haconf, hBnerase, hBnrun, hBT, hmem⟩
  -- The window majority over the set for the domain time.
  have hwin : ∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
        S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v ⇢ ins v) →
      S.E.electorate.weightOf (Finset.univ \ Hs (M.domain S.E S.hc (q + 1) p)) <
        S.E.electorate.weightOf ((Hs (M.domain S.E S.hc (q + 1) p)).filter
          fun v => (ins v).Nonempty) := by
    intro ins hins
    have hsubset : Hs (M.domain S.E S.hc (q + 1) p) ⊆
        (Hs (M.domain S.E S.hc (q + 1) p)).filter fun v => (ins v).Nonempty := by
      intro v hv
      obtain ⟨a, -, -, -, -, -, -, -, -, -, hmem⟩ := hvoteIn v hv
      exact Finset.mem_filter.2 ⟨hv, ⟨_, hmem _ (hins v)⟩⟩
    exact lt_of_lt_of_le
      (by simpa only [HonestWeightMajority] using
        honestWeightMajorityOn_of_belowOneThirdOn hbelow _ hdomainHor)
      (S.E.electorate.weightOf_mono hsubset)
  -- An honest positive supporter of `B`, with its latest interpreted input.
  obtain ⟨v, hv, I, hI, u, hu, head, hconf, hfind, -, hBhead, -, hmax⟩ :=
    facts.gr.exists_honest_max_positive_supporter_of_relativeGrade S.E S.hc hwin true hgrade rfl
  obtain ⟨a, Bk, Bn, haval, haround, hemit, haconf, hBnerase, hBnrun, hBT, hmem⟩ := hvoteIn v hv
  have hqle : q ≤ u.round := by
    have h := hmax (M.sgVote a.erase) (hmem I hI)
    rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round, haround] at h
    exact h
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v
  obtain ⟨bu, hbu⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.F
    (M.early S.E S.hc (q + 1) p) u
  have huraw := ((facts.gr.mem_interpretedInputs_iff I hI R hR bu hbu).mp hu).1
  obtain ⟨b, -, hbround, hbproj, huwindow, -, hbemit⟩ :=
    Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (M.domain S.E S.hc (q + 1) p)
      (M.early S.E S.hc (q + 1) p) w S.hc.η_SG (q + 1) v hv R hR huraw
  have hule : u.round ≤ q := Nat.le_of_lt_succ (facts.fc.window_bounds huwindow).2
  have huroundEq : u.round = q := Nat.le_antisymm hule hqle
  have hba : b = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hbemit hemit
    ((hbround.trans huroundEq).trans haround.symm)
  have huEq : u = M.sgVote a.erase := by
    rw [← hbproj, hba]
  have hheadRoot : head.root = Bk.root := by
    have huconf := congrArg Protocol.SGVote.confirmed huEq
    rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed, hconf, haconf] at huconf
    exact Option.some.inj huconf
  have hheadMem : head ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) p)) w).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  obtain ⟨Headn, hHeaderase, hHeadrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts
    S Hs Xb hf (hHsXb _ hw) (M.domain S.E S.hc (q + 1) p) hheadMem
  have hheadBnRoot : Headn.erase.root = Bn.erase.root := by
    rw [hHeaderase, hBnerase]
    exact hheadRoot
  have hheadB : head = Bk := by
    rw [← hHeaderase, ← hBnerase]
    exact Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHeadrun hBnrun hheadBnRoot
  rw [hheadB] at hBhead
  exact (rah% actionHistory_compatible_ancestor) hBhead hBT

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

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hbelow`: if slot `s`'s
    confirmation time is in the horizon, `1 ≤ c` for `c` the round of `s + 1`, every round-`(c − 1)`
    action emission of a member of the set for `S.a (c − 1)` selects only blocks compatible with `T`
    (`hsg`), `lo ≤ S.a (c − 1)`, `w` is in the set for `domain c g1`, `cv` is an outcome of `w`'s
    cache update at `vote_time (s + 1)`, the FG root of the node state staged with `cv` is
    compatible with `T` (`hroot`), and every member of the set for `S.a (c − 1) + Δ` is awake at
    `c − 1`, then every anchor of that node state is compatible with `T`. -/
theorem voterAnchorAt_compatible_of_previousSGHistory_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : BelowOneThirdOn S rho Hs)
    {s : Slot} {T : Block V}
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hc : 1 ≤ (M.round_of S.hc (s + 1)))
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs
      ((M.round_of S.hc (s + 1)) - 1) T)
    (hsgPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)))
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc ((M.round_of S.hc (s + 1))) .g1))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core)
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ cv)
    (hroot : Block.compatible
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cv).st.core).toFG) T = true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1))) → M.awake_for_grade2 S u (W j u) ((M.round_of S.hc (s + 1)) - 1)) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cv
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A0 →
    Block.compatible A0 T = true := by
  intro n A0 hA0
  generalize hcdef : M.round_of S.hc (s + 1) = c at hc hsg hsgPost hw hA
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon := by
    have h := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s
    linarith [S.E.Δ_pos]
  have hparts := dutyNode_parts₆₅ facts S
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w) (s + 1) cv
  have hnS : n.st.core.s = s + 1 := hparts.2.2.1
  have hnRoot : M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG :=
    hparts.2.2.2.2.2
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
    ⟨W (strictEventIndex rho (M.vote_time S.E (s + 1))),
      mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath _, cv, hcv, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w (s + 1) n hnmem
      A0 hA0 with
    hfg | ⟨root, L, hframe, hactive, hanchor⟩
  · rw [hfg]
    exact hroot
  · rw [hanchor]
    have hroundRead : M.round_of S.hc n.st.core.s = c := by
      rw [hnS]
      exact hcdef
    rw [hroundRead] at hframe
    have hslo : (M.opening_slot S.hc c) ≤ s + 1 := by
      rw [← hcdef]
      exact facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    have hshi : s + 1 < (M.opening_slot S.hc (c + 1)) := by
      rw [← hcdef]
      exact facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
    have hnext : M.vote_time S.E (s + 1) ≤ M.opening S.E S.hc (c + 1) := by
      rw [facts.gr.opening_eq_proposal_time]
      exact (vote_time_le_proposal_time_succ₆₅ facts S.E (s + 1)).trans
        (facts.sch.proposal_time_mono S.E (Nat.succ_le_of_lt hshi))
    have hdomainEq : M.domain S.E S.hc c .g1 = M.proposal_time S.E ((M.opening_slot S.hc c)) :=
      (facts.gr.Sts_domain_g1_eq_opening S c).trans (facts.gr.opening_eq_proposal_time _ _ _)
    have hdomainVote : M.domain S.E S.hc c .g1 ≤ M.vote_time S.E (s + 1) := by
      rw [hdomainEq]
      exact (facts.sch.proposal_time_mono S.E hslo).trans
        (facts.sch.proposal_time_lt_vote_time S.E (s + 1)).le
    have hdomainHor : M.domain S.E S.hc c .g1 ≤ rho.horizon := hdomainVote.trans hvoteHor
    have hactionDomain : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
        M.domain S.E S.hc c .g1 := by
      have h := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
        facts S (Nat.sub_lt hcPos Nat.zero_lt_one)
      rw [hdomainEq]
      exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h
    obtain ⟨-, hLgrade⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
      S Hs Xb hf hcPos hslo hcdef hnext hvoteHor hw cv hcv hframe hactive
      (hsgPost.trans hactionDomain)
    rcases compatible_cases hroot with hrootT | hTroot
    · have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        facts S rho (M.vote_time S.E (s + 1)) w _
        (mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath _)
      have hvoteFroot : Block.Preceq
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.F
          (M.get_fg_root
            (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG) :=
        Restated.Vocabulary.Proofs.StoreFinality.finalized_preceq_fgRoot facts
          (st := (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core)
          (preceq_eq_true_iff_Preceq.mpr hFJ)
      have hdomainFvoteF : Block.Preceq
          (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.F :=
        F_mono_along₆₅ facts S hf.onePath w (strictEventIndex_mono₆₅ rho hdomainVote)
      have hrootT' : Block.Preceq
          (M.get_fg_root
            (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG) T := by
        rw [← hnRoot]
        exact hrootT
      have hFT : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F T :=
        preceq_trans_Preceq hdomainFvoteF (preceq_trans_Preceq hvoteFroot hrootT')
      have hgrade : M.gradeBool S.E
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F
          S.hc.η_SG c (M.early S.E S.hc c .g1) (M.late S.E S.hc c .g1) L ⇢ true :=
        storeGrade_true_of_all₆₅ facts S.E S.hc _ c .g1 L hLgrade
      exact Restated.phaseGrade_compatible_previousSGHistory_l65 facts S Hs Xb hf hHs hHsXb
        hbelow hc hsgPost hdomainHor hw hFT hsg hgrade hA
    · have hrootL : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) L := by
        have hLmem : L ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
          facts.gr.activePrefix_mem _ _ _ hactive
        exact preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hLmem)
      exact compatible_of_cases (Or.inr (preceq_trans_Preceq hTroot hrootL))

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

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hbelow`: if
    `lo ≤ S.a (c − 1)`, `domain c p` is in the horizon, `w` is in the set for `domain c p`, the
    finalized block of `w`'s store in `W` before `domain c p` is an ancestor of `T`, every
    round-`(c − 1)` action emission of a member of the set for `S.a (c − 1)` selects only blocks
    compatible with `T` (`hsg`), the relative phase-`p` grade test of round `c` for `B` at that
    store can return `true`, and every member of the set for `S.a (c − 1) + Δ` is awake at `c − 1`,
    then `B` is compatible with `T`. -/
theorem phaseGrade_compatible_of_previousSGHistory_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : BelowOneThirdOn S rho Hs)
    {c : Round} (hc : 1 ≤ c) {p : DecoupledConsensusModel.Protocol.Phase}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hdomainHor : M.domain S.E S.hc c p ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc c p))
    {T B : Block V}
    (hFT : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core.F T)
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1) T)
    (hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.core.F
      S.hc.η_SG c (M.early S.E S.hc c p) (M.late S.E S.hc c p) B ⇢ true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    Block.compatible B T = true :=
  Restated.phaseGrade_compatible_previousSGHistory_l65 facts S Hs Xb hf hHs hHsXb hbelow hc
    hpost hdomainHor hw hFT hsg hgrade hA

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

/-- Along the path `W` with the admissible fields `hf`: if `S.a r` is in the horizon, `w` is in the
    set for `domain r g1`, `n` is a node state of `w`'s round-`r` action read along `W` (`hn`), the
    grade-one entry of `n`'s frame at round `r` is `root`, `L` is the active prefix of `root` in
    `n`'s filtered tree, and `lo ≤ domain r g1`, then every outcome of the grade-1 store grade of
    round `r` for `L` at `w`'s store in `W (strictEventIndex rho (domain r g1))` is `true`. -/
theorem activeActionAnchor_storeGrade_g1_actionHistoryOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    {root L : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hframe : (M.readFrame n.cache (M.toHealing n.st.core) r).g1 = some (some root))
    (hactive : M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) root =
      some L)
    (hgat : lo ≤ M.domain S.E S.hc r .g1) :
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 L ⇢ b → b = true := by
  intro b hb
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hbase := Restated.actionFrame_g1On facts S Hs Xb hf hr hhor hw hgat n hn fr hfr
  have hfs := hframe.symm.trans hbase
  rcases fr with _ | raw
  · cases hfs
  have hrootEq : root = M.clipGrade raw n.st.core.F := Option.some.inj (Option.some.inj hfs)
  have hLraw : Block.Preceq L raw := by
    have hLroot : Block.Preceq L root :=
      preceq_eq_true_iff_Preceq.mp (facts.gr.activePrefix_preceq hactive)
    rw [hrootEq] at hLroot
    exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw _)
  obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) raw
  have hrawTrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl braw hbraw
  exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ r .g1 hLraw braw hbraw hrawTrue b hb

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

end

/-! ## SG emissions and FG confirmation witnesses after the opening votes -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open scoped DC
local macro "rah% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Execution.RecoveryInitialSourceNamedActionHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))
local macro "p62% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_62)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along the path `W`, if the votes of round `r + 1`'s opening slot by the set form a cone over
    `T`, those committee members pass the grade-1 awake test at their vote ticks (`hrun`), and a
    node state `n` of `w`'s round-`(r + 1)` action read has its FG root compatible with `T`
    (`hroot`), then the live confirmed block of `n` is compatible with `T`. -/
private theorem liveConfirmed_compatible_of_openingVotes₆₅ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {r : Round} {T : Block V}
    (hgf : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc (r + 1))
      (fun X => Block.Preceq T X))
    (hpost : lo ≤ M.vote_time S.E (M.opening_slot S.hc (r + 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w) (r + 1))
    (hroot : Block.compatible (M.get_fg_root (M.toHealing n.st.core).toFG) T = true)
    (hrun : ∀ x ∈ S.E.committee (M.opening_slot S.hc (r + 1)),
      x ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (r + 1))) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc (M.opening_slot S.hc (r + 1)))) :
    Block.compatible n.st.core.live_confirmed T = true := by
  have hca := Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S
    (r + 1)
  have hconfHor : M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) ≤ rho.horizon := by
    rw [hca]; exact hhor
  have hopen : 0 < M.opening_slot S.hc (r + 1) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hvoteConf := facts.sch.Protocol_vote_time_le_confirmation_time S.E
    (M.opening_slot S.hc (r + 1))
  have hmemA := mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
      facts S rho w (r + 1) _ hmemA n hn with ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
  · -- Case: the live confirmed block is a confirmation of the opening slot.
    have hheads : ∀ x ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc (r + 1))),
        x ∈ S.E.committee (M.opening_slot S.hc (r + 1)) →
        ∃ c : M.Cache, M.onPhaseTick S.E S.hc
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st.core.toHealing
            (M.vote_time S.E (M.opening_slot S.hc (r + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).cache ⇢ c ∧
        let n := M.mkNode
          (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st
            (M.vote_time S.E (M.opening_slot S.hc (r + 1))))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).record c
        ∃ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr ∧
        ∃ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
        ∃ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
        ∃ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H ∧
          Block.Preceq T H := by
      intro x hx hxc
      have hxV : x ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (r + 1))) := hHs _ _ hvoteConf hx
      obtain ⟨X, hTX, hXrun, hXemit⟩ := hgf x hxV hxc
      obtain ⟨cx, hcx, -⟩ := (p62% exists_read_of_world₆₂) facts S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x)
        (M.vote_time S.E (M.opening_slot S.hc (r + 1)))
      obtain ⟨Tr, L, L', Hd, hTr, hL, hL', hHd⟩ := (p62% voterHead_outcome₆₂) facts S
        (M.mkNode
          (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st
            (M.vote_time S.E (M.opening_slot S.hc (r + 1))))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).record cx)
      obtain ⟨Cn, hCerase, hCrun, hCemit⟩ :=
        Restated.voterHead_runBlock_and_emitsOn facts S Hs Xb hf hHsXb hxV hopen hxc
          (hvoteConf.trans hconfHor) hpost cx hcx (hrun x hxc hxV) Tr hTr L hL L' hL' Hd hHd
      have heq := Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hCemit rfl
      have hrootEq : X.root = Cn.root := by
        simpa only [Proofs.NamedWire.erase_root] using congrArg GoldfishVote.head heq
      have hXC : X = Cn :=
        hf.rootCollisionFree.root_injective X Cn hXrun hCrun
          X Cn (Or.inl (Proofs.NamedAncestry.named_self X))
            (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrootEq
      refine ⟨cx, hcx, ?_⟩
      refine ⟨Tr, hTr, L, hL, L', hL', Hd, hHd, ?_⟩
      rw [← hCerase, ← hXC]
      exact hTX
    have hcutAction : M.support_cutoff S.E (M.opening_slot S.hc (r + 1)) ≤
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
      (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _).trans (le_of_eq hca)
    obtain ⟨c0, hc0, st0, hst0, hneq⟩ := hn
    have hcache : n.cache = c0 := by
      subst hneq
      exact facts.nd.mkNode_cache _ _ _
    rw [hcache] at hC
    rw [← hca] at hc0 hC
    have hTC := Restated.genuineConfirmation_compatible_of_priorProtectedHeadsOn facts
      S Hs Xb hf hHs hHsXb hcom (hHs _ _ hcutAction hw) hopen hpost hconfHor c0 hc0 hC hheads
      (fun x hxc hx => hrun x hxc (hHs _ _ hvoteConf hx))
    rw [← hClive]
    exact compatible_of_cases (compatible_cases hTC).symm
  · rw [← hRlive, hRroot,
      ← Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_openingConfStore facts
        S rho w (r + 1) _ hmemA n hn]
    exact hroot

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hbelow`: if every round-`r` action emission of a member of the set for `S.a r` selects
    only blocks compatible with `T` (`hsg`), the votes of round `r + 1`'s opening slot by the set
    form a cone over `T` (`hgf`), `lo ≤ S.a r`, `S.a (r + 1)` is in the horizon, every node state of
    the round-`(r + 1)` action read of every member of the set for `S.a (r + 1)` has its FG root
    compatible with `T` (`hroots`), and every member of the set for `S.a r + Δ` is awake at `r`,
    then every round-`(r + 1)` action emission of a member of the set for `S.a (r + 1)` selects only
    blocks compatible with `T`. -/
theorem sgEmissionsCompatible_succ_of_previousSGHistory_and_openingVotes_namedOn
    (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {r : Round} {T : Block V}
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs r T)
    (hgf : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc (r + 1))
      (fun X => Block.Preceq T X))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ rho.horizon)
    (hroots : ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 1)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w) (r + 1),
      Block.compatible (M.get_fg_root (M.toHealing n.st.core).toFG) T = true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (r + 1) T := by
  have hΔ := S.E.Δ_pos
  have hc : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
  have hcPred : r + 1 - 1 = r := Nat.add_sub_cancel r 1
  have hactProp := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
    facts S (Nat.lt_succ_self r)
  have hopenPost : lo ≤ M.vote_time S.E (M.opening_slot S.hc (r + 1)) := by
    have h := facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc (r + 1))
    linarith
  have hdomainEq : M.domain S.E S.hc (r + 1) .g1 =
      M.proposal_time S.E (M.opening_slot S.hc (r + 1)) :=
    (facts.gr.Sts_domain_g1_eq_opening S (r + 1)).trans (facts.gr.opening_eq_proposal_time _ _ _)
  have hgatG1 : lo ≤ M.domain S.E S.hc (r + 1) .g1 := by
    rw [hdomainEq]; linarith
  intro w hw n hn0 D hD hemit
  show ∀ A2 : Option (Block V),
    M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ G : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G →
    G.compatible T = true
  intro A2 hA2 G hG
  have hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w) (r + 1) := hn0
  have hmemA := mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho w (r + 1) :=
    ⟨_, hmemA, hn⟩
  have hrootT := hroots w hw n hn
  -- Every committee member of round `r + 1`'s opening slot passes the grade-1 awake test at its
  -- vote ticks.
  have hrunO : ∀ x ∈ S.E.committee (M.opening_slot S.hc (r + 1)),
      x ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (r + 1))) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc (M.opening_slot S.hc (r + 1))) := by
    intro x _ hx j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (r + 1))) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc (r + 1)]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S (r + 1)
      have h3 : lo ≤ M.a S.hc S.E.Δ r := hpost
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx hwin
  have hliveT := liveConfirmed_compatible_of_openingVotes₆₅ facts S Hs Xb hf hHs hHsXb hcom
    hgf hopenPost hhor hw n hn hrootT hrunO
  have hdomainHor : ∀ p : DecoupledConsensusModel.Protocol.Phase,
      M.domain S.E S.hc (r + 1) p ≤ rho.horizon :=
    fun p => (facts.gr.domain_le_a S (r + 1) p).trans hhor
  have hwDomain : ∀ p : DecoupledConsensusModel.Protocol.Phase,
      w ∈ Hs (M.domain S.E S.hc (r + 1) p) :=
    fun p => hHs _ _ (facts.gr.domain_le_a S (r + 1) p) hw
  have hpostC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 - 1)) := by
    rw [hcPred]; exact hpost
  have hAC : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 - 1)) + S.E.Δ),
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (r + 1 - 1))) →
        M.awake_for_grade2 S u (W j u) (r + 1 - 1) := by
    rw [hcPred]; exact hA
  have hsgC : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (r + 1 - 1) T := by
    rw [hcPred]; exact hsg
  rcases compatible_cases hrootT with hrootBelow | hTBelow
  · have hFT : ∀ p : DecoupledConsensusModel.Protocol.Phase, Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F T := by
      intro p
      have hFmono : Block.Preceq
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core.F :=
        F_mono_along₆₅ facts S hf.onePath w
          (strictEventIndex_mono₆₅ rho (facts.gr.domain_le_a S (r + 1) p))
      have hFroot := (p62% F_preceq_fgRoot_along₆₂s) facts S hf.sorted hf.onePath w
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
      have hfg := (p62% actionReadFrom_fgRoot₆₂s) facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w) (r + 1) n hn
      rw [← hfg] at hFroot
      exact preceq_trans_Preceq hFmono (preceq_trans_Preceq hFroot hrootBelow)
    obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (r + 1)
    have hgR : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n (r + 1) ⇢ g := hg
    have hanchorT : Block.compatible g.anchor T = true := by
      obtain ⟨a0, ha0⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) (r + 1)
        (M.readFrame n.cache (M.toHealing n.st.core) (r + 1)).g1
      have hga := facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc
        (M.toHealing n.st.core) (r + 1) g hg a0 ha0
      rcases facts.gr.anchor_cases S.E S.hc _ _ _ a0 ha0 with
        hroot0 | ⟨root, L, hframe, hactive, haL⟩
      · rw [hga, hroot0]
        exact hrootT
      · rw [hga, haL]
        have hLgrade := Restated.activeActionAnchor_storeGrade_g1_actionHistoryOn facts
          S Hs Xb hf (Nat.succ_pos r) hhor (hwDomain .g1) n hn hframe hactive hgatG1
        exact Restated.phaseGrade_compatible_of_previousSGHistory_namedOn facts
          S Hs Xb hf hHs hHsXb hbelow hc (p := .g1) hpostC (hdomainHor .g1) (hwDomain .g1)
          (hFT .g1) hsgC
          (storeGrade_true_of_all₆₅ facts S.E S.hc _ (r + 1) .g1 L hLgrade) hAC
    rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers facts S rho w (r + 1)
        n hnAt g hgR A2 hA2 G hG with
      hwalk | ⟨Q, hQ, hout⟩ | ⟨_, _, hout⟩ | ⟨_, _, hout⟩
    · exact (rah% actionHistory_compatible_ancestor) hwalk.2.1 hliveT
    · rw [hout]
      have hsel : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (r + 1) ⇢ some Q := by
        have h := returns_map_intro₆₅
          (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ g hgR
        rwa [hQ] at h
      have hQgrade := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hsel
      exact Restated.phaseGrade_compatible_of_previousSGHistory_namedOn facts
        S Hs Xb hf hHs hHsXb hbelow hc (p := .g2) hpostC (hdomainHor .g2) (hwDomain .g2)
        (hFT .g2) hsgC
        (storeGrade_true_of_all₆₅ facts S.E S.hc _ (r + 1) .g2 Q hQgrade) hAC
    · rw [hout]
      exact hrootT
    · rw [hout]
      exact hanchorT
  · have hrootVote := Restated.Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt
      facts S rho w (r + 1) _ hmemA n hn A2 hA2 G hG
    exact compatible_of_cases (Or.inr (preceq_trans_Preceq hTBelow hrootVote))

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₅w {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- If `n` is a node state of `v`'s round-`r` action read and the FG source at the round of `n`'s
    slot can return `some B`, then the FG source of `n` at round `r` can return `some B`. -/
private theorem nodeFGSource_of_actionFGSource₆₅ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some B := by
  have hmem := mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r := ⟨_, hmem, hn⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hnAt
  have h : (do
      let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s)
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some B := hsource
  rw [hround] at h
  exact h

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hbelow`: if every round-`r` action emission of a member of the set for `S.a r` selects
    only blocks compatible with `T` (`hsg`), the votes of round `r + 1`'s opening slot by the set
    form a cone over `T` (`hgf`), `lo ≤ S.a r`, `lo` is at most that slot's vote time, its
    confirmation time is in the horizon, `w` is in the set for `S.a (r + 1)`, `n` is a node state of
    `w`'s round-`(r + 1)` action read whose FG root is compatible with `T` and whose FG confirmation
    witness can return `some Wb`, and every member of the set for `S.a r + Δ` is awake at `r`, then
    `Wb` is compatible with `T`. -/
theorem fgConfirmationWitness_compatible_of_previousSGHistory_and_openingVotes_namedOn
    (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {r : Round} {T Wb : Block V}
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs r T)
    (hgf : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc (r + 1))
      (fun X => Block.Preceq T X))
    (hprevPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hpost : lo ≤ M.vote_time S.E (M.opening_slot S.hc (r + 1)))
    (hhor : M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w) (r + 1))
    (hroot : Block.compatible (M.get_fg_root (M.toHealing n.st.core).toFG) T = true)
    (hW : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some Wb)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    Block.compatible Wb T = true := by
  have hc : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
  have hcPred : r + 1 - 1 = r := Nat.add_sub_cancel r 1
  have hca := Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S
    (r + 1)
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ rho.horizon := by
    rw [← hca]; exact hhor
  -- Every committee member of round `r + 1`'s opening slot passes the grade-1 awake test at its
  -- vote ticks.
  have hrunO : ∀ x ∈ S.E.committee (M.opening_slot S.hc (r + 1)),
      x ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (r + 1))) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc (M.opening_slot S.hc (r + 1))) := by
    intro x _ hx j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (r + 1))) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc (r + 1)]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S (r + 1)
      have h3 : lo ≤ M.a S.hc S.E.Δ r := hprevPost
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx hwin
  have hliveT := liveConfirmed_compatible_of_openingVotes₆₅ facts S Hs Xb hf hHs hHsXb hcom
    hgf hpost hactionHor hw n hn hroot hrunO
  have hmemA := mem_stateBeforeTime_along₆₅ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho w (r + 1) :=
    ⟨_, hmemA, hn⟩
  obtain ⟨o, hsource0, hmap⟩ := returns_map_elim₆₅w _ _ _ hW
  obtain ⟨Cfg, ho, hWCfg⟩ := Option.map_eq_some_iff.mp hmap
  subst ho
  have hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Cfg :=
    hsource0
  have hsourceNode := nodeFGSource_of_actionFGSource₆₅ facts S hf n hn hsource
  -- the Q2 of `n` has an outcome `some Q`
  obtain ⟨Q, hQ⟩ : ∃ Q : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (r + 1) ⇢ some Q := by
    have hsrc0 := hsourceNode
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsrc0
    obtain ⟨A2, hA2, hsrc⟩ := ((p60% returns_bind_iff₆₀s) _ _ _).1 hsrc0
    obtain ⟨Q2, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
    subst hA2Q
    obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (r + 1)
    have hGQ : G.Q2 = some Q2 :=
      (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
    refine ⟨Q2, ?_⟩
    have h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (r + 1) ⇢ G.Q2 :=
      returns_map_intro₆₅
        (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG
    rwa [hGQ] at h
  have hQaction := Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts
    S rho w (r + 1) _ hmemA n hn hQ
  have hrootQ : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) Q :=
    preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hQaction)
  have hQCfg : Block.Preceq Q Cfg :=
    Restated.Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 facts S rho w (r + 1)
      _ hmemA n hn hQ (Proofs.ModelProperties.Preceq_self Q) hsourceNode
  have hCfgT : Block.compatible Cfg T = true := by
    rcases compatible_cases hroot with hrootBelow | hTBelow
    · have hdomainHor : M.domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
        (facts.gr.domain_le_a S (r + 1) .g2).trans hactionHor
      have hFmono : Block.Preceq
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core.F :=
        F_mono_along₆₅ facts S hf.onePath w
          (strictEventIndex_mono₆₅ rho (facts.gr.domain_le_a S (r + 1) .g2))
      have hFroot := (p62% F_preceq_fgRoot_along₆₂s) facts S hf.sorted hf.onePath w
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
      have hfg := (p62% actionReadFrom_fgRoot₆₂s) facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w) (r + 1) n hn
      rw [← hfg] at hFroot
      have hFT : Block.Preceq
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F T :=
        preceq_trans_Preceq hFmono (preceq_trans_Preceq hFroot hrootBelow)
      have hQgrade := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
      have hQT : Block.compatible Q T = true :=
        Restated.phaseGrade_compatible_of_previousSGHistory_namedOn facts
          S Hs Xb hf hHs hHsXb hbelow hc (p := .g2)
          (by rw [hcPred]; exact hprevPost) hdomainHor
          (hHs _ _ (facts.gr.domain_le_a S (r + 1) .g2) hw) hFT
          (by rw [hcPred]; exact hsg)
          (storeGrade_true_of_all₆₅ facts S.E S.hc _ (r + 1) .g2 Q hQgrade)
          (by rw [hcPred]; exact hA)
      rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
          facts S rho w (r + 1) _ hmemA n hn hQ hsource with ⟨C, -, hClive, -, -, hCfgC⟩ | hlocal
      · rw [hClive] at hCfgC
        exact (rah% actionHistory_compatible_ancestor) hCfgC hliveT
      · rw [hlocal]
        exact hQT
    · exact compatible_of_cases
        (Or.inr (preceq_trans_Preceq hTBelow (preceq_trans_Preceq hrootQ hQCfg)))
  apply (rah% actionHistory_compatible_ancestor) (B := Cfg) ?_ hCfgT
  rw [← hWCfg]
  obtain ⟨D, -, hDerase, hDderiv, -⟩ :=
    Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho w (r + 1) n hnAt
      Cfg hsource
  rw [hDderiv, ← hDerase]
  exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg D

end

end DecoupledConsensusModel.Sts.Restated
