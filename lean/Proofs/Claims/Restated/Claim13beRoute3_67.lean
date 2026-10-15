import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_51b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_56b
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_66
import Proofs.Claims.Restated.Claim13beRoute3_66b
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGRepresentation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGTargetCanonicality
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeSeedK3
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeSeedSettlement
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The FG source under a fixed-height justification root

Theorems about the FG source of an action read when a fixed-height justification root holds, and the
bound of that source's height by the parent of the next opening proposal, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`. Every theorem reads the run along a
path `W` of the run.
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

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₇ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₇ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₇ S rho hsorted]
  exact (hW _).1

/-- Every node state of the round-`r` action read from `before` has as its core store an outcome of
    the confirmation update of `before`'s store staged at round `r`'s action instant. -/
private theorem actionReadFrom_core₆₇ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ st : M.NS, n.st = M.store_with_cache st n.cache ∧
      M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1) ⇢ st.core := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨st, by rw [facts.nd.mkNode_st, facts.nd.mkNode_cache], ?_⟩
  rw [facts.nd.mkNode_cache, facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX]
  exact hX

/-- Every node state of the round-`r` action read from `before` has the FG root of `before`'s core
    store. -/
private theorem actionReadFrom_fgRoot₆₇ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₇ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- Every node state of the round-`r` action read from `before` has the filtered tree of `before`'s
    core store. -/
private theorem actionReadFrom_filtered₆₇ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
        M.get_filtered_block_tree (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₇ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_filtered_block_tree,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₇ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₆₇ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- If the grade read at `n` can return `G`, then `n`'s candidate read can return `G`'s candidate. -/
private theorem nodeQ2_of_read₆₇ (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₇ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

/-- If every outcome of a store grade is `true`, the store grade can return `true`. -/
private theorem storeGrade_true_of_all₆₇ (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) (B : Block V)
    (h : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ b → b = true) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ true := by
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty E (M.gradeView (M.toHealing st.core)) st.core.F
    hc.η_SG r (M.early E hc r p) (M.late E hc r p) B
  have hbt : b = true := h b hb
  subst hbt
  exact hb

/-- The node state staged at slot `d`'s vote instant from `b` with the cache `cv` has slot `d` and
    the finality root of `b`'s core store. -/
private theorem dutyNode_parts₆₇ (facts : Record.Facts M) (S : Setup V) (b : M.N) (d : Slot)
    (cv : M.Cache) :
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core.s = d ∧
    M.get_fg_root (M.toHealing
        (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core).toFG =
      M.get_fg_root (M.toHealing b.st.core).toFG := by
  refine ⟨?_, ?_⟩
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s]
    exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-! ## Helpers of the source-height bound -/

omit [DecidableEq V] [Fintype V] in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₇ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

omit [DecidableEq V] [Fintype V] in
/-- Bounds on the rounds of the source-height bound, over `Nat`. -/
private theorem round_bounds₆₇ {r q1 c delay e : Nat} (hlo : r + 3 ≤ q1) (hlt : q1 < c + 1)
    (hspace : q1 + 2 + delay ≤ c + 1) (hend : c + 1 ≤ e) :
    0 < c ∧ q1 < c ∧ q1 ≤ c - 1 ∧ c - 1 < c ∧ c ≤ e ∧ c - 1 ≤ e ∧ r + 1 ≤ c ∧ r < q1 ∧ c < c + 1 := by
  omega

omit [DecidableEq V] [Fintype V] in
/-- If `o' = o + R` with `2 ≤ R`, then `o + 1 ≤ o' − 1 < o'`, `0 < o' − 1` and `o' − 1 + 1 = o'`. -/
private theorem slot_bounds₆₇ {o o' R : Nat} (h : o' = o + R) (hR : 2 ≤ R) :
    o + 1 ≤ o' - 1 ∧ o' - 1 < o' ∧ 0 < o' - 1 ∧ o' - 1 + 1 = o' := by
  omega

omit [DecidableEq V] [Fintype V] in
private theorem height_bound₆₇ {H : Nat} (h : 0 < H - 1) : H ≤ H - 1 + 1 := by
  omega

/-- The store a tick at `t` hands its first duty, staged from `st`'s core store, is the core store
    of `st` with the clock set to `t`. -/
private theorem tickStore_eq₆₇ (facts : Record.Facts M) (S : Setup V) (st : M.NS) (t : Time) :
    Restated.Vocabulary.Proofs.Optimistic.tickStore M S st.core t = (M.ns_setClock S.E st t).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, is the core store of `n`'s
    store with the clock set to the slot's vote instant. -/
private theorem voteStore_eq₆₇ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- Setting the clock of a named store keeps the FG root of its core store. -/
private theorem setClock_fgRoot₆₇ (facts : Record.Facts M) (E : Env V) (st : M.NS) (t : Time) :
    M.get_fg_root (M.toHealing (M.ns_setClock E st t).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- The store a tick at `t` hands its first duty has the FG root of the store it is staged from. -/
private theorem tickStore_fgRoot₆₇ (facts : Record.Facts M) (S : Setup V) (st : M.S) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t)).toFG =
      M.get_fg_root (M.toHealing st).toFG :=
  facts.fc.get_fg_root_toHealing_clock _ _ _

/-- The store a tick at `t` hands its first duty has the filtered tree of the store it is staged
    from. -/
private theorem tickStore_filtered₆₇ (facts : Record.Facts M) (S : Setup V) (st : M.S) (t : Time) :
    M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t)).toFG =
      M.get_filtered_block_tree (M.toHealing st).toFG :=
  facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- Every SG root the grade contract of `n`'s cache can return for `n`'s healing store at round `r`
    is an outcome of `n`'s anchor at `r`. -/
private theorem nodeAnchor_of_sgRoot₆₇ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round)
    {R : Block V}
    (hR : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ R) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ R := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  have hanchor := (facts.nd.gradeContract_sgRoot_eq_frameAnchor n.cache S.E S.hc _ r R).1 hR
  have hGR : G.anchor = R := facts.nd.Sts_gradeContract_read_anchor n.cache S.E S.hc _ r G hG R hanchor
  rw [← hGR]
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  unfold Record.Returns at hG ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, hG, rfl⟩

/-- At every node state `n`, the voter-filtered tree, the voter view, the voter support view and the
    head computed from them each have an outcome. -/
private theorem exists_headOutcome₆₇ (facts : Record.Facts M) (S : Setup V) (n : M.N) :
    ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
    ∃ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
    ∃ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
    ∃ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H := by
  obtain ⟨T0, hT0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T0 L L' (n.st.core.s - 1)
  exact ⟨T0, hT0, L, hL, L', hL', H, hH⟩

/-- A slot `d` from round `c`'s opening slot to its last slot is a slot of round `c`. -/
private theorem seedEntryRoundOf₆₇ (facts : Record.Facts M) (S : Setup V) {c : Round} {d : Slot}
    (hlo : (M.opening_slot S.hc c) ≤ d) (hhi : d ≤ (M.opening_slot S.hc (c + 1)) - 1) :
    (M.round_of S.hc d) = c := by
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hpos : 0 < (M.opening_slot S.hc c) + S.hc.R :=
    lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_two hR) (Nat.le_add_left _ _)
  rw [facts.gr.opening_slot_succ S.hc c] at hhi
  have hlt : d < (M.opening_slot S.hc c) + S.hc.R := lt_of_le_of_lt hhi (Nat.sub_lt hpos Nat.one_pos)
  have h := facts.gr.round_of_opening_slot_add S.hc c (Nat.sub_lt_left_of_lt_add hlo hlt)
  rw [Nat.add_sub_cancel' hlo] at h
  exact h

/-- Every outcome of the early confirmation votes of `st` at slot `s` is among the late confirmation
    votes. -/
private theorem confEarly_subset_late₆₇ (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₆₇ _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- If `B` is a `GenuineConfirmation` of `st` at slot `s`, then for some outcome of the early
    confirmation votes and some choice of Goldfish score outcomes, those votes are an outcome of the
    confirmation votes and the count of the late voters is less than twice the score of `B`. -/
private theorem genuine_eligible₆₇ (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
    {hc : Protocol.HealConfig} {st : M.S} {s : Slot} {B : Block V}
    (hB : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) E hc st s B) :
    ∃ (early : Finset (GoldfishVote V)) (sc : Block V → Nat),
      Restated.Vocabulary.Protocol.confEarly M E st s ⇢ early ∧
      Restated.Vocabulary.Protocol.confVotes M E st s ⇢
        early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true) ∧
      (∀ B', M.goldfish_score E st.T
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        s B' ⇢ sc B') ∧
      M.voters_count E (Restated.Vocabulary.Protocol.confLate M E st s) s < 2 * sc B := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty contract E hc st.toHealing
    (M.round_of hc st.s)
  have hearly : Restated.Vocabulary.Protocol.confEarly M E st s ⇢
      beforeCutoff tm (M.support_cutoff E s) (st.pool s) :=
    returns_map_intro₆₇ _ _ _ htm
  have hu := returns_map_intro₆₇
    (fun e => e.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    _ _ hearly
  choose sc hsc using fun B' => facts.fc.goldfish_score_nonempty E st.T
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true)) s B'
  obtain ⟨H, hH⟩ := facts.fc.ghost_nonempty R (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B' => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B'))
  have helig := hB.genuine R hR _ hu sc hsc H hH
  obtain ⟨st', hst'⟩ := facts.dt.update_confirmation_with_nonempty contract E hc st s
  have hW := facts.hd.update_confirmation_with_live_confirmed_of_eligible contract E hc st s tm htm
    R hR sc hsc H hH helig st' hst'
  have hBH : B = H := (hB.selected st' hst').symm.trans hW
  subst hBH
  exact ⟨_, sc, hearly, hu, hsc, of_decide_eq_true helig⟩

/-- Under the source and target vote conditions, if `g` is an outcome of `B`'s Goldfish score over
    the source votes with the late voter count less than `2 * g`, and `A` is compatible with `B`,
    then `B` is an ancestor of every outcome of the Goldfish fork choice from `A`. -/
private theorem captures_of_confirmation_one₆₇ (facts : Record.Facts M)
    (E : Env V) (σ : Block V → M.CS) (h_max : Height)
    (sourceTree targetTree tree : Finset (Block V)) (cur : Slot)
    (sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hN : Restated.Vocabulary.Protocol.Numerator M sourceEarly sourceLate sourceVotes)
    (hT : Restated.Vocabulary.Protocol.AdoptionTransport M sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (g : ℕ) (hg : M.goldfish_score E sourceTree sourceVotes sourceVotes s B ⇢ g)
    (heligible : M.voters_count E sourceLate s < 2 * g)
    (hsub : targetSupport ⊆ targetVotes)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    ∀ X : Block V, M.goldfish_fork_choice E σ h_max targetTree cur A tree
        targetVotes targetSupport s ⇢ X → Block.Preceq B X := by
  intro X hX
  have hS := fun u => facts.fc.targets_under_nonempty sourceTree B u
  have hTt := fun u => facts.fc.targets_under_nonempty targetTree B u
  let tS : GoldfishVote V → Bool := fun u => Classical.choose (hS u)
  let tT : GoldfishVote V → Bool := fun u => Classical.choose (hTt u)
  have htS : ∀ u, M.targets_under sourceTree B u ⇢ tS u := fun u => Classical.choose_spec (hS u)
  have htT : ∀ u, M.targets_under targetTree B u ⇢ tT u := fun u => Classical.choose_spec (hTt u)
  obtain ⟨sS, hsS⟩ := facts.fc.raw_supporters_nonempty sourceTree sourceVotes sourceVotes s B
  obtain ⟨sT, hsT⟩ := facts.fc.raw_supporters_nonempty targetTree targetVotes targetSupport s B
  have hforward : ∀ u ∈ sourceVotes, tS u = true →
      (u ∈ targetSupport ∧ tT u = true) ∨ M.equivocates targetVotes u.val_index = true := by
    intro u hu htu
    rcases hT.forward u hu (tS u) (htS u) htu with ⟨hmem, hall⟩ | heq
    · exact Or.inl ⟨hmem, hall (tT u) (htT u)⟩
    · exact Or.inr heq
  have hadopt := facts.fc.confirmation_adoption hN.early_late hN.filtered tS htS tT htT hforward
    hT.backward g hg heligible sS hsS sT hsT
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority E σ h_max targetTree tree cur
    targetVotes targetSupport s hsub sT hsT hadopt.2 hcompatible hpath X hX

/-- If a member of the set for the confirmation instant of round `r`'s opening slot has a
    `GenuineConfirmation` of a descendant of `T.erase`, and every voter of the interior slots up to
    `s` has FG root `J.erase`, `h_max` at most `J`'s height plus one and anchors compatible with
    `T.erase`, then every committee member of those slots in the set for its vote instant votes
    along `W` for a descendant of `T.erase`. -/
private theorem genuineClearCone₆₇ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {r : Round}
    {J T : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    (hTrun : Restated.RunBlockOn M S rho W Xb T) (hJT : Block.Preceq J.erase T.erase)
    {u : V} (huConf : u ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc r))) {C : Block V}
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) u).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      (M.opening_slot S.hc r) C)
    (hTC : Block.Preceq T.erase C)
    (hpost : lo ≤ M.proposal_time S.E (M.opening_slot S.hc r))
    (hsourceHor : M.confirmation_time S.E (M.opening_slot S.hc r) ≤ rho.horizon)
    {s : Slot} (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    (hvoteRoot : ∀ d : Slot, (M.opening_slot S.hc r) + 1 ≤ d → d ≤ s →
      ∀ w ∈ Hs (M.vote_time S.E d),
      M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)).core).toFG =
          J.erase)
    (hvoteCap : ∀ d : Slot, (M.opening_slot S.hc r) + 1 ≤ d → d ≤ s →
      ∀ w ∈ Hs (M.vote_time S.E d),
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hanchor : ∀ d : Slot, (M.opening_slot S.hc r) + 1 ≤ d → d ≤ s →
      ∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
            (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c)
          (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
            (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).st.core.s) ⇢ A →
        Block.compatible A T.erase = true)
    (hrun : ∀ d : Slot, (M.opening_slot S.hc r) + 1 ≤ d → d ≤ s →
      ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) → ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    ∀ k : Slot, (M.opening_slot S.hc r) + 1 ≤ k → k ≤ s →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb k (fun X => Block.Preceq T.erase X) := by
  have huSC : u ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc r)) :=
    hHs _ _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _) huConf
  have hpostLo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc r) + 1) :=
    hpost.trans ((facts.sch.proposal_time_lt_vote_time S.E _).le.trans
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _)))
  intro k hklo
  induction k, hklo using Nat.le_induction with
  | base =>
      intro hks w hw hcommittee
      have hvoteHor1 : M.vote_time S.E ((M.opening_slot S.hc r) + 1) ≤ rho.horizon :=
        (facts.sch.vote_time_mono_slots S.E hks).trans hvoteHor
      have hwVF : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc r)) :=
        hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E _).le hw
      have hloVF : lo ≤ M.view_freeze S.E (M.opening_slot S.hc r) :=
        hpost.trans ((facts.sch.proposal_time_lt_vote_time S.E _).le.trans
          (facts.sch.vote_time_le_view_freeze S.E _))
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc r) + 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).cache
      have hcompat := hanchor _ (le_refl _) hks w hw c hc
      set n := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc r) + 1)))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).record c
        with hn_def
      have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) _ := facts.nd.mkNode_st _ _ _
      have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w
          ((M.opening_slot S.hc r) + 1) :=
        ⟨_, mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath _, c, hc, rfl⟩
      have hroot := hvoteRoot _ (le_refl _) hks w hw
      have hcap := hvoteCap _ (le_refl _) hks w hw
      have hrootC : Block.Preceq
          (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core
            ((M.opening_slot S.hc r) + 1))).toFG) C := by
        rw [voteStore_eq₆₇ facts, hroot]
        exact Proofs.ModelProperties.Preceq_trans hJT hTC
      have hCproc := Restated.voterProcessedTarget_of_genuineConfirmation_after_gstOn facts
        S Hs Xb hf hHs hHsXb huSC hwVF hpost hsourceHor hgenuine hrootC
      obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core
          ((M.opening_slot S.hc r) + 1))).toFG.toSG.toGoldfishStore
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core
          ((M.opening_slot S.hc r) + 1))).s
      have hTP : T.erase ∈ P := Restated.ancestorProcessed_of_voterProcessedOn facts
        S Hs Xb hf hwVF P hP (hCproc P hP) hloVF T.erase hTC
      have hcandpath := Restated.fixedRoot_targetCandidateAndPathOn facts S Hs Xb hf hHsXb
        hJrun hTrun hJT (d := (M.opening_slot S.hc r) + 1) (Nat.succ_pos _)
        (by simpa only [Nat.add_sub_cancel] using hwVF) hroot hcap P hP hTP
        (by simpa only [Nat.add_sub_cancel] using hloVF) c hc
      have hslot : n.st.core.s = (M.opening_slot S.hc r) + 1 := by
        rw [hnst]
        try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
        rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
      obtain ⟨T0, hT0, L, hL, L', hL', H, hH⟩ := exists_headOutcome₆₇ facts S n
      have hhead : Block.Preceq T.erase H := by
        by_cases hall : ∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) ⇢ R → Block.Preceq R T.erase
        · obtain ⟨P1, hP1⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
            (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s
          have hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
              (M.toHealing n.st.core) ⇢
                M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P1 := by
            unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
            exact (returns_bind_iff₆₇ _ _ _).2 ⟨P1, hP1, (Record.returns_pure _ _).2 rfl⟩
          have hTK : T.erase ∈ M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P1 := by
            rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E n.st.core P1
              hP1 T0 hT0]
            exact (hcandpath T0 hT0).1
          obtain ⟨htransport, hsub, hanchorCompat, hpath, -, -⟩ :=
            Restated.nextVoteAdoption_of_frozenCandidateAtReadOn facts S Hs Xb hf hHs hHsXb
              huConf hpost hsourceHor hw c hc hK hTK hall (hrun _ (le_refl _) hks w hcommittee hw)
          obtain ⟨early, sc, hearly, hvotes, hsc, helig⟩ := genuine_eligible₆₇ facts hgenuine
          have hscT : sc C ≤ sc T.erase :=
            facts.fc.goldfish_score_le_of_Preceq _ _ _ _ _ hTC _ (hsc C) _ (hsc T.erase)
          have hel := confEarly_subset_late₆₇ facts S.E _ _ early hearly
          obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
          have hs' : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s n.st.core
          have hTn : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_T n.st.core
          have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc n.st.core.s) ⇢ R := by
            rw [hs'] at hR
            exact hR
          have hprev : n.st.core.s - 1 = M.opening_slot S.hc r := by
            rw [hslot]
            simp
          have hX := (facts.fc.get_head_in_tree_split_with (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) T0 L L' (n.st.core.s - 1) R hR H).1 hH
          rw [hprev] at hX
          exact captures_of_confirmation_one₆₇ facts S.E (M.toHealing n.st.core).σ
            (M.toHealing n.st.core).h_max _ (M.toHealing n.st.core).T T0 (M.toHealing n.st.core).s
            early _ _ L L' (M.opening_slot S.hc r) ⟨hel, rfl⟩
            (by rw [hTn]; exact htransport _ hvotes L hL L' hL')
            (sc T.erase) (hsc T.erase) (by omega) (hsub L hL L' hL') (hanchorCompat R hR')
            (fun hRB D hRD hDR hDB => hpath R hR' hRB D hRD hDR hDB T0 hT0) H hX
        · push Not at hall
          obtain ⟨R, hR, hRT⟩ := hall
          have hA := nodeAnchor_of_sgRoot₆₇ facts S n _ hR
          rcases compatible_cases (hcompat R hA) with hRT' | hTR
          · exact absurd hRT' hRT
          · exact Proofs.ModelProperties.Preceq_trans hTR
              (Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts
                S rho w _ n hnmem R hA T0 hT0 L hL L' hL' H hH)
      obtain ⟨X, hXH, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts S Hs Xb hf
        hHsXb hw (Nat.succ_pos _) hcommittee hvoteHor1 hpostLo c hc
        (hrun _ (le_refl _) hks w hcommittee hw) T0 hT0 L hL L' hL' H hH
      exact ⟨X, by rw [hXH]; exact hhead, hXrun, hXemit⟩
  | succ k hk ih =>
      intro hsuccLast
      have hkLast : k ≤ s := (Nat.le_succ k).trans hsuccLast
      have hcone := ih hkLast
      have hkPos : 0 < k := (Nat.succ_pos _).trans_le hk
      have hdlo : (M.opening_slot S.hc r) + 1 ≤ k + 1 := hk.trans (Nat.le_succ k)
      have hdHor : M.vote_time S.E (k + 1) ≤ rho.horizon :=
        (facts.sch.vote_time_mono_slots S.E hsuccLast).trans hvoteHor
      have hpostK : lo ≤ M.vote_time S.E k :=
        hpostLo.trans (facts.sch.vote_time_mono_slots S.E hk)
      intro w hw hcommittee
      have hwVF : w ∈ Hs (M.view_freeze S.E k) :=
        hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E k).le hw
      have hwSC : w ∈ Hs (M.support_cutoff S.E k) :=
        hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E k) hw
      have hloVF : lo ≤ M.view_freeze S.E k :=
        hpostK.trans (facts.sch.vote_time_le_view_freeze S.E k)
      have hroot := hvoteRoot (k + 1) hdlo hsuccLast w hw
      have hcap := hvoteCap (k + 1) hdlo hsuccLast w hw
      have hrootC : Block.Preceq
          (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).toFG) C := by
        rw [voteStore_eq₆₇ facts, hroot]
        exact Proofs.ModelProperties.Preceq_trans hJT hTC
      have hCproc :=
        Restated.voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gstOn facts
          S Hs Xb hf hHs hHsXb huSC hwVF hk hpost hdHor hgenuine hrootC
      obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).toFG.toSG.toGoldfishStore
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).s
      have hTP : T.erase ∈ P := Restated.ancestorProcessed_of_voterProcessedOn facts
        S Hs Xb hf hwVF P hP (hCproc P hP) hloVF T.erase hTC
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core.toHealing
        (M.vote_time S.E (k + 1)) (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).cache
      have hanchor' := hanchor (k + 1) hdlo hsuccLast w hw c hc
      set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st
          (M.vote_time S.E (k + 1))) (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).record c
        with hn_def
      have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st (M.vote_time S.E (k + 1))) _ := facts.nd.mkNode_st _ _ _
      have hcandpath := Restated.fixedRoot_targetCandidateAndPathOn facts S Hs Xb hf hHsXb
        hJrun hTrun hJT (d := k + 1) (Nat.succ_pos k)
        (by simpa only [Nat.add_sub_cancel] using hwVF) hroot hcap P hP hTP
        (by simpa only [Nat.add_sub_cancel] using hloVF) c hc
      have hstep := Restated.fixedRoot_goldfishConeStepOn facts S Hs Xb hf hHs hHsXb hcom
        hkPos hpostK hdHor hcone hwSC c hc
        ⟨fun K hK => (hcandpath K hK).1,
          by rw [hnst, facts.nd.store_with_cache_get_fg_root, hroot]; exact hJT,
          hanchor',
          fun A hA K hK D hAD hDA hDT hDne => (hcandpath K hK).2 A hA D hAD hDA hDT hDne⟩
      obtain ⟨T0, hT0, L, hL, L', hL', H, hH⟩ := exists_headOutcome₆₇ facts S n
      have hloVote : lo ≤ M.vote_time S.E (k + 1) :=
        hpostK.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ k))
      obtain ⟨X, hXH, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts S Hs Xb hf
        hHsXb hw (Nat.succ_pos k) hcommittee hdHor hloVote c hc
        (hrun (k + 1) hdlo hsuccLast w hcommittee hw) T0 hT0 L hL L' hL' H hH
      exact ⟨X, by rw [hXH]; exact hstep T0 hT0 L hL L' hL' H hH, hXrun, hXemit⟩

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `w`'s store in the world `wd` holds a fixed-height justification root at `H`, then some run
    block `J` read through `Xb` along `W` erases to that store's justified block and has height
    `H − 1`. -/
theorem fixedRootSource_namedTargetOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {W : Nat → V → M.N}
    {H : Height} {w : V} {read : Time} {wd : V → M.N}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read wd) :
    ∃ J : NamedBlock V,
      J.erase = (wd w).st.J ∧
        Restated.RunBlockOn M S rho W Xb J ∧
          (M.derive_named S.E S.cfg J).h = H - 1 :=
  Restated.fixedRoot_namedTarget_of_fixedRootOn facts S Hs Xb hfix

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the committees condition, if the opening cone root lock of
    height `H`, round `q` and slot `opening_slot (q + 1) − 1` holds along `W`, then some member `v0`
    of the set for `S.a q` has a round-`q` action block `K` that is a descendant of every round-`q`
    action block in `W` of every member of that set, and the committee of slot
    `opening_slot (q + 1) − 1` votes along `W` for descendants of `K`. -/
theorem fixedRootSource_commonActionCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hcom : Restated.HonestCommitteesOn M S Hs) {H : Height} {q : Round} {wd : V → M.N}
    (hlock : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H
      q ((M.opening_slot S.hc (q + 1)) - 1) wd
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)))) :
    ∃ K : Block V,
      (∃ v0 ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
        ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v0) q,
        ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
          M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ K) ∧
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
        ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
        ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
          Block.Preceq B K) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc (q + 1)) - 1)
        (fun X => Block.Preceq K X) :=
  Restated.fixedRoot_commonActionCeiling_of_lockOn facts S Hs Xb hf hHs hcom (H := H) (q := q + 1)
    (wd := wd) hlock

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `v ∈ Xb`, then for every node state `n` of `v`'s round-`r`
    action read along `W` whose FG source read can return `some Q`, some body `Cn` of `n` erases to
    `Q`, is a run block read through `Xb` along `W`, and the chain state of `n`'s core store at `Q`
    is `Cn`'s named derivation. -/
theorem fixedRootSource_namedSource_witnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {Q : Block V} :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
    ∃ Cn : NamedBlock V,
      Cn ∈ n.st.bodies ∧
      Cn.erase = Q ∧
      Restated.RunBlockOn M S rho W Xb Cn ∧
      (M.toHealing n.st.core).toFG.σ Q = M.derive_named S.E S.cfg Cn :=
  Restated.seedFresh_namedSource_witnessOn facts S Hs Xb hf hv

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the weight bound, if every round-`q` action block along `W`
    of every member of the set for `S.a q` is an ancestor of `C`, the next opening proposer is in
    the set for its proposal instant, the finality root of its node state staged with the cache
    outcome `c` is an ancestor of `C`, and the awake condition holds at `q`, then every anchor that
    node state can read at round `q + 1` is an ancestor of `C`. -/
theorem fixedRootSource_proposalAnchor_preceq_of_previousCarriersOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc (q + 1))) ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    (hprop : S.E.proposer ((M.opening_slot S.hc (q + 1))) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (S.E.proposer (M.opening_slot S.hc (q + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (S.E.proposer (M.opening_slot S.hc (q + 1)))).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).record c).st.core).toFG) C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).record c) (q + 1) ⇢ A →
      Block.Preceq A C :=
  Restated.fixedRoot_preparedProposalAnchor_preceq_of_previousCarriersOn facts S Hs Xb hf hHs
    hHsXb hfb hpost hcut hproposalHor hupper hprop c hc hroot hA

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `0 < c` and every member of the sets for `S.a (c − 1)` and
    `S.a c` has FG root `J` and `h_max = H` in the world of `W` before that instant, then no block
    the SG selector can return at a node state of a first-set member's round-`(c − 1)` action read
    along `W` interferes with the store of a second-set member in
    `W (strictEventIndex rho (S.a c))`. -/
theorem previousActionCarriersQuietAt_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {c : Round} (hc : 0 < c) {H : Height} {J : Block V}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      M.get_fg_root
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.toHealing.toFG = J ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = H)
    (hcurrent : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      M.get_fg_root
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w).st.toHealing.toFG = J ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w).st.h_max = H)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u) (c - 1),
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let k := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
        ∀ A : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ A →
          Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
            (Restated.Vocabulary.Execution.Setup.a M S c)
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))) A := by
  intro u hu w hw n hn gc st k A2 hA2 A hAsel
  obtain ⟨Wn, hWbody, hcarrierW, hWh⟩ :=
    Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf (hprev u hu).2 n hn A2 hA2 A hAsel
  have hJcarrier : Block.Preceq J A := by
    have h := preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered
      (Restated.actionSGBlockAt_mem_filtered_actionStoreOn facts S Hs Xb hf u (c - 1) n hn A2 hA2
        A hAsel))
    rw [actionReadFrom_fgRoot₆₇ facts S _ (c - 1) n hn] at h
    rw [← (hprev u hu).1]
    exact h
  have hJW : Block.Preceq J Wn.erase := preceq_trans_Preceq hJcarrier hcarrierW
  have hrootW : Block.Preceq
      (M.get_fg_root
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w).st.toHealing.toFG)
      Wn.erase := by
    rw [(hcurrent w hw).1]
    exact hJW
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Protocol.previous_action_add_delta_le_action facts S hc
  obtain ⟨hWtarget, -, -⟩ := Restated.actionConeWitness_visibleAtReader_after_gstOn facts
    S Hs Xb hf hHs hHsXb (r := c - 1) hu (hHs _ _ hdelay hw) hn hWbody
    (Proofs.ModelProperties.Preceq_self Wn.erase) hWh hpost hdelay hhor hrootW
  have hcap : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w).st.core.h_max ≤
      (M.derive_named S.E S.cfg Wn).h + 1 := by
    have h2 : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w).st.core.h_max = H :=
      (hcurrent w hw).2
    rw [h2]
    exact Nat.sub_le_iff_le_add.mp hWh
  have hquiet : Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
      (Restated.Vocabulary.Execution.Setup.a M S c)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))) Wn.erase :=
    Or.inr (Restated.Vocabulary.Proofs.HealingSurface.mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      facts S rho w (Restated.Vocabulary.Execution.Setup.a M S c) _
      (mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath _) hWtarget rfl (hcurrent w hw).1 hJW hcap)
  exact Restated.ancestorOn facts S Hs Xb hf hcarrierW hquiet

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the weight bound, if `w`'s store in
    `W (strictEventIndex rho read)` holds the fixed-height justification root at `H`, the action
    instants `S.a (c − 1)` and `S.a c` are at least one delay after `read`, in the horizon, with the
    largest `h_max` over their sets at most `H`, and the awake condition holds at `c − 1`, then
    every block graded 1 at round `c` by a member of the set for `domain c g1` does not interfere
    with the store of any member of the set for `S.a c` in `W` before `S.a c`. -/
theorem namedLiveG1SettledAt_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs) {c : Round} (hc : 0 < c)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    (hpostRead : lo ≤ read)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hprevDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hprevHor : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ rho.horizon)
    (hprevCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (c - 1))).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) x).st.core.h_max)
        ≤ H)
    (hactionDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S c))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hactionCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S c)).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) x).st.core.h_max) ≤ H)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    ∀ u ∈ Hs (M.domain S.E S.hc c .g1), ∀ B : Block V,
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st c .g1 B ⇢ b → b = true) →
      ∀ w' ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w'
          (Restated.Vocabulary.Execution.Setup.a M S c)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))) B := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hprev := fun (u : V) (hu : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)))) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hu hpostRead hprevDelay hprevHor hprevCap
  have hcurrent := fun (u : V) (hu : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hu hpostRead hactionDelay hactionHor hactionCap
  have hquiet := Restated.previousActionCarriersQuietAt_of_fixedRootOn facts S Hs Xb hf hHs hHsXb hc hpost
    hprev hcurrent hactionHor
  have hG1Hor : M.domain S.E S.hc c .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_a S c .g1).trans hactionHor
  have hwindow := Restated.relativeCarrierWindowAt_of_fixedRootOn facts S Hs Xb hf hHs hHsXb hfb hc
    (p := .g1) hfix hpostRead hpost hprevDelay hprevHor hprevCap hactionDelay hactionHor
      hactionCap hG1Hor hA
  have hprevDelta : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤ M.domain S.E S.hc c .g1 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three
      (Nat.sub_lt hc Nat.one_pos)).trans (facts.gr.early_g2_lt_domain S c .g1).le
  have hmajority := Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf
    hHs hfb hc hprevDelta hG1Hor hpost hA
  exact Restated.namedLiveG1SettledAt_of_previousActionCarriersQuietOn facts S Hs Xb
    (Hs (M.domain S.E S.hc c .g1)) hf hHs hc hwindow hmajority (subset_refl _) hquiet

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, for every node state `n` of `v`'s round-`r` action read along
    `W`, if `n`'s FG source read can return `some C`, then `C` is in the filtered tree of `n`'s
    store. -/
theorem fixedRootSource_mem_filtered_actionStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) {C : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some C) :
    C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
  Restated.freshFGSource_mem_filtered_actionStoreOn facts S Hs Xb hf v r n hn hsource

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if every member of the set for `S.a c` has FG root `J`, every
    block graded 1 at round `c ≥ 1` does not interfere with those members' stores, round `c` is
    ready, the voter `w` of a slot `d` of round `c` after its opening slot has FG root `J` at its
    vote read, and the FG source read of a node state `nv` of `v`'s round-`c` action read can return
    `some C`, then every anchor of `w`'s vote-read node state is compatible with `C`. -/
theorem preparedAnchor_compatible_freshFGSource_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {c : Round} (hc : 1 ≤ c) {J : Block V}
    (hactionRoot : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u).st.core).toFG = J)
    (hsettled : ∀ u ∈ Hs (M.domain S.E S.hc c .g1), ∀ B : Block V,
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st c .g1 B ⇢ b → b = true) →
      ∀ w' ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w'
          (Restated.Vocabulary.Execution.Setup.a M S c)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))) B)
    (hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {w v : V} {d : Slot}
    (hw : w ∈ Hs (M.vote_time S.E d)) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hd1 : (M.opening_slot S.hc c) + 1 ≤ d)
    (hd2 : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)
    (hround : (M.round_of S.hc d) = c)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core)
      (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cv)
    (hvoteRoot : M.get_fg_root
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cv).st.core).toFG = J)
    {C : Block V}
    (nv : M.N)
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S nv c ⇢ some C)
    (hlo : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG)) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cv
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A0 →
    Block.compatible A0 C = true := by
  intro n A0 hA0
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon := haCSucc.trans hhorNext
  have hlod : (M.opening_slot S.hc c) ≤ d := (Nat.le_succ _).trans hd1
  have hopenPos : 0 < M.opening_slot S.hc (c + 1) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (Nat.succ_pos c)
  have hdSucc : d + 1 ≤ M.opening_slot S.hc (c + 1) := by
    have hd2' : d ≤ M.opening_slot S.hc (c + 1) - 1 := hd2
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hd2' (Nat.sub_lt hopenPos Nat.one_pos))
  have hnext : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    have h1 := facts.sch.vote_time_le_view_freeze S.E d
    have h2 := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E d
    have h3 := facts.sch.proposal_time_mono S.E hdSucc
    have hΔ := S.E.Δ_pos
    linarith
  have hvoteHi : M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    have h1 := facts.sch.vote_time_mono_slots S.E (Nat.le_of_succ_le hdSucc)
    have h2 := facts.sch.Protocol_vote_time_le_confirmation_time S.E (M.opening_slot S.hc (c + 1))
    have h3 := facts.sch.a_eq_confirmation_time S.hc S.E (c + 1)
    show M.vote_time S.E d ≤ M.a S.hc S.E.Δ (c + 1)
    rw [h3]
    exact h1.trans h2
  have hvoteHor : M.vote_time S.E d ≤ rho.horizon := hvoteHi.trans hhorNext
  have hloOpenC : lo ≤ M.opening S.E S.hc c :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _))
  have hloG1 : lo ≤ M.domain S.E S.hc c .g1 := by
    rw [facts.gr.Sts_domain_g1_eq_opening]; exact hloOpenC
  have hloG0 : lo ≤ M.domain S.E S.hc c .g0 := by
    have h := facts.gr.domain_g1_add_delta_le_domain_g0 S c
    have hd := S.E.Δ_pos
    linarith
  have hG1le : M.domain S.E S.hc c .g1 ≤ M.vote_time S.E d := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E hlod).trans
      (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d))
  have hwG1 : w ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ hG1le hw
  have hvG2 : v ∈ Hs (M.domain S.E S.hc c .g2) := hHs _ _ (facts.gr.domain_le_a S c .g2) hv
  have hvG1 : v ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ (facts.gr.domain_le_a S c .g1) hv
  have hvG0 : v ∈ Hs (M.domain S.E S.hc c .g0) := hHs _ _ (facts.gr.domain_le_a S c .g0) hv
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmemA : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S c) :=
    mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath _
  have hmemG0 : W (strictEventIndex rho (M.domain S.E S.hc c .g0)) v ∈
      Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc c .g0) v :=
    ⟨_, mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath _, rfl⟩
  have hfilt := actionReadFrom_filtered₆₇ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c nv hnv
  have hrootEq := actionReadFrom_fgRoot₆₇ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c nv hnv
  have hJC : Block.Preceq J C := by
    have h := preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered
      (Restated.fixedRootSource_mem_filtered_actionStoreOn facts S Hs Xb hf v c nv hnv hsource))
    rw [hrootEq, hactionRoot v hv] at h
    exact h
  have hparts := dutyNode_parts₆₇ facts S (W (strictEventIndex rho (M.vote_time S.E d)) w) d cv
  have hnS : n.st.core.s = d := hparts.1
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath _, cv, hcv, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w d n hnmem A0 hA0 with
    hfgAnchor | ⟨root, A, hframeG1, hactive, hanchor⟩
  ·
    rw [hfgAnchor, hvoteRoot]
    exact Proofs.ModelProperties.compatible_eq_true_of_Preceq hJC
  have hroundRead : M.round_of S.hc n.st.core.s = c := by
    rw [hnS]
    exact hround
  rw [hroundRead] at hframeG1
  rw [hanchor]
  obtain ⟨-, hAG1⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
    S Hs Xb hf hcPos hlod hround hnext hvoteHor hwG1 cv hcv hframeG1 hactive hloG1
  have hAG1t := storeGrade_true_of_all₆₇ facts S.E S.hc _ c .g1 A hAG1
  have hset : Block.Preceq A (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG) ∨
      A ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG :=
    hsettled w hwG1 A hAG1 v hv
  have hAG0_of : A ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG →
      A ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nv ∧
      Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g0)) v).st c .g0 A ⇢ true := by
    intro hAactive
    have hAaction : A ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nv := by
      show A ∈ M.get_filtered_block_tree (M.toHealing nv.st.core).toFG
      rw [hfilt]
      exact hAactive
    exact ⟨hAaction, storeGrade_true_of_all₆₇ facts S.E S.hc _ c .g0 A
      (Restated.storeGrade_g0_of_g1_and_targetActionActiveOn facts
        S Hs Xb hf hHs hHsXb hsb hcPos ready hwG1 hvG0 hAG1t nv hnv hAaction hlo)⟩
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsource
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₇ _ _ _).1 hsource
  obtain ⟨Q, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing nv.st.core) c
  have hGQ : G.Q2 = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nv c ⇢ some Q := by
    have h := nodeQ2_of_read₆₇ S nv c G hG
    rwa [hGQ] at h
  have hQaction : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nv :=
    Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho v c _ hmemA nv hnv hq
  have hrootQ : Block.Preceq (M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG) Q := by
    rw [← hrootEq]
    exact preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hQaction)
  cases hwalk : M.deepest_clear (some Q)
      (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | none =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hwalk _ hsrc
      have hCQ : C = Q := Option.some_inj.mp h
      subst hCQ
      rcases hset with hAroot | hAactive
      · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAroot hrootQ))
      · obtain ⟨-, hAG0t⟩ := hAG0_of hAactive
        have hQG2t := storeGrade_true_of_all₆₇ facts S.E S.hc _ c .g2 C
          (Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf nv hnv hq)
        have hQG1t := storeGrade_true_of_all₆₇ facts S.E S.hc _ c .g1 C
          (Restated.storeGrade_g1_of_g2_and_targetActionActiveOn facts
            S Hs Xb hf hHs hHsXb hsb hcPos ready hvG2 hvG1 hQG2t nv hnv hQaction hlo)
        have hQG0t := storeGrade_true_of_all₆₇ facts S.E S.hc _ c .g0 C
          (Restated.storeGrade_g0_of_g1_and_targetActionActiveOn facts
            S Hs Xb hf hHs hHsXb hsb hcPos ready hvG1 hvG0 hQG1t nv hnv hQaction hlo)
        exact Restated.relativeSeed_sameReaderG0_compatible_l66 facts S rho c v _ hmemG0 hAG0t hQG0t
  | some B =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hwalk _ hsrc
      have hCB : C = B := Option.some_inj.mp h
      subst hCB
      have hQC : Block.Preceq Q C := facts.gr.deepest_clear_floor_Preceq hwalk
      have hclearRet : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nv c C ⇢ true := by
        have h' : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nv c C ⇢ G.clear C :=
          returns_map_intro₆₇ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.clear C) _ G
            hG
        rw [facts.gr.deepest_clear_test hwalk] at h'
        exact h'
      rcases hset with hAroot | hAactive
      · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAroot
          (preceq_trans_Preceq hrootQ hQC)))
      · obtain ⟨hAaction, hAG0t⟩ := hAG0_of hAactive
        exact Restated.relativeG0_compatible_clearSourceOn facts S Hs Xb hf hcPos hhorC hvG0
          hAG0t
          (Restated.Vocabulary.Proofs.HealingSurface.storeGrade_g0_mem_domainTree facts S rho _ hmemG0
            hAG0t)
          nv hnv hAaction hclearRet hloG0

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- A slot's vote instant plus one delay is strictly before its confirmation instant. -/
theorem vote_time_add_delta_lt_confirmation_l67 (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.vote_time E s + E.Δ < M.confirmation_time E s := by
  obtain ⟨h1, -, -, -, -, h6⟩ := facts.sch.slot_instants_l55 E s
  have hΔ := E.Δ_pos
  rw [h1, h6]
  linarith

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "frs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FixedRootSourceCap)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committees condition and the weight bound, if `w` holds the
    fixed-height justification root at `H`, every member of the set for each action instant of
    rounds `r + 1` to `endpointRound` has FG root `J` and `h_max = H`, and the proposal lifecycles
    of rounds `q1` and `q'` and the boundary locks hold along `W`, then for every member `v` of the
    set for `S.a (q' − 1)` and every block `Q` that the FG source read of a node state of `v`'s
    round-`(q' − 1)` action read can return, the height of the chain state at `Q` is at most the
    height of `B2`'s parent. -/
theorem fixedRoot_sourceHeight_le_nextOpeningParentOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read0 : Time}
    {r endpointRound q1 q' : Round} {B1 B2 : NamedBlock V}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read0
      (W (strictEventIndex rho read0)))
    (hpostRead : lo ≤ read0)
    (hreadAction : read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hq1lo : r + 3 ≤ q1)
    (hreadAction2 : read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q1))
    (hq1pos : 0 < q1) (hq1q2 : q1 < q')
    (hq2End : q' ≤ endpointRound)
    (_hcarrier1 : Restated.ProposerCarrierAtOn M S Hs q1)
    (hpostQ1 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q1))
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon)
    (hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max)
        ≤ H)
    (_hplusTwoFacts : ∃ Bplus : NamedBlock V,
      (∃ cp : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
            (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.core.toHealing
          (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
            (S.E.proposer ((M.opening_slot S.hc q1) + 2))).cache ⇢ cp ∧
        M.proposal_with (M.gradeContract cp) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
          (S.node (S.E.proposer ((M.opening_slot S.hc q1) + 2)))
          (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
              (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st
            (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) ⇢ some Bplus) ∧
      Restated.RunBlockOn M S rho W Xb Bplus ∧
      S.E.proposer ((M.opening_slot S.hc q1) + 2) ∈
        Hs (M.confirmation_time S.E ((M.opening_slot S.hc q1) + 2)) ∧
      M.proposal_time S.E ((M.opening_slot S.hc q1) + 2) ≤ rho.horizon ∧
      M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
            (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.core).toFG =
        (W (strictEventIndex rho read0) w).st.J ∧
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
        (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.h_max = H)
    {w₁ w₂ w₁' w₂' : V → M.N}
    (hpacket1 : Restated.NamedSGProposalLifecyclePacketOn M S rho W
      (fun t => W (strictEventIndex rho t)) w₁ w₂ Hs Xb (q1 - 1)
      ((M.opening_slot S.hc q1) - 1) B1)
    (hpacket2 : Restated.NamedSGProposalLifecyclePacketOn M S rho W
      (fun t => W (strictEventIndex rho t)) w₁' w₂' Hs Xb (q' - 1)
      ((M.opening_slot S.hc q') - 1) B2)
    (hB1pred : (M.derive_named S.E S.cfg B1).h = H - 1)
    {wd1 wd2 : V → M.N}
    (_hlock1 : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q1 - 1)
      ((M.opening_slot S.hc q1) - 1) wd1
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q1 - 1)))))
    (hlock2 : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q' - 1)
      ((M.opening_slot S.hc q') - 1) wd2
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)))))
    (hfixedAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        M.get_fg_root
            (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core).toFG =
          (W (strictEventIndex rho read0) w).st.J ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.h_max = H)
    (hrootDuty2 : M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
            (S.E.proposer (M.opening_slot S.hc q'))).st.core
          (M.proposal_time S.E (M.opening_slot S.hc q')))).toFG =
      (W (strictEventIndex rho read0) w).st.J)
    (hmaxDuty2 : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc q'))).h_max = H)
    (_hformsB1Prev : ∀ v ∈ Hs (M.domain S.E S.hc (q' - 1) Phase.g2),
      B1.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v).st (q' - 1) Phase.g2
            B1.erase ⇢ b → b = true)
    (_hactionB1 : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v) (q' - 1),
      B1.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hB1ParentRows : Block.Preceq B1.erase B2.parent.erase)
    (_hmature2 : ∀ P : NamedBlock V, NamedBlock.parent? B2 = some P →
      (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q')
    (hq2Spacing : q1 + 2 + delayExtra ≤ q')
    (hloOpen : lo ≤ M.opening S.E S.hc (q' - 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v) (q' - 1),
      ∀ Q : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n (q' - 1) ⇢ some Q →
        ((M.toHealing n.st.core).toFG.σ Q).h ≤ (M.derive_named S.E S.cfg B2.parent).h := by
  obtain ⟨c, rfl⟩ : ∃ c : Nat, q' = c + 1 :=
    ⟨q' - 1, (Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le _) hq1q2)).symm⟩
  simp only [Nat.add_sub_cancel] at hpacket2 hlock2 hloOpen ⊢
  intro v hv n hn Q hsource
  obtain ⟨hcRound, hq1c, hq1cMinus, hcPredLt, hcEnd, hcPredEnd, hr1c, hrq1, hcSucc⟩ :=
    round_bounds₆₇ hq1lo hq1q2 hq2Spacing hq2End
  have hΔ := S.E.Δ_pos
  have hpostCPred : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) :=
    hpostQ1.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq1cMinus)
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hcEnd).trans hendHor
  have hhorCPred : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hcPredEnd).trans hendHor
  have hhorQ' : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq2End).trans hendHor
  have haQ1 := Restated.a_eq_confirmation_opening_l58 facts S q1
  have haC := Restated.a_eq_confirmation_opening_l58 facts S c
  have haQ' := Restated.a_eq_confirmation_opening_l58 facts S (c + 1)
  have hreadDeltaQ1 : read0 + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S q1) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S hrq1
    have h2 := facts.sch.proposal_time_le_confirmation_time S.E (M.opening_slot S.hc q1)
    linarith
  have hreadDeltaC : read0 + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    hreadDeltaQ1.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_of_lt hq1c))
  have hreadDeltaCPred : read0 + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) :=
    hreadDeltaQ1.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq1cMinus)
  have hloC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := by linarith
  have hloCPred : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) := by linarith
  have hcapC := (Restated.honestHMaxAtOn_action_mono_l56 facts S Hs Xb hf hHs hHsXb hcom hcEnd hloC
    hendHor).trans hcapEnd
  have hcapCPred := (Restated.honestHMaxAtOn_action_mono_l56 facts S Hs Xb hf hHs hHsXb hcom
    hcPredEnd hloCPred hendHor).trans hcapEnd
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.fixedRootSource_namedTargetOn facts S Hs Xb hfix
  have hactionRootPre : ∀ z ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) z).st.core).toFG =
          Jn.erase :=
    fun z hz => (hfixedAt hr1c hcEnd z hz).1.trans hJnErase.symm
  have hsourceFiltered := Restated.fixedRootSource_mem_filtered_actionStoreOn facts S Hs Xb hf v c
    n hn hsource
  have hrootN : M.get_fg_root (M.toHealing n.st.core).toFG = Jn.erase :=
    (actionReadFrom_fgRoot₆₇ facts S _ _ n hn).trans (hactionRootPre v hv)
  have hJC : Block.Preceq Jn.erase Q := by
    have h := Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      (facts.fc.preceq_get_fg_root_of_mem_filtered hsourceFiltered)
    rwa [hrootN] at h
  obtain ⟨Cn, hCbody, hCerase, hCrun, hσ⟩ :=
    Restated.fixedRootSource_namedSource_witnessOn facts S Hs Xb hf (hHsXb _ hv) n hn hsource
  have hJCn : Block.Preceq Jn.erase Cn.erase := by
    rw [hCerase]
    exact hJC
  have hσheight : ((M.toHealing n.st.core).toFG.σ Q).h = (M.derive_named S.E S.cfg Cn).h := by
    rw [hσ]
  have hB2run : Restated.RunBlockOn M S rho W Xb B2 := hpacket2.lifecycle.runBlock
  have hB2ParentRun : Restated.RunBlockOn M S rho W Xb B2.parent :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hB2run
      ((frs% fixedRootSource_parent_preceq_self) B2)
  have hB1ParentNamed : NamedBlock.Preceq B1 B2.parent :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hpacket1.lifecycle.runBlock
      hB2ParentRun hB1ParentRows
  have hparentLower : H - 1 ≤ (M.derive_named S.E S.cfg B2.parent).h := by
    rw [← hB1pred]
    exact facts.cs.derive_height_mono S.E S.cfg hB1ParentNamed
  by_cases hsourceBand : H - 1 ≤ (M.derive_named S.E S.cfg Cn).h
  swap
  · rw [hσheight]
    exact (Nat.le_of_lt (Nat.lt_of_not_ge hsourceBand)).trans hparentLower
  have hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c :=
    Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_previousAction facts S hcRound
      hpostCPred hhorC
  have hloR : lo ≤ Restated.Vocabulary.Execution.Setup.a M S r := hpostRead.trans hreadAction
  have hkCPred : lo ≤ M.early S.E S.hc (c - 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloR (lt_of_lt_of_le hrq1 hq1cMinus)
  have hkC : lo ≤ M.early S.E S.hc c .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloR (Nat.lt_of_succ_le hr1c)
  have hwinC : lo ≤ M.early S.E S.hc c .g1 - S.E.Δ := by
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S c
    linarith
  have hsettled := Restated.namedLiveG1SettledAt_of_fixedRootOn facts S Hs Xb hf hHs hHsXb
    hfb hcRound hfix hpostRead hloCPred hreadDeltaCPred hhorCPred hcapCPred hreadDeltaC hhorC hcapC
    (hA (c - 1) hkCPred)
  obtain ⟨hlastLo, hlastLt, hlastPos, hlastSucc⟩ :=
    slot_bounds₆₇ (facts.gr.opening_slot_succ_eq S.hc c) S.hc.R_ge_two
  have hwinSlot : ∀ d : Slot, (M.opening_slot S.hc c) + 1 ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      lo ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
    intro d hdlo hdhi
    rw [facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hdlo
      (lt_of_le_of_lt hdhi hlastLt)]
    exact hwinC
  have hproposalHor : M.proposal_time S.E (M.opening_slot S.hc (c + 1)) ≤ rho.horizon := by
    have h := facts.sch.proposal_time_le_confirmation_time S.E (M.opening_slot S.hc (c + 1))
    linarith
  have hq1ToC := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
    facts S hq1c
  have hpropToFirst : M.proposal_time S.E (M.opening_slot S.hc c) ≤
      M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    (facts.sch.proposal_time_lt_vote_time S.E _).le.trans
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _))
  have hsourceVoteDelay : ∀ {d : Slot}, (M.opening_slot S.hc c) + 1 ≤ d →
      read0 + S.E.Δ ≤ M.vote_time S.E d := by
    intro d hdlo
    have h := facts.sch.vote_time_mono_slots S.E hdlo
    linarith
  have hconfLe : ∀ {d : Slot}, d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      M.confirmation_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S endpointRound) := by
    intro d hdhi
    have h1 := Restated.confirmationTime_mono_l58 facts S.E (hdhi.trans hlastLt.le)
    have h2 := Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq2End
    linarith
  have hsourceVoteHor : ∀ {d : Slot}, d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      M.vote_time S.E d ≤ rho.horizon := by
    intro d hdhi
    have h1 := facts.sch.Protocol_vote_time_le_confirmation_time S.E d
    have h2 := hconfLe hdhi
    linarith
  have hnonemptyEnd := Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs
    (Restated.Vocabulary.Execution.Setup.a M S endpointRound)
  have hsourceVoteFacts : ∀ {d : Slot}, (M.opening_slot S.hc c) + 1 ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ z ∈ Hs (M.vote_time S.E d),
      M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) z).st.core).toFG =
        Jn.erase ∧
      (W (strictEventIndex rho (M.vote_time S.E d)) z).st.core.h_max = H := by
    intro d hdlo hdhi z hz
    have hvoteLo : lo ≤ M.vote_time S.E d := by
      have h := hsourceVoteDelay hdlo
      linarith
    have hvoteCap := (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hvoteLo
      (lt_of_lt_of_le (Restated.vote_time_add_delta_lt_confirmation_l67 facts S.E d) (hconfLe hdhi))
      hendHor hnonemptyEnd).trans hcapEnd
    have hfixed :=
      Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
        facts S Hs Xb hf hHs hHsXb hf.slashableBound hfix hz hpostRead (hsourceVoteDelay hdlo)
        (hsourceVoteHor hdhi) hvoteCap
    exact ⟨hfixed.1.trans hJnErase.symm, hfixed.2⟩
  have hvoteRootS : ∀ d : Slot, (M.opening_slot S.hc c) + 1 ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ z ∈ Hs (M.vote_time S.E d),
      M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E d)) z).st (M.vote_time S.E d)).core).toFG =
          Jn.erase := by
    intro d hdlo hdhi z hz
    rw [setClock_fgRoot₆₇ facts]
    exact (hsourceVoteFacts hdlo hdhi z hz).1
  have hvoteCapS : ∀ d : Slot, (M.opening_slot S.hc c) + 1 ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ z ∈ Hs (M.vote_time S.E d),
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) z).st
        (M.vote_time S.E d)).core.h_max ≤ (M.derive_named S.E S.cfg Jn).h + 1 := by
    intro d hdlo hdhi z hz
    rw [facts.hd.setClock_core_h_max, (hsourceVoteFacts hdlo hdhi z hz).2, hJnHeight]
    exact height_bound₆₇ hfix.targetHeightPositive
  have hsourceAnchorCompat : ∀ d : Slot, (M.opening_slot S.hc c) + 1 ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ z ∈ Hs (M.vote_time S.E d), ∀ cv : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) z).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) z).cache ⇢ cv →
      ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) z).st
            (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) z).record cv)
          (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E d)) z).st (M.vote_time S.E d))
            (W (strictEventIndex rho (M.vote_time S.E d)) z).record cv).st.core.s) ⇢ A0 →
        Block.compatible A0 Q = true := by
    intro d hdlo hdhi z hz cv hcv
    exact Restated.preparedAnchor_compatible_freshFGSource_of_fixedRootOn facts S Hs Xb hf hHs
      hHsXb (c := c) (Nat.succ_le_iff.mpr hcRound) hactionRootPre hsettled hhorQ' hready hz hv hdlo
      hdhi (seedEntryRoundOf₆₇ facts S ((Nat.le_succ _).trans hdlo) hdhi) cv hcv
      (((dutyNode_parts₆₇ facts S _ d cv).2).trans (hsourceVoteFacts hdlo hdhi z hz).1)
      n hn hsource hloOpen
  have hwmem := mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S c)
  have hpostSource : lo ≤ M.proposal_time S.E (M.opening_slot S.hc c) := by
    have h := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S hcPredLt
    linarith
  have hsourceHor : M.confirmation_time S.E (M.opening_slot S.hc c) ≤ rho.horizon := by
    rw [← haC]
    exact hhorC
  have hvConf : v ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc c)) := by
    rw [← haC]
    exact hv
  have hpostLo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) := hpostSource.trans hpropToFirst
  have hpostLast : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1) :=
    hpostLo.trans (facts.sch.vote_time_mono_slots S.E hlastLo)
  have hsourceCone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb
      ((M.opening_slot S.hc (c + 1)) - 1) (fun X => Block.Preceq Q X) := by
    have hsrc0 := hsource
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsrc0
    obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₇ _ _ _).1 hsrc0
    obtain ⟨Q2, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
    subst hA2Q
    obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) c
    have hGQ : G.Q2 = some Q2 :=
      (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
    have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n c ⇢ some Q2 := by
      have h := nodeQ2_of_read₆₇ S n c G hG
      rwa [hGQ] at h
    cases hwalk : M.deepest_clear (some Q2)
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
    | none =>
        have h := facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hwalk _ hsrc
        have hQeq : Q = Q2 := Option.some_inj.mp h
        obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
        obtain ⟨T, hT⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g
        have hQT : Block.Preceq Q2 T := Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf
          hHs hHsXb hcRound hhorC (hHs _ _ (facts.gr.domain_le_a S c .g1) hv) hloOpen n hn hq
          (Proofs.ModelProperties.Preceq_self Q2) g hg T hT
        have hcone := hlock2.canonical v hv n hn g hg T hT
        intro x hx hcommittee
        obtain ⟨X, hTX, hXrun, hXemit⟩ := hcone x hx hcommittee
        exact ⟨X, by rw [hQeq]; exact Proofs.ModelProperties.Preceq_trans hQT hTX, hXrun, hXemit⟩
    | some Cclear =>
        have h := facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hwalk _ hsrc
        have hQeq : Q = Cclear := Option.some_inj.mp h
        have hCL : Block.Preceq Cclear n.st.core.live_confirmed := by
          have h1 := facts.gr.deepest_clear_Preceq hwalk
          rwa [facts.sto.toHealing_live_confirmed] at h1
        have hCeraseClear : Cn.erase = Cclear := hCerase.trans hQeq
        rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
            facts S rho v c _ hwmem n hn with ⟨L, hgenuine, hLlive⟩ | ⟨R, hRroot, hRlive⟩
        · have hCLive : Block.Preceq Cn.erase L := by
            rw [hCeraseClear, hLlive]
            exact hCL
          have hgenuine' : Restated.Vocabulary.Protocol.GenuineConfirmation M
              (contract := M.gradeContract n.cache) S.E S.hc
              (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
                (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc c))) v).st.core
                (M.confirmation_time S.E (M.opening_slot S.hc c)))
              (M.opening_slot S.hc c) L := by
            rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S c]
            rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S c]
              at hgenuine
            exact ⟨hgenuine.selected, hgenuine.genuine⟩
          have hcone := genuineClearCone₆₇ facts S Hs Xb hf hHs hHsXb hcom (r := c)
            hJnRun hCrun hJCn hvConf hgenuine' hCLive hpostSource hsourceHor
            (s := (M.opening_slot S.hc (c + 1)) - 1) (hsourceVoteHor (le_refl _))
            hvoteRootS hvoteCapS
            (fun d hdlo hdhi z hz cv hcv A0 hA0 => by
              rw [hCeraseClear, ← hQeq]
              exact hsourceAnchorCompat d hdlo hdhi z hz cv hcv A0 hA0)
            (fun d hdlo hdhi z _ hz j hj =>
              hf.awake_g1 _ _ j _ (Or.inr rfl) hj hz (hwinSlot d hdlo hdhi))
            ((M.opening_slot S.hc (c + 1)) - 1) hlastLo (le_refl _)
          rw [hQeq, ← hCeraseClear]
          exact hcone
        · have hRJ : R = Jn.erase := by
            rw [hRroot, tickStore_fgRoot₆₇ facts]
            exact hactionRootPre v hv
          have hCeq : Cclear = Jn.erase :=
            Proofs.ModelProperties.Preceq_antisymm (by rw [← hRJ, hRlive]; exact hCL)
              (by rw [← hCeraseClear]; exact hJCn)
          intro x hx hcommittee
          obtain ⟨cx, hcx⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))) x).st.core.toHealing
            (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))) x).cache
          have hrootX := ((dutyNode_parts₆₇ facts S
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))) x)
            ((M.opening_slot S.hc (c + 1)) - 1) cx).2).trans
              (hsourceVoteFacts hlastLo (le_refl _) x hx).1
          set nx := M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))) x).st
              (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1)))
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))) x).record cx
            with hnx_def
          have hnxmem : nx ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho x
              ((M.opening_slot S.hc (c + 1)) - 1) :=
            ⟨_, mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath _, cx, hcx, rfl⟩
          obtain ⟨T0, hT0, L, hL, L', hL', Hd, hHd⟩ := exists_headOutcome₆₇ facts S nx
          obtain ⟨R', hR'⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract nx.cache) S.E S.hc
            (M.toHealing nx.st.core) (M.round_of S.hc nx.st.core.s)
          have hA' := nodeAnchor_of_sgRoot₆₇ facts S nx _ hR'
          have hrootA := Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S nx _ R' hA'
          have hAH := Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts
            S rho x _ nx hnxmem R' hA' T0 hT0 L hL L' hL' Hd hHd
          obtain ⟨X, hXH, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts S Hs Xb hf
            hHsXb hx hlastPos hcommittee (hsourceVoteHor (le_refl _)) hpostLast cx hcx
            (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx (hwinSlot _ hlastLo (le_refl _)))
            T0 hT0 L hL L' hL' Hd hHd
          refine ⟨X, ?_, hXrun, hXemit⟩
          rw [hXH, hQeq, hCeq, ← hrootX]
          exact Proofs.ModelProperties.Preceq_trans hrootA hAH
  have hsourceDelayProposal : (Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ ≤
      M.proposal_time S.E (M.opening_slot S.hc (c + 1)) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
      hcSucc
  have hrootPre : M.get_fg_root
      (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core).toFG = Jn.erase :=
    (tickStore_fgRoot₆₇ facts S _ _).symm.trans (hrootDuty2.trans hJnErase.symm)
  have hpropConf : S.E.proposer (M.opening_slot S.hc (c + 1)) ∈
      Hs (M.confirmation_time S.E (M.opening_slot S.hc (c + 1))) :=
    hpacket2.lifecycle.proposerHonest
  have hpropProposal : S.E.proposer (M.opening_slot S.hc (c + 1)) ∈
      Hs (M.proposal_time S.E (M.opening_slot S.hc (c + 1))) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hpropConf
  have hpropRelay : S.E.proposer (M.opening_slot S.hc (c + 1)) ∈
      Hs ((Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ) :=
    hHs _ _ hsourceDelayProposal hpropProposal
  have hrootProposalPre : Block.Preceq
      (M.get_fg_root (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.toHealing.toFG) Jn.erase := by
    show Block.Preceq (M.get_fg_root
      (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core).toFG) Jn.erase
    rw [hrootPre]
    exact Proofs.ModelProperties.Preceq_self _
  have hvisible := Restated.actionConeWitness_visibleAtReader_after_gstOn facts S Hs Xb hf hHs hHsXb
    hv hpropRelay hn hCbody hJCn hsourceBand hloC hsourceDelayProposal hproposalHor hrootProposalPre
  have hmaxProposal : (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
      (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.h_max = H := by
    have h := hmaxDuty2
    rwa [tickStore_eq₆₇ facts, facts.hd.setClock_core_h_max] at h
  have hactiveSource : Cn.erase ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core).toFG :=
    Restated.Vocabulary.Proofs.HealingSurface.mem_filtered_of_mem_tree_of_exactFGRoot_heightCap facts
      S rho (S.E.proposer (M.opening_slot S.hc (c + 1)))
      (M.proposal_time S.E (M.opening_slot S.hc (c + 1))) _
      (mem_stateBeforeTime_along₆₇ hf.sorted hf.onePath _) hvisible.1 rfl hrootPre hvisible.2.1
      (by rw [hmaxProposal]; exact Nat.sub_le_iff_le_add.mp hsourceBand)
  have hactiveQ : Q ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))).toFG := by
    rw [tickStore_filtered₆₇ facts, ← hCerase]
    exact hactiveSource
  obtain ⟨K, ⟨v0, hv0, n0, hn0, g0, hg0, hK0⟩, hupperK, hKcone⟩ :=
    Restated.fixedRootSource_commonActionCeilingOn facts S Hs Xb hf hHs hcom (H := H) (q := c)
      (wd := wd2) hlock2
  have hJK : Block.Preceq Jn.erase K := by
    have hroot0 : M.get_fg_root (M.toHealing n0.st.core).toFG = Jn.erase :=
      (actionReadFrom_fgRoot₆₇ facts S _ _ n0 hn0).trans (hactionRootPre v0 hv0)
    have h : Block.Preceq (M.get_fg_root (M.toHealing n0.st.core).toFG) K :=
      Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
        (facts.fc.preceq_get_fg_root_of_mem_filtered
          (Restated.actionSGBlockAt_mem_filtered_actionStoreOn facts S Hs Xb hf v0 c n0 hn0 g0 hg0
            K hK0))
    rwa [hroot0] at h
  have hKC : Block.compatible K Q = true :=
    Restated.sgTargetCompatible_of_honestVotesConeOn facts S Hs Xb hf hHs hcom hKcone hsourceCone
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (c + 1) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S c).le.trans hhorQ'
  have hproposalB2 : ∃ cp : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).cache ⇢ cp ∧
      M.proposal_with (M.gradeContract cp)
        Protocol.ProposalRowSource.poolAndCarried S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc (c + 1))))
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
          (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))) ⇢ some B2 :=
    hpacket2.lifecycle.proposal
  obtain ⟨cp, hcp, hP⟩ := hproposalB2
  have hrootK : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).record cp).st.core).toFG) K := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [setClock_fgRoot₆₇ facts, hrootPre]
    exact hJK
  have hanchorK := Restated.fixedRootSource_proposalAnchor_preceq_of_previousCarriersOn facts S Hs
    Xb hf hHs hHsXb hfb hloC hcut hproposalHor hupperK hpropProposal cp hcp hrootK (hA c hkC)
  have hsupportHor : M.support_cutoff S.E ((M.opening_slot S.hc (c + 1)) - 1) ≤ rho.horizon := by
    have h1 := facts.sch.Protocol_support_cutoff_le_confirmation_time S.E
      ((M.opening_slot S.hc (c + 1)) - 1)
    have h2 := Restated.confirmationTime_mono_l58 facts S.E hlastLt.le
    linarith
  have hpropSupport : S.E.proposer ((M.opening_slot S.hc (c + 1)) - 1 + 1) ∈
      Hs (M.support_cutoff S.E ((M.opening_slot S.hc (c + 1)) - 1)) := by
    rw [hlastSucc]
    exact hHs _ _ ((facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _).trans
      (Restated.confirmationTime_mono_l58 facts S.E hlastLt.le)) hpropConf
  have hkey := Restated.coneTarget_preceq_nextProposedParent_namedOn facts S Hs Xb hf hHs
    hHsXb hcom (s := (M.opening_slot S.hc (c + 1)) - 1) hlastPos hpostLast hsupportHor hpropSupport
    hsourceCone
  rw [hlastSucc] at hkey
  have hparentCapture := hkey hactiveQ cp hcp
  set np := M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
      (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
      (S.E.proposer (M.opening_slot S.hc (c + 1)))).record cp with hnp_def
  have hnpst : np.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))) (S.E.proposer (M.opening_slot S.hc (c + 1)))).st (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))) _ := facts.nd.mkNode_st _ _ _
  have hnpcache : np.cache = cp := facts.nd.mkNode_cache _ _ _
  have hroundP : M.round_of S.hc np.st.core.s = c + 1 := by
    rw [hnpst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_opening_slot_eq_schedule S.hc (c + 1)
  obtain ⟨R0, hR0⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract np.cache) S.E S.hc
    (M.toHealing np.st.core) (c + 1)
  have hA0 := nodeAnchor_of_sgRoot₆₇ facts S np (c + 1) hR0
  have hcompat0 : Block.compatible R0 Q = true :=
    (frs% fixedRootSource_compatible_left) (hanchorK R0 hA0) hKC
  obtain ⟨I0, hI0⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract np.cache) S.E S.hc
    (S.node (S.E.proposer (M.opening_slot S.hc (c + 1)))) (M.toHealing np.st.core)
  have hQI : Block.Preceq Q I0.parent :=
    hparentCapture R0 (by rw [hroundP]; exact hA0) hcompat0 I0 hI0
  have hI0' : M.with_proposal_input (M.gradeContract cp) S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (c + 1))))
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))) cp).core) id ⇢ I0 := by
    have h := hI0
    rw [hnpcache, hnpst] at h
    exact h
  obtain ⟨p, hp, hparentErase⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ B2 _
    (by rw [facts.dt.proposal_with_store_with_cache]; exact hP) rfl I0 hI0'
  have hparentEq : B2.parent = p := by
    cases B2 with
    | genesis => cases hp
    | node parent slot root votes support rows proposer =>
        rw [namedBlock_parent_node]
        exact Option.some.inj hp
  have hsourceParent : Block.Preceq Cn.erase B2.parent.erase := by
    rw [hCerase, hparentEq, hparentErase]
    exact hQI
  have hCnParent : NamedBlock.Preceq Cn B2.parent :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hCrun hB2ParentRun hsourceParent
  rw [hσheight]
  exact facts.cs.derive_height_mono S.E S.cfg hCnParent

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

end

end DecoupledConsensusModel.Sts.Restated
