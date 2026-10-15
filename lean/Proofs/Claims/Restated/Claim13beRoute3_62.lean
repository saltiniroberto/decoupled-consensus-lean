import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_StoreFinalityCore
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The round-ceiling step along a path

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, with every store
read in a world of the bundle's path `W`: the relay fold of a round ceiling, the prepared frame and
the proposal anchor at the opening, the FG roots read in the next round, the re-based ceiling, and
the round ceiling's construction and iteration.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ### Helpers -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- For every node state `x` and instant `t`, the cache update at `t` on `x` can return some cache
    `c`, and the node state staged at `t` from `x` with `c` has the filtered block tree and the FG
    root of the store `tickStore` stages at `t` from `x`'s core store. -/
private theorem exists_read_of_world₆₂ (facts : Record.Facts M) (S : Setup V) (x : M.N)
    (t : Time) :
    ∃ c : M.Cache, M.onPhaseTick S.E S.hc x.st.core.toHealing t x.cache ⇢ c ∧
      M.get_filtered_block_tree
          (M.toHealing (M.mkNode (M.ns_setClock S.E x.st t) x.record c).st.core).toFG =
        M.get_filtered_block_tree
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S x.st.core t)).toFG ∧
      M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E x.st t) x.record c).st.core).toFG =
        M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S x.st.core t)).toFG := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc x.st.core.toHealing t x.cache
  refine ⟨c, hc, ?_, ?_⟩
  · rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_filtered_block_tree,
      Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  · rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_fg_root,
      Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- Every slot `s` from the opening slot of round `q + 1` to the slot before its last slot has its
    successor in round `q + 1`. -/
private theorem roundOf_succ_eq_step₆₂ (facts : Record.Facts M) (S : Setup V) {q : Round}
    {s : Slot} (hlo : M.opening_slot S.hc (q + 1) ≤ s)
    (hhi : s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) :
    M.round_of S.hc (s + 1) = q + 1 := by
  have hlast := Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1)
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) :=
    Nat.zero_lt_of_lt hlast
  have h1 : s + 1 ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) :=
    Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hhi (Nat.sub_lt hlastPos Nat.one_pos))
  have h2 : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) <
      M.opening_slot S.hc (q + 1 + 1) := by
    have hpos : 0 < M.opening_slot S.hc (q + 1 + 1) - 1 := hlastPos
    show M.opening_slot S.hc (q + 1 + 1) - 1 < M.opening_slot S.hc (q + 1 + 1)
    exact Nat.sub_lt (Nat.lt_of_lt_of_le hpos (Nat.sub_le _ _)) Nat.one_pos
  apply facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
  · exact Nat.succ_le_succ hlo
  · exact lt_of_le_of_lt h1 h2

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₆₂ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The store `tickStore` stages from `n`'s core store has the tree of `n`'s core store. -/
private theorem tickStore_T₆₂ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store `tickStore` stages from `n`'s core store has the `h_max` of `n`'s core store. -/
private theorem tickStore_h_max₆₂ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- The store `tickStore` stages from `n`'s core store has the `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₆₂ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₂ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₂ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₂ S rho hsorted]
  exact (hW _).1

/-- The store `tickStore` stages from `n`'s core store has the FG root of `n`'s core store. -/
private theorem tickStore_fgRoot₆₂ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_fg_root (M.toHealing n.st.core).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store `tickStore` stages from `n`'s core store has the filtered block tree of `n`'s core
    store. -/
private theorem tickStore_filtered₆₂ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_filtered_block_tree
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
  facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₂ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- Every node state `n` of the round-`r` action read computed from `before` has as core store an
    outcome of the confirmation write on `before`'s core store with its clock set to round `r`'s
    action instant, under the grade contract of `n`'s cache. -/
private theorem actionReadFrom_core₆₂ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- The cache of every node state of the round-`r` action read computed from `before` is an outcome
    of the phase tick at round `r`'s action instant on `before`'s cache. -/
private theorem actionReadFrom_cache₆₂ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.onPhaseTick S.E S.hc (M.toHealing before.st.core)
        (Restated.Vocabulary.Execution.Setup.a M S r) before.cache ⇢ n.cache := by
  rintro _ ⟨c, hc, st, -, rfl⟩
  rw [facts.nd.mkNode_cache]
  exact hc

/-- The SG root read under any grade contract from the healing view of a store with a cache written
    in is the one read from the store's own healing view. -/
private theorem sgRoot_store_with_cache₆₂ (facts : Record.Facts M) {E : Env V}
    {hc : Protocol.HealConfig} {st : M.NS} {c c' : M.Cache} {r : Round} {x : Block V} :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

/-- A grade read under any grade contract from the healing view of a store with a cache written in
    can return `g` exactly when the read from the store's own healing view can. -/
private theorem gradeRead_store_with_cache₆₂ (facts : Record.Facts M) {E : Env V}
    {hc : Protocol.HealConfig} {st : M.NS} {c c' : M.Cache} {r : Round}
    {g : DecoupledConsensusModel.Protocol.GradeRead V} :
    M.read (M.gradeContract c') E hc (M.store_with_cache st c).core.toHealing r ⇢ g ↔
      M.read (M.gradeContract c') E hc st.core.toHealing r ⇢ g := by
  have h1 := facts.nd.gradeContract_read c' E hc (M.toHealing (M.store_with_cache st c).core) r g
  have h2 := facts.nd.gradeContract_read c' E hc (M.toHealing st.core) r g
  rw [facts.nd.store_with_cache_frameGradeRead] at h1
  exact h1.trans h2.symm

/-- Every outcome of the round-`r` anchor of a node state `n` of the round-`r` action read computed
    from `x` is an outcome of the confirmation anchor of the node state staged at round `r`'s action
    instant from `x` with `n`'s cache. -/
private theorem actionAnchor_confirmationAnchor₆₂ (facts : Record.Facts M) (S : Setup V)
    (x : M.N) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S x r,
      ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ a →
        Restated.Vocabulary.Internal.namedConfirmationAnchor M S
          (M.mkNode (M.ns_setClock S.E x.st (Restated.Vocabulary.Execution.Setup.a M S r)) x.record
            n.cache) ⇢ a := by
  intro n hn a ha
  obtain ⟨st₀, hst₀, hcore⟩ := actionReadFrom_core₆₂ facts S x r n hn
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at ha
  obtain ⟨G, hG, hGa⟩ := returns_map_elim₆₂ _ _ _ ha
  rw [hst₀, gradeRead_store_with_cache₆₂ facts] at hG
  obtain ⟨a', ha'⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing st₀.core) r
    (M.readFrame n.cache (M.toHealing st₀.core) r).g1
  have hGa' := facts.nd.ModelProperties_gradeContract_read_anchor _ _ _ _ _ G hG a' ha'
  have hframe : (M.readFrame n.cache (M.toHealing st₀.core) r).g1 =
      (M.readFrame n.cache (M.toHealing
        (M.ns_setClock S.E x.st (Restated.Vocabulary.Execution.Setup.a M S r)).core) r).g1 :=
    facts.gr.readFrame_g1_eq_of_F _ r (facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ _ hcore)
  have ha'' : M.anchor S.E S.hc
      (M.toHealing (M.ns_setClock S.E x.st (Restated.Vocabulary.Execution.Setup.a M S r)).core) r
      (M.readFrame n.cache (M.toHealing
        (M.ns_setClock S.E x.st (Restated.Vocabulary.Execution.Setup.a M S r)).core) r).g1 ⇢ a' := by
    rw [← hframe]
    exact (facts.gr.anchor_eq_of_filtered_fg_root S.E S.hc r _
      (facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _ hcore)
      (facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _ hcore) a').1 ha'
  have hround : M.round_of S.hc
      (M.mkNode (M.ns_setClock S.E x.st (Restated.Vocabulary.Execution.Setup.a M S r)) x.record
        n.cache).st.core.s = r := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s, facts.sto.store_with_t_s_s]
    exact facts.sch.round_of_slotOf_a S r
  unfold Restated.Vocabulary.Internal.namedConfirmationAnchor
  rewrite [hround, facts.nd.mkNode_st, facts.nd.mkNode_cache, sgRoot_store_with_cache₆₂ facts,
    facts.nd.gradeContract_sgRoot_eq_frameAnchor, ← hGa, hGa']
  exact ha''

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₂ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If the contract's grade read at `n` can return `G`, then `n`'s candidate read can return `G`'s
    candidate. -/
private theorem nodeQ2_of_read₆₂ (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₂ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

/-- If the contract's grade read at `n` can return `G`, then `n`'s anchor read can return `G`'s
    anchor. -/
private theorem nodeAnchor_of_read₆₂ (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ G.anchor := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₂ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G
    hG

/-- For every node state `n`, the voter's filtered block tree of `n`'s core store at its slot, the
    voter's two vote views of it, and the head computed from them under the grade contract of `n`'s
    cache each have an outcome. -/
private theorem voterHead_outcome₆₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) :
    ∃ (T : Finset (Block V)) (L L' : Finset (GoldfishVote V)) (H : Block V),
      M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  exact ⟨T, L, L', H, hT, hL, hL', hH⟩

/-- For every node state `n` and round `r`, the anchor of `n` at `r` can return some block. -/
private theorem nodeAnchor_outcome₆₂ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  exact ⟨G.anchor, returns_map_intro₆₂ (fun g : Protocol.GradeRead V => g.anchor) _ G hG⟩

/-- The round-`r` action read computed from `M.wake n` gives exactly the node states it gives
    computed from `n`. -/
private theorem actionReadFrom_wake₆₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

end

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under the bundle with path `W`, if the round ceiling holds at `q` for `C`,
    `lo ≤ opening (q − η_SG)`, `C`'s block is an ancestor of `X`, `v` is in the set for `S.a q`, `n`
    is a node state of `v`'s round-`q` action read along `W`, and `n`'s live confirmed block is an
    ancestor of `X`, then every block the SG vote selector can return at `n` is an ancestor of `X`. -/
private theorem actionSG_preceq_of_live₆₂ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hloOpen : lo ≤ M.opening S.E S.hc (q - S.hc.η_SG)) {X : Block V}
    (hCX : Block.Preceq C.erase X)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q)
    (hlive : Block.Preceq n.live_confirmed X) :
    ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
      Block.Preceq B X := by
  intro A2 hA2 B hB
  have hw := mem_stateBeforeTime_along₆₂ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S q)
  set st := M.toHealing n.st.core with hst
  have hk : M.round_of S.hc st.s = q := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = q
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v q n ⟨_, hw, hn⟩
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc st q
  rw [hk] at hA2 hB
  have heq : B = M.currentSGVote st G :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc st q A2 hA2 G hG B hB
  have hGanchor : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n q ⇢ G.anchor :=
    nodeAnchor_of_read₆₂ S n q G hG
  have hanchorX : Block.Preceq G.anchor X :=
    preceq_trans_Preceq (h.actionAnchor v hv n hn G.anchor hGanchor) hCX
  have hliveSt : Block.Preceq st.toFG.toSG.toGoldfishStore.live_confirmed X := by
    rw [hst, facts.sto.toHealing_live_confirmed]
    exact hlive
  rw [heq]
  cases hdc : M.deepest_clear (some G.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | some D =>
      rw [facts.gr.ModelProperties_currentSGVote_of_deepest_clear hdc]
      exact preceq_trans_Preceq (facts.gr.deepest_clear_Preceq hdc) hliveSt
  | none =>
      cases hgrade : G.Q2 with
      | some Q =>
          have hQ2 : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n q ⇢ some Q := by
            rw [← hgrade]
            exact nodeQ2_of_read₆₂ S n q G hG
          have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon := by
            rw [Restated.a_eq_confirmation_opening_l58 facts S q]
            exact (Restated.confirmationTime_mono_l58 facts S.E
              (Restated.openingSlot_le_seedRoundLastSlot_pred_l58 facts S q)).trans
              h.roundConfirmationInHorizon
          have hdomainAction : M.domain S.E S.hc q .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
            rw [facts.gr.Sts_domain_g1_eq_opening S q, Restated.a_eq_confirmation_opening_l58 facts S q,
              facts.gr.opening_eq_proposal_time]
            exact (Restated.proposal_time_le_vote_time_l58 facts S.E _).trans
              (facts.sch.Protocol_vote_time_le_confirmation_time S.E _)
          have hQA := Restated.actionQ2_preceq_actionAnchorOn facts S Hs Xb hf hHs hHsXb
            h.roundPositive hactionHor (hHs _ _ hdomainAction hv) hloOpen n hn hQ2 G.anchor hGanchor
          rw [facts.gr.currentSGVote_of_Q2 hdc hgrade]
          exact preceq_trans_Preceq hQA hanchorX
      | none =>
          by_cases hraw : G.rawG2
          · rw [facts.gr.currentSGVote_of_rawG2 hdc hgrade hraw]
            obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc st q (M.readFrame n.cache st q).g1
            have hGa := facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc st q G hG a ha
            have hfa := facts.gr.preceq_anchor_of_fgRoot S.E S.hc st q _
              (Proofs.ModelProperties.Preceq_self _) a ha
            rw [← hGa] at hfa
            exact preceq_trans_Preceq hfa hanchorX
          · rw [facts.gr.currentSGVote_of_not_rawG2 hdc hgrade hraw]
            exact hanchorX

/-- Every node state of the round-`r` action read computed from `before` has the tree of `before`'s
    core store. -/
private theorem actionReadFrom_T₆₂ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₂ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

open DecoupledConsensusModel.Statements.Instantiation in
/-- Under the bundle with path `W` and the committee majority, if `hrun` holds, the round ceiling
    holds at `q` for `C` and `lo ≤ vote_time (opening_slot q − 1)`, then some run block `Cstar`
    along `W` through `Xb` is a descendant of `C`'s block and of the live confirmed block of every
    node state of every round-`q` action read of the set for `S.a q`, and either `Cstar` is `C`, or
    a member of the set for the confirmation instant of round `q`'s opening slot confirms `Cstar`'s
    block there. -/
private theorem exists_frontier_all₆₂ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ w ∈ S.E.committee (M.opening_slot S.hc q),
      w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc q))) :
    ∃ Cstar : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb Cstar ∧
      Block.Preceq C.erase Cstar.erase ∧
      (∀ v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
        Block.Preceq n.live_confirmed Cstar.erase) ∧
      (Cstar = C ∨ ∃ v ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc q)), ∃ c : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.confirmation_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c ∧
        Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core
            (M.confirmation_time S.E (M.opening_slot S.hc q)))
          (M.opening_slot S.hc q) Cstar.erase) := by
  classical
  have ha := Restated.a_eq_confirmation_opening_l58 facts S q
  have hconf : ∀ {u : V}, u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)) →
      u ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    intro u hu
    rw [← ha]
    exact hu
  let outs : V → Finset (Block V) := fun v =>
    ((W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T).filter
      (fun B => ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
        n.live_confirmed = B)
  let cands := insert C.erase ((Hs (Restated.Vocabulary.Execution.Setup.a M S q)).biUnion outs)
  have hmemOut : ∀ v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      n.live_confirmed ∈ cands := by
    intro v hv n hn
    refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨?_, n, hn, rfl⟩⟩)
    have h1 := Restated.liveConfirmed_mem_filtered_actionStoreOn facts S Hs Xb hf v q n hn
    have h2 := facts.fc.get_filtered_block_tree_subset _ h1
    rw [facts.sto.toHealing_gs_T, actionReadFrom_T₆₂ facts S _ q n hn] at h2
    exact h2
  have hcase : ∀ X ∈ cands, X = C.erase ∨
      ∃ v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q), ∃ c : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.confirmation_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c ∧
        ((Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core
              (M.confirmation_time S.E (M.opening_slot S.hc q)))
            (M.opening_slot S.hc q) X ∧ Block.Preceq C.erase X) ∨
          Block.Preceq X C.erase) := by
    intro X hX
    rcases Finset.mem_insert.mp hX with hXC | hXo
    · exact Or.inl hXC
    · obtain ⟨v, hv, hXv⟩ := Finset.mem_biUnion.mp hXo
      obtain ⟨-, n, hn, rfl⟩ := Finset.mem_filter.mp hXv
      have hgp := Restated.roundCeiling_openingOutput_genuine_or_preceqOn facts S Hs Xb hf hHs
        hHsXb hcom h hv hlo hrun n hn
      obtain ⟨c, hc, st, -, rfl⟩ := hn
      rw [facts.nd.mkNode_cache] at hgp
      refine Or.inr ⟨v, hv, c, ?_, ?_⟩
      · rw [ha] at hc
        exact hc
      · rw [ha] at hgp ⊢
        exact hgp
  have hcompat : ∀ X ∈ cands, ∀ Y ∈ cands, Block.compatible X Y = true := by
    intro X hX Y hY
    rcases hcase X hX with hXC | ⟨v, hv, cv, hcv, hvgp⟩ <;>
      rcases hcase Y hY with hYC | ⟨w, hw, cw, hcw, hwgp⟩
    · rw [hXC, hYC]
      exact Block.compatible_of_preceq_common (Block.preceq_self C.erase) (Block.preceq_self C.erase)
    · rw [hXC]
      rcases hwgp with hwGen | hwBelow
      · exact compatible_of_cases (Or.inl hwGen.2)
      · exact compatible_of_cases (Or.inr hwBelow)
    · rw [hYC]
      rcases hvgp with hvGen | hvBelow
      · exact compatible_of_cases (Or.inr hvGen.2)
      · exact compatible_of_cases (Or.inl hvBelow)
    · rcases hvgp with hvGen | hvBelow <;> rcases hwgp with hwGen | hwBelow
      · exact Restated.roundCeiling_openingConfirmationsCompatibleOn facts
          S Hs Xb hf hHs hHsXb h (hconf hv) (hconf hw) cv hcv hvGen.1 cw hcw hwGen.1 hlo
      · exact compatible_of_cases (Or.inr (preceq_trans_Preceq hwBelow hvGen.2))
      · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hvBelow hwGen.2))
      · exact compatible_of_preceq_common_Preceq hvBelow hwBelow
  have hnonempty : cands.Nonempty := ⟨C.erase, Finset.mem_insert_self _ _⟩
  obtain ⟨Craw, hsel⟩ := Option.isSome_iff_exists.mp
    (deepest?_isSome_of_compatible hcompat hnonempty)
  have hstarMem : Craw ∈ cands := Proofs.Engine.deepest?_mem hsel
  have hCmem : C.erase ∈ cands := Finset.mem_insert_self _ _
  have hold : Block.Preceq C.erase Craw :=
    preceq_eq_true_iff_Preceq.mp (deepest?_dominates hsel hCmem (hcompat _ hCmem _ hstarMem))
  have houts : ∀ v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      Block.Preceq n.live_confirmed Craw := fun v hv n hn =>
    preceq_eq_true_iff_Preceq.mp (deepest?_dominates hsel (hmemOut v hv n hn)
      (hcompat _ (hmemOut v hv n hn) _ hstarMem))
  by_cases hEq : Craw = C.erase
  · rw [hEq] at hold houts
    exact ⟨C, h.run, hold, houts, Or.inl rfl⟩
  · rcases hcase Craw hstarMem with hC | ⟨v, hv, c, hc, hgp⟩
    · exact (hEq hC).elim
    · rcases hgp with hgen | hbelow
      · obtain ⟨Cstar, hCerase, hCrun⟩ := h.genuineRun v (hconf hv) Craw c hc
          (by rw [facts.nd.mkNode_cache]; exact hgen.1)
        refine ⟨Cstar, hCrun, ?_, ?_, Or.inr ⟨v, hconf hv, c, hc, ?_⟩⟩
        · rw [hCerase]; exact hold
        · intro w hw n hn; rw [hCerase]; exact houts w hw n hn
        · rw [hCerase]; exact hgen.1
      · exact (hEq (Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr hbelow)
          (preceq_eq_true_iff_Preceq.mpr hold))).elim

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committee majority, the weight bound and the slashable
    bound, if the committee of the boundary slot `s0 = opening_slot (q + 1) − 1` voted descendants
    of `C`, a thin head of `s0` of height at least `Mh − 1` is a descendant of `C`, every action
    block of round `q` of the set for `S.a q` is an ancestor of `C`, the root order and the regime
    of round `q + 1` hold at the worlds of `W`, and the timing and awake hypotheses of the signature
    hold, then the relay fold holds at `q` and `C` at the worlds of `W`. -/
theorem roundCeilingRelayFold_of_regimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {q : Round} {C : Block V}
    (hpostAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    (hpost0 : lo ≤ M.vote_time S.E
      ((M.opening_slot S.hc (q + 1)) - 1))
    (hhor0 : M.confirmation_time S.E
      ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon)
    (hlastVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb
      ((M.opening_slot S.hc (q + 1)) - 1) (fun X => Block.Preceq C X))
    (hboundaryThin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh
      ((M.opening_slot S.hc (q + 1)) - 1) C)
    (hupper : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    (hrootOrder : Restated.RoundCeilingNextRootOrderAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs q C)
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    Restated.RoundCeilingRelayFoldAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs q C := by
  let o := (M.opening_slot S.hc (q + 1))
  let last := Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1)
  let s0 := o - 1
  have hs0Pos : 0 < s0 := facts.gr.openingSlot_pred_pos_l58 S (Nat.succ_pos q)
  have hs0Succ : s0 + 1 = o := Restated.openingSlot_pred_succ_l58 facts S (Nat.succ_pos q)
  have hlastPos : 0 < last :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1))
  have hoPos : 0 < o := facts.gr.openingSlot_pos_l58 S (Nat.succ_pos q)
  have hopenLast : o ≤ last :=
    Nat.le_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1))
  have hlastPredSucc : last - 1 + 1 = last :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenHiSucc : o ≤ (last - 1) + 1 := by
    rw [hlastPredSucc]
    exact hopenLast
  have hround0 : (M.round_of S.hc (s0 + 1)) = q + 1 := by
    rw [hs0Succ]
    exact facts.gr.round_of_opening_slot_eq_schedule S.hc (q + 1)
  have hvoteHorAt : ∀ d : Slot, d ≤ last →
      M.vote_time S.E d ≤ rho.horizon := by
    intro d hd
    have hlastToConf : M.vote_time S.E last ≤
        M.confirmation_time S.E (last - 1) := by
      have h := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E (last - 1)
      rw [hlastPredSucc] at h
      exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h
    exact (facts.sch.vote_time_mono_slots S.E hd).trans
      (hlastToConf.trans (by simpa only [last] using
        hreg.roundConfirmationInHorizon))
  have hloVote : ∀ s : Slot, s0 ≤ s → lo ≤ M.vote_time S.E s :=
    fun s hs => hpost0.trans (Restated.vote_time_mono_l58 facts S.E hs)
  have hloFreeze : ∀ s : Slot, s0 ≤ s → lo ≤ M.view_freeze S.E s :=
    fun s hs => (hloVote s hs).trans (Restated.vote_time_le_view_freeze_l58 facts S.E s)
  have hrunR : ∀ d : Slot, o ≤ d → d ≤ last → ∀ w ∈ S.E.committee d,
      w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d) := by
    intro d hdlo hdhi w _ hw j hj
    have hround : M.round_of S.hc d = q + 1 := by
      rcases Nat.eq_or_lt_of_le hdlo with h | h
      · rw [← h]
        exact facts.gr.round_of_opening_slot_eq S.hc (q + 1)
      · have hdhi' : d ≤ M.opening_slot S.hc (q + 1 + 1) - 1 := hdhi
        have hlt : d < M.opening_slot S.hc (q + 1 + 1) :=
          (Nat.le_sub_one_iff_lt (facts.gr.openingSlot_pos_l58 S (Nat.succ_pos (q + 1)))).1 hdhi'
        exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc h hlt
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
      rw [hround]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self q)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S (q + 1)
      have h3 : lo ≤ M.a S.hc S.E.Δ q := hpostAction
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  have hvoteO : ∀ {P : V → Prop},
      (∀ w ∈ Hs (M.vote_time S.E o), P w) →
        ∀ w ∈ Hs (M.vote_time S.E (s0 + 1)), P w := by
    intro P h w hw
    rw [hs0Succ] at hw
    exact h w hw
  have hopening := Restated.relayVoteInputs_stepOn facts S Hs Xb hf hHs hHsXb hfb hsb hround0
    hpostAction hcut hpost0 hhor0 hlastVotes hboundaryThin hupper
    (hvoteO (fun w hw => by
      simpa only [hs0Succ] using
        hreg.window.voteFrontier o (le_refl _) hopenHiSucc w hw))
    (hvoteO (fun w hw => by
      simpa only [hs0Succ] using
        hreg.window.voteGateOff o (le_refl _) hopenHiSucc w hw))
    (hvoteO (fun w hw => by
      simpa only [hs0Succ] using
        hrootOrder.voteDuty o (le_refl _) hopenLast w hw))
    hA
  have hopeningInput : ∀ w ∈ Hs (M.vote_time S.E (s0 + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s0 + 1))) w).st.core.toHealing
        (M.vote_time S.E (s0 + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s0 + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s0 C w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s0 + 1))) w).st
          (M.vote_time S.E (s0 + 1))) (W (strictEventIndex rho (M.vote_time S.E (s0 + 1))) w).record c) :=
    fun w hw c hc =>
      let b := hopening.1 w hw c hc
      ⟨b.1, b.2.1, b.2.2.1, b.2.2.2⟩
  have hopeningAnchor := hopening.2
  have hrun0 := hrunR (s0 + 1) (by rw [hs0Succ]) (by rw [hs0Succ]; exact hopenLast)
  have hopeningVotes0 := Restated.honestVotesCone_succ_stepOn facts S Hs Xb hf hHs hHsXb hcom
    hs0Pos hpost0 hhor0 hlastVotes hopeningInput hrun0
  have hopeningVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb o
      (fun X => Block.Preceq C X) := by
    rw [← hs0Succ]
    exact hopeningVotes0
  have hopeningThin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh o C := by
    have hthin := Restated.seedThinHead_of_voteInputsOn facts S Hs Xb hf hHs hHsXb hcom
      (s := s0) (C := C) (E := C)
      (by
        rw [hs0Succ]
        exact hvoteHorAt o hopenLast)
      hopeningInput hopeningAnchor
      (hvoteO (fun w hw => by
        simpa only [hs0Succ] using
          hreg.window.voteFrontier o (le_refl _) hopenHiSucc w hw))
      hopeningVotes0 (hloFreeze s0 (le_refl _)) hrun0
    rw [← hs0Succ]
    exact hthin
  have hslotInput : ∀ s : Slot, o ≤ s → s ≤ last - 1 →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X) →
      Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C →
      Restated.GoldfishConeSlotInputsOn M S rho (fun t => W (strictEventIndex rho t)) Hs s C ∧
        (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
            (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
          let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
          ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A → Block.Preceq A C) := by
    intro s hlo hhi hvotes hthin
    have hround : (M.round_of S.hc (s + 1)) = q + 1 := roundOf_succ_eq_step₆₂ facts S hlo hhi
    have hs0s : s0 ≤ s := by
      have hs0o : s0 ≤ o := by rw [← hs0Succ]; exact Nat.le_succ s0
      exact hs0o.trans hlo
    have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
      (Restated.confirmationTime_mono_l58 facts S.E hhi).trans
        (by simpa only [last] using hreg.roundConfirmationInHorizon)
    have hsuccLast : s + 1 ≤ last := by
      rw [← hlastPredSucc]
      exact Nat.succ_le_succ hhi
    refine (fun h => ?_) (Restated.relaySlotInputs_stepOn facts S Hs Xb hf hHs hHsXb hfb hsb
      hround hpostAction hcut (hloVote s hs0s) hhorS hvotes hthin hupper ?_ ?_ ?_ ?_ ?_ ?_ hA)
    · refine ⟨⟨fun w hw c hc => ?_, fun w hw c hc => ?_⟩, h.2.2⟩
      · obtain ⟨b1, b2, b3, b4⟩ := h.1 w hw c hc
        exact ⟨b1, b2, b3, b4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := h.2.1 w hw c hc
        exact ⟨b1, b2, b3, b4⟩
    · intro w hw
      exact hreg.window.voteFrontier (s + 1)
        (hlo.trans (Nat.le_succ s))
        (Nat.succ_le_succ hhi) w hw
    · intro w hw
      exact hreg.window.voteGateOff (s + 1)
        (hlo.trans (Nat.le_succ s))
        (Nat.succ_le_succ hhi) w hw
    · intro w hw
      exact hrootOrder.voteDuty (s + 1)
        (by simpa only [o] using hlo.trans (Nat.le_succ s))
        (by simpa only [last] using hsuccLast) w hw
    · intro w hw
      exact hreg.window.confirmationFrontier s
        (by simpa only [o] using hlo) hhi w hw
    · intro w hw
      exact hreg.window.confirmationGateOff s
        (by simpa only [o] using hlo) hhi w hw
    · intro w hw
      exact hrootOrder.confirmation s
        (by
          simpa only [o, s0] using
            (Nat.sub_le o 1).trans hlo)
        (by
          simpa only [last] using
            lt_of_le_of_lt hhi (Nat.sub_lt hlastPos Nat.zero_lt_one)) w hw
  have hfold : ∀ s : Slot, o ≤ s → s ≤ last - 1 →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X) ∧
        Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C ∧
        Restated.GoldfishConeSlotInputsOn M S rho (fun t => W (strictEventIndex rho t)) Hs s C ∧
        (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
            (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
          let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
          ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A → Block.Preceq A C) := by
    intro s hlo
    induction s, hlo using Nat.le_induction with
    | base =>
        intro hhi
        have hin := hslotInput o (le_refl _) hhi hopeningVotes hopeningThin
        exact ⟨hopeningVotes, hopeningThin, hin.1, hin.2⟩
    | succ s hlo ih =>
        intro hsuccHi
        have hsHi : s ≤ last - 1 := (Nat.le_succ s).trans hsuccHi
        obtain ⟨hcone, hthin, hinp, hanch⟩ := ih hsHi
        have hsPos : 0 < s := lt_of_lt_of_le hoPos hlo
        have hs0s : s0 ≤ s := by
          have hs0o : s0 ≤ o := by rw [← hs0Succ]; exact Nat.le_succ s0
          exact hs0o.trans hlo
        have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
          (Restated.confirmationTime_mono_l58 facts S.E hsHi).trans
            (by simpa only [last] using hreg.roundConfirmationInHorizon)
        have hsuccLast : s + 1 ≤ last := by
          rw [← hlastPredSucc]
          exact Nat.succ_le_succ hsHi
        have hrunNext := hrunR (s + 1) (hlo.trans (Nat.le_succ s)) hsuccLast
        have hvotesNext := Restated.honestVotesCone_succ_stepOn facts S Hs Xb hf hHs hHsXb hcom
          hsPos (hloVote s hs0s) hhorS hcone hinp.vote hrunNext
        have hthinNext : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh (s + 1) C :=
          Restated.seedThinHead_of_voteInputsOn facts S Hs Xb hf hHs hHsXb hcom
            (hvoteHorAt (s + 1) hsuccLast)
            hinp.vote hanch
            (fun w hw => hreg.window.voteFrontier (s + 1)
              (hlo.trans (Nat.le_succ s)) (Nat.succ_le_succ hsHi) w hw)
            hvotesNext (hloFreeze s hs0s) hrunNext
        have hin := hslotInput (s + 1) (hlo.trans (Nat.le_succ s)) hsuccHi
          hvotesNext hthinNext
        exact ⟨hvotesNext, hthinNext, hin.1, hin.2⟩
  have hroundInputs : ∀ s : Slot, o ≤ s → s < last →
      Restated.GoldfishConeSlotInputsOn M S rho (fun t => W (strictEventIndex rho t)) Hs s C := by
    intro s hlo hhi
    exact (hfold s hlo (Nat.le_pred_of_lt hhi)).2.2.1
  have hvote : ∀ d : Slot, o ≤ d → d ≤ last → ∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho (d - 1) C w
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
            (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c) ∧
        ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
            (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c)
          (M.round_of S.hc (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
            (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).st.core.s)
            ⇢ A → Block.Preceq A C := by
    intro d hdlo hdhi w hw
    have hdPos : 0 < d := hoPos.trans_le hdlo
    have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdPos)
    by_cases heq : d = o
    · have hw' : w ∈ Hs (M.vote_time S.E (s0 + 1)) := by
        rw [hs0Succ, ← heq]; exact hw
      have h1 := hopeningInput w hw'
      have h2 := hopeningAnchor w hw'
      rw [hs0Succ, ← heq] at h1 h2
      intro c hc
      have b := h1 c hc
      exact ⟨⟨b.candidate, b.root, b.anchor, b.path⟩, h2 c hc⟩
    · have hdLt : o < d := lt_of_le_of_ne hdlo (Ne.symm heq)
      have hdPred : o ≤ d - 1 := Nat.le_pred_of_lt hdLt
      have hpredLt : d - 1 < last := by
        exact lt_of_lt_of_le (Nat.sub_lt hdPos Nat.zero_lt_one) hdhi
      have hw' : w ∈ Hs (M.vote_time S.E (d - 1 + 1)) := by
        rw [hdSucc]; exact hw
      have hf' := hfold (d - 1) hdPred (Nat.le_pred_of_lt hpredLt)
      have h1 := hf'.2.2.1.vote w hw'
      have h2 := hf'.2.2.2 w hw'
      rw [hdSucc] at h1 h2
      intro c hc
      exact ⟨h1 c hc, h2 c hc⟩
  refine
    { openingStepInputs := hopeningInput
      roundInputs := by
        intro s hlo hhi
        exact hroundInputs s (by simpa only [o] using hlo)
          (by simpa only [last] using hhi)
      voteActive := ?_
      voteAnchor := ?_
      confirmationAnchor := ?_ }
  · intro d hdlo hdhi w hw
    obtain ⟨c, hc, hcore, -⟩ := exists_read_of_world₆₂ facts S
      (W (strictEventIndex rho (M.vote_time S.E d)) w) (M.vote_time S.E d)
    have hin := (hvote d hdlo hdhi w hw c hc).1
    obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).st.core
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).st.core.s
    have h := facts.fc.voter_filtered_block_tree_subset_filtered S.E _ T hT (hin.candidate T hT)
    rw [hcore] at h
    exact h
  · intro d hdlo hdhi w hw c hc
    exact (hvote d hdlo hdhi w hw c hc).2
  · intro s hslo hshi w hw c hc
    by_cases heq : s = s0
    · subst s
      exact Restated.confirmationAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs hHsXb hfb
        hround0 hpostAction hcut hhor0 hupper hw
        (hrootOrder.confirmation s0 (le_refl _)
          (by
            simpa only [s0, last] using
              lt_of_lt_of_le (Nat.sub_lt hoPos Nat.zero_lt_one) hopenLast)
          w hw) hA c hc
    · have hsLt : s0 < s := lt_of_le_of_ne hslo (Ne.symm heq)
      have hsMain : o ≤ s := by
        rw [← hs0Succ]
        exact Nat.succ_le_iff.mpr hsLt
      have hround : (M.round_of S.hc (s + 1)) = q + 1 :=
        roundOf_succ_eq_step₆₂ facts S hsMain (Nat.le_pred_of_lt hshi)
      have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
        (Restated.confirmationTime_mono_l58 facts S.E
          (Nat.le_pred_of_lt hshi)).trans
          (by exact hreg.roundConfirmationInHorizon)
      exact Restated.confirmationAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs hHsXb hfb
        hround hpostAction hcut hhorS hupper hw
        (hrootOrder.confirmation s
          (by
            simpa only [o, s0] using
              (Nat.sub_le o 1).trans hsMain)
          (by simpa only [last] using hshi)
          w hw) hA c hc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `0 < r`, `t` is a time of round `r` equal to its grade-1
    domain instant inside the horizon, and `c` is an outcome of `w`'s cache update at `t`, then for
    every outcome `fr` of the grade-1 store root of `w`'s store in
    `W (strictEventIndex rho (domain r .g1))`, the grade-1 frame of the node state staged with `c`
    is `fr` clipped to that node state's finalized block. -/
theorem preparedFrame_g1_eq_storeRoot_at_openingOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (r : Round) (hr : 0 < r) (t : Time) (hw : w ∈ Hs t)
    (hround : (M.round_of S.hc (S.E.slotOf t)) = r)
    (hopen : M.domain S.E S.hc r .g1 = t)
    (hhor : M.domain S.E S.hc r .g1 ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) w).st.core.toHealing t
      (W (strictEventIndex rho t) w).cache ⇢ c) :
    ∀ fr, Restated.Vocabulary.Internal.PhaseGrades.storeRoot M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 ⇢ fr →
    (M.readFrame
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).cache
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).st.core) r).g1 =
      some (fr.map
        (fun X => M.clipGrade X
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
            (W (strictEventIndex rho t) w).record c).st.core.F)) :=
  Restated.fixedRoot_preparedFrame_g1_eq_storeRoot_at_openingOn facts S rho Hs Xb hf w r hr t hw hround hopen
    hhor c hc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the weight bound, if `lo ≤ S.a q`, round `q + 1`'s earliest
    grade cutoff and the next opening's proposal instant are in the horizon, every action block of
    round `q` of the set for `S.a q` is an ancestor of `C`, the next opening proposer is in the set
    for its proposal instant, `c` is an outcome of its cache update there, the finality root of the
    node state `n` staged with `c` is an ancestor of `C`, and every member of the set for
    `S.a q + Δ` is awake at `q`, then every anchor `n` can read at round `q + 1` is an ancestor of
    `C`. -/
theorem proposalAnchorAt_preceq_of_previousCarriersOn (facts : Record.Facts M)
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
  Restated.fixedRoot_preparedProposalAnchor_preceq_of_previousCarriersOn facts S Hs Xb hf hHs hHsXb hfb
    hpost hcut hproposalHor hupper hprop c hc hroot hA

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committee majority and the weight bound, if the boundary
    cone of round `q + 1` holds at `Cstar` with frontier `Mh` along `W`, the next-round regime holds
    for `Mh` and `q` at the worlds of `W`, `lo ≤ S.a q`,
    `lo ≤ vote_time (opening_slot (q + 1) − 1)`, and every member of the set for `S.a q + Δ` is
    awake at `q`, then every residual field of the round-ceiling step holds at `Cstar`. -/
theorem roundCeilingStepResidual_of_boundaryConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {Cstar : NamedBlock V}
    (hboundary : Restated.RoundCeilingBoundaryConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb Mh q Cstar)
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    Restated.RoundCeilingStepResidualAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q
      Cstar.erase := by
  let o := (M.opening_slot S.hc (q + 1))
  let last := Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1)
  let s0 := o - 1
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hlastVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s0
      (fun X => Block.Preceq Cstar.erase X) := hboundary.boundaryVotes
  have hlastPos : 0 < last :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1))
  have hopenLastPred : o ≤ last - 1 := Restated.openingSlot_le_seedRoundLastSlot_pred_l58 facts S (q + 1)
  have hs0LastPred : s0 ≤ last - 1 :=
    (Nat.sub_le o 1).trans hopenLastPred
  have hhor0 : M.confirmation_time S.E s0 ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E hs0LastPred).trans hreg.roundConfirmationInHorizon
  have hactionEq : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) = M.confirmation_time S.E o :=
    Restated.a_eq_confirmation_opening_l58 facts S (q + 1)
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon := by
    rw [hactionEq]
    exact (Restated.confirmationTime_mono_l58 facts S.E hopenLastPred).trans hreg.roundConfirmationInHorizon
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q)).trans hactionHor
  have hwindowTop : o ≤ (last - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)]
    exact Nat.le_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1))
  have hvoteConfO : M.vote_time S.E o ≤ M.confirmation_time S.E o :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E o
  have hM : 1 ≤ Mh := by
    have hpositive : 0 < ((S.E.committee o) ∩ Hs (M.confirmation_time S.E o)).card := by
      have hc := hcom o
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
    have hgate := hreg.window.voteGateOff o (le_refl _) hwindowTop w
      (hHs _ _ hvoteConfO (Finset.mem_inter.mp hw).2)
    exact (by decide : 1 ≤ 2).trans ((Nat.le_add_left 2 _).trans hgate)
  have hfold := Restated.roundCeilingRelayFold_of_regimeOn facts S Hs Xb hf hHs hHsXb hcom hfb hsb
    hloAction hcut hlo hhor0 hlastVotes hboundary.boundaryThinHead hboundary.previousCarriers
    hboundary.rootOrder hreg hA
  have hoLast : o < last := Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1)
  have hactionActive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      Cstar.erase ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG := by
    intro w hw
    rw [hactionEq] at hw ⊢
    obtain ⟨c, hc, hcore, -⟩ := exists_read_of_world₆₂ facts S
      (W (strictEventIndex rho (M.confirmation_time S.E o)) w) (M.confirmation_time S.E o)
    have h := ((hfold.roundInputs o (le_refl _) hoLast).confirmation w hw c hc).candidate
    unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree at h
    rw [hcore, tickStore_filtered₆₂ facts] at h
    exact h
  have hactionAnchor : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w) (q + 1),
        ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (q + 1) ⇢ a →
          a ⪯ Cstar.erase := by
    intro w hw n hn a ha
    have h := actionAnchor_confirmationAnchor₆₂ facts S _ (q + 1) n hn a ha
    have hc := actionReadFrom_cache₆₂ facts S _ (q + 1) n hn
    rw [hactionEq] at hw h hc
    exact hfold.confirmationAnchor o (Nat.sub_le _ _) hoLast w hw n.cache hc a h
  have hpropFacts : S.E.proposer o ∈ Hs (M.confirmation_time S.E o) →
      Cstar.erase ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E o)) (S.E.proposer o)).st.core
        (M.proposal_time S.E o))).toFG ∧
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.proposal_time S.E o)) (S.E.proposer o)).st.core.toHealing
          (M.proposal_time S.E o)
          (W (strictEventIndex rho (M.proposal_time S.E o)) (S.E.proposer o)).cache ⇢ c →
        ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
            (M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.proposal_time S.E o)) (S.E.proposer o)).st
              (M.proposal_time S.E o))
              (W (strictEventIndex rho (M.proposal_time S.E o)) (S.E.proposer o)).record c)
            (q + 1) ⇢ a → a ⪯ Cstar.erase := by
    intro hprop
    have hroot : Block.Preceq
        (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E o)) (S.E.proposer o)).st.core
          (M.proposal_time S.E o))).toFG) Cstar.erase :=
      hboundary.rootOrder.proposer hprop
    have hs0Succ : s0 + 1 = o := Restated.openingSlot_pred_succ_l58 facts S (Nat.succ_pos q)
    have hproposalVote : M.proposal_time S.E o ≤ M.vote_time S.E o :=
      Restated.proposal_time_le_vote_time_l58 facts S.E o
    have hpropP : S.E.proposer o ∈ Hs (M.proposal_time S.E o) :=
      hHs _ _ (hproposalVote.trans hvoteConfO) hprop
    have hsupportConf : M.support_cutoff S.E s0 ≤ M.confirmation_time S.E o := by
      obtain ⟨-, -, -, h4, -⟩ := Restated.relay_slot_instants_l61 facts S.E s0
      rw [hs0Succ] at h4
      exact h4.trans hvoteConfO
    have hpropSupport : S.E.proposer (s0 + 1) ∈ Hs (M.support_cutoff S.E s0) := by
      rw [hs0Succ]
      exact hHs _ _ hsupportConf hprop
    have hresolve := Restated.headsResolveIn_proposerDutyStore_of_postHealingConeOn facts
      S Hs Xb hf hHs hHsXb hlo
        ((facts.sch.Sts_support_cutoff_le_confirmation_time S.E s0).trans hhor0)
        hpropSupport
        (by rw [hs0Succ]; exact hroot)
        hlastVotes
    obtain ⟨X, hXhonest, hCX, hXheight⟩ := hboundary.boundaryThinHead
    obtain ⟨x, hxHonest, hxCommittee, hXrun, hXemit⟩ := hXhonest
    have hXhead : Restated.HonestHeadOn M S rho W Hs Xb s0 X.erase :=
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hfind := (hresolve X.erase hXhead).1
    have hXpre : X.erase ∈ (W (strictEventIndex rho (M.proposal_time S.E o)) (S.E.proposer o)).st.T := by
      have h := Proofs.HealingLemmas.find?_mem hfind
      rw [hs0Succ, tickStore_T₆₂ facts] at h
      exact h
    have hproposalHor : M.proposal_time S.E o ≤ rho.horizon :=
      (le_of_lt (by simpa only [hs0Succ] using
        facts.sch.proposal_time_succ_lt_confirmation_time S.E s0)).trans hhor0
    have hfilteredPre := Restated.frontierAncestor_filtered_of_gateOffOn facts
      S Hs Xb hf hsb (hHsXb _ hpropP) hproposalHor hXpre rfl hXrun hCX hXheight hM
        (hreg.proposalFrontier _ hpropP) (hreg.proposalGateOff _ hpropP)
        (by rw [tickStore_fgRoot₆₂ facts] at hroot; exact hroot)
    refine ⟨by rw [tickStore_filtered₆₂ facts]; exact hfilteredPre, ?_⟩
    intro c hc
    exact Restated.proposalAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs hHsXb hfb
      hloAction hcut hproposalHor hboundary.previousCarriers hpropP c hc
      (by rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_fg_root, setClock_core_tickStore₆₂ facts S]
          exact hroot) hA
  exact
    { postOpeningProposal := hreg.postOpeningProposal
      roundConfirmationInHorizon := hreg.roundConfirmationInHorizon
      openingStepInputs := hfold.openingStepInputs
      roundInputs := hfold.roundInputs
      voteActive := hfold.voteActive
      actionActive := hactionActive
      voteAnchor := hfold.voteAnchor
      confirmationAnchor := hfold.confirmationAnchor
      actionAnchor := hactionAnchor
      proposerAnchorCeiling := fun hp => (hpropFacts hp).2
      proposerActive := fun hp => (hpropFacts hp).1
      gateOff := hreg.window
      genuineRun := fun w hw D c hc hD =>
        Restated.genuineConfirmation_runBlock_stepOn facts S Hs Xb hf (hHsXb _ hw) c hc
          (by rw [facts.nd.mkNode_cache] at hD; exact hD) }

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `w ∈ Xb`, the FG root of `w`'s core store in
    `W (strictEventIndex rho read)` erases a run block along `W` through `Xb`. -/
theorem seedRootRunBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time) :
    ∃ R : NamedBlock V,
      R.erase = M.get_fg_root
        (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG ∧
      Restated.RunBlockOn M S rho W Xb R := by
  have hroot := Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts
    S rho read w (W (strictEventIndex rho read)) (mem_stateBeforeTime_along₆₂ hf.sorted hf.onePath read)
  have hmem := facts.fc.get_filtered_block_tree_subset _ hroot
  rw [facts.sto.toHealing_gs_T] at hmem
  exact Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hw read hmem

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the slashable bound, if the next-round regime holds for `Mh`
    and `q` at the worlds of `W`, `Y` is an FG root read in round `q + 1` by a member of the set for
    that read's instant, and `X` is a run block along `W` through `Xb` of height at least `Mh − 1`,
    then `Y` is an ancestor of `X`. -/
theorem seedRootReadCandidate_preceq_thinOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {q : Round}
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    {Y : Block V}
    (hY : Y ∈ Restated.seedRootReadCandidatesOn M S rho (fun t => W (strictEventIndex rho t)) Hs q)
    {X : NamedBlock V} (hXrun : Restated.RunBlockOn M S rho W Xb X)
    (hXthin : Mh - 1 ≤
      (M.derive_named S.E S.cfg X).h) :
    Block.Preceq Y X.erase := by
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1))
  have hlastPredSucc : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1 + 1 =
      Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenPos : 0 < (M.opening_slot S.hc (q + 1)) := facts.gr.openingSlot_pos_l58 S (Nat.succ_pos q)
  simp only [Restated.seedRootReadCandidatesOn, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image, (scs% mem_seedSlotRange)] at hY
  rcases hY with hvote | hconf | hprop
  · obtain ⟨d, ⟨hdlo, hdhi⟩, w, hw, hYeq⟩ := hvote
    rw [← hYeq, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₂ facts]
    have hfrontier := hreg.window.voteFrontier d hdlo
      (by simpa only [hlastPredSucc] using hdhi) w hw
    have hgate := hreg.window.voteGateOff d hdlo
      (by simpa only [hlastPredSucc] using hdhi) w hw
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₂ facts] at hfrontier
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₆₂ facts] at hgate
    exact Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) rfl hXrun hXthin
      hfrontier hgate
  · obtain ⟨s, ⟨hslo, hshi⟩, w, hw, hYeq⟩ := hconf
    rw [← hYeq, Restated.Vocabulary.Protocol.confRoot]
    unfold Record.Model.S.toHealing
    rw [tickStore_fgRoot₆₂ facts]
    by_cases heq : s = (M.opening_slot S.hc (q + 1)) - 1
    · subst s
      have hfrontier := hreg.boundaryConfirmationFrontier w hw
      have hgate := hreg.boundaryConfirmationGateOff w hw
      rw [tickStore_h_max₆₂ facts] at hfrontier
      rw [tickStore_h_j₆₂ facts] at hgate
      exact Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) rfl hXrun hXthin
        hfrontier hgate
    · have hslt : (M.opening_slot S.hc (q + 1)) - 1 < s :=
        lt_of_le_of_ne hslo (Ne.symm heq)
      have hsMain : (M.opening_slot S.hc (q + 1)) ≤ s := by
        rw [← Nat.sub_add_cancel (Nat.succ_le_iff.mpr hopenPos)]
        exact Nat.succ_le_iff.mpr hslt
      have hfrontier := hreg.window.confirmationFrontier s hsMain hshi w hw
      have hgate := hreg.window.confirmationGateOff s hsMain hshi w hw
      rw [tickStore_h_max₆₂ facts] at hfrontier
      rw [tickStore_h_j₆₂ facts] at hgate
      exact Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) rfl hXrun hXthin
        hfrontier hgate
  · obtain ⟨w, hw, hYeq⟩ := hprop
    rw [← hYeq]
    exact Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) rfl hXrun hXthin
      (hreg.proposalFrontier w hw) (hreg.proposalGateOff w hw)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if every set of the family is inside `Xb` and `Y` is an FG root
    read in round `q + 1` by a member of the set for that read's instant, then `Y` erases a run
    block along `W` through `Xb`. -/
theorem seedRootReadCandidate_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} {Y : Block V}
    (hY : Y ∈ Restated.seedRootReadCandidatesOn M S rho (fun t => W (strictEventIndex rho t)) Hs q) :
    ∃ R : NamedBlock V, R.erase = Y ∧ Restated.RunBlockOn M S rho W Xb R := by
  simp only [Restated.seedRootReadCandidatesOn, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image, (scs% mem_seedSlotRange)] at hY
  rcases hY with hvote | hconf | hprop
  · obtain ⟨d, -, w, hw, hYeq⟩ := hvote
    rw [← hYeq, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₂ facts]
    exact Restated.seedRootRunBlockOn facts S Hs Xb hf (hHsXb _ hw) (M.vote_time S.E d)
  · obtain ⟨s, -, w, hw, hYeq⟩ := hconf
    rw [← hYeq, Restated.Vocabulary.Protocol.confRoot]
    unfold Record.Model.S.toHealing
    rw [tickStore_fgRoot₆₂ facts]
    exact Restated.seedRootRunBlockOn facts S Hs Xb hf (hHsXb _ hw) (M.confirmation_time S.E s)
  · obtain ⟨w, hw, hYeq⟩ := hprop
    rw [← hYeq]
    exact Restated.seedRootRunBlockOn facts S Hs Xb hf (hHsXb _ hw) _

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the slashable bound, if the next-round regime holds for `Mh`
    and `q`, `C` and `X0` are run blocks along `W` through `Xb`, `X0` has height at least `Mh − 1`,
    and `C` is an ancestor of `X0`, then some run block `R` is a descendant of `C` and of every FG
    root read in round `q + 1`, and an ancestor of every run block of height at least `Mh − 1` that
    descends from `C`. -/
theorem exists_seedRebaseCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {q : Round} {C X0 : NamedBlock V}
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hX0run : Restated.RunBlockOn M S rho W Xb X0)
    (hX0thin : Mh - 1 ≤
      (M.derive_named S.E S.cfg X0).h)
    (hCX0 : Block.Preceq C.erase X0.erase) :
    ∃ R : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb R ∧
        Block.Preceq C.erase R.erase ∧
        (∀ Y ∈ Restated.seedRootReadCandidatesOn M S rho (fun t => W (strictEventIndex rho t)) Hs q,
          Block.Preceq Y R.erase) ∧
        (∀ X : NamedBlock V, Restated.RunBlockOn M S rho W Xb X →
          Mh - 1 ≤ (M.derive_named S.E S.cfg X).h →
            Block.Preceq C.erase X.erase →
            Block.Preceq R.erase X.erase) := by
  let candidates := insert C.erase
    (Restated.seedRootReadCandidatesOn M S rho (fun t => W (strictEventIndex rho t)) Hs q)
  have hbelow : ∀ Y ∈ candidates, ∀ X : NamedBlock V, Restated.RunBlockOn M S rho W Xb X →
      Mh - 1 ≤ (M.derive_named S.E S.cfg X).h →
        Block.Preceq C.erase X.erase → Block.Preceq Y X.erase := by
    intro Y hY X hXrun hXthin hCX
    rcases Finset.mem_insert.mp hY with hYC | hYroot
    · rw [hYC]
      exact hCX
    · exact Restated.seedRootReadCandidate_preceq_thinOn facts
        S Hs Xb hf hHsXb hsb hreg hYroot hXrun hXthin
  have hcompatible : ∀ Y ∈ candidates, ∀ Z ∈ candidates,
      Block.compatible Y Z = true := by
    intro Y hY Z hZ
    exact compatible_of_preceq_common_Preceq
      (hbelow Y hY X0 hX0run hX0thin hCX0)
      (hbelow Z hZ X0 hX0run hX0thin hCX0)
  have hnonempty : candidates.Nonempty :=
    ⟨C.erase, Finset.mem_insert_self _ _⟩
  obtain ⟨Rraw, hR⟩ := Option.isSome_iff_exists.mp
    (deepest?_isSome_of_compatible hcompatible hnonempty)
  have hRmem : Rraw ∈ candidates := Proofs.Engine.deepest?_mem hR
  have hCmem : C.erase ∈ candidates := Finset.mem_insert_self _ _
  obtain ⟨R, hRerase, hRrun⟩ : ∃ R : NamedBlock V,
      R.erase = Rraw ∧ Restated.RunBlockOn M S rho W Xb R := by
    rcases Finset.mem_insert.mp hRmem with hRC | hRroot
    · exact ⟨C, hRC.symm, hCrun⟩
    · exact Restated.seedRootReadCandidate_runBlockOn facts S Hs Xb hf hHsXb hRroot
  have hCRraw : Block.Preceq C.erase Rraw :=
    preceq_eq_true_iff_Preceq.mp
      (Proofs.HealingLemmas.deepest?_dominates hR hCmem (hcompatible C.erase hCmem Rraw hRmem))
  refine ⟨R, hRrun, ?_, ?_, ?_⟩
  · simpa only [hRerase] using hCRraw
  · intro Y hY
    have hYmem : Y ∈ candidates := Finset.mem_insert_of_mem hY
    have hYRraw := Proofs.HealingLemmas.deepest?_dominates hR hYmem
      (hcompatible Y hYmem Rraw hRmem)
    simpa only [hRerase] using preceq_eq_true_iff_Preceq.mp hYRraw
  · intro X hXrun hXthin hCX
    have hRXraw := hbelow Rraw hRmem X hXrun hXthin hCX
    simpa only [hRerase] using hRXraw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the slashable bound, if the next-round regime holds for `Mh`
    and `q`, `C` and `X0` are run blocks along `W` through `Xb`, `X0` has height at least `Mh − 1`,
    and `C` is an ancestor of `X0`, then some run block `R` is a descendant of `C`, every finality
    root read in round `q + 1` by a member of the set for that read's instant is an ancestor of `R`,
    and `R` is an ancestor of every run block of height at least `Mh − 1` that descends from `C`. -/
theorem exists_roundCeilingRebaseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {q : Round} {C X0 : NamedBlock V}
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hX0run : Restated.RunBlockOn M S rho W Xb X0)
    (hX0thin : Mh - 1 ≤
      (M.derive_named S.E S.cfg X0).h)
    (hCX0 : Block.Preceq C.erase X0.erase) :
    ∃ R : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb R ∧
        Block.Preceq C.erase R.erase ∧
        Restated.RoundCeilingNextRootOrderAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs q
          R.erase ∧
        (∀ X : NamedBlock V, Restated.RunBlockOn M S rho W Xb X →
          Mh - 1 ≤ (M.derive_named S.E S.cfg X).h →
            Block.Preceq C.erase X.erase →
            Block.Preceq R.erase X.erase) := by
  obtain ⟨R, hRrun, hCR, hRoots, hRbelow⟩ :=
    Restated.exists_seedRebaseCeilingOn facts S Hs Xb hf hHsXb hsb hreg hCrun hX0run hX0thin hCX0
  refine ⟨R, hRrun, hCR, ?_, hRbelow⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d hdlo hdhi w hw
    apply hRoots
    simp only [Restated.seedRootReadCandidatesOn, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, (scs% mem_seedSlotRange)]
    exact Or.inl ⟨d, ⟨hdlo, hdhi⟩, w, hw, rfl⟩
  · intro s hslo hshi w hw
    apply hRoots
    simp only [Restated.seedRootReadCandidatesOn, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, (scs% mem_seedSlotRange)]
    exact Or.inr (Or.inl ⟨s, ⟨hslo, Nat.le_pred_of_lt hshi⟩, w, hw, rfl⟩)
  · intro hprop
    have hpropP : S.E.proposer ((M.opening_slot S.hc (q + 1))) ∈
        Hs (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))) :=
      hHs _ _ ((Restated.proposal_time_le_vote_time_l58 facts S.E _).trans
        (facts.sch.Protocol_vote_time_le_confirmation_time S.E _)) hprop
    have hmem : M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).st.core).toFG ∈
        Restated.seedRootReadCandidatesOn M S rho (fun t => W (strictEventIndex rho t)) Hs q := by
      simp only [Restated.seedRootReadCandidatesOn, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_image, (scs% mem_seedSlotRange)]
      exact Or.inr (Or.inr ⟨_, hpropP, rfl⟩)
    rw [tickStore_fgRoot₆₂ facts]
    exact hRoots _ hmem

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committee majority and the weight bound, if the boundary
    slot's confirmation instant is in the horizon, the boundary cone of round `q + 1` holds at `C`
    with frontier `Mh`, the next-round regime holds for `Mh` and `q`, `lo ≤ S.a q`,
    `lo ≤ vote_time (opening_slot (q + 1) − 1)`, and every member of the set for `S.a q + Δ` is
    awake at `q`, then the round ceiling holds at round `q + 1` for `C`. -/
theorem roundCeiling_of_boundaryConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (hboundaryConfirmationInHorizon :
      M.confirmation_time S.E
        ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon)
    (hcone : Restated.RoundCeilingBoundaryConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb Mh q C)
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh (q + 1) C := by
  have hnext :=
    Restated.roundCeilingStepResidual_of_boundaryConeOn facts S Hs Xb hf hHs hHsXb hcom hfb hcone
      hreg hloAction hlo hA
  have hreadSupport := Restated.roundCeiling_readSupport_of_inputsOn facts S
    (Wt := fun t => W (strictEventIndex rho t)) Hs
    (q := q + 1) (C := C.erase) (Nat.succ_pos q)
      hnext.openingStepInputs hnext.roundInputs hnext.actionActive
      hnext.proposerActive
  exact
    { roundPositive := Nat.succ_pos q
      run := hcone.run
      boundaryThinHead := hcone.boundaryThinHead
      aboveRoot := hreadSupport.1
      active := hreadSupport.2
      postPreviousVote := hcone.postBoundaryVote
      previousConfirmationInHorizon := hboundaryConfirmationInHorizon
      postOpeningProposal := hnext.postOpeningProposal
      postOpeningVote := hnext.postOpeningProposal.trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _))
      roundConfirmationInHorizon := hnext.roundConfirmationInHorizon
      lastVotes := hcone.boundaryVotes
      openingStepInputs := hnext.openingStepInputs
      roundInputs := hnext.roundInputs
      voteActive := hnext.voteActive
      actionActive := hnext.actionActive
      voteAnchor := hnext.voteAnchor
      confirmationAnchor := hnext.confirmationAnchor
      actionAnchor := hnext.actionAnchor
      proposerAnchorCeiling := hnext.proposerAnchorCeiling
      proposerActive := hnext.proposerActive
      previousCarriers := hcone.previousCarriers
      gateOff := hnext.gateOff
      genuineRun := hnext.genuineRun }

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committee majority and the weight bound, with
    `s0 = opening_slot (q + 1) − 1` and the timing hypotheses of the signature, if `C` and `Wb` are
    run blocks along `W` with `C` an ancestor of `Wb` and `Wb` of height at least `Mh − 1`, every
    action block of round `q` of the set for `S.a q` is an ancestor of `C`, the committee of `s0`
    voted descendants of `C`, every head voted at `s0` by a committee member of the set for
    `vote_time s0` has height at least `Mh − 1`, the next-round regime holds, and every member of
    the set for `S.a q + Δ` is awake at `q`, then some `B` descending from `C` has the round ceiling
    at round `q + 1`. -/
theorem roundCeiling_base_of_carrierFrontierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {C Wb : NamedBlock V}
    (hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hpostBoundaryVote : S.E.t_GST ≤
      M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (hboundaryConfirmationInHorizon :
      M.confirmation_time S.E
        ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon)
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hWrun : Restated.RunBlockOn M S rho W Xb Wb)
    (hCW : Block.Preceq C.erase Wb.erase)
    (hWthin : Mh - 1 ≤
      (M.derive_named S.E S.cfg Wb).h)
    (hcarriers : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C.erase)
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb
      ((M.opening_slot S.hc (q + 1)) - 1)
      (fun X => Block.Preceq C.erase X))
    (hheadThin : ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W
        (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
        ((M.opening_slot S.hc (q + 1)) - 1) X →
        Mh - 1 ≤ (M.derive_named S.E S.cfg X).h)
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    ∃ B : NamedBlock V,
      Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh (q + 1) B ∧
        Block.Preceq C.erase B.erase := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  obtain ⟨R, hRrun, hCR, hrootOrder, hRbelow⟩ :=
    Restated.exists_roundCeilingRebaseOn facts S Hs Xb hf hHs hHsXb hsb hreg hCrun hWrun hWthin hCW
  have hvotesR : Restated.NamedHonestVotesConeOn M S rho W Hs Xb
      ((M.opening_slot S.hc (q + 1)) - 1)
      (fun X => Block.Preceq R.erase X) := by
    intro w hw hwcommittee
    obtain ⟨X, hCX, hXrun, hXemit⟩ := hcone w hw hwcommittee
    exact ⟨X,
      hRbelow X hXrun
        (hheadThin X ⟨w, hw, hwcommittee, hXrun, hXemit⟩) hCX,
      hXrun, hXemit⟩
  have hthinHead : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh
      ((M.opening_slot S.hc (q + 1)) - 1) R.erase := by
    have hpositive : 0 < ((S.E.committee
        ((M.opening_slot S.hc (q + 1)) - 1)) ∩
          Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1))).card := by
      have hc := hcom ((M.opening_slot S.hc (q + 1)) - 1)
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
    have hwCommittee : w ∈ S.E.committee
        ((M.opening_slot S.hc (q + 1)) - 1) :=
      (Finset.mem_inter.mp hw).1
    have hwConf : w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) :=
      (Finset.mem_inter.mp hw).2
    have hwVote : w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hwConf
    obtain ⟨X, hRX, hXrun, hXemit⟩ :=
      hvotesR w hwVote hwCommittee
    exact ⟨X, ⟨w, hwConf, hwCommittee, hXrun, hXemit⟩, hRX,
      hheadThin X ⟨w, hwVote, hwCommittee, hXrun, hXemit⟩⟩
  refine ⟨R, Restated.roundCeiling_of_boundaryConeOn facts S Hs Xb hf hHs hHsXb hcom hfb
    hboundaryConfirmationInHorizon
    { run := hRrun
      boundaryThinHead := hthinHead
      postAction := hpostAction
      postBoundaryVote := hpostBoundaryVote
      boundaryVotes := hvotesR
      previousCarriers := fun v hv n hn g hg B hB =>
        preceq_trans_Preceq (hcarriers v hv n hn g hg B hB) hCR
      rootOrder := hrootOrder } hreg hloAction hlo hA, hCR⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `RoundCeilingAtOn` holds at `q` for `C`, `d` is a slot of
    round `q`, `w` is a committee member of `d` in the set for `vote_time d` that emitted at
    `vote_time d` the vote naming the run block `X`, `lo ≤ vote_time (opening_slot q − 1)`, and
    `hrun` holds, then `X` has height at least `Mh − 1`. -/
theorem roundCeiling_headThin_atVote_l62 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    {d : Slot} (hdlo : (M.opening_slot S.hc q) ≤ d)
    (hdhi : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)
    {X : NamedBlock V}
    (hX : Restated.NamedHonestHeadOn M S rho W (fun _ => Hs (M.vote_time S.E d)) Xb d X)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    Mh - 1 ≤ (M.derive_named S.E S.cfg X).h := by
  obtain ⟨w, hw, hwCommittee, hXrun, hXemit⟩ := hX
  have hdpos : 0 < d := lt_of_lt_of_le (facts.gr.openingSlot_pos_l58 S h.roundPositive) hdlo
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)
  have hlastPred : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 + 1 = Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hvoteHor : M.vote_time S.E d ≤ rho.horizon :=
    Restated.roundCeiling_voteInHorizonOn facts S Hs Xb h hdhi
  have hloPred : lo ≤ M.vote_time S.E (d - 1) :=
    hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le_sub_right hdlo 1))
  have hloVote : lo ≤ M.vote_time S.E d :=
    hloPred.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le d 1))
  have hfreezeVote : M.view_freeze S.E (d - 1) ≤ M.vote_time S.E d := by
    have hlt := facts.sch.view_freeze_lt_vote_time_succ S.E (d - 1)
    rw [hpred] at hlt
    exact le_of_lt hlt
  have hwFreeze : w ∈ Hs (M.view_freeze S.E (d - 1)) := hHs _ _ hfreezeVote hw
  have hloFreeze : lo ≤ M.view_freeze S.E (d - 1) :=
    hloPred.trans (Restated.vote_time_le_view_freeze_l58 facts S.E (d - 1))
  have hfrontier := h.gateOff.voteFrontier d hdlo
    (by simpa only [hlastPred] using hdhi) w hw
  obtain ⟨c, hc, -, -⟩ := exists_read_of_world₆₂ facts S
    (W (strictEventIndex rho (M.vote_time S.E d)) w) (M.vote_time S.E d)
  have hin := Restated.roundCeiling_voteInputsOn facts S Hs Xb h hdlo hdhi hw c hc
  have hanc := h.voteAnchor d hdlo hdhi w hw c hc
  have hYemit := Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw hdpos hwCommittee hvoteHor
    hloVote c hc (hrun w hwCommittee hw)
  rw [← hpred] at hc hin hanc hYemit hfrontier
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d - 1 + 1))) w).st
    (M.vote_time S.E (d - 1 + 1))) (W (strictEventIndex rho (M.vote_time S.E (d - 1 + 1))) w).record c
    with hn
  obtain ⟨T, L, L', H, hT, hL, hL', hH⟩ := voterHead_outcome₆₂ facts S n
  obtain ⟨A, hA⟩ := nodeAnchor_outcome₆₂ facts S n (M.round_of S.hc n.st.core.s)
  have hrootEq : X.erase.root = H.root :=
    congrArg GoldfishVote.head
      (Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit (hYemit T hT L hL L' hL' H hH)
        (by simp only [hpred]))
  obtain ⟨Hn, hHerase, hHrun, hfloor⟩ :=
    Restated.voteDutyHead_height_ge_frontier_sub_one_of_candidateOn facts
      S Hs Xb hf hHsXb hwFreeze c hc ⟨hin.candidate, hin.root, hin.anchor, hin.path⟩ A hA
      (hanc A hA) hloFreeze T hT L hL L' hL' H hH
  have hrootNamed : X.root = Hn.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root Hn, hHerase]
    exact hrootEq
  have hXH : X = Hn :=
    hf.rootCollisionFree.root_injective
      X Hn hXrun hHrun X Hn (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self Hn)) hrootNamed
  rw [hXH]
  rw [hfrontier] at hfloor
  exact hfloor

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committee majority and the weight bound, if the round
    ceiling holds at `q` for `C`, the next-round regime holds for `Mh` and `q`,
    `lo ≤ vote_time (opening_slot q − 1)`, `lo ≤ opening (q − η_SG)`, and every member of the set
    for `S.a q + Δ` is awake at `q`, then some `B` descending from `C` has the round ceiling at
    `q + 1`, and the live confirmed block of every node state of every member's round-`q` action
    read along `W` is an ancestor of `B`. -/
theorem roundCeiling_step_or_rebaseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    ∃ B : NamedBlock V,
      Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh (q + 1) B ∧
      Block.Preceq C.erase B.erase ∧
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
        Block.Preceq n.live_confirmed B.erase := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hrunQ : ∀ d : Slot, (M.opening_slot S.hc q) ≤ d →
      d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
      ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d) := by
    intro d hdlo hdhi w _ hw j hj
    have hround : M.round_of S.hc d = q := by
      rcases Nat.eq_or_lt_of_le hdlo with hd | hd
      · rw [← hd]
        exact facts.gr.round_of_opening_slot_eq S.hc q
      · have hdhi' : d ≤ M.opening_slot S.hc (q + 1) - 1 := hdhi
        have hlt : d < M.opening_slot S.hc (q + 1) :=
          (Nat.le_sub_one_iff_lt (facts.gr.openingSlot_pos_l58 S (Nat.succ_pos q))).1 hdhi'
        exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hd hlt
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
      rw [hround]
      have h1 := facts.gr.lo_le_early_g2_of_window_start S h.roundPositive hloOpen
      have h2 := facts.gr.early_g2_add_delta_le_early_g1 S q
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  have hopenLastQ' : (M.opening_slot S.hc q) ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.le_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)
  have hrunLast := hrunQ _ hopenLastQ' le_rfl
  obtain ⟨Cstar, hrun, hold, houtputs, hsource⟩ :=
    exists_frontier_all₆₂ facts S Hs Xb hf hHs hHsXb hcom h hlo (hrunQ _ le_rfl hopenLastQ')
  have hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B Cstar.erase := fun v hv n hn =>
    actionSG_preceq_of_live₆₂ facts S Hs Xb hf hHs hHsXb h hloOpen hold hv n hn
      (houtputs v hv n hn)
  have hopenLastQ : (M.opening_slot S.hc q) ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.le_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)
  have hpostBoundary : S.E.t_GST ≤
      M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1) := by
    have hpostLast : S.E.t_GST ≤
        M.vote_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q) :=
      h.postOpeningVote.trans (Restated.vote_time_mono_l58 facts S.E hopenLastQ)
    simpa only [Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot] using hpostLast
  have hloBoundary : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1) := by
    have hloLast : lo ≤ M.vote_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q) :=
      hlo.trans (Restated.vote_time_mono_l58 facts S.E ((Nat.sub_le _ 1).trans hopenLastQ))
    simpa only [Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot] using hloLast
  have hlastVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)
      (fun X => Block.Preceq Cstar.erase X) := by
    rcases hsource with heq | ⟨v, hv, c, hc, hgen⟩
    · rw [heq]
      exact Restated.roundCeiling_votesThroughOn facts S Hs Xb hf hHs hHsXb hcom h hlo hrunQ
        (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q) hopenLastQ (le_refl _)
    · exact (Restated.roundCeiling_persistenceOn facts S Hs Xb hf hHs hHsXb hcom hsb h hv c hc hgen
        hlo hrunQ).1
        (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)
        (Nat.succ_le_iff.mpr (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)) (le_refl _)
  have hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    exact (h.postOpeningVote.trans
        (facts.sch.Protocol_vote_time_le_confirmation_time S.E
          ((M.opening_slot S.hc q)))).trans (Restated.confirmation_time_opening_slot facts S q).le
  have hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S q]
    exact (hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le _ 1))).trans
      (facts.sch.Protocol_vote_time_le_confirmation_time S.E _)
  obtain ⟨X0, hX0honest, hCstarX0, hX0thin⟩ :=
    Restated.roundCeiling_thinHead_of_coneOn facts S Hs Xb hf hHs hHsXb hcom h hopenLastQ
      (le_refl _) hlastVotes hlo hrunLast
  have hX0run : Restated.RunBlockOn M S rho W Xb X0 := by
    obtain ⟨-, -, -, hrunX0, -⟩ := hX0honest
    exact hrunX0
  obtain ⟨R, hRrun, hCstarR, hRoots, hRbelow⟩ :=
    Restated.exists_roundCeilingRebaseOn facts S Hs Xb hf hHs hHsXb hsb hreg hrun hX0run hX0thin hCstarX0
  have hlastVotesR : Restated.NamedHonestVotesConeOn M S rho W Hs Xb
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)
      (fun X => Block.Preceq R.erase X) := by
    intro w hw hwcommittee
    obtain ⟨X, hCstarX, hXrun, hXemit⟩ := hlastVotes w hw hwcommittee
    exact ⟨X,
      hRbelow X hXrun
        (Restated.roundCeiling_headThin_atVote_l62 facts S Hs Xb hf hHs hHsXb h hopenLastQ
          (le_refl _) ⟨w, hw, hwcommittee, hXrun, hXemit⟩ hlo hrunLast) hCstarX,
      hXrun, hXemit⟩
  have hboundaryThinR : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh
      ((M.opening_slot S.hc (q + 1)) - 1) R.erase := by
    have hthinHead := Restated.roundCeiling_thinHead_of_coneOn facts S Hs Xb hf hHs hHsXb hcom h
      hopenLastQ (le_refl _) hlastVotesR hlo hrunLast
    simpa only [Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot] using hthinHead
  have hrootOrder : Restated.RoundCeilingNextRootOrderAtOn M S rho (fun t => W (strictEventIndex rho t))
      Hs q R.erase := hRoots
  have hboundaryHor : M.confirmation_time S.E
      ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E
      ((Nat.sub_le _ 1).trans
        (Restated.openingSlot_le_seedRoundLastSlot_pred_l58 facts S (q + 1)))).trans
      hreg.roundConfirmationInHorizon
  refine ⟨R, Restated.roundCeiling_of_boundaryConeOn facts S Hs Xb hf hHs hHsXb hcom hfb
    hboundaryHor
    { run := hRrun
      boundaryThinHead := hboundaryThinR
      postAction := hpostAction
      postBoundaryVote := hpostBoundary
      boundaryVotes := by simpa only [Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot] using hlastVotesR
      previousCarriers := fun v hv n hn g hg B hB =>
        preceq_trans_Preceq (hupper v hv n hn g hg B hB) hCstarR
      rootOrder := hrootOrder } hreg hloAction hloBoundary hA, ?_, ?_⟩
  · exact preceq_trans_Preceq hold hCstarR
  · intro v hv n hn
    exact preceq_trans_Preceq (houtputs v hv n hn) hCstarR

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committee majority and the weight bound, if the round
    ceiling holds at `base` for `C`, the next-round regime holds for `Mh` at every round from `base`
    to before `last`, `lo ≤ vote_time (opening_slot base − 1)`, `lo ≤ opening (base − η_SG)`, and
    every member of the set for `S.a k + Δ` is awake at `k` for every round `k`, then at every round
    from `base` to `last` some `B` descending from `C` has the round ceiling. -/
theorem roundCeiling_through_or_rebaseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {base last : Round} {C : NamedBlock V}
    (hbase : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh base C)
    (hregime : ∀ k : Round, base ≤ k → k < last →
      Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh k)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc base) - 1))
    (hloOpen : lo ≤ M.opening S.E S.hc (base - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ k : Round, base ≤ k → k ≤ last →
      ∃ B : NamedBlock V,
        Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh k B ∧
        Block.Preceq C.erase B.erase := by
  intro k hklo
  induction k, hklo using Nat.le_induction with
  | base =>
      intro _
      exact ⟨C, hbase, (preceq_eq_true_iff_Preceq.mp (Block.preceq_self C.erase))⟩
  | succ k hklo ih =>
      intro hsuccLast
      have hkLast : k ≤ last := (Nat.le_succ k).trans hsuccLast
      obtain ⟨B, hB, hCB⟩ := ih hkLast
      have hklt : k < last :=
        lt_of_lt_of_le (Nat.lt_succ_self k) hsuccLast
      have hloK : lo ≤ M.vote_time S.E ((M.opening_slot S.hc k) - 1) :=
        hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le_sub_right
          (facts.gr.opening_slot_le_of_le S.hc hklo) 1))
      have hloOpenK : lo ≤ M.opening S.E S.hc (k - S.hc.η_SG) := by
        rw [facts.gr.opening_eq_proposal_time] at hloOpen ⊢
        exact hloOpen.trans (facts.sch.proposal_time_mono S.E
          (facts.gr.opening_slot_le_of_le S.hc (Nat.sub_le_sub_right hklo S.hc.η_SG)))
      obtain ⟨Bnext, hBnext, hBBnext, -⟩ :=
        Restated.roundCeiling_step_or_rebaseOn facts S Hs Xb hf hHs hHsXb hcom hfb hB
          (hregime k hklo hklt) hloK hloOpenK
          (hA k (Restated.lo_le_early_g2_sub_delta_of_opening facts S hB.roundPositive hloOpenK le_rfl))
      exact ⟨Bnext, hBnext, preceq_trans_Preceq hCB hBBnext⟩

end

/-! ### Helpers for the opening proposal and the action reads -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₂s (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₂s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₂s S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₂s {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₆₂s {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₂s W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W` of a run, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an
    ancestor of the one in `W n`. -/
private theorem F_mono_along₆₂s (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₆₂s W hW hjn)

/-- On a path `W` of a run sorted by key, the finalized block of `v`'s core store in
    `W (strictEventIndex rho t)` is an ancestor of that store's finality root. -/
private theorem F_preceq_fgRoot_along₆₂s (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (t : Time) :
    Block.Preceq (W (strictEventIndex rho t) v).st.core.F
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho t) v).st.core).toFG) := by
  have hFroot := facts.fc.preceq_get_fg_root_of_F
    (st := (M.toHealing (W (strictEventIndex rho t) v).st.core).toFG)
    (by
      rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
      exact preceq_eq_true_iff_Preceq.mpr
        (Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
          S rho t v _ (mem_stateBeforeTime_along₆₂s hsorted hW t)))
  rw [facts.sto.Sts_toHealing_F] at hFroot
  exact preceq_eq_true_iff_Preceq.mp hFroot

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₆₂s (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The store `tickStore` stages from `n`'s core store has the FG root of `n`'s core store. -/
private theorem tickStore_fgRoot₆₂s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_fg_root (M.toHealing n.st.core).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store `tickStore` stages from `n`'s core store has the filtered block tree of `n`'s core
    store. -/
private theorem tickStore_filtered₆₂s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_filtered_block_tree
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
  facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- On a path `W` of a run sorted by key, the node state staged at `t` from `v`'s node state in
    `W (strictEventIndex rho t)` with an outcome of the cache update there is one of `v`'s prepared
    reads at `t`. -/
private theorem mkNode_mem_confirmationReadAt₆₂s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (t : Time) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) v).st.core.toHealing t
      (W (strictEventIndex rho t) v).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) v).st t)
        (W (strictEventIndex rho t) v).record c ∈
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v t :=
  ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₆₂s hsorted hW t, c, hc, rfl⟩

/-- On a path `W` of a run sorted by key, a node state of `v`'s round-`r` action read from its node
    state in `W (strictEventIndex rho (S.a r))` is one of `v`'s round-`r` action reads. -/
private theorem mem_actionReadAt_along₆₂s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (r : Round) {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r) :
    n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
  ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)),
    mem_stateBeforeTime_along₆₂s hsorted hW _, hn⟩

/-- Every node state of the round-`r` action read computed from `before` has as core store an
    outcome of the confirmation update of `before`'s store staged at round `r`'s action instant. -/
private theorem actionReadFrom_core₆₂s (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state of the round-`r` action read computed from `before` has the FG root of
    `before`'s core store. -/
private theorem actionReadFrom_fgRoot₆₂s (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₂s facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- When `before` is a node state a run reaches (`hb`), every node state of the round-`r` action
    read computed from `before` has the grade view of `before`'s core store. -/
private theorem actionReadFrom_gradeView₆₂s (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
    ∀ (hb : M.reachedNode before),
      M.gradeView (M.toHealing n.st.core) = M.gradeView (M.toHealing before.st.core) := by
  intro n hn hb
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₂s facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_gradeView,
    facts.dt.update_confirmation_with_toHealing_gradeView _ _ _ _ _ _
    hX₀ (facts.nd.reachedCore_of_store _ (facts.sto.reachedStore_setClock S.E _ _
      (facts.nd.reachedStore_of_node _ hb))), facts.hd.setClock_gradeView]

/-- Every node state of the round-`r` action read computed from `before` has the finalized block of
    `before`'s core store. -/
private theorem actionReadFrom_F₆₂s (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.F = before.st.core.F := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₂s facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_F,
    facts.dt.update_confirmation_with_F _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_F]

/-- Every node state of the round-`r` action read computed from `before` holds the bodies `before`
    holds. -/
private theorem actionReadFrom_bodies₆₂s (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

omit [DecidableEq V] [Fintype V] in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₂s {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- The round-`r` action read computed from any node state `before` has a node state. -/
private theorem actionReadFrom_nonempty₆₂s (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- On a path `W` of a run sorted by key, if `P` is a proposal slot `s`'s proposer's duty can return
    at its read with the cache `c`, then some proposal input at that read has its parent among the
    proposed parents of `s`, and that parent is an ancestor of `P`'s block. -/
private theorem proposalParent₆₂s (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (s : Slot)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P) :
    ∃ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer s))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core) ⇢ I ∧
      I.parent ∈ Restated.Vocabulary.Proofs.HealingSurface.proposedParent M S rho s ∧
      Block.Preceq I.parent P.erase := by
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node (S.E.proposer s))
    (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core)
  have hI' : M.with_proposal_input (M.gradeContract c) S.E S.hc (S.node (S.E.proposer s))
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s)) c).core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  obtain ⟨par, hpar, hparE⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ P _
    (by rw [facts.dt.proposal_with_store_with_cache]; exact hP) rfl I hI'
  have hparentEq : P.erase.parent = I.parent := by
    rw [Proofs.NamedWire.erase_parent]
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hpar
    | node q' _ _ _ _ _ _ =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hpar
      subst hpar
      rw [Proofs.ModelProperties.named_parent_node]
      exact hparE
  refine ⟨I, hI, ⟨I, ⟨_, mkNode_mem_confirmationReadAt₆₂s hsorted hW (S.E.proposer s)
      (M.proposal_time S.E s) c hc, by rw [facts.nd.mkNode_cache]; exact hI⟩, rfl⟩, ?_⟩
  rw [← hparentEq]
  exact preceq_eq_true_iff_Preceq.1 (Proofs.preceq_parent P.erase)

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

/-- Under the bundle with path `W`, if `hrun` holds, `w`'s store in `W (strictEventIndex rho read)`
    is a fixed-height justification root at `H`, `A` is a descendant of its justified block and an
    ancestor of the parent of every proposal input at the opening proposer's read with the cache
    `c`, `B` is a proposal that proposer can return there, `q > 0`, `lo ≤ read`, `read + Δ` is at
    most the opening slot's confirmation instant, which is in the horizon, no `h_max` over the set
    for that instant exceeds `H`, `lo ≤ tp`, and the proposer is in that set, then every member of
    that set accepts `B` before the opening slot's vote instant. -/
theorem openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} {A : Block V} {B : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some B)
    (hq : 0 < q)
    (hpostRead : lo ≤ read)
    (hdelay : read + S.E.Δ ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)))
    (hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤
      rho.horizon)
    (hcap : ((Hs (M.confirmation_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H)
    (hpostProposal : lo ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposer : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hJA : Block.Preceq (W (strictEventIndex rho read) w).st.J A)
    (hAparent : ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      Block.Preceq A I.parent)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
      Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v B.erase
        (M.vote_time S.E ((M.opening_slot S.hc q))) := by
  set s := M.opening_slot S.hc q with hs_def
  set p := S.E.proposer s with hp_def
  set tp := M.proposal_time S.E s with htp_def
  set J := (W (strictEventIndex rho read) w).st.J with hJ_def
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc (S.node p)
    (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
      (W (strictEventIndex rho tp) p).record c).st.core)
  have hAI : Block.Preceq A I.parent := hAparent I hI
  have hI' : M.with_proposal_input (M.gradeContract c) S.E S.hc (S.node p)
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp) c).core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  obtain ⟨par, hpar, hparE⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ B _
    (by rw [facts.dt.proposal_with_store_with_cache]; exact hB) rfl I hI'
  have hparentEq : B.erase.parent = I.parent := by
    rw [Proofs.NamedWire.erase_parent]
    cases B with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hpar
    | node q' _ _ _ _ _ _ =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hpar
      subst hpar
      rw [Proofs.ModelProperties.named_parent_node]
      exact hparE
  have hparentB : Block.Preceq I.parent B.erase := by
    rw [← hparentEq]
    exact preceq_eq_true_iff_Preceq.1 (Proofs.preceq_parent B.erase)
  have hJB : Block.Preceq J B.erase :=
    preceq_trans_Preceq hJA (preceq_trans_Preceq hAI hparentB)
  have hroot : ∀ v ∈ Hs (M.confirmation_time S.E s),
      M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core).toFG
        = J := by
    intro v hv
    exact (Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
      facts S Hs Xb hf hHs hHsXb hsb hfix hv hpostRead hdelay hconfHor hcap).1
  have hFconf : ∀ v ∈ Hs (M.confirmation_time S.E s),
      Block.Preceq (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.F B.erase := by
    intro v hv
    have h := F_preceq_fgRoot_along₆₂s facts S hf.sorted hf.onePath v (M.confirmation_time S.E s)
    rw [hroot v hv] at h
    exact preceq_trans_Preceq h hJB
  have hs : 0 < s := facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hvoteConf : M.vote_time S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E s
  have hvoteHor : M.vote_time S.E s ≤ rho.horizon := hvoteConf.trans hconfHor
  have hproposalVote : tp + S.E.Δ = M.vote_time S.E s :=
    (facts.sch.slot_instants_l55 S.E s).1.symm
  have hproposalLeVote : tp ≤ M.vote_time S.E s :=
    le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)
  have hproposalConf : tp ≤ M.confirmation_time S.E s := hproposalLeVote.trans hvoteConf
  have hproposalHor : tp ≤ rho.horizon := hproposalLeVote.trans hvoteHor
  have hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p tp) →
      ∃ out : M.N × List (NamedObject V), M.tick S p (W j p) tp ⇢ out :=
    fun j hj => hf.tick_outcome j _ _ hj
  obtain ⟨B0, hB0, hB0slot, hemit0⟩ :=
    Restated.proposedBlockAt_emits_of_honestOn facts S Hs Xb hf hHs s hs hproposer hproposalHor
      hpostProposal hneTick hrun c hc (some B) hB
  cases hB0
  have hBslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact hB0slot
  have hBpos : 0 < B.slot := by
    rw [hB0slot]
    exact hs
  obtain ⟨i0, hacc0⟩ := Restated.acceptsAt_proposedBlockOn facts S Hs Xb hf hHs hs hproposer
    hproposalHor hpostProposal hneTick hrun c hc hB
  intro v hv
  have hdeadline : tp + S.E.Δ ≤ rho.horizon := by
    rw [hproposalVote]
    exact hvoteHor
  have hguard : ∀ B' : NamedBlock V, Object.block B = .block B' →
      Block.compatible (W (strictEventIndex rho (tp + S.E.Δ)) v).st.core.F B'.erase = true := by
    intro B' hB'
    cases hB'
    rw [hproposalVote]
    exact compatible_of_cases (Or.inl (preceq_trans_Preceq
      (Restated.fixedRoot_strict_finality_monoOn facts S Hs Xb hf v hvoteConf) (hFconf v hv)))
  have hpropP : p ∈ Hs tp := hHs _ _ hproposalConf hproposer
  have hvRecv : v ∈ Hs (tp + S.E.Δ) := by
    rw [hproposalVote]
    exact hHs _ _ hvoteConf hv
  obtain ⟨t, hlo, hhi, j, hcall⟩ :=
    hf.broadcast p _ _ hpropP hemit0 v hvRecv hpostProposal hdeadline hguard
  have hbeforeVote : t < M.vote_time S.E s := by
    rw [← hproposalVote]
    exact hhi
  obtain ⟨e, hej, -, heTime⟩ := hcall.2
  have hjBound : j + 1 ≤ strictEventIndex rho (M.vote_time S.E s) :=
    index_succ_le_strict_filter_length rho hf.sorted (M.vote_time S.E s) hej
      (by rw [heTime]; exact hbeforeVote)
  have hFj : Block.Preceq (W j v).st.core.F B.erase :=
    preceq_trans_Preceq
      (F_mono_along₆₂s facts S hf.onePath v
        ((Nat.le_succ j).trans (hjBound.trans (strict_filter_length_mono rho hvoteConf))))
      (hFconf v hv)
  have hvProp : v ∈ Hs (M.proposal_time S.E B.erase.slot) := by
    rw [hBslot]
    exact hHs _ _ hproposalConf hv
  have hheld := Restated.handled_block_held_of_finalized_prefixOn facts S rho Hs Xb hf hHsXb
    (hHsXb _ hpropP) hvProp (Or.inr (by rw [hBslot]; exact hpostProposal)) hacc0 hcall hlo hFj
  obtain ⟨j', t', hacc', ht'⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.acceptsAt_before_of_processed_after_event facts S rho
      hf.sorted (w := v) hBpos hej (by rw [heTime]; exact hbeforeVote) W hf.onePath
      (by simp only [Restated.Vocabulary.Execution.Object.processed]; exact decide_eq_true hheld)
  exact ⟨B, rfl, j', t', hacc', ht'⟩

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

/-- Under the hypotheses of `openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRiseOn`
    other than `hrun`, for the proposal `P`, the weight bound, `lo ≤ S.a (q − 1)`, the fixed-height
    opening parent run at `q`, and every member of the set for `S.a (q − 1) + Δ` awake at `q − 1`:
    for every member `v` of the set for the opening slot's confirmation instant and every node state
    `n` staged there with an outcome of `v`'s cache update, the FG root of `n`'s store and every SG
    root of `n` at its slot's round are ancestors of `P`'s block, and `P`'s block is in `n`'s
    filtered tree. -/
theorem sgOpeningConfirmationReads_of_fixedJustificationRootNoRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} {A : Block V} {P : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P)
    (hq : 0 < q)
    (hpostRead : lo ≤ read)
    (hdelay : read + S.E.Δ ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)))
    (hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤
      rho.horizon)
    (hcap : ((Hs (M.confirmation_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H)
    (hpostProposal : lo ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hproposer : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hJA : Block.Preceq (W (strictEventIndex rho read) w).st.J A)
    (hAparent : ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      Block.Preceq A I.parent)
    (hparents : Restated.FixedHeightRootOpeningParentRunOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs q)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
    ∀ c' : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
        (M.confirmation_time S.E (M.opening_slot S.hc q))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c' →
      let n := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st
        (M.confirmation_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).record c'
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) P.erase ∧
        (∀ a : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc n.st.core.s) ⇢ a →
          Block.Preceq a P.erase) ∧
        P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
  set s := M.opening_slot S.hc q with hs_def
  set p := S.E.proposer s with hp_def
  set tp := M.proposal_time S.E s with htp_def
  set J := (W (strictEventIndex rho read) w).st.J with hJ_def
  have hqOne : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc (S.node p)
    (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
      (W (strictEventIndex rho tp) p).record c).st.core)
  have hAI : Block.Preceq A I.parent := hAparent I hI
  have hI' : M.with_proposal_input (M.gradeContract c) S.E S.hc (S.node p)
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp) c).core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  obtain ⟨par, hpar, hparE⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ P _
    (by rw [facts.dt.proposal_with_store_with_cache]; exact hP) rfl I hI'
  have hparentEq : P.erase.parent = I.parent := by
    rw [Proofs.NamedWire.erase_parent]
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hpar
    | node q' _ _ _ _ _ _ =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hpar
      subst hpar
      rw [Proofs.ModelProperties.named_parent_node]
      exact hparE
  have hparentP : Block.Preceq I.parent P.erase := by
    rw [← hparentEq]
    exact preceq_eq_true_iff_Preceq.1 (Proofs.preceq_parent P.erase)
  have hJparent : Block.Preceq J I.parent := preceq_trans_Preceq hJA hAI
  have hJP : Block.Preceq J P.erase := preceq_trans_Preceq hJparent hparentP
  have hspos : 0 < s := facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hproposalHor : tp ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E s).trans hconfHor
  have hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p tp) →
      ∃ out : M.N × List (NamedObject V), M.tick S p (W j p) tp ⇢ out :=
    fun j hj => hf.tick_outcome j _ _ hj
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p tp) →
      M.awake_for_grade1 S p (W j p) (M.round_of S.hc s) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ := by
      rw [hs_def, facts.gr.round_of_opening_slot_eq S.hc q]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hq Nat.one_pos)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q
      have h3 : lo ≤ M.a S.hc S.E.Δ (q - 1) := hpostPreviousAction
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E s) hproposer) hwin
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      s hspos hproposer hproposalHor hpostProposal hneTick hrunP c hc hP
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.fixedRoot_namedTarget_of_fixedRootOn facts S Hs Xb hfix
  obtain ⟨Jp, hJpP, hJpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift P hJP
  have hJpRun : Restated.RunBlockOn M S rho W Xb Jp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hPrun hJpP
  have hrootEq : Jp.root = Jn.root := by
    rw [← Proofs.NamedWire.erase_root Jp, ← Proofs.NamedWire.erase_root Jn,
      hJpErase, hJnErase]
  have hJpEq : Jp = Jn :=
    hf.rootCollisionFree.root_injective
      Jp Jn hJpRun hJnRun Jp Jn
      (Or.inl (Proofs.NamedAncestry.named_self Jp))
      (Or.inr (Proofs.NamedAncestry.named_self Jn)) hrootEq
  have hPheight : H - 1 ≤
      (M.derive_named S.E S.cfg P).h := by
    rw [← hJnHeight, ← hJpEq]
    exact facts.cs.derive_height_mono S.E S.cfg hJpP
  have hconfAction : M.confirmation_time S.E s = Restated.Vocabulary.Execution.Setup.a M S q :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S q
  have hcutQ : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q - 1 + 1) ≤
      rho.horizon := by
    refine (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S
      (q - 1))).trans ?_
    rw [Nat.sub_add_cancel hqOne, ← hconfAction]
    exact hconfHor
  have hround : (M.round_of S.hc (s + 1)) = (q - 1) + 1 := by
    rw [Nat.sub_add_cancel hqOne]
    exact facts.gr.HealingLemmas_round_of_opening_succ S.hc q
  have hupper : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B I.parent := by
    intro u hu n hn g hg B hB
    exact hparents.actionTargetParent u hu n hn g hg B hB c hc I hI
  intro v hv c' hc'
  have hrootMax :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hv hpostRead hdelay hconfHor hcap
  have hadmit :=
    openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRiseOn facts
      S Hs Xb hf hHs hHsXb hfix c hc hP hq hpostRead hdelay hconfHor hcap hpostProposal
        hproposer hJA hAparent hrunP v hv
  have hPtree := (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit
      (facts.sch.Protocol_vote_time_le_confirmation_time S.E s)).1
  have hcandidateRaw :=
    Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts S Hs Xb hf (hHsXb _ hv) hPrun hPtree
      hJP hPheight hrootMax.1 hrootMax.2
  have hrootW : M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core).toFG = J := hrootMax.1
  have hrootRead : M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c').st.core).toFG = J := by
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_fg_root, setClock_core_tickStore₆₂s facts S,
      tickStore_fgRoot₆₂s facts]
    exact hrootW
  have hanchor := Restated.confirmationAnchorAt_preceq_of_previousCarriersOn facts
    S Hs Xb hf hHs hHsXb hfb hround hpostPreviousAction hcutQ hconfHor hupper hv
      (by
        show Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s))).toFG) I.parent
        rw [tickStore_fgRoot₆₂s facts, hrootW]
        exact hJparent)
      hA c' hc'
  refine ⟨?_, ?_, ?_⟩
  · rw [hrootRead]
    exact hJP
  · intro a ha
    exact preceq_trans_Preceq (hanchor a ha) hparentP
  · show P.erase ∈ M.get_filtered_block_tree (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c').st.core).toFG
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_filtered_block_tree,
      setClock_core_tickStore₆₂s facts S, tickStore_filtered₆₂s facts]
    exact hcandidateRaw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle with path `W`, if `0 < q`, `w`'s store in `W (strictEventIndex rho read)` is a
    fixed-height justification root at `H`, `lo ≤ read`, `lo ≤ S.a (q − 1)`, `read + Δ` is at most
    `S.a (q − 1)` and at most `S.a q`, both are in the horizon, no `h_max` over the set for either
    instant exceeds `H`, and every member of the set for `S.a (q − 1) + Δ` is awake at `q − 1`, then
    for every reader `v` in the set for `S.a q` and every author `u` in the set for round `q`'s
    early grade-0 cutoff, the SG vote of `u`'s round-`(q − 1)` action attestation is an interpreted
    input of every round-`q` action read of `v` for `u`. -/
theorem previousActionVote_mem_interpretedInputs_actionRead_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} (hq : 0 < q)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    (hpostRead : lo ≤ read)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprevDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprevHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon)
    (hprevCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1))).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) x).st.core.h_max)
        ≤ H)
    (hactionDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hactionCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S q)).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.core.h_max) ≤ H)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)), ∀ u ∈ Hs (M.early S.E S.hc q .g0),
    ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
    ∀ D, M.duties_attest_with (M.gradeContract na.cache) S.E S.hc (S.node u) na.st na.record ⇢ D →
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
    ∀ Y, M.interpretedInputs (M.gradeView (M.toHealing nv.st.core)) nv.st.core.F
        S.hc.η_SG q (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc q) u ⇢ Y →
      M.sgVote D.2.2.erase ∈ Y := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hcut0 : M.late S.E S.hc q .g0 = M.early S.E S.hc q .g0 :=
    facts.gr.allPhasesCutoff_eq_early_g0 S q
  have hprevPkg := fun x (hx : x ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hx hpostRead hprevDelay hprevHor hprevCap
  have hactionPkg := fun x (hx : x ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q)) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hx hpostRead hactionDelay hactionHor hactionCap
  have hqr : q - 1 < q := Nat.sub_lt hq (by decide)
  have hk : q - 1 ∈ M.latest_window S.hc.η_SG q := by
    apply facts.fc.mem_latest_window
    · exact Nat.sub_le_sub_left S.hc.η_SG_ge_one q
    · exact hqr
  have hactionDelta : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤
      M.early S.E S.hc q .g0 := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hqr
    have h2 := facts.gr.early_g2_add_delta_le_early_g1 S q
    have h3 := facts.gr.early_g1_add_delta_le_early_g0 S q
    have hΔ := S.E.Δ_pos
    show M.a S.hc S.E.Δ (q - 1) + S.E.Δ ≤ M.early S.E S.hc q .g0
    linarith
  have hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) lo + S.E.Δ ≤
      M.early S.E S.hc q .g0 := by
    rw [max_eq_left hpost]
    exact hactionDelta
  have hearlyDomain : M.early S.E S.hc q .g0 ≤ M.domain S.E S.hc q .g0 := by
    have h1 := facts.gr.early_add_two_delta_le_domain S q .g0
    linarith [S.E.Δ_pos]
  have horder : M.early S.E S.hc q .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hearlyDomain.trans (facts.gr.domain_le_a S q .g0)
  have hcut : M.early S.E S.hc q .g0 ≤ rho.horizon := horder.trans hactionHor
  intro v hv u huHon na hna D hD nv hnv Y hY
  have huDelta : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ) :=
    hHs _ _ hactionDelta huHon
  have huPrev : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
    hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) huDelta
  have hvEarly : v ∈ Hs (M.early S.E S.hc q .g0) := hHs _ _ horder hv
  set a := D.2.2 with ha
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest a)
      ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf (q - 1) huPrev hprevHor hpost
      (hA u huDelta) (fun j hj => hf.tick_outcome j _ _ hj) na hna D hD
  obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract na.cache) S.E S.hc
    (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s)
  obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract na.cache) S.E S.hc
    (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) g2
  have hshape : a.val_index = u ∧ a.round = q - 1 ∧ a.confirmed = some G.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u (q - 1) na
      (mem_actionReadAt_along₆₂s hf.sorted hf.onePath u (q - 1) hna) D hD g2 hg2 G hG
  obtain ⟨i, hi, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath hemit
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i u) a.round := by
    rw [hshape.2.1]
    rcases Restated.action_read_indexOn facts S rho Hs Xb hf i u (q - 1) hi with hstate | hstate
    · rw [hstate]
      exact hna
    · rw [hstate, actionReadFrom_wake₆₂ facts]
      exact hna
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hna'
  obtain ⟨Wn, hWnBody, hcarrierW, -⟩ :=
    Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf (hprevPkg u huPrev).2 na hna g2 hg2 G hG
  have hcarrierFiltered : G ∈ M.get_filtered_block_tree (M.toHealing na.st.core).toFG :=
    Restated.actionSGBlockAt_mem_filtered_actionStoreOn facts S Hs Xb hf u (q - 1) na hna g2 hg2 G hG
  have hrootCarrier : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.core).toFG) G := by
    have hmem := preceq_eq_true_iff_Preceq.mp
      (facts.fc.preceq_get_fg_root_of_mem_filtered hcarrierFiltered)
    rwa [actionReadFrom_fgRoot₆₂s facts S _ (q - 1) na hna] at hmem
  have hprevRoot : M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.core).toFG =
        (W (strictEventIndex rho read) w).st.J := (hprevPkg u huPrev).1
  have hJcarrier : Block.Preceq (W (strictEventIndex rho read) w).st.J G := by
    rw [← hprevRoot]
    exact hrootCarrier
  have hJW : Block.Preceq (W (strictEventIndex rho read) w).st.J Wn.erase :=
    preceq_trans_Preceq hJcarrier hcarrierW
  have hactionRoot : M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG =
        (W (strictEventIndex rho read) w).st.J := (hactionPkg v hv).1
  have hFC : Block.Preceq
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.F Wn.erase := by
    have h := F_preceq_fgRoot_along₆₂s facts S hf.sorted hf.onePath v
      (Restated.Vocabulary.Execution.Setup.a M S q)
    rw [hactionRoot] at h
    exact preceq_trans_Preceq h hJW
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hbodies := actionReadFrom_bodies₆₂s facts S _ (q - 1) na hna
  have hWnRun : Restated.RunBlockOn M S rho W Xb Wn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hWnBody)
  have hHrun : Restated.RunBlockOn M S rho W Xb Hb :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hHb)
  obtain ⟨Gp, hGpW, hGpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Wn hcarrierW
  have hGpRun : Restated.RunBlockOn M S rho W Xb Gp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hWnRun hGpW
  have hroot : Gp.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root Gp, hGpErase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hGpH : Gp = Hb :=
    hf.rootCollisionFree.root_injective Gp Hb
      hGpRun hHrun Gp Hb (Or.inl (Proofs.NamedAncestry.named_self Gp))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHC : Block.Preceq Hb.erase Wn.erase := by
    rw [← hGpH, hGpErase]
    exact hcarrierW
  have hpostA : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [hshape.2.1]
    exact hpost
  have hdeadlineA : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.early S.E S.hc q .g0 := by
    rw [hshape.2.1]
    exact hdeadline
  have hinput :=
    Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb (t := Restated.Vocabulary.Execution.Setup.a M S q) .g0 hk huHon hvEarly
      ⟨hshape.1, hshape.2.1, hemit⟩
      ⟨i, hi, ⟨na, hna', hHb⟩, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  apply hinput Y
  rw [← actionReadFrom_gradeView₆₂s facts S _ q nv hnv
    (facts.ndRun.stateBeforeOf_reachedNode S rho _ (W _) (hf.onePath _).1 v),
    ← actionReadFrom_F₆₂s facts S _ q nv hnv,
    ← hcut0]
  exact hY

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the hypotheses of `previousActionVote_mem_interpretedInputs_actionRead_of_fixedRootOn`, if
    `P` is a proposal the opening proposer of round `q` can return at its read with the cache `c`,
    and the fixed-height opening parent run holds at `q`, then at every round-`q` action read of
    every member of the set for `S.a q`, the latest interpreted input of every author in that set
    with a resolved head has that head an ancestor of `P`'s block. -/
theorem actionBatchAlignedAt_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} (hq : 0 < q)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    (hpostRead : lo ≤ read)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprevDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprevHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon)
    (hprevCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1))).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) x).st.core.h_max)
        ≤ H)
    (hactionDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hactionCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S q)).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.core.h_max) ≤ H)
    {P : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P)
    (hparents : Restated.FixedHeightRootOpeningParentRunOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs q)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      Restated.Vocabulary.Internal.PhaseGrades.BatchAlignedAt M S.hc
        (M.gradeView (M.toHealing nv.st.core)) nv.st.core.F
        (Hs ((Restated.Vocabulary.Execution.Setup.a M S q))) q
        (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc q) P.erase := by
  obtain ⟨I, hI, -, hIP⟩ := proposalParent₆₂s facts S hf.sorted hf.onePath _ c hc hP
  have hprevAction : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S q) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le q 1)
  have hcarriers : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
        let gc := M.gradeContract n'.cache
        let st := M.toHealing n'.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq G P.erase := by
    intro u hu n' hn' _ _ _ A2 hA2 G hG
    exact preceq_trans_Preceq (hparents.actionTargetParent u (hHs _ _ hprevAction hu) n' hn'
      A2 hA2 G hG c hc I hI) hIP
  have hearlyAction : M.early S.E S.hc q .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    have hearlyDomain : M.early S.E S.hc q .g0 ≤ M.domain S.E S.hc q .g0 := by
      have h1 := facts.gr.early_add_two_delta_le_domain S q .g0
      have hd := S.E.Δ_pos
      linarith
    exact hearlyDomain.trans (facts.gr.domain_le_a S q .g0)
  have hprev := previousActionVote_mem_interpretedInputs_actionRead_of_fixedRootOn facts
    S Hs Xb hf hHs hHsXb hq hfix hpostRead hpost hprevDelay hprevHor hprevCap
      hactionDelay hactionHor hactionCap hA
  intro v hv nv hnv x hx Y hY u hu hmax head hconf hfind
  obtain ⟨n', hn'⟩ := actionReadFrom_nonempty₆₂s facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) x) (q - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n'.cache) S.E S.hc (S.node x)
    n'.st n'.record
  exact Restated.nextActionBatchAligned_preceq_of_carriersPreceq_at_latestOn facts
    S Hs Xb hf hHs hHsXb hactionHor hcarriers v (hHsXb _ hv) x hx nv hnv n' hn' D hD Y hY
    (hprev v hv x (hHs _ _ hearlyAction hx) n' hn' D hD nv hnv Y hY) u hu hmax head hconf hfind

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle with path `W`, if `0 < q`, `lo ≤ S.a (q − 1)`, `S.a q` is in the horizon, every
    member of the set for `S.a (q − 1)` has `h_max = Mh` there, every member of the set for `S.a q`
    has `h_max = Mh` and `h_j + 2 ≤ Mh` there, and every member of the set for `S.a (q − 1) + Δ` is
    awake at `q − 1`, then for every reader `v` in the set for `S.a q` and every author `u` in the
    set for round `q`'s early grade-0 cutoff, the SG vote of `u`'s round-`(q − 1)` action
    attestation is an interpreted input of every round-`q` action read of `v` for `u`. -/
theorem previousActionVote_mem_interpretedInputs_actionRead_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} (hq : 0 < q)
    {Mh : Height}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.h_max = Mh)
    (hgateOff : ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.h_j + 2 ≤ Mh)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)), ∀ u ∈ Hs (M.early S.E S.hc q .g0),
    ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
    ∀ D, M.duties_attest_with (M.gradeContract na.cache) S.E S.hc (S.node u) na.st na.record ⇢ D →
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
    ∀ Y, M.interpretedInputs (M.gradeView (M.toHealing nv.st.core)) nv.st.core.F
        S.hc.η_SG q (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc q) u ⇢ Y →
      M.sgVote D.2.2.erase ∈ Y := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hcut0 : M.late S.E S.hc q .g0 = M.early S.E S.hc q .g0 :=
    facts.gr.allPhasesCutoff_eq_early_g0 S q
  have hqr : q - 1 < q := Nat.sub_lt hq (by decide)
  have hk : q - 1 ∈ M.latest_window S.hc.η_SG q := by
    apply facts.fc.mem_latest_window
    · exact Nat.sub_le_sub_left S.hc.η_SG_ge_one q
    · exact hqr
  have hactionDelta : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤
      M.early S.E S.hc q .g0 := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hqr
    have h2 := facts.gr.early_g2_add_delta_le_early_g1 S q
    have h3 := facts.gr.early_g1_add_delta_le_early_g0 S q
    have hΔ := S.E.Δ_pos
    show M.a S.hc S.E.Δ (q - 1) + S.E.Δ ≤ M.early S.E S.hc q .g0
    linarith
  have hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) lo + S.E.Δ ≤
      M.early S.E S.hc q .g0 := by
    rw [max_eq_left hpost]
    exact hactionDelta
  have hearlyDomain : M.early S.E S.hc q .g0 ≤ M.domain S.E S.hc q .g0 := by
    have h1 := facts.gr.early_add_two_delta_le_domain S q .g0
    linarith [S.E.Δ_pos]
  have horder : M.early S.E S.hc q .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hearlyDomain.trans (facts.gr.domain_le_a S q .g0)
  have hcut : M.early S.E S.hc q .g0 ≤ rho.horizon := horder.trans hactionHor
  have hprevHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le q 1)).trans hactionHor
  intro v hv u huHon na hna D hD nv hnv Y hY
  have huDelta : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ) :=
    hHs _ _ hactionDelta huHon
  have huPrev : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
    hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) huDelta
  have hvEarly : v ∈ Hs (M.early S.E S.hc q .g0) := hHs _ _ horder hv
  set a := D.2.2 with ha
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest a)
      ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf (q - 1) huPrev hprevHor hpost
      (hA u huDelta) (fun j hj => hf.tick_outcome j _ _ hj) na hna D hD
  obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract na.cache) S.E S.hc
    (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s)
  obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract na.cache) S.E S.hc
    (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) g2
  have hshape : a.val_index = u ∧ a.round = q - 1 ∧ a.confirmed = some G.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u (q - 1) na
      (mem_actionReadAt_along₆₂s hf.sorted hf.onePath u (q - 1) hna) D hD g2 hg2 G hG
  obtain ⟨i, hi, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath hemit
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i u) a.round := by
    rw [hshape.2.1]
    rcases Restated.action_read_indexOn facts S rho Hs Xb hf i u (q - 1) hi with hstate | hstate
    · rw [hstate]
      exact hna
    · rw [hstate, actionReadFrom_wake₆₂ facts]
      exact hna
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hna'
  obtain ⟨Wn, hWnBody, hcarrierW, hWnHeight⟩ :=
    Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf (hprev u huPrev) na hna g2 hg2 G hG
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hbodies := actionReadFrom_bodies₆₂s facts S _ (q - 1) na hna
  have hWnRun : Restated.RunBlockOn M S rho W Xb Wn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hWnBody)
  have hHrun : Restated.RunBlockOn M S rho W Xb Hb :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hHb)
  have hrootW : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG)
      Wn.erase :=
    Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hv)
      (X := Wn.erase) (Xn := Wn) rfl hWnRun hWnHeight (hfrontier v hv) (hgateOff v hv)
  have hgate : ¬ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.h_max =
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.h_j + 1 := by
    have h1 : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.h_max = Mh :=
      hfrontier v hv
    have h2 : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.h_j + 2 ≤ Mh :=
      hgateOff v hv
    intro heq
    rw [h1] at heq
    rw [heq] at h2
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h2)
  have hFC : Block.Preceq
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.F Wn.erase := by
    rw [← facts.fc.get_fg_root_toHealing_of_ne _ hgate]
    exact hrootW
  obtain ⟨Gp, hGpW, hGpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Wn hcarrierW
  have hGpRun : Restated.RunBlockOn M S rho W Xb Gp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hWnRun hGpW
  have hroot : Gp.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root Gp, hGpErase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hGpH : Gp = Hb :=
    hf.rootCollisionFree.root_injective Gp Hb
      hGpRun hHrun Gp Hb (Or.inl (Proofs.NamedAncestry.named_self Gp))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHC : Block.Preceq Hb.erase Wn.erase := by
    rw [← hGpH, hGpErase]
    exact hcarrierW
  have hpostA : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [hshape.2.1]
    exact hpost
  have hdeadlineA : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.early S.E S.hc q .g0 := by
    rw [hshape.2.1]
    exact hdeadline
  have hinput :=
    Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb (t := Restated.Vocabulary.Execution.Setup.a M S q) .g0 hk huHon hvEarly
      ⟨hshape.1, hshape.2.1, hemit⟩
      ⟨i, hi, ⟨na, hna', hHb⟩, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  apply hinput Y
  rw [← actionReadFrom_gradeView₆₂s facts S _ q nv hnv
    (facts.ndRun.stateBeforeOf_reachedNode S rho _ (W _) (hf.onePath _).1 v),
    ← actionReadFrom_F₆₂s facts S _ q nv hnv,
    ← hcut0]
  exact hY

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the hypotheses of `previousActionVote_mem_interpretedInputs_actionRead_of_gateOffOn`, if
    every block the SG selector can return on the round-`(q − 1)` action read of a member of the set
    for `S.a q` is an ancestor of `Can`, then at every round-`q` action read of every member of that
    set, the latest interpreted input of every author in that set with a resolved head has that head
    an ancestor of `Can`. -/
theorem actionBatchAlignedAt_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} (hq : 0 < q)
    {Mh : Height}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.h_max = Mh)
    (hgateOff : ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.h_j + 2 ≤ Mh)
    {Can : Block V}
    (hcarriers : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
        let gc := M.gradeContract n'.cache
        let st := M.toHealing n'.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq G Can)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      Restated.Vocabulary.Internal.PhaseGrades.BatchAlignedAt M S.hc
        (M.gradeView (M.toHealing nv.st.core)) nv.st.core.F
        (Hs ((Restated.Vocabulary.Execution.Setup.a M S q))) q
        (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc q) Can := by
  have hearlyAction : M.early S.E S.hc q .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    have hearlyDomain : M.early S.E S.hc q .g0 ≤ M.domain S.E S.hc q .g0 := by
      have h1 := facts.gr.early_add_two_delta_le_domain S q .g0
      have hd := S.E.Δ_pos
      linarith
    exact hearlyDomain.trans (facts.gr.domain_le_a S q .g0)
  have hprevInput := previousActionVote_mem_interpretedInputs_actionRead_of_gateOffOn facts
    S Hs Xb hf hHs hHsXb hq hpost hactionHor hprev hfrontier hgateOff hA
  intro v hv nv hnv x hx Y hY u hu hmax head hconf hfind
  obtain ⟨n', hn'⟩ := actionReadFrom_nonempty₆₂s facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) x) (q - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n'.cache) S.E S.hc (S.node x)
    n'.st n'.record
  exact Restated.nextActionBatchAligned_preceq_of_carriersPreceq_at_latestOn facts
    S Hs Xb hf hHs hHsXb hactionHor hcarriers v (hHsXb _ hv) x hx nv hnv n' hn' D hD Y hY
    (hprevInput v hv x (hHs _ _ hearlyAction hx) n' hn' D hD nv hnv Y hY) u hu hmax head hconf hfind

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedOutageEntry

/-- Under the bundle with path `W` and the weight bound, if `0 < r`, `S.a (r − 1) + Δ ≤ t ≤`
    horizon, `lo ≤ S.a (r − 1)`, and every member of the set for `S.a (r − 1) + Δ` is awake at
    `r − 1`, then the round-`(r − 1)` voters inside `Hs t` outweigh the validators outside `Hs t`
    together with the stale historical voters of `r`. -/
theorem gradeFormingMajority_of_admissible_belowOneThirdOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hfb : BelowOneThirdOn S rho Hs) {r : Round} (_hr : 0 < r)
    {t : Time} (hprevt : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ ≤ t) (hhor : t ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) → M.awake_for_grade2 S u (W j u) (r - 1)) :
    Restated.GradeFormingMajorityOn M S rho W Hs (Hs t) r := by
  have hq : HonestWeightMajority S (Hs t) :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb t hhor
  have hprevHor : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hprevt.trans hhor)
  have hvoters : Hs t ⊆ Restated.honestRoundVotersOn M S rho W Hs (r - 1) := by
    intro v hv
    have hvD : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ) := hHs _ _ hprevt hv
    have hvA : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) :=
      hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hvD
    apply (Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs v (r - 1)).mpr
    obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₂s facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) v) (r - 1)
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) S.E S.hc (S.node v)
      n.st n.record
    have hemit := Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf (r - 1) hvA
      hprevHor hpost (hA v hvD) (fun j hj => hf.tick_outcome j _ _ hj) n hn D hD
    obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
    obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g2
    have hshape := Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho v
      (r - 1) n (mem_actionReadAt_along₆₂s hf.sorted hf.onePath v (r - 1) hn) D hD g2 hg2 G hG
    exact ⟨hvA, D.2.2, hshape.1, hshape.2.1, hemit⟩
  have hstale : Restated.staleHistoricalVotersOn M S rho W Hs r ⊆ Finset.univ \ Hs t := by
    intro v hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, fun hvt => ?_⟩
    exact (Finset.mem_sdiff.mp hv).2 (hvoters hvt)
  unfold Restated.GradeFormingMajorityOn
  rw [Finset.union_eq_left.mpr hstale]
  exact lt_of_lt_of_le hq
    (S.E.electorate.weightOf_mono (Finset.subset_inter hvoters (subset_refl _)))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedOutageEntry

/-- Under the bundle with path `W`, if `0 < r`, `lo ≤ S.a (r − 1)`, every member of the set for
    `S.a (r − 1)` has `h_max = Mh` there, every member of the set for the phase-`p` domain instant
    of round `r` has `h_max = Mh` and `h_j + 2 ≤ Mh` there, that instant is in the horizon, and
    every member of the set for `S.a (r − 1) + Δ` is awake at `r − 1`, then the relative carrier
    window holds at round `r − 1` and phase `p` at the worlds of `W`. -/
theorem relativeCarrierWindowAt_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    {p : Phase} {Mh : Height} (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ w ∈ Hs (M.domain S.E S.hc r p),
      (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.h_max = Mh)
    (hgateOff : ∀ w ∈ Hs (M.domain S.E S.hc r p),
      (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.h_j + 2 ≤ Mh)
    (hhor : M.domain S.E S.hc r p ≤ rho.horizon)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) → M.awake_for_grade2 S u (W j u) (r - 1)) :
    Restated.RelativeCarrierWindowAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs
      (r - 1) p := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hqr : r - 1 < r := Nat.sub_lt hr (by decide)
  have hk : r - 1 ∈ M.latest_window S.hc.η_SG r := by
    apply facts.fc.mem_latest_window
    · exact Nat.sub_le_sub_left S.hc.η_SG_ge_one r
    · exact hqr
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hactionDelta : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ ≤
      M.early S.E S.hc r p := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hqr
    have h2 := facts.gr.early_g2_add_delta_le_early_g1 S r
    have h3 := facts.gr.early_g1_add_delta_le_early_g0 S r
    have hΔ := S.E.Δ_pos
    show M.a S.hc S.E.Δ (r - 1) + S.E.Δ ≤ M.early S.E S.hc r p
    cases p <;> linarith
  have hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) lo + S.E.Δ ≤
      M.early S.E S.hc r p := by
    rw [max_eq_left hpost]
    exact hactionDelta
  have horder : M.early S.E S.hc r p ≤ M.domain S.E S.hc r p := by
    have h := facts.gr.early_add_two_delta_le_domain S r p
    linarith [S.E.Δ_pos]
  have hcut : M.early S.E S.hc r p ≤ rho.horizon := horder.trans hhor
  have hsourceHor : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hactionDelta.trans hcut)
  rw [Restated.RelativeCarrierWindowAtOn, hpred]
  intro w hw u hu huEarly na hna g2 hg2 A hAsel I hI
  have huDelta : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ) :=
    hHs _ _ hactionDelta huEarly
  have huHon : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) :=
    ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u (r - 1)).mp hu).1
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hwEarly : w ∈ Hs (M.early S.E S.hc r p) := hHs _ _ horder hw
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache) S.E S.hc (S.node u)
    na.st na.record
  set a := D.2.2 with ha
  have hshape : a.val_index = u ∧ a.round = r - 1 ∧ a.confirmed = some A.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u (r - 1) na
      (mem_actionReadAt_along₆₂s hf.sorted hf.onePath u (r - 1) hna) D hD g2 hg2 A hAsel
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest a)
      ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf (r - 1) huHon hsourceHor hpost
      (hA u huDelta) (fun j hj => hf.tick_outcome j _ _ hj) na hna D hD
  obtain ⟨i, hi, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath hemit
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i u) a.round := by
    rw [hshape.2.1]
    rcases Restated.action_read_indexOn facts S rho Hs Xb hf i u (r - 1) hi with hstate | hstate
    · rw [hstate]
      exact hna
    · rw [hstate, actionReadFrom_wake₆₂ facts]
      exact hna
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hna'
  obtain ⟨Wn, hWnBody, hcarrierW, hWnHeight⟩ :=
    Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf (hprev u huHon) na hna g2 hg2 A hAsel
  have hbodies := actionReadFrom_bodies₆₂s facts S _ (r - 1) na hna
  have hWsource : Wn ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.bodies := by
    rw [← hbodies]
    exact hWnBody
  have hWnRun : Restated.RunBlockOn M S rho W Xb Wn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb hWsource
  have hHrun : Restated.RunBlockOn M S rho W Xb Hb :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hHb)
  have hrootW : Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core).toFG)
      Wn.erase :=
    Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw)
      (X := Wn.erase) (Xn := Wn) rfl hWnRun hWnHeight (hfrontier w hw) (hgateOff w hw)
  have hgate : ¬ (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.h_max =
      (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.h_j + 1 := by
    have h1 : (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.h_max = Mh :=
      hfrontier w hw
    have h2 : (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.h_j + 2 ≤ Mh :=
      hgateOff w hw
    intro heq
    rw [h1] at heq
    rw [heq] at h2
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h2)
  have hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.F Wn.erase := by
    rw [← facts.fc.get_fg_root_toHealing_of_ne _ hgate]
    exact hrootW
  obtain ⟨Gp, hGpW, hGpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Wn hcarrierW
  have hGpRun : Restated.RunBlockOn M S rho W Xb Gp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hWnRun hGpW
  have hroot : Gp.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root Gp, hGpErase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hGpH : Gp = Hb :=
    hf.rootCollisionFree.root_injective Gp Hb
      hGpRun hHrun Gp Hb (Or.inl (Proofs.NamedAncestry.named_self Gp))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHErase : Hb.erase = A := by
    rw [← hGpH, hGpErase]
  have hHC : Block.Preceq Hb.erase Wn.erase := by
    rw [hHErase]
    exact hcarrierW
  have hpostA : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [hshape.2.1]
    exact hpost
  have hdeadlineA : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.early S.E S.hc r p := by
    rw [hshape.2.1]
    exact hdeadline
  have hinput :=
    Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb (t := M.domain S.E S.hc r p) p hk huEarly hwEarly
      ⟨hshape.1, hshape.2.1, hemit⟩
      ⟨i, hi, ⟨na, hna', hHb⟩, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  have huSource : u ∈ Hs (max ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) lo) := by
    rw [max_eq_left hpost]
    exact huHon
  have hWtarget := Restated.healthy_head_body_at_read_after_gst_admitOn facts
    S rho Hs Xb hf hHs hHsXb u w Wn ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (M.early S.E S.hc r p) (M.domain S.E S.hc r p) huSource hwEarly hWsource hdeadline horder hcut
    hFC
  have hwmem := mem_stateBeforeTime_along₆₂s hf.sorted hf.onePath (M.domain S.E S.hc r p)
  have htargetCore : Wn.erase ∈ (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.T := by
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.domain S.E S.hc r p) w _ hwmem).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWtarget.1
  have hcarrierTarget : A ∈ (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.T := by
    have hclosed := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.domain S.E S.hc r p) w _ hwmem
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hclosed
    rw [facts.sto.toHealing_gs_T] at hclosed
    exact Proofs.Records.mem_of_preceq hclosed.2 _ _
      htargetCore (preceq_eq_true_iff_Preceq.2 hcarrierW)
  have hfind : Block.find? (W (strictEventIndex rho (M.domain S.E S.hc r p)) w).st.core.T A.root =
      some A := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hcarrierTarget
    intro Y hY hYroot
    obtain ⟨Yn, hYerase, hYrun⟩ :=
      Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
        (M.domain S.E S.hc r p) hY
    have hYHroot : Yn.root = Hb.root := by
      rw [← Proofs.NamedWire.erase_root Yn, hYerase, hYroot, ← hHErase,
        Proofs.NamedWire.erase_root Hb]
    have hYH := hf.rootCollisionFree.root_injective
      Yn Hb hYrun hHrun Yn Hb (Or.inl (Proofs.NamedAncestry.named_self Yn))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hYHroot
    rw [← hYerase, hYH, hHErase]
  refine ⟨M.sgVote a.erase, hinput I hI, ?_, ?_, hfind⟩
  · rw [facts.sto.sgVote_round]
    exact hshape.2.1
  · rw [facts.sto.sgVote_confirmed, hshape.2.2]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle with path `W` and the weight bound, if `0 < q`, `S.a q` and round `q`'s grade-2
    domain instant are in the horizon, `lo ≤ S.a (q − 1)`, the relative carrier window holds at
    round `q − 1` and phase `g0`, `P` is a proposal the opening proposer of round `q` can return at
    its read with the cache `c`, every block the SG selector of a member of the set for
    `S.a (q − 1)` can return on its round-`(q − 1)` action read is an ancestor of the parent of
    every proposal input at that read, and every member of the set for `S.a (q − 1) + Δ` is awake at
    `q − 1`, then every outcome of the grade-0 test of `P`'s block at every round-`q` action read of
    a member of the set for round `q`'s grade-0 domain instant is `true`. -/
theorem g0ClearAtAction_of_relativeCarrierWindowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round} (hq : 0 < q)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (_hgradeHor : M.domain S.E S.hc q .g2 ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (q - 1) .g0)
    {P : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P)
    (hparent : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
        let gc := M.gradeContract n'.cache
        let st := M.toHealing n'.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G →
        ∀ I : Protocol.ProposalInput V,
          Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
            (S.node (S.E.proposer (M.opening_slot S.hc q)))
            (M.toHealing (M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
                (S.E.proposer (M.opening_slot S.hc q))).st
                (M.proposal_time S.E (M.opening_slot S.hc q)))
              (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
                (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
          Block.Preceq G I.parent)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs (M.domain S.E S.hc q .g0),
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nv q P.erase ⇢ b → b = true := by
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hqr : q - 1 < q := Nat.sub_lt hq (by decide)
  have hdomainHor : M.domain S.E S.hc q .g0 ≤ rho.horizon :=
    (facts.gr.domain_le_a S q .g0).trans hactionHor
  have hprevDomain : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤
      M.domain S.E S.hc q .g0 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three hqr).trans
      (le_of_lt (facts.gr.early_g2_lt_domain S q .g0))
  have hloDomain : lo ≤ M.domain S.E S.hc q .g0 :=
    hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans hprevDomain)
  have hforming : Restated.GradeFormingMajorityOn M S rho W Hs
      (Hs (M.domain S.E S.hc (q - 1 + 1) .g0)) (q - 1 + 1) := by
    rw [hqPred]
    exact gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hq
      hprevDomain hdomainHor hpost hA
  obtain ⟨I, hI, -, hIP⟩ := proposalParent₆₂s facts S hf.sorted hf.onePath _ c hc hP
  intro v hv nv hnv b hb
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) v).st.core.F S.hc.η_SG q
    (M.early S.E S.hc q .g0) (M.late S.E S.hc q .g0)
  have hframe := Restated.actionFrame_g0On facts S Hs Xb hf hq hactionHor hv hloDomain
    nv hnv fr hfr
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeClear
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hb
  obtain ⟨g, hg, hgb⟩ := returns_map_elim₆₂s _ _ _ hb
  have hg' := (facts.nd.gradeContract_read nv.cache S.E S.hc _ q g).mp hg
  rw [facts.gr.frameGradeRead_clear nv.cache S.E S.hc _ q g hg'] at hgb
  rw [← hgb]
  cases fr with
  | none =>
      rw [Option.map_none] at hframe
      exact facts.gr.clear_of_g0_some_none hframe _
  | some raw =>
      rw [Option.map_some] at hframe
      refine (facts.gr.clear_of_g0 hframe P.erase).trans ?_
      have hrawGrade : M.gradeBool S.E
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q - 1 + 1) .g0)) v).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1 + 1) .g0)) v).st.core.F
          S.hc.η_SG (q - 1 + 1) (M.early S.E S.hc (q - 1 + 1) .g0)
          (M.late S.E S.hc (q - 1 + 1) .g0) raw ⇢ true := by
        rw [hqPred]
        obtain ⟨g0, hg0⟩ := facts.gr.gradeBool_nonempty S.E
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) v).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) v).st.core.F S.hc.η_SG q
          (M.early S.E S.hc q .g0) (M.late S.E S.hc q .g0) raw
        have htrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl g0 hg0
        rw [htrue] at hg0
        exact hg0
      have hv' : v ∈ Hs (M.domain S.E S.hc (q - 1 + 1) .g0) := by
        rw [hqPred]
        exact hv
      obtain ⟨u, hu, hrawCarrier⟩ := Restated.relativeGrade_has_roundCarrierOn facts
        S Hs Xb (Hs (M.domain S.E S.hc (q - 1 + 1) .g0)) hf hHs hwindow hforming
        (subset_refl _) hv' hrawGrade
      have huHon : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
        ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u (q - 1)).mp hu).1
      obtain ⟨n', hn'⟩ := actionReadFrom_nonempty₆₂s facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1)
      obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n'.cache) S.E S.hc
        (M.toHealing n'.st.core) (M.round_of S.hc (M.toHealing n'.st.core).s)
      obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n'.cache) S.E S.hc
        (M.toHealing n'.st.core) (M.round_of S.hc (M.toHealing n'.st.core).s) A2
      have hrawP : Block.Preceq raw P.erase :=
        preceq_trans_Preceq (hrawCarrier n' hn' A2 hA2 G hG)
          (preceq_trans_Preceq (hparent u huHon n' hn' A2 hA2 G hG I hI) hIP)
      exact compatible_of_cases (Or.inr (preceq_trans_Preceq
        (facts.gr.q10_clip_preceq raw nv.st.core.F) hrawP))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the hypotheses of `g0ClearAtAction_of_relativeCarrierWindowOn` with the parent condition
    replaced by the fixed-height opening parent run at `q`, every outcome of the grade-0 test of
    `P`'s block at every round-`q` action read of a member of the set for round `q`'s grade-0 domain
    instant is `true`. -/
theorem g0ClearAtAction_of_relativeCarrierWindow_of_openingParentRunOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round} (hq : 0 < q)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hgradeHor : M.domain S.E S.hc q .g2 ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (q - 1) .g0)
    (hparents : Restated.FixedHeightRootOpeningParentRunOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs q)
    {P : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs (M.domain S.E S.hc q .g0),
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nv q P.erase ⇢ b → b = true :=
  g0ClearAtAction_of_relativeCarrierWindowOn facts S Hs Xb hf hHs hfb hq hactionHor hgradeHor
    hpost hwindow c hc hP
    (fun u hu n' hn' A2 hA2 G hG I hI =>
      hparents.actionTargetParent u hu n' hn' A2 hA2 G hG c hc I hI)
    hA

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.NamedOutageEntry

end

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-! ## The round voters' emissions and the vote anchor's compatibility -/

/-- Under the bundle with path `W`, if `u` is a round-`k` voter of the family along `W`, then `u` is
    in the set for `S.a k` and, for every node state `n` of `u`'s round-`k` action read along `W`
    and every outcome `D` of `u`'s attestation duty on `n`, `u` emits the attestation of `D` at
    `S.a k`. -/
theorem delayedSource_honestRoundVoter_emits_exactActionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {u : V} {k : Round}
    (hu : u ∈ Restated.honestRoundVotersOn M S rho W Hs k) :
    u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) ∧
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) u) k,
      ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node u) n.st n.record ⇢ D →
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest D.2.2)
          (Restated.Vocabulary.Execution.Setup.a M S k) := by
  obtain ⟨huHon, a, _, haround, hemit⟩ :=
    (Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u k).mp hu
  obtain ⟨-, -, hrow⟩ := (Restated.action_run_emissionOn facts S rho Hs Xb hf u k a).mp hemit
  refine ⟨huHon, ?_⟩
  intro n hn D hD
  rw [← hrow n hn D hD]
  exact hemit

/-- Under the bundle with path `W`, if slot `d` is in round `q + 1` with its vote instant in the
    horizon, the relative carrier window holds at round `q` and phase `g1`, the round-`q` voters
    outweigh the validators outside `X` and the stale historical voters of `q + 1`, `X` is inside
    the set for round `q + 1`'s grade-1 domain instant, every block a member of the set for `S.a q`
    can select in its round-`q` action is compatible with `T`, `w` is in the set for that domain
    instant, `c` is an outcome of `w`'s cache update at `vote_time d`, the FG root of `w`'s store
    there is an ancestor of `T`, and `lo ≤ domain (q + 1) g1`, then every outcome of the anchor of
    the node state staged with `c` is compatible with `T`. -/
theorem voterAnchorAt_compatible_of_previousRelativeCarrierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {q : Round} {d : Slot} (hround : M.round_of S.hc d = q + 1)
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs q .g1)
    (hmajority : Restated.GradeFormingMajorityOn M S rho W Hs X (q + 1))
    (hX : X ⊆ Hs (M.domain S.E S.hc (q + 1) .g1))
    {T : Block V}
    (hprev : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs q T)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc (q + 1) .g1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing (M.vote_time S.E d)
      (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)).core).toFG) T)
    (hgat : lo ≤ M.domain S.E S.hc (q + 1) .g1) :
    ∀ A0, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).st.core.s) ⇢ A0 →
    Block.compatible A0 T = true := by
  intro A0 hA0
  have hn : M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c ∈
      Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      mem_stateBeforeTime_along₆₂ hf.sorted hf.onePath _, c, hc, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w d _ hn A0 hA0 with
    hfg | ⟨root, A, hframe, hactive, hanchor⟩
  · rewrite [hfg, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact compatible_of_cases (Or.inl hroot)
  · rw [hanchor]
    have hroundRead : M.round_of S.hc
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).st.core.s =
        q + 1 := by
      rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
      exact hround
    rw [hroundRead] at hframe
    have hslo : M.opening_slot S.hc (q + 1) ≤ d := by
      rw [← hround]
      exact facts.gr.opening_slot_round_of_le_slot S.hc d
    have hshi : d < M.opening_slot S.hc ((q + 1) + 1) := by
      rw [← hround]
      exact facts.gr.lt_opening_slot_round_of_succ S.hc d
    have hnext : M.vote_time S.E d ≤ M.opening S.E S.hc ((q + 1) + 1) := by
      rw [facts.gr.opening_eq_proposal_time]
      exact (facts.sch.voteTime_lt_nextProposal_l86d S.E d).le.trans
        (facts.sch.proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    obtain ⟨_, hAGrade⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
      S Hs Xb hf (Nat.succ_pos q) hslo hround hnext hvoteHor hw c hc hframe hactive hgat
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F S.hc.η_SG (q + 1)
      (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1) A
    have hbt : b = true := hAGrade b hb
    subst hbt
    obtain ⟨u, hu, hAu⟩ := Restated.relativeGrade_has_roundCarrierOn facts
      S Hs Xb X hf hHs hwindow hmajority hX hw hb
    obtain ⟨huHon, hemit⟩ := Restated.delayedSource_honestRoundVoter_emits_exactActionOn facts
      S Hs Xb hf hu
    obtain ⟨nu, hnu⟩ := actionReadFrom_nonempty₆₂s facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u) q
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nu.cache) S.E S.hc (S.node u)
      nu.st nu.record
    obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nu.cache) S.E S.hc
      (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s)
    obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract nu.cache) S.E S.hc
      (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s) A2
    have hcompat := hprev u huHon nu hnu D hD (hemit nu hnu D hD) A2 hA2 G hG
    have hAG := hAu nu hnu A2 hA2 G hG
    exact (priv% Proofs.Vocabulary.Protocol.Grades.RecoveryDelayedSourceSeed
      DecoupledConsensusModel.Proofs.HealingSurface.delayedSource_compatible_ancestor_left)
      hAG hcompat

end

end DecoupledConsensusModel.Sts.Restated
