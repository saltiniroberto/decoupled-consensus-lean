import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_66
import Proofs.Claims.Restated.Claim13beRoute3_67b
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_Execution_SeedCommonRootComplement
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Cones, round ceilings and the seed discharge over the record

Theorems on the band witnesses of action carriers, the persistence of vote cones with a thin head
across the slots of a round, the round ceilings and the second-slot cones, and the discharge of the
height-progress seed from them, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`. Every theorem that takes `Restated.AdmissibleFieldsOn` reads the run along
that bundle's path `W`; the height written `M` in prose is named `Mh`, since `M` names the model.
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
private theorem stateBeforeTime_eq_strict₆₈ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₈ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₈ S rho hsorted]
  exact (hW _).1

/-- Every node state of the round-`r` action read from `before` has as its core store an outcome of
    the confirmation update of `before`'s store staged at round `r`'s action instant. -/
private theorem actionReadFrom_core₆₈ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state of the round-`r` action read from `before` has the tree of `before`'s core
    store. -/
private theorem actionReadFrom_T₆₈ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₈ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

/-- The round-`r` action read from any node state `before` has a node state. -/
private theorem actionReadFrom_nonempty₆₈ (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- For `1 ≤ c` and a slot `d` at or after round `c`'s opening slot, round `c − 1`'s action instant
    is at or before the support cutoff of slot `d − 1`. -/
private theorem prevAction_le_supportCutoff_pred₆₈ (facts : Record.Facts M) (S : Setup V)
    {c : Round} (hc : 1 ≤ c) {d : Slot} (hd : M.opening_slot S.hc c ≤ d) :
    Restated.Vocabulary.Execution.Setup.a M S (c - 1) ≤ M.support_cutoff S.E (d - 1) := by
  have hsucc : M.opening_slot S.hc c = M.opening_slot S.hc (c - 1) + S.hc.R := by
    have h := facts.gr.opening_slot_succ S.hc (c - 1)
    rwa [Nat.sub_add_cancel hc] at h
  have hR := S.hc.R_ge_two
  have h2 : M.opening_slot S.hc (c - 1) + 1 + 1 ≤ d :=
    (Nat.add_le_add_left hR _).trans (hsucc ▸ hd)
  have hle : M.opening_slot S.hc (c - 1) + 1 ≤ d - 1 := Nat.le_sub_of_add_le h2
  show M.a S.hc S.E.Δ (c - 1) ≤ M.support_cutoff S.E (d - 1)
  rw [facts.sch.a_eq_confirmation_time, facts.sch.confirmation_time_eq_support_cutoff_succ]
  exact facts.sch.support_cutoff_mono S.E hle

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, is the core store of `n`'s
    store with the clock set to the slot's vote instant. -/
private theorem voteStore_eq₆₈ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₆₈ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the `h_max` of
    `n`'s core store. -/
private theorem tickStore_h_max₆₈ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the justified
    height `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₆₈ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the FG root of
    `n`'s core store. -/
private theorem tickStore_fgRoot₆₈ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_fg_root (M.toHealing n.st.core).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- For every outcome `T` of the voter's filtered block tree of `st` at its slot, some outcome of
    the voter candidate tree of `st` is `T`. -/
private theorem candidateTree_of_filtered₆₈ (facts : Record.Facts M) (E : Env V) (st : M.S)
    (T : Finset (Block V)) (hT : M.voter_filtered_block_tree E st st.s ⇢ T) :
    ∃ K : Finset (Block V),
      Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E (M.toHealing st) ⇢ K ∧ K = T := by
  obtain ⟨P0, hP0⟩ := facts.fc.voter_processed_block_tree_nonempty E
    (M.toHealing st).toFG.toSG.toGoldfishStore (M.toHealing st).s
  refine ⟨_, ?_, facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E st P0 hP0 T hT⟩
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
  exact (returns_bind_iff₆₈ _ _ _).2 ⟨P0, hP0, (Record.returns_pure _ _).2 rfl⟩

/-- The voter candidate tree of the core store of `st` with the cache `c` written in can return `K`
    exactly when the voter candidate tree of `st`'s own core store can. -/
private theorem candidateTree_store_with_cache₆₈ (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (c : M.Cache) (K : Finset (Block V)) :
    Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E
        (M.toHealing (M.store_with_cache st c).core) ⇢ K ↔
      Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E (M.toHealing st.core) ⇢ K := by
  have hs : ∀ x : M.S, (M.toHealing x).s = x.s := fun x => facts.sto.toHealing_gs_s x
  have hP : ∀ P : Finset (Block V),
      M.voter_processed_block_tree E (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore
        (M.toHealing (M.store_with_cache st c).core).s ⇢ P ↔
      M.voter_processed_block_tree E (M.toHealing st.core).toFG.toSG.toGoldfishStore
        (M.toHealing st.core).s ⇢ P := by
    intro P
    rw [hs, hs, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_processed_block_tree]
  have hfrom : ∀ P : Finset (Block V),
      M.voter_processed_block_tree E (M.toHealing st.core).toFG.toSG.toGoldfishStore
        (M.toHealing st.core).s ⇢ P →
      M.get_filtered_block_tree_from (M.toHealing (M.store_with_cache st c).core).toFG P =
        M.get_filtered_block_tree_from (M.toHealing st.core).toFG P := by
    intro P hP0
    obtain ⟨X, hX⟩ := facts.fc.voter_filtered_block_tree_nonempty E st.core st.core.s
    have hX1 : M.voter_filtered_block_tree E (M.store_with_cache st c).core
        (M.store_with_cache st c).core.s ⇢ X := by
      rw [facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree]
      exact hX
    rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E _ P ((hP P).2 hP0) X hX1,
      facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E _ P hP0 X hX]
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
  rw [returns_bind_iff₆₈, returns_bind_iff₆₈]
  constructor
  · rintro ⟨P, hP1, hK⟩
    have hP0 := (hP P).1 hP1
    exact ⟨P, hP0, by rw [← hfrom P hP0]; exact hK⟩
  · rintro ⟨P, hP0, hK⟩
    exact ⟨P, (hP P).2 hP0, by rw [hfrom P hP0]; exact hK⟩

/-- The node state `n` has an outcome of each read its vote-duty head is computed from: the voter's
    filtered block tree, the voter view, the voter support view, and the head selected from them. -/
private theorem voterHead_outcome₆₈ (facts : Record.Facts M) (S : Setup V) (n : M.N) :
    ∃ (T : Finset (Block V)) (L L' : Finset (GoldfishVote V)) (Hd : Block V),
      M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        T L L' (n.st.core.s - 1) ⇢ Hd := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
    n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  exact ⟨T, L, L', Hd, hT, hL, hL', hHd⟩

/-- The slot after round `c`'s opening slot is at or before the last slot of round `c`. -/
private theorem openingSucc_le_boundary₆₈ (facts : Record.Facts M) (S : Setup V) (c : Round) :
    M.opening_slot S.hc c + 1 ≤ M.opening_slot S.hc (c + 1) - 1 := by
  rw [facts.gr.opening_slot_succ S.hc c]
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left S.hc.R_ge_two _)

/-- The last slot of round `c` is before the opening slot of round `c + 1`. -/
private theorem boundary_lt_openingSucc₆₈ (facts : Record.Facts M) (S : Setup V) (c : Round) :
    M.opening_slot S.hc (c + 1) - 1 < M.opening_slot S.hc (c + 1) := by
  have h := openingSucc_le_boundary₆₈ facts S c
  exact Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos _) (h.trans (Nat.sub_le _ 1))) Nat.one_pos

/-- The vote instant of the slot after round `q`'s opening slot is at or before round `q`'s action
    instant. -/
private theorem openingSuccVote_le_action₆₈ (facts : Record.Facts M) (S : Setup V) (q : Round) :
    M.vote_time S.E (M.opening_slot S.hc q + 1) ≤ Restated.Vocabulary.Execution.Setup.a M S q := by
  have h := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E (M.opening_slot S.hc q)
  have h2 : M.confirmation_time S.E (M.opening_slot S.hc q) =
      Restated.Vocabulary.Execution.Setup.a M S q := Restated.confirmation_time_opening_slot facts S q
  linarith [S.E.Δ_pos]

/-- If every outcome of a store grade is `true`, the store grade can return `true`. -/
private theorem storeGrade_true_of_all₆₈ (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) (B : Block V)
    (h : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ b → b = true) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ true := by
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty E (M.gradeView (M.toHealing st.core)) st.core.F
    hc.η_SG r (M.early E hc r p) (M.late E hc r p) B
  have hbt : b = true := h b hb
  subst hbt
  exact hb

/-- On a path `W` of a run sorted by key, the node state staged at `t` from `v`'s node state in
    `W (strictEventIndex rho t)`, with an outcome `c` of the cache update there, is one of `v`'s
    prepared reads at `t`. -/
private theorem mkNode_mem_confirmationReadAt₆₈ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (t : Time) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) v).st.core.toHealing t
      (W (strictEventIndex rho t) v).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) v).st t)
        (W (strictEventIndex rho t) v).record c ∈
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v t :=
  ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₆₈ hsorted hW t, c, hc, rfl⟩

/-- For `0 < c`, round `c − 1`'s action instant plus one delay is at or before round `c`'s grade-1
    domain instant. -/
private theorem prevAction_add_delta_le_domain_g1₆₈ (facts : Record.Facts M) (S : Setup V)
    {c : Round} (hc : 0 < c) :
    Restated.Vocabulary.Execution.Setup.a M S (c - 1) + S.E.Δ ≤ M.domain S.E S.hc c .g1 := by
  have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hc Nat.one_pos : c - 1 < c)
  have h2 := facts.gr.early_g2_add_delta_le_early_g1 S c
  have h3 := facts.gr.early_add_two_delta_le_domain S c .g1
  have hΔ := S.E.Δ_pos
  show M.a S.hc S.E.Δ (c - 1) + S.E.Δ ≤ M.domain S.E S.hc c .g1
  linarith

/-- Round `c`'s grade-1 domain instant is at or before the vote instant of every slot at or after
    round `c`'s opening slot. -/
private theorem domain_g1_le_vote_time₆₈ (facts : Record.Facts M) (S : Setup V)
    (c : Round) {d : Slot} (hslo : M.opening_slot S.hc c ≤ d) :
    M.domain S.E S.hc c .g1 ≤ M.vote_time S.E d := by
  have h0 := facts.gr.domain_g1_add_delta_le_domain_g0 S c
  have h1 := facts.gr.domain_add_five_delta_le_action S c .g0
  have h2 : M.confirmation_time S.E (M.opening_slot S.hc c) = M.a S.hc S.E.Δ c :=
    Restated.confirmation_time_opening_slot facts S c
  have h3 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc c)
  have h4 := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc c)
  have h5 := facts.sch.vote_time_mono S.E hslo
  have h6 := S.E.Δ_pos
  linarith

/-- Along `W`, under the committee majority, if every member of the set for `S.a q` has `h_max = Mh`
    in `W (strictEventIndex rho (S.a q))` and every two round-`q` action carriers along `W` of
    members of that set are compatible, then some block is a deepest round-`q` action carrier
    ceiling at `Mh`, read from that world. -/
private theorem exists_deepestActionCarrierCeiling_along₆₈ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round}
    (hfrontier : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.h_max = Mh)
    (hchain : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u) q,
      ∀ gu, M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ gu →
      ∀ Au, M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) gu ⇢ Au →
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ gv, M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ gv →
      ∀ Av, M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) gv ⇢ Av →
      Block.compatible Au Av = true) :
    ∃ C : Block V, Restated.DeepestActionCarrierCeilingAtOn M S rho W Hs Xb Mh q C
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))) := by
  classical
  set i := strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q) with hi
  let Act : V → Block V → Prop := fun v B =>
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i v) q,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B
  have hwmem := mem_stateBeforeTime_along₆₈ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S q)
  have hActT : ∀ v B, Act v B → B ∈ (W i v).st.core.T := by
    rintro v B ⟨n, hn, g, hg, hB⟩
    exact Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v
      q _ hwmem n hn g hg B hB
  let Fin : Finset (Block V) := (Hs ((Restated.Vocabulary.Execution.Setup.a M S q))).biUnion
    (fun v => (W i v).st.core.T.filter (fun B => Act v B))
  have hmemFin : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)), ∀ B, Act v B →
      B ∈ Fin := fun v hv B hB =>
    Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨hActT v B hB, hB⟩⟩
  have hnonempty : (Hs ((Restated.Vocabulary.Execution.Setup.a M S q))).Nonempty := by
    have ha : Restated.Vocabulary.Execution.Setup.a M S q =
        M.confirmation_time S.E (M.opening_slot S.hc q) := facts.sch.a_eq_confirmation_time S.hc S.E q
    rw [ha]
    exact Restated.honest_nonempty_of_committeesOn facts S Hs hcom (M.opening_slot S.hc q)
  have hne : Fin.Nonempty := by
    obtain ⟨v0, hv0⟩ := hnonempty
    obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₈ facts S (W i v0) q
    obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
    obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g
    exact ⟨B, hmemFin v0 hv0 B ⟨n, hn, g, hg, hB⟩⟩
  obtain ⟨C, hCFin, hCmax⟩ := Finset.exists_max_image Fin (fun B => B.depth) hne
  obtain ⟨v0, hv0, hCv0⟩ := Finset.mem_biUnion.mp hCFin
  obtain ⟨hCT, n0, hn0, g0, hg0, hC0⟩ := Finset.mem_filter.mp hCv0
  obtain ⟨Cn, hCnErase, hCnRun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hv0)
      (Restated.Vocabulary.Execution.Setup.a M S q) hCT
  obtain ⟨Wn, hWnT, hCWn, hWnRun, hWnH⟩ :=
    Restated.actionCarrierFrontierWitnessOn facts S Hs Xb hf (hHsXb _ hv0) (hfrontier v0 hv0)
      n0 hn0 g0 hg0 C hC0
  refine ⟨C, ⟨⟨v0, hv0, n0, hn0, ⟨g0, hg0, hC0⟩, Wn, hWnT, hCWn, hWnRun, hWnH⟩,
    ⟨Cn, hCnErase, hCnRun⟩, ?_⟩⟩
  intro v hv n hn g hg B hB
  have hcompat : Block.compatible B C = true :=
    hchain v hv v0 hv0 n hn g hg B hB n0 hn0 g0 hg0 C hC0
  exact DecoupledConsensusModel.Proofs.AlignedRoundLemmas.preceq_of_compatible_of_depth_le hcompat
    (hCmax B (hmemFin v hv B ⟨n, hn, g, hg, hB⟩))

/-- For every outcome `c` of the cache update at slot `s`'s proposer's node state in
    `W (strictEventIndex rho (proposal_time s))`, the proposal duty with `c`'s grade contract can
    return some named block. -/
private theorem proposal_some_along₆₈ (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c) :
    ∃ P : NamedBlock V, M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P := by
  have hn : M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
    mkNode_mem_confirmationReadAt₆₈ hf.sorted hf.onePath (S.E.proposer s) (M.proposal_time S.E s) c hc
  have hinv := Restated.Vocabulary.Proofs.HealingSurface.proposerReadAt_invariant facts S rho s _ hn
  rewrite [facts.nd.mkNode_st] at hinv; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hinv
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract c)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
  obtain ⟨P, hoP⟩ := facts.dt.proposal_with_gradeContract_isSome c .poolAndCarried S.E S.hc S.cfg
    (S.node (S.E.proposer s)) _ hinv o (by rw [facts.dt.proposal_with_store_with_cache]; exact ho)
  exact ⟨P, hoP ▸ ho⟩

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `v ∈ Xb` and `v`'s store in `W (strictEventIndex rho (S.a r))` has `h_max = Mh`,
    then for every block `B` the SG selector can return at a node state of `v`'s round-`r` action
    read from that world, some run block `Wn` read through `Xb` is in the tree of that store, is a
    descendant of `B`, and has height at least `Mh − 1`. -/
theorem actionCarrierFrontierWitnessOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {Mh : Height}
    (hfrontier : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.h_max = Mh) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      ∃ Wn : NamedBlock V,
        Wn.erase ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T ∧
          Block.Preceq B Wn.erase ∧
          Restated.RunBlockOn M S rho W Xb Wn ∧
            Mh - 1 ≤ (M.derive_named S.E S.cfg Wn).h := by
  intro n hn gc st k A2 hA2 B hB
  obtain ⟨Wn, hWT, hcarrierW, hWrun, hWh⟩ :=
    Restated.actionCarrierFrontierWitnessOn facts S Hs Xb hf hv hfrontier n hn A2 hA2 B hB
  refine ⟨Wn, ?_, hcarrierW, hWrun, hWh⟩
  rw [← actionReadFrom_T₆₈ facts S _ r n hn]
  exact hWT

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `1 ≤ c`, `lo ≤ S.a (c − 1)`, every member of the set for `S.a (c − 1)` has
    `h_max = Mh` there, `B` is an ancestor of every round-`(c − 1)` action carrier of some member of
    that set, `w` is in the set for `vote_time d` with `d` at or after round `c`'s opening slot and
    in the horizon, and `w`'s store there has `h_j + 2 ≤ Mh`, then some run block `Wn` read through
    `Xb`, a descendant of `B` at height at least `Mh − 1`, is genesis or admitted at `w` along `W`
    before `view_freeze (d − 1)`. -/
theorem g1_bandWitness_relayedOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (_hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hprevFrontier : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = Mh)
    {B : Block V}
    (hcarrier : ∃ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u) (c - 1),
        let gc := M.gradeContract nr.cache
        let st := M.toHealing nr.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2, M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ Bk, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ Bk →
        Block.Preceq B Bk)
    {w : V} {d : Slot} (hw : w ∈ Hs (M.vote_time S.E d))
    (hd : (M.opening_slot S.hc c) ≤ d)
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    (hgateDuty : (W (strictEventIndex rho (M.vote_time S.E d)) w).st.h_j + 2 ≤ Mh) :
    ∃ Wn : NamedBlock V, Restated.RunBlockOn M S rho W Xb Wn ∧ Block.Preceq B Wn.erase ∧
      Mh - 1 ≤ (M.derive_named S.E S.cfg Wn).h ∧
      (Wn.erase = Block.genesis ∨
        Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w Wn.erase (M.view_freeze S.E (d - 1))) := by
  have hoPos : 0 < (M.opening_slot S.hc c) := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hc
  have hdPos : 0 < d := lt_of_lt_of_le hoPos hd
  have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel hdPos
  obtain ⟨u, hu, hBu⟩ := hcarrier
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₈ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u) (c - 1)
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  obtain ⟨Wn, hWpre, hcarrierW, hWrun, hWh⟩ :=
    Restated.actionCarrierFrontierWitnessOn' facts S Hs Xb hf (hHsXb _ hu) (r := c - 1)
      (hprevFrontier u hu) n hn A2 hA2 G hG
  have hBW : Block.Preceq B Wn.erase := preceq_trans_Preceq (hBu n hn A2 hA2 G hG) hcarrierW
  refine ⟨Wn, hWrun, hBW, hWh, ?_⟩
  have hfreezeLe : M.view_freeze S.E (d - 1) ≤ M.vote_time S.E d := by
    have h := facts.sch.view_freeze_lt_vote_time_succ S.E (d - 1)
    rw [hdSucc] at h
    exact le_of_lt h
  have hprevLeCut : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.support_cutoff S.E (d - 1) :=
    prevAction_le_supportCutoff_pred₆₈ facts S hc hd
  have hcutIn : lo ≤ M.support_cutoff S.E (d - 1) := hpost.trans hprevLeCut
  have hFW : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F Wn.erase :=
    Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw hgateDuty hWrun hWh
  rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts S Hs Xb hf u
      ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) hWpre with hgen | ⟨D, i, t, hDerase, hacc, ht⟩
  · exact Or.inl hgen
  · right
    have htIn : t < M.support_cutoff S.E (d - 1) := lt_of_lt_of_le ht hprevLeCut
    have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt
        (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
    have hfreezeHor : M.view_freeze S.E (d - 1) ≤ rho.horizon :=
      hfreezeLe.trans hvoteHor
    have hmaxLe : max t lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) := max_le (le_of_lt ht) hpost
    have hhop : M.support_cutoff S.E (d - 1) + S.E.Δ = M.view_freeze S.E (d - 1) := by
      obtain ⟨-, h2, h3, -⟩ := facts.sch.slot_instants_l55 S.E (d - 1)
      rw [h2, h3]
      ring
    rw [← hDerase]
    apply Restated.block_admittedBefore_of_accepted_after_cutoffOn facts S Hs Xb hf hHs hHsXb
      (hHs _ _ hmaxLe hu) (hHs _ _ hfreezeLe hw) hDpos hacc htIn hcutIn hhop hfreezeHor
    exact Restated.finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterReadOn facts S Hs Xb hf
      hfreezeLe (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) (by rw [hDerase]; exact hFW)

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `w` is in the set for `view_freeze s` and `lo ≤ view_freeze s`, then at the node
    state `n` staged at `vote_time (s + 1)` from `w`'s node state in `W` with a cache outcome, for
    every outcome `T` of the voter's filtered block tree, every `C` in `T` and every anchor outcome
    `A`, every block strictly between `A` and `C` is in `T`. -/
theorem votePathAt_of_candidateOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hgat : lo ≤ M.view_freeze S.E s) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ C : Block V, C ∈ T →
    ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
    ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T :=
  Restated.votePathAt_of_candidateOn facts S Hs Xb hf hw c hc hgat

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority, if `0 < s`, `lo ≤ vote_time s`, `confirmation_time s`
    is in the horizon, the slot-`s` votes of the set form a cone over `C` with a thin head, and
    every member of the set for `vote_time (s + 1)` has at its vote store `h_max = Mh`,
    `h_j + 2 ≤ Mh`, an FG root comparable with `C`, anchors compatible with `C` and heads at height
    at least `h_max − 1`, then the slot-`(s + 1)` votes of the set form a cone over `C` with a thin
    head. -/
theorem coneAndThin_succOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {s : Slot} {C : Block V} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hthin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C)
    (hframe : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_j + 2 ≤ Mh ∧
      (Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) C ∨
        Block.Preceq C (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG)))
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.compatible A C = true)
    (hband : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max - 1 ≤
          (M.derive_named S.E S.cfg Hn).h)
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun X => Block.Preceq C X) ∧
      Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh (s + 1) C := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hpostSucc : lo ≤ M.vote_time S.E (s + 1) :=
    hpost.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s))
  have hfreezeVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
    le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)
  have hpostFreeze : lo ≤ M.view_freeze S.E s :=
    hpost.trans (Restated.vote_time_le_view_freeze_l58 facts S.E s)
  have hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' M S rho s C w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c) := by
    intro w hw c hc
    have hnst : (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st =
        M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) c := facts.nd.mkNode_st _ _ _
    obtain ⟨hfrontier, hgate, hroot⟩ := hframe w hw
    refine { rootSide := ?_, anchor := hanchor w hw c hc }
    intro A hA T hT
    rcases hroot with hrootC | hCroot
    · left
      have hfacts := Restated.seedRelayVoteFactsOn facts S Hs Xb hf hHs hHsXb hsb hpost hhor
        hvotes hthin hw hfrontier hgate hrootC c hc
      obtain ⟨K, hK, hKT⟩ := candidateTree_of_filtered₆₈ facts S.E _ T hT
      rw [hnst, candidateTree_store_with_cache₆₈ facts, ← voteStore_eq₆₈ facts] at hK
      have hCT : C ∈ T := by
        rw [← hKT]
        exact (hfacts K hK).1
      refine ⟨by rw [hnst, facts.nd.store_with_cache_get_fg_root, ← voteStore_eq₆₈ facts]; exact hrootC,
        hCT, ?_⟩
      exact Restated.votePathAt_of_candidateOn' facts S Hs Xb hf (hHs _ _ hfreezeVote hw) c hc
        hpostFreeze T hT C hCT A hA
    · exact Or.inr (by rw [hnst]; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]); rw [← voteStore_eq₆₈ facts]; exact hCroot)
  have hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1)
      (fun X => Block.Preceq C X) := by
    intro w hw hwCommittee
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
    obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₆₈ facts S
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
    obtain ⟨H, hHerase, hHrun⟩ := Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hw)
      (s + 1) c hc T hT L hL L' hL' Hd hHd
    refine ⟨H, ?_, hHrun, ?_⟩
    · rw [hHerase]
      exact Restated.goldfishCone_stepOn'_GoldfishCone facts S Hs Xb hf hHs hHsXb hcom hs hpost
        hhor hvotes hw c hc (hinputs w hw c hc) T hT L hL L' hL' Hd hHd
    · rw [hHerase]
      exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos s) hwCommittee
        hvoteHor hpostSucc c hc (hrun w hwCommittee hw) T hT L hL L' hL' Hd hHd
  refine ⟨hcone, ?_⟩
  have hpositive : 0 < ((S.E.committee (s + 1)) ∩
      Hs (M.confirmation_time S.E (s + 1))).card := by
    have hc := hcom (s + 1)
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee (s + 1) := (Finset.mem_inter.mp hw).1
  have hwConf : w ∈ Hs (M.confirmation_time S.E (s + 1)) := (Finset.mem_inter.mp hw).2
  have hwVote : w ∈ Hs (M.vote_time S.E (s + 1)) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hwConf
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
  obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₆₈ facts S
    (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
  obtain ⟨H, hHerase, hHrun, hHband⟩ := hband w hwVote c hc T hT L hL L' hL' Hd hHd
  have hHemit : Restated.Vocabulary.Execution.Run.emits M S rho W w
      (.gfVote ⟨w, s + 1, H.erase.root⟩) (M.vote_time S.E (s + 1)) := by
    rw [hHerase]
    exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hwVote (Nat.succ_pos s)
      hwCommittee hvoteHor hpostSucc c hc (hrun w hwCommittee hwVote) T hT L hL L' hL' Hd hHd
  refine ⟨H, ⟨w, hwConf, hwCommittee, hHrun, hHemit⟩, ?_, ?_⟩
  · rw [hHerase]
    exact Restated.goldfishCone_stepOn'_GoldfishCone facts S Hs Xb hf hHs hHsXb hcom hs hpost
      hhor hvotes hwVote c hc (hinputs w hwVote c hc) T hT L hL L' hL' Hd hHd
  · have hM := (hframe w hwVote).1
    rw [hM] at hHband
    exact hHband

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority, if `0 < s0`, `lo ≤ vote_time s0`,
    `confirmation_time s1` is in the horizon, the slot-`s0` votes form a cone over `C` with a thin
    head, and every slot `d` with `s0 < d ≤ s1` has the frame, the anchors and the heads of
    `coneAndThin_succOn'`, then every slot from `s0` to `s1` has the cone over `C` with a thin head. -/
theorem coneAndThin_throughOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {s0 s1 : Slot} {C : Block V} (hs0 : 0 < s0)
    (hpost : lo ≤ M.vote_time S.E s0)
    (hhor : M.confirmation_time S.E s1 ≤ rho.horizon)
    (hbase : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s0 (fun X => Block.Preceq C X) ∧
      Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s0 C)
    (hframe : ∀ d : Slot, s0 < d → d ≤ s1 → ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max = Mh ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_j + 2 ≤ Mh ∧
      (Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG) C ∨
        Block.Preceq C (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG)))
    (hanchor : ∀ d : Slot, s0 < d → d ≤ s1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.compatible A C = true)
    (hband : ∀ d : Slot, s0 < d → d ≤ s1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max - 1 ≤
          (M.derive_named S.E S.cfg Hn).h)
    (hrun : ∀ d : Slot, s0 < d → d ≤ s1 → ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    ∀ k : Slot, s0 ≤ k → k ≤ s1 →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb k (fun X => Block.Preceq C X) ∧
        Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh k C := by
  intro k hk0 hk1
  induction k, hk0 using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
    have hkle : k ≤ s1 := (Nat.le_succ k).trans hk1
    have hprev := ih hkle
    have hkpos : 0 < k := lt_of_lt_of_le hs0 hk
    have hpostK : lo ≤ M.vote_time S.E k :=
      hpost.trans (facts.sch.vote_time_mono_slots S.E hk)
    have hhorK : M.confirmation_time S.E k ≤ rho.horizon :=
      (facts.sch.confirmation_time_mono S hkle).trans hhor
    exact Restated.coneAndThin_succOn' facts S Hs Xb hf hHs hHsXb hcom hkpos hpostK hhorK
      hprev.1 hprev.2
      (hframe (k + 1) (Nat.lt_succ_of_le hk) hk1)
      (hanchor (k + 1) (Nat.lt_succ_of_le hk) hk1)
      (hband (k + 1) (Nat.lt_succ_of_le hk) hk1)
      (hrun (k + 1) (Nat.lt_succ_of_le hk) hk1)

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority, if `lo ≤ vote_time (o + 1)`, `S.a (c + 1)` is in the
    horizon, the slot-`(o + 1)` votes form a cone over `D` with a thin head, and every later slot of
    round `c` has the frame, the anchors and the heads of `coneAndThin_succOn'`, then round `c`'s
    last slot has the cone over `D` with a thin head. -/
theorem boundaryConeAndThin_of_baseConeOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {c : Round} {D : Block V}
    (hpostVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1))
    (hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (hbase : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
        (fun X => Block.Preceq D X) ∧
      Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh ((M.opening_slot S.hc c) + 1) D)
    (hframe : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max = Mh ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_j + 2 ≤ Mh ∧
      (Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG) D ∨
        Block.Preceq D (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG)))
    (hanchor : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ ch : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ ch →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record ch
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.compatible A D = true)
    (hband : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ ch : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ ch →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record ch
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max - 1 ≤
          (M.derive_named S.E S.cfg Hn).h)
    (hrun : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc (c + 1)) - 1)
        (fun X => Block.Preceq D X) ∧
      Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh ((M.opening_slot S.hc (c + 1)) - 1) D := by
  have hb := openingSucc_le_boundary₆₈ facts S c
  have hboundaryConf : M.confirmation_time S.E
      ((M.opening_slot S.hc (c + 1)) - 1) ≤ rho.horizon :=
    ((facts.sch.confirmation_time_mono S (le_of_lt (boundary_lt_openingSucc₆₈ facts S c))).trans
      (Restated.confirmation_time_opening_slot facts S (c + 1)).le).trans hhorNext
  exact Restated.coneAndThin_throughOn' facts S Hs Xb hf hHs hHsXb hcom
    (Nat.succ_pos _) hpostVote hboundaryConf hbase hframe hanchor hband hrun
    ((M.opening_slot S.hc (c + 1)) - 1) hb le_rfl

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `D` and `Wb` are run blocks
    with `D` an ancestor of `Wb` at height at least `Mh − 1`, every round-`c` action carrier of the
    set for `S.a c` is an ancestor of `D`, the base cone over `D` with a thin head holds at `o + 1`,
    the later slots of round `c` have the frame, the anchors and the heads, the regime of round `c`
    holds, and the bounds on `t_GST`, `lo` and the awake conditions hold, then some round ceiling at
    `c + 1` is a descendant of `D`. -/
theorem roundCeiling_succ_of_baseConeOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} {D Wb : NamedBlock V}
    (hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S c))
    (hpostVote : S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1))
    (hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (hDrun : Restated.RunBlockOn M S rho W Xb D) (hWrun : Restated.RunBlockOn M S rho W Xb Wb)
    (hDW : Block.Preceq D.erase Wb.erase)
    (hWthin : Mh - 1 ≤ (M.derive_named S.E S.cfg Wb).h)
    (hcarriers : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B D.erase)
    (hbase : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
        (fun X => Block.Preceq D.erase X) ∧
      Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh ((M.opening_slot S.hc c) + 1) D.erase)
    (hframe : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max = Mh ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_j + 2 ≤ Mh ∧
      (Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG) D.erase ∨
        Block.Preceq D.erase (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG)))
    (hanchor : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ ch : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ ch →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record ch
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.compatible A D.erase = true)
    (hband : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ ch : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ ch →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record ch
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max - 1 ≤
          (M.derive_named S.E S.cfg Hn).h)
    (hheadThin : ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W
        (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))) Xb
        ((M.opening_slot S.hc (c + 1)) - 1) X →
        Mh - 1 ≤ (M.derive_named S.E S.cfg X).h)
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh c)
    (hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S c))
    (hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S u (W j u) c)
    (hrun : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    ∃ B : NamedBlock V,
      Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh (c + 1) B ∧
        Block.Preceq D.erase B.erase := by
  have hb := openingSucc_le_boundary₆₈ facts S c
  have hboundaryConf : M.confirmation_time S.E
      ((M.opening_slot S.hc (c + 1)) - 1) ≤ rho.horizon :=
    ((facts.sch.confirmation_time_mono S (le_of_lt (boundary_lt_openingSucc₆₈ facts S c))).trans
      (Restated.confirmation_time_opening_slot facts S (c + 1)).le).trans hhorNext
  have hthrough := Restated.boundaryConeAndThin_of_baseConeOn' facts S Hs Xb hf hHs hHsXb hcom
    hloVote hhorNext hbase hframe hanchor hband hrun
  have hpostBoundaryVote : S.E.t_GST ≤
      M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1) :=
    hpostVote.trans (facts.sch.vote_time_mono_slots S.E hb)
  have hloBoundary : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1) :=
    hloVote.trans (facts.sch.vote_time_mono_slots S.E hb)
  exact Restated.roundCeiling_base_of_carrierFrontierOn facts S Hs Xb hf hHs hHsXb hcom hfb
    hpostAction hpostBoundaryVote hboundaryConf hDrun hWrun hDW hWthin hcarriers
    hthrough.1 hheadThin hreg hloAction hloBoundary hA

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `freeze ≤ read` and `Wb` is genesis or admitted at `w` along `W` before `freeze`,
    then `Wb` is in the tree of `w`'s store in `W (strictEventIndex rho read)` and stamped there
    before `freeze`. -/
theorem relayedWitness_memOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {Wb : Block V} {freeze read : Time} (hle : freeze ≤ read)
    (h : Wb = Block.genesis ∨ Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w Wb freeze) :
    Wb ∈ (W (strictEventIndex rho read) w).st.T ∧
      stampedBefore (W (strictEventIndex rho read) w).st.timestamp_block freeze Wb = true :=
  Restated.seedCanonicalRelayedWitness_mem_and_stampOn facts S Hs Xb hf hle h

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the weight bound, if `1 ≤ c`, `lo ≤ S.a (c − 1)`, `S.a c` is in the horizon,
    `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to `S.a c`, round `c` is ready, the
    grade-2 block read can return `some Q` at a node state of the round-`c` action read of a member
    `v` of the set for `S.a c`, `lo ≤ opening (c − η_SG)` and the awake condition holds at `c − 1`,
    then every committee member of slot `o + 1` in the set for its vote instant voted along `W` a
    run block that is a descendant of `Q`. -/
theorem secondSlotCone_of_grade2On' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh (c - 1) c)
    (hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n c ⇢ some Q)
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq Q X) := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hpredLe : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hvote1Action : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    openingSuccVote_le_action₆₈ facts S c
  have hpredVote1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) :=
      (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
    exact h2.trans ((le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _)).trans
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _)))
  have hvote1Hor : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤ rho.horizon :=
    hvote1Action.trans hhor
  have hfreezeVote : M.view_freeze S.E ((M.opening_slot S.hc c)) ≤
      M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E _)
  have hframeV1 : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.h_max = Mh :=
    fun w hw => hframe _ hpredVote1 hvote1Action w hw
  have hprevFrontier : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = Mh :=
    fun u hu => (hframe ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) le_rfl hpredLe u hu).2
  have hdomainG0Le : M.domain S.E S.hc c .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := facts.gr.domain_le_a S c .g0
  have hdomainG1Le : M.domain S.E S.hc c .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := facts.gr.domain_le_a S c .g1
  have hdomainG2Le : M.domain S.E S.hc c .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := facts.gr.domain_le_a S c .g2
  have hvG0 : v ∈ Hs (M.domain S.E S.hc c .g0) := hHs _ _ hdomainG0Le hv
  have hvG1 : v ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ hdomainG1Le hv
  have hvG2 : v ∈ Hs (M.domain S.E S.hc c .g2) := hHs _ _ hdomainG2Le hv
  have hG1v : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) v).st c .g1 Q ⇢ true :=
    storeGrade_true_of_all₆₈ facts S.E S.hc _ c .g1 Q
      (Restated.namedG1At_of_nodeQ2On facts S Hs Xb hf hHs hHsXb hcPos hhor hloOpen v hvG0 Q n hn hQ)
  have hprevG1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤ M.domain S.E S.hc c .g1 :=
    prevAction_add_delta_le_domain_g1₆₈ facts S hcPos
  have hprevLeG1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g1 :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hprevG1
  have hdomainG1Hor : M.domain S.E S.hc c .g1 ≤ rho.horizon := hdomainG1Le.trans hhor
  have hG1Vote1 : M.domain S.E S.hc c .g1 ≤
      M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    domain_g1_le_vote_time₆₈ facts S c (Nat.le_succ _)
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1) .g1 :=
    Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hcPos hpost hprevFrontier
      (fun x hx => (hframe _ hprevLeG1 hdomainG1Le x hx).2)
      (fun x hx => (hframe _ hprevLeG1 hdomainG1Le x hx).1) hdomainG1Hor hA
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs (Hs (M.domain S.E S.hc c .g1)) c :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hcPos hprevG1
      hdomainG1Hor hpost hA
  have hcarrier := Restated.namedG1At_preceq_honestPreviousActionCarrierOn facts S Hs Xb
    (Hs (M.domain S.E S.hc c .g1)) hf hHs hc hwindow hmajority (subset_refl _) hvG1 hG1v
  have hround1 : (M.round_of S.hc ((M.opening_slot S.hc c) + 1)) = c :=
    facts.gr.ActionRound_round_of_opening_succ S.hc c
  have hnextOpening : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤
      M.opening S.E S.hc (c + 1) := by
    have hlt : (M.opening_slot S.hc c) + 1 < (M.opening_slot S.hc (c + 1)) := by
      have h : (M.opening_slot S.hc (c + 1)) = (M.opening_slot S.hc c) + S.hc.R :=
        facts.gr.opening_slot_succ S.hc c
      have h1R : 1 < S.hc.R := lt_of_lt_of_le Nat.one_lt_two S.hc.R_ge_two
      rw [h]
      exact Nat.add_lt_add_left h1R _
    have hstep : M.proposal_time S.E ((M.opening_slot S.hc c) + 1 + 1) ≤
        M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) :=
      facts.sch.proposal_time_mono S.E (Nat.succ_le_of_lt hlt)
    have hopen : M.opening S.E S.hc (c + 1) =
        M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) :=
      facts.gr.opening_eq_proposal_time S.E S.hc (c + 1)
    rw [hopen]
    exact (le_of_lt (facts.sch.voteTime_lt_nextProposal_l86d S.E ((M.opening_slot S.hc c) + 1))).trans
      hstep
  have hpostVote1 : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    hpost.trans hpredVote1
  intro w hw hwCommittee
  have hM : 1 ≤ Mh := by
    have h2 : 2 ≤ Mh := (Nat.le_add_left 2 _).trans (hframeV1 w hw).1
    exact le_trans (by decide) h2
  obtain ⟨Wn, hWrun, hQW, hWh, hrelay⟩ := Restated.g1_bandWitness_relayedOn' facts S Hs Xb hf hHs hHsXb hc
    hpost hhor hprevFrontier hcarrier hw (Nat.le_succ _) hvote1Hor (hframeV1 w hw).1
  simp only [Nat.add_sub_cancel] at hrelay
  have hrootV1 : M.get_fg_root
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core).toFG
        = (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.F :=
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts (hframeV1 w hw).1 (hframeV1 w hw).2
  have hFW : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.F Wn.erase :=
    Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw (hframeV1 w hw).1 hWrun hWh
  obtain ⟨cw, hcw⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
    (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache
  obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₆₈ facts S
    (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
      (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw)
  obtain ⟨H, hHerase, hHrun⟩ :=
    Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hw) ((M.opening_slot S.hc c) + 1)
      cw hcw T hT L hL L' hL' Hd hHd
  have hemit : Restated.Vocabulary.Execution.Run.emits M S rho W w
      (.gfVote ⟨w, (M.opening_slot S.hc c) + 1, H.erase.root⟩)
      (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) := by
    rw [hHerase]
    have hrunW : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w
        (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc ((M.opening_slot S.hc c) + 1)) := by
      intro j hj
      have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc ((M.opening_slot S.hc c) + 1)) .g1 -
          S.E.Δ := by
        rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc c]
        have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
        have h2 := facts.gr.q10_early_g2_le_early_g1 S c
        have h3 : lo ≤ M.a S.hc S.E.Δ (c - 1) := hpost
        linarith
      exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
    exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos _) hwCommittee
      hvote1Hor hpostVote1 cw hcw hrunW T hT L hL L' hL' Hd hHd
  refine ⟨H, ?_, hHrun, hemit⟩
  rw [hHerase]
  rcases preceq_linear_Preceq hFW hQW with hFQ | hQF
  ·
    have hWduty := (Restated.relayedWitness_memOn' facts S Hs Xb hf hfreezeVote hrelay).1
    have hactiveDuty : Q ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core).toFG :=
      Restated.frontierAncestor_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) hvote1Hor hWduty rfl
        hWrun hQW hWh hM (hframeV1 w hw).2 (hframeV1 w hw).1 (by rw [hrootV1]; exact hFQ)
    have hactiveRead : Q ∈ M.get_filtered_block_tree (M.toHealing
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1))).core).toFG := by
      have hEq : M.get_filtered_block_tree (M.toHealing (M.store_with_t_s
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
            (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
            (S.E.slotOf (M.vote_time S.E ((M.opening_slot S.hc c) + 1))))).toFG =
          M.get_filtered_block_tree (M.toHealing
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core).toFG :=
        facts.fc.get_filtered_block_tree_set_clock_slot _ _ _
      rw [facts.hd.setClock_core_eq_store_with_t_s, hEq]
      exact hactiveDuty
    exact Restated.preceq_voterHeadAt_of_nodeQ2_activeAtDutyReadOn facts S Hs Xb hf hHs hHsXb hsb hcPos
      (Nat.le_succ _) hround1 hnextOpening hvote1Hor
      (facts.gr.lo_le_early_g2_of_window_start S hcPos hloOpen) hready.2 hvG2
      (hHs _ _ hG1Vote1 hw) n hn hQ hactiveRead hloOpen cw hcw T hT L hL L' hL' Hd hHd
  ·
    have hmem := mkNode_mem_confirmationReadAt₆₈ hf.sorted hf.onePath w
      (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) cw hcw
    have hrootHead := Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts S rho w
      ((M.opening_slot S.hc c) + 1) _ hmem T hT L hL L' hL' Hd hHd
    refine preceq_trans_Preceq ?_ hrootHead
    have hEq : M.get_fg_root (M.toHealing (M.store_with_t_s
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
          (S.E.slotOf (M.vote_time S.E ((M.opening_slot S.hc c) + 1))))).toFG =
        M.get_fg_root (M.toHealing
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core).toFG :=
      facts.fc.get_fg_root_set_clock_slot _ _ _
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s, hEq, hrootV1]
    exact hQF

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `w` is in the set for `t`, `w`'s store in `W (strictEventIndex rho t)` has
    `h_j + 2 ≤ Mh` and `h_max = Mh`, and `D` is an ancestor of a run block `Wb` at height at least
    `Mh − 1`, then the FG root of that store is an ancestor or a descendant of `D`. -/
theorem fgRoot_comparable_of_bandWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {t : Time} (hw : w ∈ Hs t) {Mh : Height}
    (hgate : (W (strictEventIndex rho t) w).st.h_j + 2 ≤ Mh)
    (hmax : (W (strictEventIndex rho t) w).st.h_max = Mh)
    {D : Block V} {Wb : NamedBlock V} (hWrun : Restated.RunBlockOn M S rho W Xb Wb)
    (hDW : Block.Preceq D Wb.erase)
    (hWh : Mh - 1 ≤ (M.derive_named S.E S.cfg Wb).h) :
    Block.Preceq (M.get_fg_root (M.toHealing (W (strictEventIndex rho t) w).st.core).toFG) D ∨
      Block.Preceq D (M.get_fg_root (M.toHealing (W (strictEventIndex rho t) w).st.core).toFG) := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts
    (st := (W (strictEventIndex rho t) w).st.core) hgate hmax]
  exact preceq_linear_Preceq (Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw hgate hWrun hWh)
    hDW

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `1 ≤ c`, `t_GST ≤ S.a (c − 1)`,
    `S.a (c + 2)` is in the horizon, `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to
    `S.a (c + 2)`, `Restated.SeedRoundDischargeAtOn` holds for round `c`, `lo ≤ S.a (c − 1)` and the
    awake condition holds at `c`, then `Restated.SeedBoundaryAdoptionAtOn` holds for round `c` and
    some round ceiling at `c + 1` exists. -/
theorem seedBoundaryAdoption_of_dischargeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh (c - 1) (c + 2))
    (hdis : Restated.SeedRoundDischargeAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh c)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S u (W j u) c) :
    Restated.SeedBoundaryAdoptionAtOn M S rho W Hs Xb Mh c
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))) ∧
      ∃ B : NamedBlock V,
        Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh (c + 1) B := by
  have hclaim1 := hdis.claim1
  have hanchorCompat := hdis.anchorCompat
  have hheadBand := hdis.headBand
  have hpredLe : c - 1 ≤ c := Nat.sub_le c 1
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have hb := openingSucc_le_boundary₆₈ facts S c
  have haPredC : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredLe
  have haCSucc2 : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right c 2)
  have haSucc12 : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ (c + 1))
  have hpostC : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := hpost.trans haPredC
  have hloC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := hlo.trans haPredC
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon := haCSucc2.trans hhor
  have hhorC1 : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon := haSucc12.trans hhor
  have hvoteLo : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d →
      (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E d := by
    intro d hlod
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    exact (((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc c)))).trans
      (facts.sch.vote_time_mono_slots S.E hlod)
  have hpredVote : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
      M.vote_time S.E ((M.opening_slot S.hc c) + 1) := hvoteLo _ (Nat.le_succ _)
  have hvoteSuccAction : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    openingSuccVote_le_action₆₈ facts S c
  have hpostVote : S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    hpost.trans hpredVote
  have hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) := hlo.trans hpredVote
  have hvoteSuccHor : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤ rho.horizon :=
    hvoteSuccAction.trans hhorC
  have hfrontierC : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w).st.h_max = Mh :=
    fun w hw => (hframe ((Restated.Vocabulary.Execution.Setup.a M S c)) haPredC haCSucc2 w hw).2
  have hrunR : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d) := by
    intro d hdlo hdhi w _ hw j hj
    have hround : M.round_of S.hc d = c := by
      rcases Nat.eq_or_lt_of_le hdlo with h | h
      · rw [← h]
        exact facts.gr.round_of_opening_slot_eq S.hc c
      · have hlt : d < M.opening_slot S.hc (c + 1) :=
          (Nat.le_sub_one_iff_lt (facts.gr.openingSlot_pos_l58 S (Nat.succ_pos c))).1 hdhi
        exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc h hlt
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
      rw [hround]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
      have h2 := facts.gr.q10_early_g2_le_early_g1 S c
      have h3 : lo ≤ M.a S.hc S.E.Δ (c - 1) := hlo
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  have hrunInner : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d) :=
    fun d hlod hhi => hrunR d ((Nat.le_succ _).trans (le_of_lt hlod)) hhi
  have hvoteLeNext : ∀ d : Slot, d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    intro d hhi
    have h1 : M.vote_time S.E d ≤ M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1) :=
      facts.sch.vote_time_mono_slots S.E hhi
    have h2 : M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1) ≤
        M.confirmation_time S.E ((M.opening_slot S.hc (c + 1)) - 1) :=
      facts.sch.Protocol_vote_time_le_confirmation_time S.E _
    have h3 : M.confirmation_time S.E ((M.opening_slot S.hc (c + 1)) - 1) ≤
        M.confirmation_time S.E (M.opening_slot S.hc (c + 1)) :=
      facts.sch.confirmation_time_mono S (Nat.sub_le _ 1)
    exact h1.trans (h2.trans (h3.trans (Restated.confirmation_time_opening_slot facts S (c + 1)).le))
  have hfrontD : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max = Mh := by
    intro d hlod hhi w hw
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₈ facts]
    exact (hframe _ (hvoteLo d hlod) ((hvoteLeNext d hhi).trans haSucc12) w hw).2
  have hgateD : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_j + 2 ≤ Mh := by
    intro d hlod hhi w hw
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₆₈ facts]
    exact (hframe _ (hvoteLo d hlod) ((hvoteLeNext d hhi).trans haSucc12) w hw).1
  have hbandAt : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ ch : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ ch →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record ch
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max - 1 ≤
          (M.derive_named S.E S.cfg Hn).h := by
    intro d hlod hhi w hw ch hch n T hT L hL L' hL' Hd hHd
    obtain ⟨Hn, hHe, hHr, hHb⟩ := hheadBand d hlod hhi w hw ch hch T hT L hL L' hL' Hd hHd
    exact ⟨Hn, hHe, hHr, by rw [hfrontD d hlod hhi w hw]; exact hHb⟩
  have hchain := Restated.honestActionCarriersOneChainAt_of_secondSlotConeOn facts S Hs Xb hf hHs hcom
    hclaim1
  obtain ⟨D, hD⟩ :=
    exists_deepestActionCarrierCeiling_along₆₈ facts S Hs Xb hf hHsXb hcom hfrontierC hchain
  obtain ⟨vD, hvD, nD, hnD, ⟨gD, hgD, hDsel⟩, Wn, -, hDW, hWrun, hWthin⟩ := hD.sourceAndWitness
  obtain ⟨Dn, hDnErase, hDrun⟩ := hD.run
  have hcarriers := hD.previousCarriers
  have hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq D X) := hclaim1 vD hvD nD hnD gD hgD D hDsel
  have hthin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh ((M.opening_slot S.hc c) + 1) D := by
    have hpositive : 0 < ((S.E.committee ((M.opening_slot S.hc c) + 1)) ∩
        Hs (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1))).card := by
      have hc := hcom ((M.opening_slot S.hc c) + 1)
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
    have hwCommittee : w ∈ S.E.committee ((M.opening_slot S.hc c) + 1) := (Finset.mem_inter.mp hw).1
    have hwConf : w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1)) :=
      (Finset.mem_inter.mp hw).2
    have hwVote : w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hwConf
    obtain ⟨X, hDX, hXrun, hXemit⟩ := hcone w hwVote hwCommittee
    refine ⟨X, ⟨w, hwConf, hwCommittee, hXrun, hXemit⟩, hDX, ?_⟩
    exact Restated.headThin_of_bandOn facts S Hs Xb hf (Nat.succ_pos _) hvoteSuccHor
      (hfrontD _ (Nat.le_succ _) hb) (hbandAt _ (Nat.le_succ _) hb) hloVote
      (hrunR _ (Nat.le_succ _) hb) X
      ⟨w, hwVote, hwCommittee, hXrun, hXemit⟩
  have hframeDuty : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max = Mh ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_j + 2 ≤ Mh ∧
      (Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG) D ∨
        Block.Preceq D (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG)) := by
    intro d hlod hhi w hw
    have hlod' : (M.opening_slot S.hc c) ≤ d := (Nat.le_succ _).trans (le_of_lt hlod)
    have h := hframe _ (hvoteLo d hlod') ((hvoteLeNext d hhi).trans haSucc12) w hw
    have hcmp := Restated.fgRoot_comparable_of_bandWitnessOn facts S Hs Xb hf hHsXb hw h.1 h.2 hWrun hDW
      hWthin
    refine ⟨hfrontD d hlod' hhi w hw, hgateD d hlod' hhi w hw, ?_⟩
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₈ facts]
    exact hcmp
  have hanchorDuty : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ ch : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ ch →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record ch
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.compatible A D = true :=
    fun d hlod hhi w hw ch hch A hA =>
      hanchorCompat d hlod hhi w hw ch hch A hA vD hvD nD hnD gD hgD D hDsel
  have hbandDuty := fun (d : Slot) (hlod : (M.opening_slot S.hc c) + 1 < d)
      (hhi : d ≤ (M.opening_slot S.hc (c + 1)) - 1) =>
    hbandAt d ((Nat.le_succ _).trans (le_of_lt hlod)) hhi
  have hheadThin : ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W
        (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) - 1))) Xb
        ((M.opening_slot S.hc (c + 1)) - 1) X →
        Mh - 1 ≤ (M.derive_named S.E S.cfg X).h :=
    Restated.headThin_of_bandOn facts S Hs Xb hf (Nat.lt_of_lt_of_le (Nat.succ_pos _) hb)
      ((hvoteLeNext _ le_rfl).trans hhorC1)
      (hfrontD _ ((Nat.le_succ _).trans hb) le_rfl) (hbandAt _ ((Nat.le_succ _).trans hb) le_rfl)
      (hloVote.trans (facts.sch.vote_time_mono_slots S.E hb))
      (hrunR _ ((Nat.le_succ _).trans hb) le_rfl)
  have hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh c :=
    Restated.regime_of_gateOffFrameOn facts S Hs hpostC hhor
      (fun read hlor hhir w hw => hframe read (haPredC.trans hlor) hhir w hw)
  obtain ⟨B, hB, -⟩ := Restated.roundCeiling_succ_of_baseConeOn' facts S Hs Xb hf hHs hHsXb hcom hfb
    hpostC hpostVote hhorC1 hDrun hWrun (by rw [hDnErase]; exact hDW)
    hWthin (by rw [hDnErase]; exact hcarriers)
    (by rw [hDnErase]; exact ⟨hcone, hthin⟩)
    (by rw [hDnErase]; exact hframeDuty)
    (by rw [hDnErase]; exact hanchorDuty)
    hbandDuty hheadThin hreg hloC hloVote hA hrunInner
  have hboundary := Restated.boundaryConeAndThin_of_baseConeOn' facts S Hs Xb hf hHs hHsXb hcom
    hloVote hhorC1 ⟨hcone, hthin⟩ hframeDuty hanchorDuty hbandDuty hrunInner
  refine ⟨{ headThin := hheadThin
            entry := ⟨Dn, hDrun, ⟨Wn, hWrun, by rw [hDnErase]; exact hDW, hWthin⟩,
              by rw [hDnErase]; exact hcarriers, ?_⟩ }, B, hB⟩
  intro X hX
  obtain ⟨x, hxVote, hxCommittee, hXrun, hXemit⟩ := hX
  rw [hDnErase]
  exact Restated.honestHead_preceq_of_coneOn facts S Hs Xb hf hboundary.1 X.erase
    ⟨x, hxVote, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `1 ≤ c`, `t_GST ≤ S.a (c − 1)`,
    `S.a (c + 2)` is in the horizon, `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to
    `S.a (c + 2)`, `Restated.SeedRoundDischargeAtOn` holds for round `c`, round `c + 1` is a carrier
    round, `lo ≤ S.a (c − 1)` and the awake conditions hold, then some block `P` the proposer of
    round `c + 1`'s opening slot can propose has `Restated.NamedGateOffOpeningWindowAtOn` at `Mh`,
    and `Restated.GateOffOpeningAdoptionOn` holds for round `c + 1` and `P`. -/
theorem gateOffOpeningAdoption_succ_of_dischargeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh (c - 1) (c + 2))
    (hdis : Restated.SeedRoundDischargeAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh c)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs (c + 1))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ P : NamedBlock V,
      Restated.NamedGateOffOpeningWindowAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh (c + 1) P ∧
      Restated.GateOffOpeningAdoptionOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb (c + 1) P := by
  have hAc := hA c (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hlo (Nat.sub_lt hc Nat.one_pos))
  obtain ⟨-, B, hB⟩ := Restated.seedBoundaryAdoption_of_dischargeOn facts S Hs Xb hf hHs hHsXb hcom
    hfb hc hpost hhor hframe hdis hlo hAc
  have hpred2Succ : c - 1 + 2 ≤ c + 1 := by
    have h : c - 1 + 1 = c := Nat.sub_add_cancel hc
    exact le_of_eq (congrArg (· + 1) h)
  have hprop : S.E.proposer ((M.opening_slot S.hc (c + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (c + 1)))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  obtain ⟨cp, hcp⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
      (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
      (S.E.proposer (M.opening_slot S.hc (c + 1)))).cache
  obtain ⟨P, hP⟩ := proposal_some_along₆₈ facts S hf (M.opening_slot S.hc (c + 1)) cp hcp
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩ :=
    Restated.gateOffOpeningWindow_of_windowOn facts S Hs Xb hf hHs hHsXb (base := c - 1)
      hpost hpred2Succ hhor hprop cp hcp hP
      (fun read hlor hhir w hw => hframe read hlor hhir w hw) hlo
  have hwindowNamed : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh (c + 1) P :=
    ⟨⟨cp, hcp, hP⟩, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
  have hpredLe : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hcLe1 : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hcLe2 : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.le_succ c).trans (Nat.le_succ (c + 1)))
  have h1Le2 : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ (c + 1))
  have hprevFrontier : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1 - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1 - 1))) u).st.h_max = Mh := by
    intro u hu
    exact (hframe ((Restated.Vocabulary.Execution.Setup.a M S c)) hpredLe hcLe2 u hu).2
  have hcutLo : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (c + 1 + 1) :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (facts.gr.action_add_delta_le_next_Γ_neg1 S (c + 1))
  have hcutHi : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (c + 1 + 1) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) :=
    le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S (c + 1))
  have hcutFrame : ∀ w ∈ Hs (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (c + 1 + 1)),
      (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (c + 1 + 1))) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (c + 1 + 1))) w).st.h_j + 2 ≤ Mh := by
    intro w hw
    have h := hframe _ ((hpredLe.trans hcLe1).trans hcutLo) hcutHi w hw
    exact ⟨h.2, h.1⟩
  have hloPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1 - 1)) := hlo.trans hpredLe
  have hG0Lo : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc (c + 1) .g0 := by
    have hG1 : (Restated.Vocabulary.Execution.Setup.a M S (c + 1 - 1)) + S.E.Δ ≤ M.domain S.E S.hc (c + 1) .g1 :=
      prevAction_add_delta_le_domain_g1₆₈ facts S (Nat.succ_pos c)
    exact (hpredLe.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hG1)).trans
      (facts.gr.domain_le_domain_g0 S (c + 1) .g1)
  have hG0Hi : M.domain S.E S.hc (c + 1) .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) :=
    (facts.gr.domain_le_a S (c + 1) .g0).trans h1Le2
  have hloFrozen : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc (c + 1)) - 1) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
      (Nat.sub_lt hc Nat.one_pos : c - 1 < c)
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) :=
      (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
    exact hlo.trans (h2.trans (facts.sch.proposal_time_mono S.E
      ((Nat.le_succ _).trans (openingSucc_le_boundary₆₈ facts S c))))
  exact ⟨P, hwindowNamed,
    Restated.gateOff_openingLifecycle_of_roundCeilingOn facts S Hs Xb hf hHs hHsXb hcom hfb hcarrier hB
      hwindowNamed hprevFrontier
      (Restated.seedOpeningProposal_nextActiveDomainOn facts S Hs Xb hf hHs hHsXb hcarrier hwindowNamed
        hcutFrame hloPrev)
      (fun w hw => (hframe _ hG0Lo hG0Hi w hw).2)
      (fun w hw => (hframe _ hG0Lo hG0Hi w hw).1)
      hloPrev hloFrozen hA (by simpa only [Nat.add_sub_cancel] using hAc)⟩

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-! ## Helpers of the second half -/

/-- The vote instant of the slot after round `q`'s opening slot is at or before round `q`'s action
    instant. -/
private theorem openingSuccVote_le_action₆₈s (facts : Record.Facts M) (S : Setup V) (q : Round) :
    M.vote_time S.E ((M.opening_slot S.hc q) + 1) ≤ Restated.Vocabulary.Execution.Setup.a M S q := by
  rw [Restated.a_eq_confirmation_opening_l58 facts S q]
  exact le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
    (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E _)

/-- The slot after round `c`'s opening slot is at or before the last slot of round `c`. -/
private theorem openingSucc_le_boundary₆₈s (facts : Record.Facts M) (S : Setup V) (c : Round) :
    (M.opening_slot S.hc c) + 1 ≤ (M.opening_slot S.hc (c + 1)) - 1 := by
  rw [facts.gr.opening_slot_succ S.hc c]
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left hR (M.opening_slot S.hc c))

/-- A slot `d` from round `c`'s opening slot to its last slot is a slot of round `c`. -/
private theorem seedEntryRoundOf₆₈s (facts : Record.Facts M) (S : Setup V) {c : Round} {d : Slot}
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

/-- The store a tick at `t` hands its first duty, staged from the store `st`, has the FG root of
    `st`. -/
private theorem tickStore_fgRoot₆₈s (facts : Record.Facts M) {S : Setup V} (st : M.S) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t)).toFG =
      M.get_fg_root (M.toHealing st).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

omit [Fintype V] in
/-- A named block's parent is an ancestor of it. -/
private theorem parent_preceq_self₆₈s (B : NamedBlock V) : NamedBlock.Preceq B.parent B :=
  (priv% Proofs.Vocabulary.Execution.SeedFreshPromotion
    DecoupledConsensusModel.Proofs.HealingSurface.seedFresh_parent_preceq_self) B

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₈s {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the `h_max` of
    `n`'s core store. -/
private theorem tickStore_h_max₆₈s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the justified
    height `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₆₈s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

open scoped DC in
/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₈s (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₈s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₈s S rho hsorted]
  exact (hW _).1

/-- At every node state `n`, the voter-filtered tree, the voter view, the voter support view and the
    head computed from them each have an outcome. -/
private theorem exists_headOutcome₆₈s (facts : Record.Facts M) (S : Setup V) (n : M.N) :
    ∃ (Tt : Finset (Block V)) (L L' : Finset (GoldfishVote V)) (Hd : Block V),
      M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt ∧
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd := by
  obtain ⟨Tt, hTt⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache)
    S.E S.hc (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1)
  exact ⟨Tt, L, L', Hd, hTt, hL, hL', hHd⟩

/-- Along `W`, under the hypotheses of `gateOffOpeningAdoption_succ_of_dischargeOn`,
    `Restated.SeedBandCarrierCoverAtOn` holds for round `c + 1`: some run block at height at least
    `Mh − 1` is an ancestor of every round-`(c + 1)` carrier of every member of the set for
    `S.a (c + 1)`. -/
theorem seedBandCarrierCover_succ_of_dischargeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 2))
    (hdis : Restated.SeedRoundDischargeAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb
      Mh c)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs (c + 1))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh (c + 1)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1)))) := by
  obtain ⟨P, hwindow, hadoption⟩ := Restated.gateOffOpeningAdoption_succ_of_dischargeOn facts S Hs Xb hf hHs
    hHsXb hcom hfb hc hpost hhor hframe hdis hcarrier hlo hA
  exact Restated.seedBandCarrierCover_of_adoption_windowOn facts S Hs Xb
    (hwindow.parentHeight.trans (facts.cs.derive_height_mono S.E S.cfg (parent_preceq_self₆₈s P)))
    hadoption

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `S.a c` is in the horizon, `Restated.GateOffFrameAtOn` at `Mh` holds from
    `S.a (c − 1)` to `S.a c`, every head a member of the set for `vote_time (o + 1)` can compute at
    its vote-duty read erases a run block at height at least `Mh − 1`, `T` is an ancestor of the
    finalized block of a member `v` of the set for `S.a c` just before `S.a c`, and
    `lo ≤ vote_time (o + 1)`, then every committee member of `o + 1` in the set for its vote instant
    voted along `W` a run block that is a descendant of `T`. -/
theorem secondSlotCone_of_rootBelowOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {c : Round}
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) c)
    (hband : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache ⇢ cw →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw
      ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {T : Block V}
    (hT : Block.Preceq T
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.F)
    (hgat : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1))
    (hrun : ∀ w ∈ S.E.committee ((M.opening_slot S.hc c) + 1),
      w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc ((M.opening_slot S.hc c) + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq T X) := by
  have hpredLe : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hvote1Hor : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤ rho.horizon :=
    (openingSuccVote_le_action₆₈s facts S c).trans hhor
  intro w hw hwCommittee
  obtain ⟨cw, hcw⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
    (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache
  obtain ⟨Tt, L, L', Hd, hTt, hL, hL', hHd⟩ := exists_headOutcome₆₈s facts S
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
        (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw)
  obtain ⟨Hn, hHerase, hHrun, hHband⟩ := hband w hw cw hcw Tt hTt L hL L' hL' Hd hHd
  refine ⟨Hn, ?_, hHrun, ?_⟩
  · exact preceq_trans_Preceq hT
      (Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hv
        (hframe ((Restated.Vocabulary.Execution.Setup.a M S c)) hpredLe le_rfl v hv).1 hHrun hHband)
  · rw [hHerase]
    exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos _) hwCommittee
      hvote1Hor hgat cw hcw (hrun w hwCommittee hw) Tt hTt L hL L' hL' Hd hHd

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `secondSlotCone_of_rootBelowOn'`, if `na` is a round-`c` action read of
    `v` along `W`, `A` is a carrier it can select, and `A` is the FG root of `na`'s store, then
    every committee member of `o + 1` in the set for its vote instant voted along `W` a run block
    that is a descendant of `A`. -/
theorem secondSlotCone_of_rootTargetOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {c : Round}
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) c)
    (hband : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache ⇢ cw →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw
      ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
      (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2)
    (A : Block V)
    (hA : M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
      (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ A)
    (hT : A = M.get_fg_root (M.toHealing na.st.core).toFG)
    (hgat : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1))
    (hrun : ∀ w ∈ S.E.committee ((M.opening_slot S.hc c) + 1),
      w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc ((M.opening_slot S.hc c) + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq A X) := by
  have hpredLe : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hfr : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.h_j + 2 ≤ Mh ∧
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.h_max = Mh :=
    hframe ((Restated.Vocabulary.Execution.Setup.a M S c)) hpredLe le_rfl v hv
  refine Restated.secondSlotCone_of_rootBelowOn' facts S Hs Xb hf hHsXb hhor hframe hband hv ?_ hgat
    hrun
  rw [hT, Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts S rho v c
      _ (mem_stateBeforeTime_along₆₈s hf.sorted hf.onePath _) na hna,
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts hfr.1 hfr.2]
  exact (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority, if `1 ≤ c`, `lo ≤ S.a (c − 1)`, `S.a (c + 1)` is in the
    horizon, `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to `S.a (c + 1)`, the
    heads of the voters of slots `o` and `o + 1` erase run blocks at height at least `Mh − 1`, `A`
    is a carrier of a round-`c` action read `na` of a member `v` of the set for `S.a c`, the anchors
    of the slot-`(o + 1)` voters are compatible with `A`, and `A` is an ancestor of the live
    confirmation of `na`'s store, then every committee member of `o + 1` in the set for its vote
    instant voted along `W` a run block that is a descendant of `A`. -/
theorem secondSlotCone_of_clearOn' (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hbandO : ∀ u ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c))),
      ∀ cu : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) u).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc c)))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) u).cache ⇢ cu →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) u).st
          (M.vote_time S.E ((M.opening_slot S.hc c))))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) u).record cu
      ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
    (hband1 : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache ⇢ cw →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw
      ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
      (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2)
    (A : Block V)
    (hA : M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
      (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ A)
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache ⇢ cw →
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw).st.core.s) ⇢ B →
        Block.compatible B A = true)
    (hclear : Block.Preceq A na.st.core.live_confirmed) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq A X) := by
  have hoPos : 0 < (M.opening_slot S.hc c) := by
    have h := facts.gr.opening_slot_succ S.hc (c - 1)
    rw [Nat.sub_add_cancel hc] at h
    rw [h]
    exact lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two) (Nat.le_add_left _ _)
  have hoo' : (M.opening_slot S.hc c) + 2 ≤ (M.opening_slot S.hc (c + 1)) := by
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left hR _
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S c) = M.confirmation_time S.E ((M.opening_slot S.hc c)) :=
    Restated.a_eq_confirmation_opening_l58 facts S c
  have hpredLe : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon := haCSucc.trans hhor
  have hframeC : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) c :=
    fun read hlor hhir w hw => hframe read hlor (hhir.trans haCSucc) w hw
  have hpredProp : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
  have hpostProp : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) :=
    hpost.trans hpredProp
  have hvoteO_le : M.vote_time S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := by
    rw [hSc]
    exact facts.sch.Protocol_vote_time_le_confirmation_time S.E _
  have hpredVoteO : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E ((M.opening_slot S.hc c)) :=
    hpredProp.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _))
  have hpostVoteO : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c)) :=
    hpost.trans hpredVoteO
  have hcutO_le : M.support_cutoff S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hvote1Action : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    openingSuccVote_le_action₆₈s facts S c
  have hpredVote1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    hpredVoteO.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _))
  have hpostVote1 : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    hpost.trans hpredVote1
  have hwinC : lo ≤ M.early S.E S.hc c .g1 - S.E.Δ := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
    have h2 := facts.gr.q10_early_g2_le_early_g1 S c
    have h3 : lo ≤ M.a S.hc S.E.Δ (c - 1) := hpost
    linarith
  have hrunO : ∀ x ∈ S.E.committee (M.opening_slot S.hc c),
      x ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc c)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E (M.opening_slot S.hc c))) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc (M.opening_slot S.hc c)) := by
    intro x _ hx j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc c)) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc c]
      exact hwinC
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj
      (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hx) hwin
  have hrunO1 : ∀ w ∈ S.E.committee ((M.opening_slot S.hc c) + 1),
      w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc ((M.opening_slot S.hc c) + 1)) := by
    intro w _ hw j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc ((M.opening_slot S.hc c) + 1)) .g1 - S.E.Δ := by
      rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc c]
      exact hwinC
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  have hconf1 : M.confirmation_time S.E ((M.opening_slot S.hc c) + 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S (c + 1)]
    exact facts.sch.confirmation_time_mono S ((Nat.le_succ _).trans hoo')
  have hconfOHor : M.confirmation_time S.E ((M.opening_slot S.hc c)) ≤ rho.horizon := by
    rw [← hSc]
    exact hhorC
  have hframeV1 : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.h_max = Mh :=
    fun w hw => hframe _ hpredVote1 (hvote1Action.trans haCSucc) w hw
  have hwa : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S c) :=
    mem_stateBeforeTime_along₆₈s hf.sorted hf.onePath _
  have hna' := hna
  obtain ⟨cv, hcv, stv, hstv, hnaEq⟩ := hna'
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot facts S rho v c
      _ hwa na hna with
    ⟨C, hgen, hCeq⟩ | ⟨R, hReq, hRlive⟩
  · rw [← hCeq] at hclear
    have hTrun : ∃ Tn : NamedBlock V, Tn.erase = A ∧ Restated.RunBlockOn M S rho W Xb Tn :=
      Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hv)
        ((Restated.Vocabulary.Execution.Setup.a M S c))
        (Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v c
          _ hwa na hna A2 hA2 A hA)
    have hcv' : M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc c)))) v).st.core.toHealing
        (M.confirmation_time S.E ((M.opening_slot S.hc c)))
        (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc c)))) v).cache ⇢ cv := by
      rw [← hSc]
      exact hcv
    have hgen' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
        S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc c)))) v).st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc c)))) ((M.opening_slot S.hc c)) C := by
      have h := hgen
      rw [hnaEq, facts.nd.mkNode_cache, hSc] at h
      exact h
    obtain ⟨x, hx, hxCommittee, hCx⟩ :=
      Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts S Hs Xb hf hHs hHsXb hcom
        (hHs _ _ hcutO_le hv) hoPos hpostVoteO hconfOHor cv hcv' hgen' hrunO
    have hxVote : x ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hx
    obtain ⟨cu, hcu⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).st.core.toHealing
      (M.vote_time S.E ((M.opening_slot S.hc c)))
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).cache
    obtain ⟨Tu, Lu, Lu', Hu, hTu, hLu, hLu', hHu⟩ := exists_headOutcome₆₈s facts S
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).st
          (M.vote_time S.E ((M.opening_slot S.hc c))))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).record cu)
    obtain ⟨Hx, hHxErase, hHxRun, hHxBand⟩ := hbandO x hxVote cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu
    have hCHx : Block.Preceq C Hx.erase := by
      rw [hHxErase]
      exact hCx cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu
    have hframe1 : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
          ((M.opening_slot S.hc c) + 1)).h_max = Mh ∧
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
          ((M.opening_slot S.hc c) + 1)).h_j + 2 ≤ Mh ∧
        (Block.Preceq (M.get_fg_root
            (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
              (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
              ((M.opening_slot S.hc c) + 1))).toFG) A ∨
          Block.Preceq A (M.get_fg_root
            (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
              (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
              ((M.opening_slot S.hc c) + 1))).toFG)) := by
      intro w hw
      have hF := Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw (hframeV1 w hw).1
        hHxRun hHxBand
      have hcmp : Block.Preceq (M.get_fg_root (M.toHealing
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core).toFG) A ∨
          Block.Preceq A (M.get_fg_root (M.toHealing
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core).toFG) := by
        rw [Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts (hframeV1 w hw).1
          (hframeV1 w hw).2]
        exact preceq_linear_Preceq hF (preceq_trans_Preceq hclear hCHx)
      refine ⟨?_, ?_, ?_⟩
      · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₈s facts]
        exact (hframeV1 w hw).2
      · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₆₈s facts]
        exact (hframeV1 w hw).1
      · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₈s facts]
        exact hcmp
    exact Restated.baseCone_succ_of_genuineSupporter_rootComparableOn facts S Hs Xb hf hHs hHsXb
      (by rw [← hSc]; exact hv) hpostProp (hconf1.trans hhor) cv hcv' hgen' hclear hTrun
      hframe1
      ⟨x, hxVote, cu, hcu, Tu, Lu, Lu', Hu, hTu, hLu, hLu', hHu, Hx, hHxErase, hHxRun, hCHx, hHxBand⟩
      hanchor hrunO1
  ·
    rw [← hRlive] at hclear
    have hfr : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.h_max = Mh :=
      hframe ((Restated.Vocabulary.Execution.Setup.a M S c)) hpredLe haCSucc v hv
    refine Restated.secondSlotCone_of_rootBelowOn' facts S Hs Xb hf hHsXb hhorC hframeC hband1 hv ?_ hpostVote1
      hrunO1
    have hR' : R = (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.F := by
      rw [hReq, tickStore_fgRoot₆₈s facts]
      exact Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts hfr.1 hfr.2
    rw [← hR']
    exact hclear

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `1 ≤ c`, `lo ≤ S.a (c − 1)`,
    `S.a (c + 1)` is in the horizon, `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to
    `S.a (c + 1)`, round `c` is ready, the voters' heads erase run blocks at height at least
    `Mh − 1`, the slot-`(o + 1)` anchors are compatible with every round-`c` carrier of the set for
    `S.a c`, each such action read has a raw grade-2 block, `lo ≤ opening (c − η_SG)` and the awake
    condition holds at `c − 1`, then for every round-`c` carrier `A` of a member of the set for
    `S.a c`, the slot-`(o + 1)` votes of the set form a cone over `A`. -/
theorem seedClaim1_of_partsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    (hband : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cw →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cw
      ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
    (hanchor1 : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache ⇢ cw →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ B →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
          (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2 →
      ∀ A : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
          (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ A →
      Block.compatible B A = true)
    (hg2 : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S na c)
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
          (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2 →
      ∀ A : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
          (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ A →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
        (fun X => Block.Preceq A X) := by
  have hb := openingSucc_le_boundary₆₈s facts S c
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon := haCSucc.trans hhor
  have hframeC : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) c :=
    fun read hlor hhir w hw => hframe read hlor (hhir.trans haCSucc) w hw
  have hbandO := hband ((M.opening_slot S.hc c)) le_rfl ((Nat.le_succ _).trans hb)
  have hband1 := hband ((M.opening_slot S.hc c) + 1) (Nat.le_succ _) hb
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have hpredVote1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) :=
      (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
    exact h2.trans ((le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _)).trans
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _)))
  have hpostVote1 : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    hpost.trans hpredVote1
  have hrunO1 : ∀ w ∈ S.E.committee ((M.opening_slot S.hc c) + 1),
      w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc ((M.opening_slot S.hc c) + 1)) := by
    intro w _ hw j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc ((M.opening_slot S.hc c) + 1)) .g1 - S.E.Δ := by
      rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc c]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
      have h2 := facts.gr.q10_early_g2_le_early_g1 S c
      have h3 : lo ≤ M.a S.hc S.E.Δ (c - 1) := hpost
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  intro v hv na hna A2 hA2 A hAc
  have hwa : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S c) :=
    mem_stateBeforeTime_along₆₈s hf.sorted hf.onePath _
  have hnaAt : na ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v c :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)), hwa, hna⟩
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract na.cache) S.E S.hc
    (M.toHealing na.st.core) c
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers facts S rho v c na hnaAt g hg
      A2 hA2 A hAc with
    ⟨-, hclear, -⟩ | ⟨Q, hQ, hTQ⟩ | ⟨-, -, hTeq⟩ | ⟨-, hnoRaw, -⟩
  · exact Restated.secondSlotCone_of_clearOn' facts S Hs Xb hf hHs hHsXb hcom hc hpost hhor hframe hbandO
      hband1 hv na hna A2 hA2 A hAc
      (fun w hw cw hcw B hB => hanchor1 w hw cw hcw B hB v hv na hna A2 hA2 A hAc) hclear
  · rw [hTQ]
    have hQ' : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S na c ⇢ some Q := by
      rw [← hQ]
      exact returns_map_intro₆₈s (fun g => g.Q2) _ g hg
    exact Restated.secondSlotCone_of_grade2On' facts S Hs Xb hf hHs hHsXb hfb hc hpost hhorC hframeC hready hv
      na hna hQ' hloOpen hA
  · exact Restated.secondSlotCone_of_rootTargetOn' facts S Hs Xb hf hHsXb hhorC hframeC hband1 hv
      na hna A2 hA2 A hAc hTeq hpostVote1 hrunO1
  · exact absurd (hg2 v hv na hna g hg) hnoRaw

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `seedClaim1_of_partsOn`, with the anchors at every duty of round `c`
    from `o + 1` to its last slot compatible with every round-`c` carrier,
    `Restated.SeedRoundDischargeAtOn` holds for round `c` along `W`. -/
theorem seedRoundDischarge_of_partsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    (hband : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cw →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cw
      ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
    (hanchor : ∀ d : Slot, (M.opening_slot S.hc c) + 1 ≤ d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cw →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cw
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ B →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
          (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2 →
      ∀ A : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
          (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ A →
      Block.compatible B A = true)
    (hg2 : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S na c)
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    Restated.SeedRoundDischargeAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh c := by
  have hb := openingSucc_le_boundary₆₈s facts S c
  refine { claim1 := ?_, anchorCompat := ?_, headBand := ?_ }
  · exact Restated.seedClaim1_of_partsOn facts S Hs Xb hf hHs hHsXb hcom hfb hc hpost hhor hframe hready hband
      (hanchor _ le_rfl hb) hg2 hloOpen hA
  · intro d hlod hhi
    exact hanchor d (le_of_lt hlod) hhi
  · exact hband

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `t_GST ≤ S.a r0`,
    `Restated.SeedBandReachFromOn`, `Restated.SeedAnchorCompatFromOn` and `Restated.SeedRawG2FromOn`
    hold from `r0`, `lo ≤ S.a r0`, `lo ≤ opening (r0 + 1 − η_SG)` and the awake conditions hold,
    then `Restated.SeedDischargeFromOn` holds from `r0`. -/
theorem seedDischargeFrom_of_partsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {r0 : Round}
    (hpost0 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hK5 : Restated.SeedBandReachFromOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb r0)
    (hK3 : Restated.SeedAnchorCompatFromOn M S rho (fun t => W (strictEventIndex rho t)) Hs r0)
    (hK2 : Restated.SeedRawG2FromOn M S rho (fun t => W (strictEventIndex rho t)) Hs r0)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.SeedDischargeFromOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb r0 := by
  intro Mh base c hbase hc hbaseC hpost hhor2 hframe2
  have hbase2C : base + 2 ≤ c :=
    (Nat.add_le_add_left (by decide : 2 ≤ 3) base).trans hbaseC
  have hbase1Pred : base + 1 ≤ c - 1 := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.add_assoc] using hbase2C
  have hr02C : r0 + 2 ≤ c :=
    (Nat.add_le_add_right hbase 2).trans hbase2C
  have hr0Pred : r0 ≤ c - 1 :=
    Nat.le_sub_of_add_le ((Nat.add_le_add_left (by decide : 1 ≤ 2) r0).trans hr02C)
  have hcSucc : c + 1 ≤ c + 2 := Nat.le_succ _
  have hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon := (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hcSucc).trans hhor2
  have hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1) :=
    fun read hlor hhir w hw => hframe2 read
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbase1Pred).trans hlor)
      (hhir.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hcSucc)) w hw
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)).trans hhor
  have hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c :=
    Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_gst_le_a facts S hpost0 hr02C hhorC
  have hloC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0Pred)
  have hloOpenC : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right ((Nat.add_le_add_left (by decide : 1 ≤ 2) r0).trans hr02C) _))
  have hg2 := hK2 Mh c hc hr02C hpost hhor hframe
  refine Restated.seedRoundDischarge_of_partsOn facts S Hs Xb hf hHs hHsXb hcom hfb hc hloC hhor hframe hready
    (hK5 Mh c hc hr02C hpost hhor hframe) ?_ hg2 hloOpenC
    (hA (c - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hlo
      (Restated.lt_pred_of_add_two_le_l54 hr02C)))
  intro d hlod hhi w hw cw hcw n B hB v hv na hna A2 hA2 A hAc
  rcases hK3 Mh c hc hr02C hpost hhor hframe d hlod hhi w hw v hv cw hcw B hB na hna A2 hA2 A hAc with
    h | hnoRaw
  · exact h
  · exact absurd (hg2 v hv na hna) hnoRaw

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, with the timeout-delay bound, the
    recurrence `Restated.MultiProposerRecurrenceOn` from `t₀`, `t_GST ≤ S.a r0`,
    `Restated.SeedPredPromotionInputsOn` and `Restated.SeedDischargeFromOn` from `r0`,
    `lo ≤ S.a r0`, `lo ≤ opening (r0 + 1 − η_SG)`, `t₀ ≤ S.a r0` and the awake conditions,
    `Restated.HeightProgressSeedFromOn` holds from `r0`. -/
theorem heightProgressSeedFrom_of_dischargeOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (hdelayBound : TimeoutDelayBound S delayExtra)
    {r0 gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hpred : Restated.SeedPredPromotionInputsOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb r0 delayExtra)
    (hdis : Restated.SeedDischargeFromOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb r0)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.HeightProgressSeedFromOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb r0 gap delayExtra := by
  refine Restated.heightProgressSeedFrom_of_carrierAdoptionOn facts S Hs Xb hf hHs hHsXb hcom hfb hrec hpost
    ?_ (Restated.seedPredCloser_of_timeoutDelayOn facts S Hs Xb hf hHs hHsXb hcom hfb hdelayBound hpred hrec
      hlo hloOpen ht₀ hA) hlo hloOpen ht₀ hA
  intro Mh base q hbase hq hpostBase hhor hframeSeed hcarrier
  have hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (base + 1) (q + 2) :=
    fun read hlor hhir w hw => hframeSeed read hlor hhir w hw
  obtain ⟨hq1, hq11, hbq1, hbq11, hbq1', hbq11', hq1succ, hq12, hbq2, hbq21⟩ :=
    (sec% entry_nat') hq
  constructor
  · have hpost' : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
      hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbq1')
    have hlo' : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
      hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (hbase.trans hbq1'))
    have hframe' : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
        (q - 1) (q + 2) :=
      fun read hlor hhir w hw => hframe read ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbq1).trans hlor) hhir w hw
    exact (Restated.seedBoundaryAdoption_of_dischargeOn facts S Hs Xb hf hHs hHsXb hcom hfb hq1 hpost' hhor
      hframe' (hdis Mh base q hbase hq1 hbq2 hpost' hhor hframe) hlo'
      (hA q (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hlo' (Nat.sub_lt hq1 Nat.one_pos)))).1
  · have hpost' : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1 - 1)) :=
      hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbq11')
    have hlo' : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1 - 1)) :=
      hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (hbase.trans hbq11'))
    have hhor' : (Restated.Vocabulary.Execution.Setup.a M S (q - 1 + 2)) ≤ rho.horizon :=
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq12).trans hhor
    have hframe' : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
        (q - 1 - 1) (q - 1 + 2) :=
      fun read hlor hhir w hw => hframe read ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbq11).trans hlor)
        (hhir.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq12)) w hw
    have hframeDis : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
        (base + 1) (q - 1 + 2) :=
      fun read hlor hhir w hw => hframe read hlor
        (hhir.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq12)) w hw
    have hcarrier' : Restated.ProposerCarrierAtOn M S Hs (q - 1 + 1) := by
      rw [hq1succ]
      exact hcarrier
    have h := Restated.seedBandCarrierCover_succ_of_dischargeOn facts S Hs Xb hf hHs hHsXb hcom hfb hq11
      hpost' hhor' hframe' (hdis Mh base (q - 1) hbase hq11 hbq21 hpost' hhor' hframeDis)
      hcarrier' hlo' hA
    rw [hq1succ] at h
    exact h

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the weight bound, if `lo ≤ S.a r0` and the awake conditions hold, then
    `Restated.SeedBandReachFromOn` holds from `r0`. -/
theorem seedBandReachFrom_of_canonicityOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs) (r0 : Round)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.SeedBandReachFromOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb r0 := by
  intro Mh c hc hr0 _hpost hhor hframe d hlod hhi w hw cw hcw
  have hloC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S
    (Nat.le_sub_of_add_le ((Nat.add_le_add_left (by decide : 1 ≤ 2) r0).trans hr0)))
  exact Restated.voteDutyHead_band_at_dutyOn facts S Hs Xb hf hHs hHsXb hfb hc hframe hloC hhor hw hlod hhi
    (seedEntryRoundOf₆₈s facts S hlod hhi)
    (hA (c - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hlo
      (Restated.lt_pred_of_add_two_le_l54 hr0))) cw hcw

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the weight bound, if `lo ≤ S.a r0` and the awake conditions hold, then
    `Restated.SeedRawG2FromOn` holds from `r0`. -/
theorem seedRawG2From_of_canonicityOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs) (r0 : Round)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.SeedRawG2FromOn M S rho (fun t => W (strictEventIndex rho t)) Hs r0 := by
  intro Mh c hc hr0 _hpost hhor hframe v hv
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hpredLe : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hloC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S
    (Nat.le_sub_of_add_le ((Nat.add_le_add_left (by decide : 1 ≤ 2) r0).trans hr0)))
  have hdomG2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g2 := by
    have h := Restated.action_add_delta_le_domain_g2_succ_l54 facts S (c - 1)
    rw [Nat.sub_add_cancel hc] at h
    exact le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) h
  have hdomG2hi : M.domain S.E S.hc c .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    (facts.gr.domain_le_a S c .g2).trans haCSucc
  exact Restated.nodeRawG2_of_gateOffFrameOn facts S Hs Xb hf hHs hHsXb hfb (Nat.succ_le_iff.mp hc)
    (haCSucc.trans hhor) hloC
    (fun u hu => (hframe ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) le_rfl (hpredLe.trans haCSucc) u hu).2)
    (fun x hx => (hframe _ hdomG2 hdomG2hi x hx).2)
    (fun x hx => (hframe _ hdomG2 hdomG2hi x hx).1)
    (hA (c - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hlo
      (Restated.lt_pred_of_add_two_le_l54 hr0))) v
    (hHs _ _ (facts.gr.domain_le_a S c .g2) hv)

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the weight bound, if `t_GST ≤ S.a r0`, `lo ≤ S.a r0`,
    `lo ≤ opening (r0 + 1 − η_SG)` and the awake conditions hold, then
    `Restated.SeedAnchorCompatFromOn` holds from `r0`. -/
theorem seedAnchorCompatFrom_of_canonicityOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (_hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (r0 : Round) (hpost0 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.SeedAnchorCompatFromOn M S rho (fun t => W (strictEventIndex rho t)) Hs r0 := by
  intro Mh c hc hr0 _hpost hhor hframe d hlod hhi w hw v hv cw hcw nw B hB na hna gc st k A2 hA2 G hG
  have hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c :=
    Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_gst_le_a facts S hpost0 hr0
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)).trans hhor)
  have hloC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S
    (Nat.le_sub_of_add_le ((Nat.add_le_add_left (by decide : 1 ≤ 2) r0).trans hr0)))
  have hloOpenC : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right ((Nat.add_le_add_left (by decide : 1 ≤ 2) r0).trans hr0) _))
  exact Or.inl (Restated.preparedAnchor_compatible_carrier_of_gateOff_relativeOn facts
    S Hs Xb hf hHs hHsXb hfb hc hframe hloC hhor hready hw hv hlod hhi
      (seedEntryRoundOf₆₈s facts S ((Nat.le_succ _).trans hlod) hhi) hloOpenC
      (hA (c - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hlo
        (Restated.lt_pred_of_add_two_le_l54 hr0)))
      cw hcw B hB na hna A2 hA2 G hG)

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `t_GST ≤ S.a r0`,
    `lo ≤ S.a r0`, `lo ≤ opening (r0 + 1 − η_SG)` and the awake conditions hold, then
    `Restated.SeedDischargeFromOn` holds from `r0`. -/
theorem seedDischargeFrom_of_canonicityOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs) {r0 : Round}
    (hpost0 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.SeedDischargeFromOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb r0 :=
  Restated.seedDischargeFrom_of_partsOn facts S Hs Xb hf hHs hHsXb hcom hfb hpost0
    (Restated.seedBandReachFrom_of_canonicityOn facts S Hs Xb hf hHs hHsXb hfb r0 hlo hA)
    (Restated.seedAnchorCompatFrom_of_canonicityOn facts S Hs Xb hf hHs hHsXb hcom hfb r0 hpost0 hlo hloOpen
      hA)
    (Restated.seedRawG2From_of_canonicityOn facts S Hs Xb hf hHs hHsXb hfb r0 hlo hA) hlo hloOpen hA

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, with the timeout-delay bound, the
    recurrence `Restated.MultiProposerRecurrenceOn` from `t₀`, `t_GST ≤ S.a r0`,
    `Restated.SeedPredPromotionInputsOn`, `lo ≤ S.a r0`, `lo ≤ opening (r0 + 1 − η_SG)`,
    `t₀ ≤ S.a r0` and the awake conditions, `Restated.HeightProgressSeedFromOn` holds from `r0`. -/
theorem heightProgressSeedFrom_of_canonicityOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (hdelayBound : TimeoutDelayBound S delayExtra)
    {r0 gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hpred : Restated.SeedPredPromotionInputsOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb r0 delayExtra)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.HeightProgressSeedFromOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb r0 gap delayExtra :=
  Restated.heightProgressSeedFrom_of_dischargeOn facts S Hs Xb hf hHs hHsXb hcom hfb hdelayBound hrec hpost
    hpred (Restated.seedDischargeFrom_of_canonicityOn facts S Hs Xb hf hHs hHsXb hcom hfb hpost hlo hloOpen hA)
    hlo hloOpen ht₀ hA

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
open DecoupledConsensusModel.Proofs.Optimistic
local macro "sec% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `1 ≤ c`, `lo ≤ S.a (c − 1)`,
    `S.a (c + 1)` is in the horizon, `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to
    `S.a (c + 1)`, round `c` is ready, `lo ≤ opening (c − η_SG)` and the awake condition holds at
    `c − 1`, then `Restated.SeedRoundDischargeAtOn` holds for round `c`. -/
theorem seedRoundDischarge_of_canonicityOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    Restated.SeedRoundDischargeAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh c := by
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hpredLe : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hdomG2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g2 := by
    have h := Restated.action_add_delta_le_domain_g2_succ_l54 facts S (c - 1)
    rw [Nat.sub_add_cancel hc] at h
    exact le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) h
  have hdomG2hi : M.domain S.E S.hc c .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    (facts.gr.domain_le_a S c .g2).trans haCSucc
  have hg2 : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S na c := by
    intro v hv
    exact Restated.nodeRawG2_of_gateOffFrameOn facts S Hs Xb hf hHs hHsXb hfb (Nat.succ_le_iff.mp hc)
      (haCSucc.trans hhor) hpost
      (fun u hu => (hframe ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))) le_rfl (hpredLe.trans haCSucc) u hu).2)
      (fun x hx => (hframe _ hdomG2 hdomG2hi x hx).2)
      (fun x hx => (hframe _ hdomG2 hdomG2hi x hx).1) hA v
      (hHs _ _ (facts.gr.domain_le_a S c .g2) hv)
  refine Restated.seedRoundDischarge_of_partsOn facts S Hs Xb hf hHs hHsXb hcom hfb hc hpost hhor hframe hready
    (fun d hlod hhi w hw cw hcw => Restated.voteDutyHead_band_at_dutyOn facts S Hs Xb hf hHs hHsXb hfb hc hframe hpost
      hhor hw hlod hhi (seedEntryRoundOf₆₈s facts S hlod hhi) hA cw hcw)
    ?_ hg2 hloOpen hA
  intro d hlod hhi w hw cw hcw n B hB v hv na hna A2 hA2 A hAc
  exact Restated.preparedAnchor_compatible_carrier_of_gateOff_relativeOn facts
    S Hs Xb hf hHs hHsXb hfb hc hframe hpost hhor hready hw hv hlod hhi
      (seedEntryRoundOf₆₈s facts S ((Nat.le_succ _).trans hlod) hhi) hloOpen hA cw hcw B hB na hna A2 hA2 A hAc

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
open DecoupledConsensusModel.Proofs.Optimistic

end

end DecoupledConsensusModel.Sts.Restated
