import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_51b
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_66b
import Proofs.Claims.Restated.Claim13beRoute3_68
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_SeedCommonRootComplement
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_JustificationCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGTargetCanonicality
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecordClean
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
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The fresh FG source and the fixed-root lemmas over the record

Theorems on the FG source of an action read under a fixed-height justification root: its second-slot
and boundary cones, its bound by the parent of the next opening, and the fixed-root locks,
certificates, rows and promotion, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
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
private theorem stateBeforeTime_eq_strict₆₉ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₉ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₉ S rho hsorted]
  exact (hW _).1

/-- Every node state of the round-`r` action read from `before` has as its core store an outcome of
    the confirmation update of `before`'s store staged at round `r`'s action instant. -/
private theorem actionReadFrom_core₆₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state of the round-`r` action read from `before` has the `h_max` of `before`'s core
    store. -/
private theorem actionReadFrom_h_max₆₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₉ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _
      hX₀,
    facts.hd.setClock_toHealing_h_max]

/-- Every node state of the round-`r` action read from `before` has the FG root of `before`'s core
    store. -/
private theorem actionReadFrom_fgRoot₆₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₉ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- The round-`r` action read from any node state `before` has a node state. -/
private theorem actionReadFrom_nonempty₆₉ (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read can
    return some `g` and the SG vote selector on `g` some block. -/
private theorem exists_actionSG₆₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₉ facts S before r
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g
  exact ⟨n, hn, g, hg, B, hB⟩

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₉ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₆₉ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- If the grade read at `n` for round `r` can return `G`, then the grade-2 candidate read there can
    return `G.Q2`. -/
private theorem nodeQ2_of_read₆₉ (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₉ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

/-- Setting the clock of `st` keeps the FG root of its core store. -/
private theorem setClock_fgRoot₆₉ (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    M.get_fg_root (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, is the core store of `n`'s
    store with the clock set to the slot's vote instant. -/
private theorem voteStore_eq₆₉ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- The store a tick at `t` hands its first duty, staged from the store `st`, has the FG root of
    `st`. -/
private theorem tickStore_fgRoot₆₉ (facts : Record.Facts M) {S : Setup V} (st : M.S) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t)).toFG =
      M.get_fg_root (M.toHealing st).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the `h_max` of
    `n`'s core store. -/
private theorem tickStore_h_max₆₉ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the justified
    height `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₆₉ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

/-- The vote instant of the slot after round `q`'s opening slot is at or before round `q`'s action
    instant. -/
private theorem openingSuccVote_le_action₆₉ (facts : Record.Facts M) (S : Setup V) (q : Round) :
    M.vote_time S.E ((M.opening_slot S.hc q) + 1) ≤ Restated.Vocabulary.Execution.Setup.a M S q := by
  rw [Restated.a_eq_confirmation_opening_l58 facts S q]
  exact le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
    (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E _)

/-- The slot after round `c`'s opening slot is at or before the last slot of round `c`. -/
private theorem openingSucc_le_boundary₆₉ (facts : Record.Facts M) (S : Setup V) (c : Round) :
    (M.opening_slot S.hc c) + 1 ≤ (M.opening_slot S.hc (c + 1)) - 1 := by
  rw [facts.gr.opening_slot_succ S.hc c]
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left hR (M.opening_slot S.hc c))

/-- A slot `d` from round `c`'s opening slot to its last slot is a slot of round `c`. -/
private theorem seedEntryRoundOf₆₉ (facts : Record.Facts M) (S : Setup V) {c : Round} {d : Slot}
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

/-- At every node state `n`, the voter-filtered tree, the voter view, the voter support view and the
    head computed from them each have an outcome. -/
private theorem exists_headOutcome₆₉ (facts : Record.Facts M) (S : Setup V) (n : M.N) :
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

/-- If every member of the set for `domain r .g2` grades `C` 2 at its node state in
    `W (strictEventIndex rho (domain r .g2))`, `v` is in the set for `domain r .g0`, and `C` is
    active at a node state `n` of `v`'s round-`r` action read from
    `W (strictEventIndex rho (S.a r))`, then `C` is an ancestor of every SG vote `n` can select. -/
private theorem formsW_preceq_actionSGBlockAt₆₉ (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) {C : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 C ⇢ b → b = true)
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hactive : C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ G : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G → Block.Preceq C G := by
  have hvG2 : v ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hv
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hd
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) C
  have hbtrue : b = true := (hformsW v hvG2).2 b hb
  subst hbtrue
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
    nodeQ2_of_read₆₉ S n r G hG
  obtain ⟨Q, hQ, hCQ⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
      (hformsW v hvG2).1 hb n hn hactive _ hGq
  rw [hQ] at hGq
  exact Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hhor
    (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv) hlo n hn hGq hCQ

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
local macro "ffc% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Duties.Inputs.FreshFGSourceCapture)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority, if `1 ≤ c`, `lo ≤ S.a (c − 1)`, `S.a (c + 1)` is in the
    horizon, `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to `S.a (c + 1)`, the
    heads of the voters of slots `o` and `o + 1` erase run blocks at height at least `Mh − 1`, `C`
    is the erasure of a run block, the anchors of the slot-`(o + 1)` voters are compatible with `C`,
    and `C` is an ancestor of the live confirmation of a round-`c` action read `na` of a member `v`
    of the set for `S.a c`, then every committee member of `o + 1` in the set for its vote instant
    voted along `W` a run block that is a descendant of `C`. -/
theorem secondSlotCone_of_clearFGSourceOn (facts : Record.Facts M)
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
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {C : Block V}
    (hCrun : ∃ Cn : NamedBlock V, Cn.erase = C ∧ Restated.RunBlockOn M S rho W Xb Cn)
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
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
        Block.compatible B C = true)
    (hclear : Block.Preceq C na.st.core.live_confirmed) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq C X) := by
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
  have hpredVoteO : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E ((M.opening_slot S.hc c)) :=
    hpredProp.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _))
  have hpostVoteO : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c)) :=
    hpost.trans hpredVoteO
  have hcutO_le : M.support_cutoff S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hvote1Action : M.vote_time S.E ((M.opening_slot S.hc c) + 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    openingSuccVote_le_action₆₉ facts S c
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
    mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath _
  have hna' := hna
  obtain ⟨cv, hcv, stv, hstv, hnaEq⟩ := hna'
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot facts S rho v c
      _ hwa na hna with
    ⟨D, hgen, hDeq⟩ | ⟨R, hReq, hRlive⟩
  · rw [← hDeq] at hclear
    have hcv' : M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc c)))) v).st.core.toHealing
        (M.confirmation_time S.E ((M.opening_slot S.hc c)))
        (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc c)))) v).cache ⇢ cv := by
      rw [← hSc]
      exact hcv
    have hgen' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
        S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc c)))) v).st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc c)))) ((M.opening_slot S.hc c)) D := by
      have h := hgen
      rw [hnaEq, facts.nd.mkNode_cache, hSc] at h
      exact h
    obtain ⟨x, hx, hxCommittee, hDx⟩ :=
      Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts S Hs Xb hf hHs hHsXb hcom
        (hHs _ _ hcutO_le hv) hoPos hpostVoteO hconfOHor cv hcv' hgen' hrunO
    have hxVote : x ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hx
    obtain ⟨cu, hcu⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).st.core.toHealing
      (M.vote_time S.E ((M.opening_slot S.hc c)))
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).cache
    obtain ⟨Tu, Lu, Lu', Hu, hTu, hLu, hLu', hHu⟩ := exists_headOutcome₆₉ facts S
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).st
          (M.vote_time S.E ((M.opening_slot S.hc c))))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c)))) x).record cu)
    obtain ⟨Hx, hHxErase, hHxRun, hHxBand⟩ := hbandO x hxVote cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu
    have hDHx : Block.Preceq D Hx.erase := by
      rw [hHxErase]
      exact hDx cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu
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
              ((M.opening_slot S.hc c) + 1))).toFG) C ∨
          Block.Preceq C (M.get_fg_root
            (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
              (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
              ((M.opening_slot S.hc c) + 1))).toFG)) := by
      intro w hw
      have hcmp := Restated.fgRoot_comparable_of_bandWitnessOn facts S Hs Xb hf hHsXb hw
        (hframeV1 w hw).1 (hframeV1 w hw).2 hHxRun (preceq_trans_Preceq hclear hDHx) hHxBand
      refine ⟨?_, ?_, ?_⟩
      · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₉ facts]
        exact (hframeV1 w hw).2
      · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₆₉ facts]
        exact (hframeV1 w hw).1
      · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₉ facts]
        exact hcmp
    exact Restated.baseCone_succ_of_genuineSupporter_rootComparableOn facts S Hs Xb hf hHs hHsXb
      (by rw [← hSc]; exact hv) hpostProp (hconf1.trans hhor) cv hcv' hgen' hclear hCrun
      hframe1
      ⟨x, hxVote, cu, hcu, Tu, Lu, Lu', Hu, hTu, hLu, hLu', hHu, Hx, hHxErase, hHxRun, hDHx, hHxBand⟩
      hanchor hrunO1
  ·
    rw [← hRlive] at hclear
    have hfr : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.h_max = Mh :=
      hframe ((Restated.Vocabulary.Execution.Setup.a M S c)) hpredLe haCSucc v hv
    refine Restated.secondSlotCone_of_rootBelowOn' facts S Hs Xb hf hHsXb hhorC hframeC hband1 hv ?_ hpostVote1
      hrunO1
    have hR' : R = (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.F := by
      rw [hReq, tickStore_fgRoot₆₉ facts]
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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "ffc% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Duties.Inputs.FreshFGSourceCapture)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `1 ≤ c`,
    `Restated.GateOffFrameAtOn` at `Mh` holds from `S.a (c − 1)` to `S.a (c + 1)`,
    `lo ≤ S.a (c − 1)`, `S.a (c + 1)` is in the horizon, round `c` is grade-ready, the voters' heads
    of round `c` erase run blocks at height at least `Mh − 1`, the FG source read of a round-`c`
    action read of a member `v` of the set for `S.a c` can return `some C` with `C` the erasure of a
    run block, `lo ≤ opening (c − η_SG)` and the awake condition holds at `c − 1`, then every
    committee member of slot `o + 1` in the set for its vote instant voted along `W` a run block
    that is a descendant of `C`. -/
theorem freshFGSource_secondSlotConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
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
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {C : Block V}
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S na c ⇢ some C)
    (hCrun : ∃ Cn : NamedBlock V, Cn.erase = C ∧ Restated.RunBlockOn M S rho W Xb Cn)
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq C X) := by
  have hb := openingSucc_le_boundary₆₉ facts S c
  have hbandO := hband ((M.opening_slot S.hc c)) le_rfl ((Nat.le_succ _).trans hb)
  have hband1 := hband ((M.opening_slot S.hc c) + 1) (Nat.le_succ _) hb
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hsource' := hsource
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsource'
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₉ _ _ _).1 hsource'
  obtain ⟨Q, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract na.cache) S.E S.hc
    (M.toHealing na.st.core) c
  have hGQ : G.Q2 = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S na c ⇢ some Q := by
    have h := nodeQ2_of_read₆₉ S na c G hG
    rwa [hGQ] at h
  cases hwalk : M.deepest_clear (some Q)
      (M.toHealing na.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | none =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hwalk _ hsrc
      have hCQ : C = Q := Option.some_inj.mp h
      subst hCQ
      exact Restated.secondSlotCone_of_grade2On' facts S Hs Xb hf hHs hHsXb hfb hc hpost
        (haCSucc.trans hhor)
        (fun read hlor hhir w hw => hframe read hlor (hhir.trans haCSucc) w hw)
        ready hv na hna hq hloOpen hA
  | some B =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hwalk _ hsrc
      have hCB : C = B := Option.some_inj.mp h
      subst hCB
      have hclear : Block.Preceq C na.st.core.live_confirmed := by
        have h' := preceq_eq_true_iff_Preceq.mp (facts.gr.deepest_clear_preceq hwalk)
        rw [facts.sto.toHealing_live_confirmed] at h'
        exact h'
      exact Restated.secondSlotCone_of_clearFGSourceOn facts S Hs Xb hf hHs hHsXb hcom hc hpost hhor
        hframe hbandO hband1 hv hCrun na hna
        (fun w hw cw hcw =>
          Restated.preparedAnchor_compatible_freshFGSource_of_gateOff_relativeOn facts
            S Hs Xb hf hHs hHsXb hfb hc hframe hpost hhor ready hw hv (Nat.le_refl _)
            hb (seedEntryRoundOf₆₉ facts S (Nat.le_succ _) hb) na hna hsource hloOpen hA cw hcw)
        hclear

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
local macro "ffc% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Duties.Inputs.FreshFGSourceCapture)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `freshFGSource_secondSlotConeOn` without the head condition, if the FG
    source read of a round-`c` action read of `v` along `W` can return `some C`, the erasure of a
    run block `Cn` at height at least `Mh − 1`, then every committee member of round `c`'s last slot
    in the set for its vote instant voted along `W` a run block that is a descendant of `C`. -/
theorem freshFGSource_boundaryConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {C : Block V}
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S na c ⇢ some C)
    {Cn : NamedBlock V} (hCerase : Cn.erase = C) (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hCband : Mh - 1 ≤ (M.derive_named S.E S.cfg Cn).h)
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)
      (fun X => Block.Preceq C X) := by
  have hb := openingSucc_le_boundary₆₉ facts S c
  have hband : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d →
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
        Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h := by
    intro d hlo hhi w hw cw hcw
    exact Restated.voteDutyHead_band_at_dutyOn facts S Hs Xb hf hHs hHsXb hfb hc hframe hpost hhor hw
      hlo hhi (seedEntryRoundOf₆₉ facts S hlo hhi) hA cw hcw
  have hbaseCone := Restated.freshFGSource_secondSlotConeOn facts S Hs Xb hf hHs hHsXb hcom hfb hc
    hframe hpost hhor ready hband hv na hna hsource ⟨Cn, hCerase, hCrun⟩ hloOpen hA
  have hbaseThin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh ((M.opening_slot S.hc c) + 1) C := by
    have hbaseCone' : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
        (fun X => Block.Preceq Cn.erase X) := by
      rw [hCerase]
      exact hbaseCone
    have h := Restated.thinHonestHeadAt_of_thin_endpointOn facts S Hs Xb hf hHs hcom hCrun hCband
      hbaseCone'
    rw [hCerase] at h
    exact h
  have hvoteLoAt : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d →
      (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E d := by
    intro d hlo
    have hpredLt : c - 1 < c := Nat.sub_lt (Nat.succ_le_iff.mp hc) Nat.one_pos
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((facts.sch.proposal_time_mono S.E hlo).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d)))
  have hvoteHiAt : ∀ d : Slot, d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    intro d hdhi
    have hdNext : d ≤ (M.opening_slot S.hc (c + 1)) := hdhi.trans (Nat.sub_le _ _)
    refine (facts.sch.Protocol_vote_time_le_confirmation_time S.E d).trans ?_
    rw [Restated.a_eq_confirmation_opening_l58 facts S (c + 1)]
    exact facts.sch.confirmation_time_mono S hdNext
  have hframe' : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 → ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max = Mh ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_j + 2 ≤ Mh ∧
      (Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG) C ∨
        Block.Preceq C (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG)) := by
    intro d hdlo hdhi w hw
    have hlo : (M.opening_slot S.hc c) ≤ d :=
      (Nat.le_succ _).trans (Nat.le_of_lt hdlo)
    have hfr : (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.h_max = Mh :=
      hframe _ (hvoteLoAt d hlo) (hvoteHiAt d hdhi) w hw
    have hcmp := Restated.fgRoot_comparable_of_bandWitnessOn facts S Hs Xb hf hHsXb hw hfr.1 hfr.2
      hCrun (by rw [hCerase]; exact Proofs.ModelProperties.Preceq_self C) hCband
    refine ⟨?_, ?_, ?_⟩
    · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₉ facts]
      exact hfr.2
    · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₆₉ facts]
      exact hfr.1
    · rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₉ facts]
      exact hcmp
  have hpostVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c) + 1) :=
    hpost.trans (hvoteLoAt _ (Nat.le_succ _))
  have hrunInner : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d →
      d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
      ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d) := by
    intro d hdlo hdhi w _ hw j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
      rw [seedEntryRoundOf₆₉ facts S ((Nat.le_succ _).trans (Nat.le_of_lt hdlo)) hdhi]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
        (Nat.sub_lt (Nat.succ_le_iff.mp hc) Nat.one_pos)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S c
      have h3 : lo ≤ M.a S.hc S.E.Δ (c - 1) := hpost
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  exact (Restated.boundaryConeAndThin_of_baseConeOn' facts S Hs Xb hf hHs hHsXb hcom hpostVote hhor
    ⟨hbaseCone, hbaseThin⟩ hframe'
    (fun d hdlo hdhi w hw ch hch =>
      Restated.preparedAnchor_compatible_freshFGSource_of_gateOff_relativeOn facts
        S Hs Xb hf hHs hHsXb hfb hc hframe hpost hhor ready hw hv (Nat.le_of_lt hdlo) hdhi
        (seedEntryRoundOf₆₉ facts S ((Nat.le_succ _).trans (Nat.le_of_lt hdlo)) hdhi) na hna hsource
        hloOpen hA ch hch)
    (fun d hdlo hdhi w hw ch hch Tt hTt L hL L' hL' Hd hHd => by
      obtain ⟨Hn, he, hr, hh⟩ := hband d ((Nat.le_succ _).trans (Nat.le_of_lt hdlo)) hdhi w hw ch hch
        Tt hTt L hL L' hL' Hd hHd
      have hmax : (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.h_max = Mh :=
        (hframe _ (hvoteLoAt d ((Nat.le_succ _).trans (Nat.le_of_lt hdlo))) (hvoteHiAt d hdhi)
          w hw).2
      refine ⟨Hn, he, hr, ?_⟩
      rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₉ facts, hmax]
      exact hh) hrunInner).1

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
local macro "ffc% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Duties.Inputs.FreshFGSourceCapture)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `freshFGSource_boundaryConeOn`, if the proposer of the next opening slot
    is in the set for the support cutoff of round `c`'s last slot, `C` is in the filtered tree of
    its duty store, and `cp` is an outcome of its cache update at its proposal instant, then for
    every anchor outcome `A` of its proposal read `n` compatible with `C`, `C` is an ancestor of the
    parent of every proposal input `n` can produce. -/
theorem freshFGSource_preceq_nextOpeningParentOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {C : Block V}
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S na c ⇢ some C)
    {Cn : NamedBlock V} (hCerase : Cn.erase = C) (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hCband : Mh - 1 ≤ (M.derive_named S.E S.cfg Cn).h)
    (hprop : S.E.proposer ((M.opening_slot S.hc (c + 1))) ∈
      Hs (M.support_cutoff S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)))
    (hactive : C ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))).toFG)
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).cache ⇢ cp) :
    let n := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).record cp
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A →
      Block.compatible A C = true →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc (c + 1)))) (M.toHealing n.st.core) ⇢ I →
      Block.Preceq C I.parent := by
  have hcone := Restated.freshFGSource_boundaryConeOn facts S Hs Xb hf hHs hHsXb hcom hfb hc hframe
    hpost hhor ready hv na hna hsource hCerase hCrun hCband hloOpen hA
  have hb := openingSucc_le_boundary₆₉ facts S c
  have hopenPos : 0 < (M.opening_slot S.hc c) := facts.gr.opening_slot_pos_of_round_pos S.hc hc
  obtain ⟨s, hs⟩ : ∃ s : Slot, s = Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c :=
    ⟨_, rfl⟩
  have hs' : s = (M.opening_slot S.hc (c + 1)) - 1 := hs
  have hlo : (M.opening_slot S.hc c) ≤ s := by
    rw [hs']
    exact (Nat.le_succ _).trans hb
  have hlastPos : 0 < s := lt_of_lt_of_le hopenPos hlo
  have hlastSucc : (M.opening_slot S.hc (c + 1)) = s + 1 := by
    rw [hs']
    exact (Nat.sub_add_cancel
      (Nat.succ_le_iff.mpr (facts.gr.opening_slot_pos_of_round_pos S.hc (Nat.succ_pos c)))).symm
  have hpostLast : lo ≤ M.vote_time S.E s := by
    have hpredLt : c - 1 < c := Nat.sub_lt (Nat.succ_le_iff.mp hc) Nat.one_pos
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    exact hpost.trans (((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((facts.sch.proposal_time_mono S.E hlo).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _))))
  have hsupportHor : M.support_cutoff S.E s ≤ rho.horizon := by
    refine (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _).trans ?_
    refine (facts.sch.confirmation_time_mono S (show s ≤ M.opening_slot S.hc (c + 1) from ?_)).trans ?_
    · rw [hlastSucc]
      exact Nat.le_succ s
    · rw [← Restated.a_eq_confirmation_opening_l58 facts S (c + 1)]
      exact hhor
  rw [← hs] at hprop hcone
  rw [hlastSucc] at hprop hactive hcp ⊢
  exact Restated.coneTarget_preceq_nextProposedParent_namedOn facts S Hs Xb hf hHs hHsXb hcom
    hlastPos hpostLast hsupportHor hprop hcone hactive cp hcp

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `w`'s store in the world `wd` holds a fixed-height justification root at `H` along `W`, then
    some run block `J` along `W` erases to that store's justified block and has height `H − 1`. -/
theorem fixedRootJustificationRoot_target_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {W : Nat → V → M.N}
    {H : Height} {w : V} {read : Time} {wd : V → M.N}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read wd) :
    ∃ J : NamedBlock V,
      J.erase = (wd w).st.J ∧
        Restated.RunBlockOn M S rho W Xb J ∧
          (M.derive_named S.E S.cfg J).h = H - 1 :=
  Restated.claimOne_fixedHeightJustificationRoot_target_namedOn facts S Hs Xb h

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `w`'s store before `read` holds a fixed-height justification root at `Mh`,
    `0 < q`, `B` is the proposal of round `q`'s proposal lifecycle packet, every member of the set
    for `S.a (q − 1)` has the justified block as its FG root and `h_max = Mh`, the largest `h_max`
    over the set for the proposal instant of `q`'s opening slot is at most `Mh`, and `lo` is at most
    that instant, then the justified block is an ancestor of `B` and `B` is at height `Mh − 1` or
    `Mh`. -/
theorem fixedRootClaimFour_height_pred_or_currentOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {Mh : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh w read
      (W (strictEventIndex rho read)))
    {q : Round} (hq : 0 < q) {B : NamedBlock V}
    {w₁ w₂ : V → M.N}
    (hpacket : Restated.NamedSGProposalLifecyclePacketOn M S rho W
      (fun t => W (strictEventIndex rho t)) w₁ w₂ Hs Xb (q - 1)
      ((M.opening_slot S.hc q) - 1) B)
    (hactionExact : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      M.get_fg_root
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.toHealing.toFG =
        (W (strictEventIndex rho read) w).st.J ∧
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.h_max = Mh)
    (hcap : ((Hs (M.proposal_time S.E ((M.opening_slot S.hc q)))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q)))) u).st.core.h_max) ≤ Mh)
    (hlo : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    Block.Preceq (W (strictEventIndex rho read) w).st.J B.erase ∧
      ((M.derive_named S.E S.cfg B).h = Mh - 1 ∨
        (M.derive_named S.E S.cfg B).h = Mh) := by
  have hqPredAdd : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hlifecycle : Restated.NamedRawOpeningLifecycleAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb q B := by
    have h := hpacket.lifecycle
    rw [hqPredAdd] at h
    exact h
  obtain ⟨cp, hcp, hP⟩ := hlifecycle.proposal
  have hpConf : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := hlifecycle.proposerHonest
  have hp : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) := by
    refine hHs _ _ ?_ hpConf
    have h1 : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le q 1)
    rw [← Restated.a_eq_confirmation_opening_l58 facts S q]
    exact h1
  obtain ⟨n, hn, A2, hA2, G, hG⟩ := exists_actionSG₆₉ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
      (S.E.proposer ((M.opening_slot S.hc q)))) (q - 1)
  have hwa := mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (q - 1))
  have hJtarget : Block.Preceq (W (strictEventIndex rho read) w).st.J G := by
    have h := Restated.Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt facts S rho
      (S.E.proposer ((M.opening_slot S.hc q))) (q - 1) _ hwa n hn A2 hA2 G hG
    rw [actionReadFrom_fgRoot₆₉ facts S _ (q - 1) n hn] at h
    rw [← (hactionExact _ hp).1]
    exact h
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    (S.node (S.E.proposer (M.opening_slot S.hc q)))
    (M.toHealing (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).record cp).st.core)
  have htargetParent : Block.Preceq G input.parent := by
    have h := hpacket.actionTargetParent (S.E.proposer ((M.opening_slot S.hc q)))
    rw [hqPredAdd] at h
    exact h hp n hn A2 hA2 G hG cp hcp input hinput
  have hparentB : Block.Preceq input.parent B.erase := by
    have hinput' := hinput
    rewrite [facts.nd.mkNode_st] at hinput'; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hinput'
    obtain ⟨pb, hpb, hpe⟩ := facts.dt.proposal_with_parent? (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q))) _ B (some B)
      (by rw [facts.dt.proposal_with_store_with_cache]; exact hP) rfl input hinput'
    rw [← hpe]
    exact Proofs.NamedWire.erase_preceq
      ((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressLadder
        DecoupledConsensusModel.Proofs.HealingSurface.namedParent_preceq_of_parent?) hpb)
  have hJB : Block.Preceq (W (strictEventIndex rho read) w).st.J B.erase :=
    preceq_trans_Preceq (preceq_trans_Preceq hJtarget htargetParent) hparentB
  obtain ⟨J, hJerase, hJrun, hJheight⟩ :=
    Restated.fixedRootJustificationRoot_target_namedOn facts S Hs Xb hfix
  obtain ⟨J', hJ'B, hJ'erase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift B hJB
  have hJ'run : Restated.RunBlockOn M S rho W Xb J' :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hlifecycle.runBlock hJ'B
  have hJ'eq : J' = J :=
    Restated.claimOne_named_run_eq_of_eraseOn facts hf hJ'run hJrun (hJ'erase.trans hJerase.symm)
  have hheightLower : Mh - 1 ≤
      (M.derive_named S.E S.cfg B).h := by
    rw [← hJheight, ← hJ'eq]
    exact facts.cs.derive_height_mono S.E S.cfg hJ'B
  have hspos : 0 < (M.opening_slot S.hc q) := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hheightUpper : (M.derive_named S.E S.cfg B).h ≤ Mh :=
    (Restated.honestProposedBlock_height_le_honestHMaxAtOn facts
      S Hs Xb hf hHs hspos hlifecycle.proposerHonest hlifecycle.proposalInHorizon
        cp hcp hP hlo (fun j hj => hf.tick_outcome j _ _ hj) hrun).trans hcap
  refine ⟨hJB, ?_⟩
  let x : Nat := (M.derive_named S.E S.cfg B).h
  let H : Nat := Mh
  have hlower : H - 1 ≤ x := by
    simpa only [H, x] using hheightLower
  have hupper : x ≤ H := by
    simpa only [H, x] using hheightUpper
  have hx : x = H - 1 ∨ x = H := by omega
  simpa only [H, x] using hx

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, two run blocks read through `Xb` with the same erasure are equal. -/
theorem fixedRootNamed_run_eq_of_eraseOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hB : Restated.RunBlockOn M S rho W Xb B)
    (herase : A.erase = B.erase) : A = B :=
  Restated.claimOne_named_run_eq_of_eraseOn facts hf hA hB herase

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committee majority and the weight bound, if `w`'s store before `read` holds
    a fixed-height justification root at `H`, `t_GST ≤ read ≤ S.a r`, `r + 3 ≤ q ≤ endRound`,
    `S.a endRound` is in the horizon with the largest `h_max` over its set at most `H`, the
    justified block is graded 2 at round `q − 1` by every member of the set for
    `domain (q − 1) .g2`, `lo ≤ read` and `lo ≤ opening (r + 2 − η_SG)`, then `lo` is at most the
    vote instant of `opening q − 1` and the opening cone-root lock at `H` holds for round `q − 1` at
    that slot. -/
theorem fixedRootConeRootLock_at_windowRoundOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {r q endRound : Round}
    (hpost : S.E.t_GST ≤ read) (hreadAction : read ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hqlo : r + 3 ≤ q) (hqEnd : q ≤ endRound)
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S endRound) ≤ rho.horizon)
    (hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S endRound)).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endRound)) v).st.core.h_max) ≤ H)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
            (W (strictEventIndex rho read) w).st.J ⇢ b →
          b = true)
    (hlo : lo ≤ read)
    (hloOpen : lo ≤ M.opening S.E S.hc (r + 2 - S.hc.η_SG)) :
    lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) ∧
      Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
        ((M.opening_slot S.hc q) - 1)
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))))
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) := by
  have hmono := (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
  have hcapAt : ∀ t : Time, (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ t →
      t + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S endRound) →
      ((Hs t).sup fun v => (W (inclusiveEventIndex rho t) v).st.core.h_max) ≤ H := by
    intro t h1 h2
    have hloT : lo ≤ t := hlo.trans (hreadAction.trans ((hmono (Nat.le_succ r)).trans h1))
    exact (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloT h2 hendHor
      (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)).trans hcapEnd
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.claimOne_fixedHeightJustificationRoot_target_namedOn facts S Hs Xb h
  have hformsNamed : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      Jn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
            Jn.erase ⇢ b → b = true := by
    rw [hJnErase]
    exact hforms
  have hqlo' : r + 1 + 2 ≤ q := by
    simpa only [Nat.add_assoc] using hqlo
  have hqTwo : 2 ≤ q := (Nat.le_add_left 2 (r + 1)).trans hqlo'
  have hqOne : 1 ≤ q := (by decide : 1 ≤ 2).trans hqTwo
  have hqPos : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hqPredPos : 0 < q - 1 := Nat.sub_pos_of_lt (show 1 < q from hqTwo)
  have hqActionLower : r + 1 ≤ q - 2 := Nat.le_sub_of_add_le hqlo'
  have hqActionSucc : q - 2 ≤ q - 1 := Nat.sub_le_sub_left (by decide : 1 ≤ 2) q
  have hqReadyLower : r + 1 ≤ q - 1 := hqActionLower.trans hqActionSucc
  have hqPred : q - 2 + 1 = q - 1 := by
    have hqEq : q - 2 + 2 = q := Nat.sub_add_cancel hqTwo
    rw [← hqEq]
    simp
  have hqPredAdd : q - 1 + 1 = q := Nat.sub_add_cancel hqOne
  have hr2q : r + 2 ≤ q - 1 := by
    simpa only [hqPred] using Nat.add_le_add_right hqActionLower 1
  have hloOpenQ : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hr2q _))
  have hnextAtEnd : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S endRound) :=
    hmono ((Nat.sub_le q 1).trans hqEnd)
  have hqAtEnd : (Restated.Vocabulary.Execution.Setup.a M S q) ≤
      (Restated.Vocabulary.Execution.Setup.a M S endRound) := hmono hqEnd
  have hr1Action : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := hmono hqActionLower
  have hr1Next : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) := hmono hqReadyLower
  have hdelayAction : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := by
    calc
      read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ :=
        Int.add_le_add_right hreadAction S.E.Δ
      _ ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) :=
        facts.gr.action_add_delta_le_next_Γ_neg1 S r
      _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r)
      _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := hr1Action
  have hdelayNext : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hdelayAction.trans (hmono hqActionSucc)
  have hnextHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
    hnextAtEnd.trans hendHor
  have hnextCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1))).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core.h_max) ≤ H :=
    hcapAt _ hr1Next (Restated.action_add_delta_lt_action_of_lt_l67 facts S
      (lt_of_lt_of_le (Nat.sub_lt hqPos (by decide : 0 < 1)) hqEnd))
  have hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho (q - 1) := by
    have hrPrev : r ≤ q - 1 - 1 :=
      (Nat.le_succ r).trans (hqActionLower.trans (le_of_eq (Nat.sub_sub q 1 1).symm))
    constructor
    · exact (hpost.trans (hreadAction.trans (hmono hrPrev))).trans
        ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hqPredPos Nat.one_pos)))
    · exact (facts.gr.domain_le_a S (q - 1) .g0).trans hnextHor
  obtain ⟨hslo, hshi, hsucc⟩ := facts.gr.lastInteriorSlot_before_opening S.hc hqPos
  have hslotPrev : (M.opening_slot S.hc (q - 2)) + 2 ≤ (M.opening_slot S.hc (q - 1)) := by
    calc
      (M.opening_slot S.hc (q - 2)) + 2 ≤ (M.opening_slot S.hc (q - 2)) + S.hc.R :=
        Nat.add_le_add_left S.hc.R_ge_two _
      _ = (M.opening_slot S.hc ((q - 2) + 1)) := (facts.gr.opening_slot_succ_eq S.hc (q - 2)).symm
      _ = (M.opening_slot S.hc (q - 1)) := congrArg (M.opening_slot S.hc) hqPred
  have hHone : 1 ≤ H := Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
  have htargetHeightSucc : (M.derive_named S.E S.cfg Jn).h + 1 = H := by
    rw [hJnHeight]
    exact Nat.sub_add_cancel hHone
  have htargetHeightLt : (M.derive_named S.E S.cfg Jn).h < H := by
    rw [hJnHeight]
    exact Nat.sub_lt (Nat.zero_lt_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive))
      (by decide : 0 < 1)
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hactionExact := fun (v : V) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb h hv hlo hdelayNext hnextHor hnextCap
  have hactionRoot : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      M.get_fg_root (M.toHealing n.st.core).toFG = Jn.erase := by
    intro v hv n hn
    rw [actionReadFrom_fgRoot₆₉ facts S _ (q - 1) n hn, hJnErase]
    exact (hactionExact v hv).1
  have hactionCap : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      n.st.core.h_max ≤ (M.derive_named S.E S.cfg Jn).h + 1 := by
    intro v hv n hn
    rw [actionReadFrom_h_max₆₉ facts S _ (q - 1) n hn]
    exact le_of_eq ((hactionExact v hv).2.trans htargetHeightSucc.symm)
  have hvoteAfter : ∀ d : Slot, (M.opening_slot S.hc (q - 1)) + 1 ≤ d →
      (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) ≤ M.vote_time S.E d := by
    intro d hdlo
    have hslot : (M.opening_slot S.hc (q - 2)) + 2 ≤ d :=
      hslotPrev.trans ((Nat.le_succ _).trans hdlo)
    exact (le_of_lt (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S (q - 2))).trans
      (facts.sch.vote_time_mono_slots S.E hslot)
  have hvoteLeActionQ : ∀ d : Slot, d < (M.opening_slot S.hc ((q - 1) + 1)) →
      M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    intro d hdhi
    have hdhiQ : d < (M.opening_slot S.hc q) := by
      simpa only [hqPredAdd] using hdhi
    exact (facts.sch.vote_time_mono_slots S.E (Nat.le_of_lt hdhiQ)).trans
      (le_of_lt (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S q))
  have hvoteExact := fun (d : Slot) (hdlo : (M.opening_slot S.hc (q - 1)) + 1 ≤ d)
      (hdhi : d < (M.opening_slot S.hc ((q - 1) + 1))) (v : V) (hv : v ∈ Hs (M.vote_time S.E d)) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb h hv hlo (hdelayAction.trans (hvoteAfter d hdlo))
      (((hvoteLeActionQ d hdhi).trans hqAtEnd).trans hendHor)
      (hcapAt _ (hr1Action.trans (hvoteAfter d hdlo))
        (lt_of_lt_of_le
          (Restated.vote_add_delta_lt_action_l53 facts S
            (Nat.le_of_lt (by simpa only [hqPredAdd] using hdhi))) hqAtEnd))
  have hslotHor : M.vote_time S.E ((M.opening_slot S.hc q) - 1) ≤ rho.horizon :=
    ((hvoteLeActionQ _ hshi).trans hqAtEnd).trans hendHor
  have hcanonical : Restated.SGTargetConeCanonicalityOn M S rho W Hs Xb (q - 1)
      ((M.opening_slot S.hc q) - 1)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) :=
    Restated.sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCapOn facts
      S Hs Xb hf hHs hHsXb hcom hqPredPos hready hJnRun hformsNamed hslo hshi hnextHor
        hslotHor hactionRoot hactionCap
        (fun d hdlo hdhi v hv => by
          rw [setClock_fgRoot₆₉ facts S, hJnErase]
          exact (hvoteExact d hdlo hdhi v hv).1)
        (fun d hdlo hdhi v hv => by
          rw [facts.hd.setClock_core_h_max]
          exact le_of_eq ((hvoteExact d hdlo hdhi v hv).2.trans htargetHeightSucc.symm))
        hloOpenQ
  have hwmemQ1 := mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (q - 1))
  have hJtarget : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq Jn.erase G := by
    intro u hu n hn gc st kk A2 hA2 G hG
    have huG2 : u ∈ Hs (M.domain S.E S.hc (q - 1) .g2) :=
      hHs _ _ (facts.gr.domain_le_a S (q - 1) .g2) hu
    have huG0 : u ∈ Hs (M.domain S.E S.hc (q - 1) .g0) :=
      hHs _ _ (facts.gr.domain_le_a S (q - 1) .g0) hu
    have hJraw := Restated.claimOne_namedGradeProcessedAtActionOn facts S Hs Xb hf hformsNamed huG2
    have hJB : Block.Preceq (W (strictEventIndex rho read) w).st.J Jn.erase := by
      rw [hJnErase]
      exact Proofs.ModelProperties.Preceq_self _
    have hfilt := Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts
      S Hs Xb hf (hHsXb _ hu) hJnRun hJraw hJB (le_of_eq hJnHeight.symm)
      (hactionExact u hu).1 (hactionExact u hu).2
    have hactive : Jn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
      Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := u)
        _ hwmemQ1 hfilt n hn
    exact formsW_preceq_actionSGBlockAt₆₉ facts S Hs Xb hf hHs hHsXb hqPredPos hnextHor
      hformsNamed huG0 n hn hactive hloOpenQ A2 hA2 G hG
  have hrq : r < q :=
    (Nat.lt_succ_self r).trans_le (hqActionLower.trans (Nat.sub_le q 2))
  have hopenDelay : read + S.E.Δ ≤ M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) := by
    rw [hsucc]
    exact ((Int.add_le_add_right hreadAction S.E.Δ).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        hrq)).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E ((M.opening_slot S.hc q))))
  have hopenEnd : M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) ≤
      (Restated.Vocabulary.Execution.Setup.a M S endRound) := by
    rw [hsucc]
    exact (le_of_lt (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S q)).trans hqAtEnd
  have hopenHor : M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) ≤ rho.horizon :=
    hopenEnd.trans hendHor
  have hopenAfter : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
      M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) := by
    have hqPredLt : q - 1 < q := Nat.sub_lt hqPos (by decide : 0 < 1)
    rw [hsucc]
    exact hr1Next.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      ((Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        hqPredLt).trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E
          ((M.opening_slot S.hc q))))))
  have hopenCap := hcapAt _ hopenAfter
    (lt_of_lt_of_le (Restated.vote_add_delta_lt_action_l53 facts S (le_of_eq hsucc)) hqAtEnd)
  have hfrontier : ∀ v ∈ Hs (M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1))) v).st.core
          (((M.opening_slot S.hc q) - 1) + 1)).h_max = H := by
    intro v hv
    rw [voteStore_eq₆₉ facts, facts.hd.setClock_core_h_max]
    exact (Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
      facts S Hs Xb hf hHs hHsXb hsb h hv hlo hopenDelay hopenHor hopenCap).2
  have hpostSlot : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) :=
    hlo.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelayAction.trans (hvoteAfter _ hslo)))
  have hcertNamed : Restated.CertificateOn M S rho W Xb (H - 1) Jn.root := by
    have hroot : Jn.root = (W (strictEventIndex rho read) w).st.J.root := by
      rw [← Proofs.NamedWire.erase_root Jn, hJnErase]
    rw [hroot]
    exact h.fixedTarget.certificate
  have hrs : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q) - 1) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S (q - 1)]
    apply Restated.confirmationTime_mono_l58 facts S.E
    have hsuccq : M.opening_slot S.hc q = M.opening_slot S.hc (q - 1) + S.hc.R := by
      rw [← facts.gr.opening_slot_succ_eq S.hc (q - 1), hqPredAdd]
    have h1 : M.opening_slot S.hc (q - 1) + 2 ≤ M.opening_slot S.hc q := by
      rw [hsuccq]
      exact Nat.add_le_add_left S.hc.R_ge_two _
    exact Nat.le_sub_of_add_le (le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) h1)
  exact ⟨hpostSlot, Restated.sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefixOn facts
    S Hs Xb hf hHs hHsXb hcom (hfb _ le_rfl) hrs hcanonical hJnRun hcertNamed htargetHeightLt
      hJtarget hpostSlot hopenHor hfrontier⟩

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `C` is a run block along `W` read through `Xb` justifying `J` at the nonzero height `h`, then
    a quorum of attestations naming `J` at `h`, each carried by a run block along `W` read through
    `Xb`, exists. -/
theorem fixedRootCertificate_of_namedJustifiedRunBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Xb : Finset V) {W : Nat → V → M.N}
    {C : NamedBlock V} {J : Block V} {h : Height}
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hjust : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg C J h)
    (hne : h ≠ 0) : Restated.CertificateOn M S rho W Xb h J.root := by
  have hderivedNe : (M.derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hjust.2]
    exact hne
  obtain ⟨J', hJ'D, hJ'earse, Q, hQ, hsign⟩ :=
    Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg C hderivedNe
  have hJroot : J'.root = J.root := by
    rw [← Proofs.NamedWire.erase_root J', hJ'earse, hjust.1]
  refine ⟨Q, (isQuorum_iff_q_le S.E Q).mp hQ, ?_⟩
  intro i hi
  obtain ⟨carrier, a, hcarrier, ha, hav, hpair⟩ := hsign i hi
  have hcarrierRun : Restated.RunBlockOn M S rho W Xb carrier :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hcarrier
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun, (hpf% fixedRootMem_named_chain_attestations_own) ha⟩,
    hav, ?_⟩
  rw [hpair, hjust.2, hJroot]

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

local macro "p46% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_46)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- For every world strictly before `S.a r` in which every body of `v`'s store is a run block along
    `W` read through `Xb`, every node state of `v`'s round-`r` action read there and every outcome
    `D` of its attestation duty, if `D` carries the finality pair `(H, T)` with `H ≠ 0`, then a
    certificate for `T` at `H` exists along `W` over `Xb`. -/
private theorem actionFinalityPair_certificate_any₆₉s (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (W : Nat → V → M.N) (Xb : Finset V) (v : V) (r : Round)
    {H : Height} {T : BlockId} (hH : H ≠ 0) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r),
    (∀ Dn ∈ (w v).st.bodies, Restated.RunBlockOn M S rho W Xb Dn) →
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    D.2.2.finality_pair = some ⟨H, T⟩ →
    Restated.CertificateOn M S rho W Xb H T := by
  intro w hw hbodies n hn D hD hpair
  have hJ := Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v w hw
  have hF := Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v w hw
  have hJ' : n.st.core.J ∈ n.st.core.T := by
    rw [(p46% actionReadFrom_J₄₆) facts S (w v) r n hn, (p46% actionReadFrom_T₄₆) facts S (w v) r n hn]
    exact hJ
  have hF' : n.st.core.F ∈ n.st.core.T := by
    rw [(p46% actionReadFrom_F₄₆) facts S (w v) r n hn, (p46% actionReadFrom_T₄₆) facts S (w v) r n hn]
    exact hF
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core)
    ((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.pool (M.toHealing n.st.core).s)
    (((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.pool (M.toHealing n.st.core).s).filter
      (fun u => (fun u => Classical.choose (facts.sto.resolved_nonempty (M.toHealing n.st.core).T u)) u = true))
    (M.toHealing n.st.core).s
  have heq := Restated.Vocabulary.Proofs.round_action_finality_pair facts
    (M.gradeContract n.cache) S.E S.hc (S.node v) (M.toHealing n.st.core) n.record A hA
    (fun u => Classical.choose (facts.sto.resolved_nonempty (M.toHealing n.st.core).T u))
    (fun u => Classical.choose_spec (facts.sto.resolved_nonempty (M.toHealing n.st.core).T u)) Hd hHd
  rw [facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA, heq] at hpair
  have hHdHeight : ((w v).st.core.σ Hd).h_j = H := by
    rw [← (p46% actionReadFrom_σ₄₆) facts S (w v) r n hn, ← facts.sto.Sts_toHealing_σ]
    exact facts.vc.finality_pair_height hpair
  have hHdTarget : ((w v).st.core.σ Hd).J.root = T := by
    rw [← (p46% actionReadFrom_σ₄₆) facts S (w v) r n hn, ← facts.sto.Sts_toHealing_σ]
    exact facts.vc.finality_pair_target hpair
  have hroot : M.get_fg_root (M.toHealing n.st.core).toFG ∈ (M.toHealing n.st.core).T := by
    rcases facts.fc.get_fg_root_eq_J_or_F n.st.core with h | h
    · rw [h, Record.Model.HS.T, facts.sto.toHealing_gs_T]
      exact hJ'
    · rw [h, Record.Model.HS.T, facts.sto.toHealing_gs_T]
      exact hF'
  have hHd' : Hd ∈ (w v).st.core.T := by
    rw [← (p46% actionReadFrom_T₄₆) facts S (w v) r n hn, ← facts.sto.toHealing_gs_T]
    obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s)
      (M.readFrame n.cache (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)).g1
    refine Restated.Vocabulary.Proofs.NamedProposalParent.get_head_with_mem facts _ _ _ _ _ _ _ G hG
      ?_ Hd hHd
    rw [facts.nd.Sts_gradeContract_read_anchor _ _ _ _ _ G hG a ha]
    exact Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts _ _ _ _ _ hroot a ha
  obtain ⟨Hn, hHnbody, hHnerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v w hw hHd'
  have hsigma := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v w hw Hn hHnbody
  have hDjust : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg Hn
      (M.derive_named S.E S.cfg Hn).J H := by
    refine ⟨rfl, ?_⟩
    rw [← hsigma, hHnerase]
    exact hHdHeight
  have hJroot : (M.derive_named S.E S.cfg Hn).J.root = T := by
    rw [← hsigma, hHnerase]
    exact hHdTarget
  have hcert := Restated.fixedRootCertificate_of_namedJustifiedRunBlockOn facts S Xb
    (hbodies Hn hHnbody) hDjust hH
  rw [hJroot] at hcert
  exact hcert

/-- Along `W`, if `v ∈ Xb` and an outcome `D` of the attestation duty at a node state of `v`'s
    round-`r` action read carries the finality pair `(H, T)` with `H ≠ 0`, then a certificate for
    `T` at `H` exists along `W` over `Xb`. -/
theorem fixedRootActionFinalityPair_certificateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (r : Round)
    {H : Height} {T : BlockId} (hH : H ≠ 0)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (D : M.NS × M.NR × NamedAttestation V)
    (hD : M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D)
    (hpair : D.2.2.finality_pair = some ⟨H, T⟩) :
    Restated.CertificateOn M S rho W Xb H T := by
  exact actionFinalityPair_certificate_any₆₉s facts S W Xb v r hH _
    (mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath _)
    (fun Dn hDn => Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hDn) n hn D hD hpair

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

local macro "p46% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_46)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along `W`, if `u`'s store before `read` holds a fixed-height justification root at `Mh` and
    `v ∈ Xb`, then for every node state `n` of `v`'s round-`r` action read and every outcome `D` of
    its attestation duty, the own lock at height `Mh − 1` is absent or names the justified block of
    `u`'s store. -/
theorem fixedRootActionOwnLock_at_fixedHeight_none_or_targetOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {Mh : Height} {u : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
      (W (strictEventIndex rho read)))
    {v : V} (hv : v ∈ Xb) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    M.own_lock n.record.legacy (Mh - 1) D.2.2.finality_pair = none ∨
      M.own_lock n.record.legacy (Mh - 1) D.2.2.finality_pair =
        some (W (strictEventIndex rho read) u).st.J.root := by
  intro n hn D hD
  have hHne : Mh - 1 ≠ 0 := Nat.ne_of_gt hfix.targetHeightPositive
  have hrec := (p46% actionReadFrom_record₄₆) facts S _ r n hn
  have hcertOfRecordLock : ∀ {T : BlockId},
      n.record.legacy.lock (Mh - 1) = some T →
        Restated.CertificateOn M S rho W Xb (Mh - 1) T := by
    intro T hlock
    rw [hrec] at hlock
    obtain ⟨i, hi, t, att, hevent, w₁, hw₁, out, hout, hmem, hpair, hslice⟩ :=
      Restated.Vocabulary.Proofs.HealingSurface.recordLock_finalityEmission_before_migration facts S
        rho v _ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)))
        (hf.onePath _).1 hlock
    have _hr_w₁ := facts.ndRun.stateBeforeOf_reachedNode S rho _ w₁ hw₁ v
    have _hv_w₁ := facts.ndRun.stateBeforeOf_runs_as S rho _ w₁ hw₁ v
    obtain ⟨htime, hrow⟩ := (p46% tick_attest₄₆) facts S v (w₁ v) t out hout att hmem
    have hle : strictEventIndex rho t ≤ i := (p46% strict_le_tick₄₆) hf.sorted hevent
    obtain ⟨w₀, hw₀, hslice₀⟩ := ((p46% mem_stateBeforeOf_split₄₆) S rho hle w₁).mp hw₁
    have hw₀' : w₀ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
      rw [stateBeforeTime_eq_strict₆₉ S rho hf.sorted]
      exact hw₀
    have hsame : w₁ v = w₀ v ∨ w₁ v = M.wake (w₀ v) :=
      Restated.Vocabulary.Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields facts S rho hf.sorted
        hf.tickIndexUnique hevent w₀ hw₀' w₁ hslice₀
    have hsameBodies : (w₁ v).st.bodies = (w₀ v).st.bodies := by
      rcases hsame with h | h
      · rw [h]
      · rw [h, (facts.nd.wake_st_record _).1]
    have hsameRead : Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w₁ v) att.round =
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w₀ v) att.round := by
      rcases hsame with h | h
      · rw [h]
      · rw [h, (p46% actionReadFrom_wake₄₆) facts]
    have hstep : Function.update w₁ v out.1 ∈
        Record.worldStepOf M S w₁ (Record.Event.tick v t) := Or.inl ⟨out, hout, rfl⟩
    have hmono := Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v
      (Nat.le_of_lt hi) w₁ hw₁ _ ((p46% mem_slice_cons₄₆) S rho hi hevent hstep hslice)
    have hbodies : ∀ Dn ∈ (w₀ v).st.bodies, Restated.RunBlockOn M S rho W Xb Dn := by
      intro Dn hDn
      rw [← hsameBodies] at hDn
      exact Restated.runBlock_of_stateBefore_memOn facts S W Xb hv (hmono hDn)
    subst htime
    rw [hsameRead] at hrow
    obtain ⟨n', hn', D', hD'⟩ :=
      (p46% actionAttestation_nonempty₄₆) facts S (w₀ v) att.round (S.node v)
    exact actionFinalityPair_certificate_any₆₉s facts S W Xb v att.round hHne w₀ hw₀' hbodies
      n' hn' D' hD' (by rw [hrow n' hn' D' hD']; exact hpair)
  cases hlock : M.own_lock n.record.legacy (Mh - 1) D.2.2.finality_pair with
  | none => exact Or.inl rfl
  | some locked =>
      refine Or.inr ?_
      have hcert : Restated.CertificateOn M S rho W Xb (Mh - 1) locked := by
        cases hfp : D.2.2.finality_pair with
        | none =>
            refine hcertOfRecordLock ?_
            rw [hfp, facts.vc.own_lock_none] at hlock
            exact hlock
        | some p =>
            rcases p with ⟨h, target⟩
            by_cases hh : h = Mh - 1
            · subst h
              have htarget : target = locked := by
                rw [hfp, facts.vc.own_lock_some_self] at hlock
                exact Option.some_inj.mp hlock
              subst target
              exact Restated.fixedRootActionFinalityPair_certificateOn facts S Hs Xb hf hv r hHne
                n hn D hD hfp
            · refine hcertOfRecordLock ?_
              rw [hfp, facts.vc.own_lock_some_pair_of_ne _ target hh] at hlock
              exact hlock
      exact congrArg some (hfix.fixedTarget.uniqueAtHeight locked hcert)

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `u`'s store before `read` holds a fixed-height justification root at `Mh`,
    `v ∈ Xb`, and the FG source read at a node state `n` of `v`'s round-`q0` action read can name
    `Q` at height `Mh − 1` with that justified block as its entry, then every outcome of the
    attestation duty at `n` votes `(Mh − 1, J)`, with or without the target flag. -/
theorem fixedRootWindowRows_of_sourceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {Mh : Height} {u : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
      (W (strictEventIndex rho read)))
    {v : V} (hv : v ∈ Xb) {q0 : Round} {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q0)) v) q0)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n q0 ⇢ some Q)
    (hheight : ((M.toHealing n.st.core).σ Q).h = Mh - 1)
    (htarget : ((M.toHealing n.st.core).σ Q).T_h.root =
      (W (strictEventIndex rho read) u).st.J.root) :
    ∀ D : M.NS × M.NR × NamedAttestation V,
      M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    D.2.2.height_pair =
        NamedHeightPair.vote (Mh - 1)
          (W (strictEventIndex rho read) u).st.J.root false ∨
      D.2.2.height_pair =
        NamedHeightPair.vote (Mh - 1)
          (W (strictEventIndex rho read) u).st.J.root true := by
  intro D hD
  have hmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v q0 :=
    ⟨_, mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath _, hn⟩
  have hround : (M.round_of S.hc) (M.toHealing n.st.core).s = q0 := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = q0
    rw [facts.sto.toHealing_s n.st.core]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v q0 n hmem
  have hsource' : Restated.Vocabulary.Proofs.HealingSurface.actionSource M
      (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) ⇢ some Q := by
    unfold Restated.Vocabulary.Proofs.HealingSurface.actionSource
    rw [hround]
    exact hsource
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  have hDA : D.2.2 = A.2 := facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA
  have hown := Restated.fixedRootActionOwnLock_at_fixedHeight_none_or_targetOn facts
    S Hs Xb hf hfix hv q0 n hn D hD
  have hlock : M.own_lock n.record.legacy ((M.toHealing n.st.core).σ Q).h
        A.2.finality_pair = none ∨
      M.own_lock n.record.legacy ((M.toHealing n.st.core).σ Q).h
        A.2.finality_pair = some ((M.toHealing n.st.core).σ Q).T_h.root := by
    rw [hheight, htarget, ← hDA]
    exact hown
  have hpairs :=
    Restated.Vocabulary.Proofs.HealingSurface.round_action_height_pair_target_or_timeout_of_source_lock_none_or_aligned facts
      (M.gradeContract n.cache) S.E S.hc (S.node v) (M.toHealing n.st.core) n.record A hA
      hsource' hlock
  rw [hheight, htarget] at hpairs
  rw [hDA]
  exact hpairs

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, if `v ∈ Xb`, then for every node state `n` of `v`'s round-`r` action read at which
    the FG source read can name `Q`, some named body `D` of `n`'s store erases to `Q`, is a run
    block along `W` read through `Xb`, and `n`'s store's view of `Q` is `D`'s derived state. -/
theorem fixedRootFresh_namedSource_witnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {Q : Block V} :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
    ∃ D : NamedBlock V,
      D ∈ n.st.bodies ∧
      D.erase = Q ∧
      Restated.RunBlockOn M S rho W Xb D ∧
      (M.toHealing n.st.core).σ Q =
        M.derive_named S.E S.cfg D :=
  fun n hn hsource => Restated.seedFresh_namedSource_witnessOn facts S Hs Xb hf hv n hn hsource

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along `W`, if `u`'s store before `read` holds a fixed-height justification root at `Mh`,
    `0 < r`, `S.a r` is in the horizon, `B0` is a run block at height `Mh − 1` whose height entry is
    that justified block, graded 2 at round `r` and in the filtered tree of every member of the set
    for `S.a r`, every FG source of those members' round-`r` action reads is at height at most
    `Mh − 1`, and `lo ≤ opening (r − η_SG)`, then every outcome of their attestation duty votes
    `(Mh − 1, J)`, with or without the target flag. -/
theorem fixedRootFreshActionRows_of_persistedGradeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {u : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
      (W (strictEventIndex rho read)))
    {r : Round} {B0 : NamedBlock V}
    (hr : 0 < r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hB0run : Restated.RunBlockOn M S rho W Xb B0)
    (hB0height : (M.derive_named S.E S.cfg B0).h = Mh - 1)
    (hB0entry : (M.derive_named S.E S.cfg B0).T_h.root =
      (W (strictEventIndex rho read) u).st.J.root)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc r Phase.g2),
      B0.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v).st r Phase.g2 B0.erase ⇢ b →
          b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      B0.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG)
    (hsourceUpper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
        ((M.toHealing n.st.core).σ Q).h ≤ Mh - 1)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      D.2.2.height_pair =
          NamedHeightPair.vote (Mh - 1)
            (W (strictEventIndex rho read) u).st.J.root false ∨
        D.2.2.height_pair =
          NamedHeightPair.vote (Mh - 1)
            (W (strictEventIndex rho read) u).st.J.root true := by
  intro v hv n hn D hD
  have hvDom : v ∈ Hs (M.domain S.E S.hc r .g0) :=
    hHs _ _ (facts.gr.domain_le_a S r .g0) hv
  have hvG2 : v ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hvDom
  have hwmem := mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)), hwmem, hn⟩
  have hactive : B0.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v)
      _ hwmem (hwindow v hv) n hn
  have hround' : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hmem
  have hsrcEq : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n =
      Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r := by
    simp only [Restated.Vocabulary.Proofs.HealingSurface.actionFGSource,
      Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource]
    rw [hround']
    rfl
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts S n
  rw [hsrcEq] at ho
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) B0.erase
  have hbtrue : b = true := (hforms v hvG2).2 b hb
  subst hbtrue
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
    nodeQ2_of_read₆₉ S n r G hG
  obtain ⟨Q2, hQ2, hCQ2⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hvDom hlo
      (hforms v hvG2).1 hb n hn hactive _ hGq
  rw [hQ2] at hGq
  obtain ⟨Q, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.exists_actionFGSource_of_actionQ2 facts
    S rho v r _ hwmem n hn hGq o ho
  have hsource := ho
  obtain ⟨Qn, hQnbody, hQnerase, hQnrun, hσ⟩ :=
    Restated.fixedRootFresh_namedSource_witnessOn facts S Hs Xb hf (hHsXb _ hv) n hn hsource
  have hB0Q : Block.Preceq B0.erase Q :=
    Restated.Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 facts S rho v r _
      hwmem n hn hGq hCQ2 hsource
  have hB0QnErase : Block.Preceq B0.erase Qn.erase := by
    rw [hQnerase]
    exact hB0Q
  obtain ⟨A, hAQn, hAerased⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift Qn hB0QnErase
  have hArun : Restated.RunBlockOn M S rho W Xb A :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hQnrun hAQn
  have hAB0 : A = B0 :=
    Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hArun hB0run hAerased
  have hB0Qn : NamedBlock.Preceq B0 Qn := by
    simpa only [hAB0] using hAQn
  have hQnUpper : (M.derive_named S.E S.cfg Qn).h ≤ Mh - 1 := by
    have h := hsourceUpper v hv n hn Q hsource
    rw [hσ] at h
    exact h
  have hQnLower : Mh - 1 ≤
      (M.derive_named S.E S.cfg Qn).h := by
    have h := facts.cs.derive_height_mono S.E S.cfg hB0Qn
    rw [hB0height] at h
    exact h
  have hQnheight : (M.derive_named S.E S.cfg Qn).h = Mh - 1 :=
    Nat.le_antisymm hQnUpper hQnLower
  have hsameHeight : (M.derive_named S.E S.cfg B0).h =
      (M.derive_named S.E S.cfg Qn).h := by
    rw [hB0height, hQnheight]
  have hentry : (M.derive_named S.E S.cfg B0).T_h =
      (M.derive_named S.E S.cfg Qn).T_h :=
    facts.cs.entry_eq_on_plateau S.E S.cfg hB0Qn hsameHeight
  have hsourceHeight :
      ((M.toHealing n.st.core).σ Q).h = Mh - 1 := by
    rw [hσ, hQnheight]
  have hsourceEntry :
      ((M.toHealing n.st.core).σ Q).T_h.root =
        (W (strictEventIndex rho read) u).st.J.root := by
    calc
      ((M.toHealing n.st.core).σ Q).T_h.root =
          (M.derive_named S.E S.cfg Qn).T_h.root :=
        congrArg (fun x : M.CS => x.T_h.root) hσ
      _ = (M.derive_named S.E S.cfg B0).T_h.root :=
        congrArg (fun x : Block V => x.root) hentry.symm
      _ = (W (strictEventIndex rho read) u).st.J.root := hB0entry
  exact Restated.fixedRootWindowRows_of_sourceOn facts S Hs Xb hf hfix (hHsXb _ hv) n hn hsource
    hsourceHeight hsourceEntry D hD

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

local macro "p54b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_54b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along `W`, under the weight bound, if `u`'s store before `read` holds a fixed-height
    justification root at `Mh`, `0 < q' − 1`, `C` is a run block at height `Mh − 1` whose height
    entry is that justified block and a named ancestor of `B2`'s parent, the round-`(q' − 1)` FG
    sources of the set for `S.a (q' − 1)` are no higher than `B2`'s parent, `C` is graded 2 at round
    `q' − 1` and retained by those members, `B2` is the proposal of round `q'`'s proposal lifecycle
    packet with a mature timeout, the bounds on `lo` hold and the awake condition holds at `q' − 1`,
    then `B2` is at height `Mh`, or the largest `h_max` over the set for the proposal instant of
    `q'`'s opening slot exceeds `Mh`. -/
theorem fixedRootFresh_predLifecycle_promotion_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {u : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
      (W (strictEventIndex rho read)))
    {q' : Round} {C B2 : NamedBlock V}
    (hq' : 0 < q')
    (hq'PredPos : 0 < q' - 1)
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : (M.derive_named S.E S.cfg C).h = Mh - 1)
    (hCtarget : (M.derive_named S.E S.cfg C).T_h.root =
      (W (strictEventIndex rho read) u).st.J.root)
    (hCP : NamedBlock.Preceq C B2.parent)
    (hsourceToParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v) (q' - 1),
      ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n (q' - 1) ⇢ some Q →
        ((M.toHealing n.st.core).σ Q).h ≤ (M.derive_named S.E S.cfg B2.parent).h)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q' - 1) Phase.g2),
      C.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v).st (q' - 1) Phase.g2
            C.erase ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
      C.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v).st.core).toFG)
    {w₁ w₂ : V → M.N}
    (hpacket : Restated.NamedSGProposalLifecyclePacketOn M S rho W
      (fun t => W (strictEventIndex rho t)) w₁ w₂ Hs Xb (q' - 1)
      ((M.opening_slot S.hc q') - 1) B2)
    (hmature : ∀ P : NamedBlock V, NamedBlock.parent? B2 = some P →
      (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q')
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q' - 1 - S.hc.η_SG))
    (hA : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) → M.awake_for_grade2 S w (W j w) (q' - 1)) :
    (M.derive_named S.E S.cfg B2).h = Mh ∨
      Mh < ((Hs (M.proposal_time S.E ((M.opening_slot S.hc q')))).sup fun x =>
        (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q')))) x).st.core.h_max) := by
  obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, (Nat.sub_add_cancel hq').symm⟩
  have e : r + 1 - 1 = r := Nat.add_sub_cancel r 1
  simp only [e] at hq'PredPos hsourceToParent hforms hwindow hpacket hpost hloOpen hA
  have hlifecycle := hpacket.lifecycle
  obtain ⟨c, hc, hB2⟩ := hlifecycle.proposal
  have hprop : S.E.proposer ((M.opening_slot S.hc (r + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) :=
    hlifecycle.proposerHonest
  have hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc (r + 1))) ≤ rho.horizon :=
    hlifecycle.proposalInHorizon
  have hspos : 0 < (M.opening_slot S.hc (r + 1)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (Nat.succ_pos r)
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc (r + 1))) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
      (Nat.lt_succ_self r)
  have hgat : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc (r + 1))) :=
    hpost.trans ((Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay)
  by_cases hrise : Mh < ((Hs (M.proposal_time S.E ((M.opening_slot S.hc (r + 1))))).sup fun x =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc (r + 1))))) x).st.core.h_max)
  · exact Or.inr hrise
  left
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
      (S.E.proposer (M.opening_slot S.hc (r + 1))) (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc (r + 1)))
        (W j (S.E.proposer (M.opening_slot S.hc (r + 1))))
        (M.round_of S.hc (M.opening_slot S.hc (r + 1))) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (r + 1))) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc (r + 1)]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S (r + 1)
      have h3 : lo ≤ M.a S.hc S.E.Δ r := hpost
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop) hwin
  have hproposalUpper : (M.derive_named S.E S.cfg B2).h ≤ Mh :=
    (Restated.honestProposedBlock_height_le_honestHMaxAtOn facts S Hs Xb hf hHs hspos hprop
      hproposalHor c hc hB2 hgat (fun j hj => hf.tick_outcome j _ _ hj) hrunP).trans
      (Nat.le_of_not_gt hrise)
  have hparentLower : Mh - 1 ≤
      (M.derive_named S.E S.cfg B2.parent).h := by
    rw [← hCheight]
    exact facts.cs.derive_height_mono S.E S.cfg hCP
  have hparentUpper :
      (M.derive_named S.E S.cfg B2.parent).h ≤ Mh :=
    (facts.cs.derive_height_mono S.E S.cfg
      ((hpf% fixedRootFresh_parent_preceq_self) B2)).trans hproposalUpper
  have hparentCases :
      (M.derive_named S.E S.cfg B2.parent).h = Mh - 1 ∨
      (M.derive_named S.E S.cfg B2.parent).h = Mh :=
    (hpf% fixedRootFresh_heightCases_nat) hparentLower hparentUpper
  rcases hparentCases with hparentPred | hparentExact
  · have hparentTarget :
        (M.derive_named S.E S.cfg B2.parent).T_h.root =
          (M.derive_named S.E S.cfg C).T_h.root := by
      rw [← facts.cs.entry_eq_on_plateau S.E S.cfg hCP
        (by rw [hCheight, hparentPred])]
    have hsourceUpper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
        ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
          ((M.toHealing n.st.core).σ Q).h ≤ Mh - 1 := by
      intro v hv n hn Q hsource
      have h := hsourceToParent v hv n hn Q hsource
      simpa only [hparentPred] using h
    have hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
      (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans (hdelay.trans hproposalHor)
    have hrowsFixed := Restated.fixedRootFreshActionRows_of_persistedGradeOn facts
      S Hs Xb hf hHs hHsXb hfix hq'PredPos hhor hCrun hCheight hCtarget hforms hwindow
        hsourceUpper hloOpen
    have hpropConf : M.proposal_time S.E ((M.opening_slot S.hc (r + 1))) ≤
        M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) :=
      facts.sch.proposal_time_le_confirmation_time S.E _
    have hpropDelta : S.E.proposer ((M.opening_slot S.hc (r + 1))) ∈
        Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) :=
      hHs _ _ (hdelay.trans hpropConf) hprop
    have hround : M.round_of S.hc (M.opening_slot S.hc (r + 1)) = r + 1 :=
      facts.gr.round_of_opening_slot_eq S.hc (r + 1)
    have hinWindow : M.inWindow S.hc
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
          (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))).core r = true := by
      rw [facts.dt.inWindow_iff, facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time,
        hround]
      have heta := S.hc.η_SG_ge_one
      exact ⟨(Nat.sub_le_sub_left heta (r + 1)).trans (Nat.le_of_eq (Nat.add_sub_cancel r 1)),
        Nat.le_succ r⟩
    have hcoverage : ∀ v ∈ Hs (M.proposal_time S.E ((M.opening_slot S.hc (r + 1)))),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
        ∀ D : M.NS × M.NR × NamedAttestation V,
          M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
        ((D.2.2 ∈ named_chain_attestations B2.parent ∧
            v ∈ (M.derive_named S.E S.cfg B2.parent).progress ∧
            (D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
                (M.derive_named S.E S.cfg C).T_h.root false →
              v ∈ (M.derive_named S.E S.cfg B2.parent).target_participation)) ∨
          D.2.2 ∈ B2.attestations) ∧
        (D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
            (M.derive_named S.E S.cfg C).T_h.root false ∨
          D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
            (M.derive_named S.E S.cfg C).T_h.root true) := by
      intro v hvp n hn D hD
      have hvDelta : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) :=
        hHs _ _ hdelay hvp
      have hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
        hHs _ _ (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hvDelta
      have hpair : D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
            (M.derive_named S.E S.cfg C).T_h.root false ∨
          D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
            (M.derive_named S.E S.cfg C).T_h.root true := by
        rw [hCtarget]
        exact hrowsFixed v hv n hn D hD
      refine ⟨?_, hpair⟩
      exact (p54b% windowW_actionAttestationAt_coveredAtProposal₅₄b) facts S Hs Xb hf hHs
        hHsXb hCrun hCheight rfl c hc hB2 hCP hparentPred hpropDelta hproposalHor hpost hdelay hvp
        (hwindow v hv) hinWindow (hA v hvDelta) n hn D hD hpair
    have hwr := mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath
      (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
    have hBmem : some B2 ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho
        (M.opening_slot S.hc (r + 1)) :=
      ⟨M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
            (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
          (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c,
        ⟨_, hwr, c, hc, rfl⟩,
        by rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact hB2⟩
    have hheight := (p54b% named_proposedBlock_height_eq_succ_along₅₄b) facts S _
      (hfb _ hproposalHor) hBmem hmature _
      (mem_stateBeforeTime_along₆₉ hf.sorted hf.onePath (Restated.Vocabulary.Execution.Setup.a M S r))
      hcoverage hparentPred hparentTarget
    have hMone : 1 ≤ Mh :=
      Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
    rw [Nat.sub_add_cancel hMone] at hheight
    exact hheight
  · exact Nat.le_antisymm hproposalUpper
      (by
        rw [← hparentExact]
        exact facts.cs.derive_height_mono S.E S.cfg
          ((hpf% fixedRootFresh_parent_preceq_self) B2))

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

local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p54% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_54)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p60b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_60b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p65b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_65b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p66b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_66b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p67b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_67b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p68% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_68)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
