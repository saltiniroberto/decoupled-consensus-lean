import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_EntryHeight
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_JustificationCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_46
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_Store
import Model.Conditions.Vocabulary_Internal_StoreFinality
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Action heights, vote-duty stores, proposals and relays along a path

Theorems over a model `M : Record.Model V` and its facts, read along the path `W` of the bundle
`AdmissibleFieldsOn`: the heights an action attestation and a lock name, the slots and root
injectivity of vote-duty stores, the transfer of the proposer's walk to a voter's walk, the
acceptance of a block after a relay delay, and the carriers of a fixed-height justification. A store
strictly before a time `t` is the store in `W (strictEventIndex rho t)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ### Helpers -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

omit [DecidableEq V] [Fintype V] in
private theorem drop_take_succ₅₁ {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

omit [DecidableEq V] [Fintype V] in
private theorem slice_split₅₁ {α : Type} (l : List α) {m j n : Nat} (hmj : m ≤ j) (hjn : j ≤ n) :
    (l.drop m).take (n - m) = (l.drop m).take (j - m) ++ (l.drop j).take (n - j) := by
  have h : n - m = (j - m) + (n - j) := by omega
  rw [h, List.take_add, List.drop_drop, Nat.add_sub_cancel' hmj]

private theorem mem_foldlM_singleton₅₁ (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

private theorem mem_foldlM_append₅₁ (S : Setup V) (l₁ l₂ : List (Record.Event V)) (w w₂ : V → M.N) :
    w₂ ∈ (l₁ ++ l₂).foldlM (Record.worldStepOf M S) w ↔
      ∃ w' ∈ l₁.foldlM (Record.worldStepOf M S) w,
        w₂ ∈ l₂.foldlM (Record.worldStepOf M S) w' := by
  rw [List.foldlM_append, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    exact ⟨w', hw', h2⟩
  · rintro ⟨w', hw', h2⟩
    exact Set.mem_iUnion₂.mpr ⟨w', hw', h2⟩

/-- For `i ≤ j`, a world can hold before event `j` of `rho` exactly when it is reached by events `i`
    to `j - 1` from a world that can hold before event `i`. -/
private theorem mem_stateBeforeOf_split₅₁ (S : Setup V) (rho : Record.Run V) {i j : Nat}
    (hij : i ≤ j) (w₂ : V → M.N) :
    w₂ ∈ Record.stateBeforeOf M S rho j ↔
      ∃ w₁ ∈ Record.stateBeforeOf M S rho i,
        w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  unfold Record.stateBeforeOf
  rw [Nat.add_sub_cancel_left, List.take_add, List.foldlM_append, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w₁, hw₁, h2⟩ := Set.mem_iUnion₂.mp h
    exact ⟨w₁, hw₁, h2⟩
  · rintro ⟨w₁, hw₁, h2⟩
    exact Set.mem_iUnion₂.mpr ⟨w₁, hw₁, h2⟩

private theorem mem_slice_split₅₁ (S : Setup V) (rho : Record.Run V) {m j n : Nat} (hmj : m ≤ j)
    (hjn : j ≤ n) (w w₂ : V → M.N) :
    w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w ↔
      ∃ w' ∈ ((rho.events.drop m).take (j - m)).foldlM (Record.worldStepOf M S) w,
        w₂ ∈ ((rho.events.drop j).take (n - j)).foldlM (Record.worldStepOf M S) w' := by
  rw [slice_split₅₁ rho.events hmj hjn]
  exact mem_foldlM_append₅₁ S _ _ w w₂

private theorem mem_slice_cons₅₁ (S : Setup V) (rho : Record.Run V) {i n : Nat} (hin : i < n)
    {e : Record.Event V} (hi : rho.events[i]? = some e) {w w' w₂ : V → M.N}
    (hw' : w' ∈ Record.worldStepOf M S w e)
    (hw₂ : w₂ ∈ ((rho.events.drop (i + 1)).take (n - (i + 1))).foldlM (Record.worldStepOf M S) w') :
    w₂ ∈ ((rho.events.drop i).take (n - i)).foldlM (Record.worldStepOf M S) w := by
  rw [mem_slice_split₅₁ S rho (Nat.le_succ i) hin w w₂]
  exact ⟨w', by rw [drop_take_succ₅₁ hi, mem_foldlM_singleton₅₁]; exact hw', hw₂⟩

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₁ (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, along every path `W` of `rho`, the world `W (strictEventIndex rho t)` is
    a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₅₁ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₁ S rho hsorted]
  exact (hW _).1

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, if the `i`-th event is `e`, the number of events with a time before
    `e`'s time is at most `i`. -/
private theorem strict_le_tick₅₁ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {i : Nat} {e : Record.Event V} (hi : rho.events[i]? = some e) :
    strictEventIndex rho e.time ≤ i := by
  by_contra hnot
  have hlt : i < (rho.events.filter (fun f => decide (f.time < e.time))).length :=
    Nat.lt_of_not_ge hnot
  have hpre : rho.events.filter (fun f => decide (f.time < e.time)) =
      rho.events.take (rho.events.filter (fun f => decide (f.time < e.time))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e' f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hmem : e ∈ rho.events.filter (fun f => decide (f.time < e.time)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
  have hp := (List.mem_filter.mp hmem).2
  simp only [decide_eq_true_eq] at hp
  exact lt_irrefl _ hp

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events has a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₁ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time}
    (hj : j < strictEventIndex rho t) : e.time < t := by
  have hpre : rho.events.filter (fun f => decide (f.time < t)) =
      rho.events.take (rho.events.filter (fun f => decide (f.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e' f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun f => decide (f.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun f => decide (f.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2

/-- Every node state `n` of the round-`r` action read from `before` has as its core store an outcome
    of the confirmation write on `before`'s core store with its clock set to round `r`'s action
    instant, under the grade contract of `n`'s cache. -/
private theorem actionReadFrom_core₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

private theorem actionReadFrom_T₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₁ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

private theorem actionReadFrom_σ₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.σ = before.st.core.σ := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₁ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_σ,
    facts.dt.update_confirmation_with_σ _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_σ]

private theorem actionReadFrom_F₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.F = before.st.core.F := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₁ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_F,
    facts.dt.update_confirmation_with_F _ _ _ _ _ _ hX₀,
    facts.hd.setClock_core_F]

private theorem actionReadFrom_J₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.J = before.st.core.J := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₁ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_J,
    ← facts.sto.Sts_toHealing_J,
    facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ _ hX₀,
    facts.sto.Sts_toHealing_J, facts.hd.setClock_core_J]

private theorem actionReadFrom_h_max₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₁ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _ hX₀,
    facts.hd.setClock_toHealing_h_max]

private theorem actionReadFrom_bodies₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The confirmation-membership invariant of a named store survives writing a grade cache into it. -/
private theorem invariant_store_with_cache₅₁ (facts : Record.Facts M) (E : Env V)
    (cfg : Protocol.HeightConfig) (st : M.NS) (c : M.Cache)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st) :
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg
      (M.store_with_cache st c) := by
  simp only [Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant,
    Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant, Restated.Vocabulary.Proofs.NamedStore.Coherent,
    Restated.Vocabulary.Proofs.NamedStore.TreeView, Restated.Vocabulary.Proofs.NamedStore.ErasureUnique,
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed, Restated.Vocabulary.Proofs.NamedStore.PoolView,
    Restated.Vocabulary.Proofs.NamedStore.DerivedView, Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree,
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Confirmed,
    facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView, facts.nd.store_with_cache_bodies,
    facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_sg_votes,
    facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau,
    facts.nd.store_with_cache_core_attestations] at h ⊢
  exact h

private theorem actionReadFrom_record₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.record = before.record := by
  rintro _ ⟨c, -, st, -, rfl⟩
  exact facts.nd.mkNode_record _ _ _

/-- The round-`r` action read computed from `M.wake n` gives the same node states as the one
    computed from `n`. -/
private theorem actionReadFrom_wake₅₁ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

/-- The confirmation-membership invariant of `before` holds at every node state of its round-`r`
    action read. -/
private theorem actionReadFrom_invariant₅₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg before.st) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st]
  exact invariant_store_with_cache₅₁ facts S.E S.cfg st c
    (facts.dt.invariant_update_gradeContract _ S.E S.hc S.cfg _ _
      (facts.hd.invariant_clock S.E S.cfg _ _ h) st hst)

/-- The round-`r` action read from `before` can give some node state on which the attestation duty
    of `nd` has some outcome. -/
private theorem actionAttestation_nonempty₅₁ (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) (nd : Protocol.Node V) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc nd n.st n.record ⇢ D := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, ?_⟩
  exact facts.dt.attest_with_nonempty _ S.E S.hc nd _ _

/-- If an outcome of `v`'s tick at `t` from `n` sends the attestation `a`, then `t` is the action
    instant of `a`'s round and every outcome of the attestation duty on every node state of that
    round's action read of `n` is `a`. -/
private theorem tick_attest₅₁ (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out) (a : NamedAttestation V)
    (ha : NamedObject.attest a ∈ out.2) (hn : M.reachedNode n := by trivial)
    (hv : M.runs_as n v := by trivial) :
    t = Restated.Vocabulary.Execution.Setup.a M S a.round ∧
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n a.round,
      ∀ D, M.duties_attest_with (M.gradeContract n'.cache) S.E S.hc (S.node v) n'.st n'.record ⇢ D →
        D.2.2 = a := by
  obtain ⟨ht, hawake, -⟩ := facts.nd.tick_attestation_fields S v n t hv out hout a ha
  subst ht
  refine ⟨rfl, ?_⟩
  rintro _ ⟨c, hc, st, hst, rfl⟩ D hD
  rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.duties_attest_with_store_with_cache,
    facts.nd.mkNode_record] at hD
  have hb := ha
  rw [facts.nd.tick_at_action_awake S v n a.round out hout c hc st hst D hD hawake] at hb
  simp only [List.mem_singleton, NamedObject.attest.injEq] at hb
  exact hb.symm

private theorem returns_bind_iff₅₁ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
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

private theorem returns_map_elim₅₁ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- The action FG source read at `n` can return some value. -/
private theorem actionFGSource_nonempty₅₁ (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff₅₁ _ _ _).2 ⟨A2, hA2, ho⟩⟩

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- For every world strictly before `S.a r`, if an outcome of the attestation duty on a node state
    `n` of `v`'s round-`r` action read carries the finality pair `(H, T)`, then `H` is less than
    `n`'s running height maximum. -/
private theorem roundActionFinality_any₅₁ (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (v : V) (r : Round) {H : Height} {T : BlockId} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    D.2.2.finality_pair = some ⟨H, T⟩ →
    H < n.st.core.h_max := by
  intro w hw n hn D hD hpair
  have hJ : n.st.core.J ∈ n.st.core.T := by
    rw [actionReadFrom_J₅₁ facts S (w v) r n hn, actionReadFrom_T₅₁ facts S (w v) r n hn]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts S rho _ v w hw
  have hF : n.st.core.F ∈ n.st.core.T := by
    rw [actionReadFrom_F₅₁ facts S (w v) r n hn, actionReadFrom_T₅₁ facts S (w v) r n hn]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime facts S rho _ v w hw
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  rw [facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA] at hpair
  obtain ⟨Hd, hHd, hHdHeight⟩ :=
    facts.nd.round_action_head_mem_gradeContract n.cache S.E S.hc (S.node v) n.st.core n.record
      hJ hF A hA hpair
  have hinv := actionReadFrom_invariant₅₁ facts S (w v) r
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho _ v w hw).1 n hn
  have hcoh := hinv.1.1
  have hHdImage := hHd
  rw [hcoh.1] at hHdImage
  obtain ⟨Dn, hDn, hDnerase⟩ := Finset.mem_image.mp hHdImage
  have hDnHeight : (M.derive_named S.E S.cfg Dn).h_j = H := by
    rw [← hcoh.2.2.2.2 Dn hDn, hDnerase]
    exact hHdHeight
  have hnoPre :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime facts
      S rho _ v w hw
  have hDnle : (M.derive_named S.E S.cfg Dn).h_j ≤ (w v).st.core.h_j := by
    rw [actionReadFrom_bodies₅₁ facts S (w v) r n hn] at hDn
    exact hnoPre Dn hDn
  have hbelowPre :
      (w v).st.core.h_j < (w v).st.core.h_max :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime facts
      S rho _ v w hw
  rw [actionReadFrom_h_max₅₁ facts S (w v) r n hn]
  exact (hDnHeight ▸ hDnle).trans_lt hbelowPre

/-- In a run sorted by key whose ticks have unique indices, for every world `w` strictly before
    `S.a r`, if `v`'s record in `w` locks `T` at height `H`, then `H` is less than the running
    height maximum of every node state of `v`'s round-`r` action read from `w`. -/
private theorem recordLock_any₅₁ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (htiu : Restated.TickIndexUnique rho)
    (v : V) (r : Round) {H : Height} {T : BlockId} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r),
    (w v).record.legacy.lock H = some T →
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    H < n.st.core.h_max := by
  intro w hw hlock n hn
  rw [stateBeforeTime_eq_strict₅₁ S rho hsorted] at hw
  obtain ⟨i, hi, t, a, hevent, w₁, hw₁, out, hout, hmem, hpair, hslice⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.recordLock_finalityEmission_before_migration facts S rho v
      _ w hw hlock
  have _hr_w₁ := facts.ndRun.stateBeforeOf_reachedNode S rho _ w₁ hw₁ v
  have _hv_w₁ := facts.ndRun.stateBeforeOf_runs_as S rho _ w₁ hw₁ v
  obtain ⟨htime, hrow⟩ := tick_attest₅₁ facts S v (w₁ v) t out hout a hmem
  have hle : strictEventIndex rho t ≤ i := strict_le_tick₅₁ hsorted hevent
  obtain ⟨w₀, hw₀, hslice₀⟩ := (mem_stateBeforeOf_split₅₁ S rho hle w₁).mp hw₁
  have hw₀' : w₀ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
    rw [stateBeforeTime_eq_strict₅₁ S rho hsorted]
    exact hw₀
  have hsame : w₁ v = w₀ v ∨ w₁ v = M.wake (w₀ v) :=
    Restated.Vocabulary.Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields facts S rho hsorted
      htiu hevent w₀ hw₀' w₁ hslice₀
  have hrow' : ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w₀ v) a.round,
      ∀ D, M.duties_attest_with (M.gradeContract n'.cache) S.E S.hc (S.node v) n'.st n'.record ⇢ D →
        D.2.2 = a := by
    rcases hsame with h | h
    · rwa [h] at hrow
    · rwa [h, actionReadFrom_wake₅₁ facts] at hrow
  have hst : (w₁ v).st = (w₀ v).st := by
    rcases hsame with h | h
    · rw [h]
    · rw [h, (facts.nd.wake_st_record _).1]
  rw [htime] at hw₀'
  obtain ⟨n₀, hn₀, D, hD⟩ := actionAttestation_nonempty₅₁ facts S (w₀ v) a.round (S.node v)
  have hlocal := roundActionFinality_any₅₁ facts S rho v a.round w₀ hw₀' n₀ hn₀ D hD
    (by rw [hrow' n₀ hn₀ D hD]; exact hpair)
  rw [actionReadFrom_h_max₅₁ facts S (w₀ v) a.round n₀ hn₀, ← hst] at hlocal
  have hstep : Function.update w₁ v out.1 ∈
      Record.worldStepOf M S w₁ (Record.Event.tick v t) := Or.inl ⟨out, hout, rfl⟩
  have hmono := Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v
    (Nat.le_of_lt hi) w₁ hw₁ w (mem_slice_cons₅₁ S rho hi hevent hstep hslice)
  rw [actionReadFrom_h_max₅₁ facts S (w v) r n hn]
  exact hlocal.trans_le hmono

end

section
open DecoupledConsensusModel.Execution

/-- In a parent-closed named store, every named ancestor of a held body is held. -/
private theorem namedAncestor_mem₅₁ {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node p s r gv gsv ats proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (by simpa only [NamedBlock.parent] using hpc.2 _ hB)
          (by unfold NamedBlock.Preceq; exact hparent)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- One event leads from any world to at least one world. -/
private theorem worldStepOf_nonempty₅₁ (S : Setup V) (w : V → M.N) (e : Record.Event V) :
    ∃ u, u ∈ Record.worldStepOf M S w e := by
  classical
  cases e with
  | wake v₁ t => exact ⟨_, Set.mem_singleton _⟩
  | tick v₁ t =>
      by_cases hex : ∃ out : M.N × List (NamedObject V), M.tick S v₁ (w v₁) t ⇢ out
      · obtain ⟨out, hout⟩ := hex
        exact ⟨Function.update w v₁ out.1, Or.inl ⟨out, hout, rfl⟩⟩
      · exact ⟨w, Or.inr ⟨fun out hout => hex ⟨out, hout⟩, rfl⟩⟩
  | deliver v₁ o t =>
      by_cases hex : ∃ n' : M.N, M.process S (w v₁) o ⇢ n'
      · obtain ⟨n', hn'⟩ := hex
        exact ⟨Function.update w v₁ n', Or.inl ⟨n', hn', rfl⟩⟩
      · exact ⟨w, Or.inr ⟨fun n' hn' => hex ⟨n', hn'⟩, rfl⟩⟩

/-- Folding any list of events from any world reaches some world. -/
private theorem foldlM_worldStepOf_nonempty₅₁ (S : Setup V) :
    ∀ (l : List (Record.Event V)) (u : V → M.N), ∃ u', u' ∈ l.foldlM (Record.worldStepOf M S) u
  | [], u => ⟨u, Set.mem_singleton u⟩
  | e :: l, u => by
      obtain ⟨u₁, hu₁⟩ := worldStepOf_nonempty₅₁ S u e
      obtain ⟨u', hu'⟩ := foldlM_worldStepOf_nonempty₅₁ S l u₁
      refine ⟨u', ?_⟩
      rw [List.foldlM_cons, Set.bind_def]
      exact Set.mem_biUnion hu₁ hu'

/-- There is a sequence of worlds starting at `u` in which each step is a world the event of `es` at
    index `s + m` can lead to. -/
private theorem exists_path_from₅₁ (S : Setup V) (es : List (Record.Event V))
    (s : Nat) (u : V → M.N) :
    ∃ g : Nat → V → M.N, g 0 = u ∧
      ∀ m, g (m + 1) ∈ ((es.drop (s + m)).take 1).foldlM (Record.worldStepOf M S) (g m) := by
  choose f hf using fun (m : Nat) (u' : V → M.N) =>
    foldlM_worldStepOf_nonempty₅₁ S ((es.drop (s + m)).take 1) u'
  exact ⟨fun m => Nat.rec u (fun m gm => f m gm) m, rfl, fun m => hf m _⟩

/-- If `W` follows `es` and `w'` is a world event `i` can lead to from `W i`, some sequence that
    follows `es` agrees with `W` up to `i` and has `w'` at `i + 1`. -/
private theorem path_splice₅₁ (S : Setup V) (es : List (Record.Event V))
    (W : Nat → V → M.N)
    (hW : ∀ j, W (j + 1) ∈ ((es.drop j).take 1).foldlM (Record.worldStepOf M S) (W j))
    (i : Nat) (w' : V → M.N)
    (hw' : w' ∈ ((es.drop i).take 1).foldlM (Record.worldStepOf M S) (W i)) :
    ∃ W' : Nat → V → M.N,
      (∀ j, W' (j + 1) ∈ ((es.drop j).take 1).foldlM (Record.worldStepOf M S) (W' j)) ∧
      (∀ j, j ≤ i → W' j = W j) ∧ W' (i + 1) = w' := by
  classical
  obtain ⟨g, hg0, hg⟩ := exists_path_from₅₁ S es (i + 1) w'
  refine ⟨fun j => if j ≤ i then W j else g (j - (i + 1)), ?_, ?_, ?_⟩
  · intro j
    rcases Nat.lt_trichotomy j i with hj | hj | hj
    · have h1 : j ≤ i := Nat.le_of_lt hj
      have h2 : j + 1 ≤ i := hj
      simp only [if_pos h1, if_pos h2]
      exact hW j
    · subst hj
      have h2 : ¬ j + 1 ≤ j := Nat.not_succ_le_self j
      simp only [if_pos (Nat.le_refl j), if_neg h2, Nat.sub_self, hg0]
      exact hw'
    · have h1 : ¬ j ≤ i := Nat.not_le_of_lt hj
      have h2 : ¬ j + 1 ≤ i := fun h => h1 (Nat.le_of_succ_le h)
      simp only [if_neg h1, if_neg h2]
      have he : j + 1 - (i + 1) = (j - (i + 1)) + 1 := by omega
      have hs : i + 1 + (j - (i + 1)) = j := by omega
      rw [he]
      have := hg (j - (i + 1))
      rw [hs] at this
      exact this
  · intro j hj
    simp only [if_pos hj]
  · have h2 : ¬ i + 1 ≤ i := Nat.not_succ_le_self i
    simp only [if_neg h2, Nat.sub_self, hg0]

/-- A world the first `i` events of `es` can reach from `w₀` is the `i`-th world of some sequence
    that starts at `w₀` and follows `es`. -/
private theorem path_of_mem_take₅₁ (S : Setup V) (es : List (Record.Event V))
    (w₀ : V → M.N) :
    ∀ (i : Nat) (w : V → M.N), w ∈ (es.take i).foldlM (Record.worldStepOf M S) w₀ →
      ∃ W : Nat → V → M.N, W 0 = w₀ ∧
        (∀ j, W (j + 1) ∈ ((es.drop j).take 1).foldlM (Record.worldStepOf M S) (W j)) ∧
        W i = w
  | 0, w, hw => by
      have hw0 : w = w₀ := by
        simpa [List.take_zero, List.foldlM_nil] using hw
      obtain ⟨g, hg0, hg⟩ := exists_path_from₅₁ S es 0 w₀
      refine ⟨g, hg0, fun j => by simpa using hg j, by rw [hg0, hw0]⟩
  | i + 1, w, hw => by
      rw [List.take_add, List.foldlM_append, Set.bind_def] at hw
      obtain ⟨u, hu, hwu⟩ := Set.mem_iUnion₂.1 hw
      obtain ⟨W, hW0, hW, hWi⟩ := path_of_mem_take₅₁ S es w₀ i u hu
      obtain ⟨W', hW', hW'le, hW'i⟩ := path_splice₅₁ S es W hW i w (by rw [hWi]; exact hwu)
      exact ⟨W', by rw [hW'le 0 (Nat.zero_le i), hW0], hW', hW'i⟩

/-- Every world that can hold before the `i`-th event of `rho` is the world before that event on
    some path of `rho`. -/
private theorem exists_onePath_through₅₁ (S : Setup V) (rho : Record.Run V) (i : Nat)
    (w : V → M.N) (hw : w ∈ Record.stateBeforeOf M S rho i) :
    ∃ W : Nat → V → M.N, Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W ∧ W i = w := by
  obtain ⟨W, hW0, hW, hWi⟩ := path_of_mem_take₅₁ S rho.events (fun v => M.initial S v) i w hw
  have hmem : ∀ j, W j ∈ Record.stateBeforeOf M S rho j := by
    intro j
    induction j with
    | zero =>
        show W 0 ∈ (rho.events.take 0).foldlM (Record.worldStepOf M S) (fun v => M.initial S v)
        rw [hW0]
        exact Set.mem_singleton _
    | succ j ih =>
        show W (j + 1) ∈ (rho.events.take (j + 1)).foldlM (Record.worldStepOf M S)
          (fun v => M.initial S v)
        rw [List.take_add, List.foldlM_append, Set.bind_def]
        exact Set.mem_biUnion ih (hW j)
  refine ⟨W, fun j => ⟨hmem j, ?_⟩, hWi⟩
  rw [Nat.add_sub_cancel_left]
  exact hW j

/-- In a run sorted by key, in every world strictly before `t`, every ancestor of a block of the
    tree of `v`'s core store has a slot at most that block's. -/
private theorem slot_le_of_preceq_any₅₁ (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (t : Time) (v : V) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
      ∀ B : Block V, B ∈ (w v).st.core.T → ∀ X : Block V, Block.Preceq X B → X.slot ≤ B.slot := by
  intro w hw
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho t v w hw
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  rw [stateBeforeTime_eq_strict₅₁ S rho hsorted] at hw
  obtain ⟨W, hW, hWn⟩ := exists_onePath_through₅₁ S rho _ w hw
  refine DecoupledConsensusModel.Sts.preceq_slot_le_of_parentClosed hpc.2 (fun C hC hne => ?_)
  rw [← hWn] at hC
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
      (strictEventIndex rho t) v _ (hW _).1 hC
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho t) v).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW _ D hprocessed with
      hgenesis | ⟨i, -, t', hacc⟩
  · exact absurd (hDe.symm.trans (by rw [hgenesis, erase_named_genesis])) hne
  · simpa only [hDe] using Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW hacc

end

section
open DecoupledConsensusModel.Execution

/-- The store the slot-`s` vote duty reads is the core store of `n`'s store with its clock set to
    the slot-`s` vote instant. -/
private theorem voteStore_eq₅₁ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

private theorem voteStore_T₅₁ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s).T = n.st.core.T := by
  rw [voteStore_eq₅₁ facts, facts.hd.Sts_setClock_core_T]

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
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- For every node state `n` of the round-`r` action read of `v`'s node state in
    `W (strictEventIndex rho (S.a r))` and every outcome `D` of `v`'s attestation duty on `n`, if
    `D`'s attestation carries the finality pair `(H, T)`, then `H` is less than `n`'s running height
    maximum. -/
theorem roundActionFinalityHeight_lt_actionHMax_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) {H : Height} {T : BlockId} :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    D.2.2.finality_pair = some ⟨H, T⟩ →
    H < n.st.core.h_max :=
  roundActionFinality_any₅₁ facts S rho v r _
    (mem_stateBeforeTime_along₅₁ _hf.sorted _hf.onePath _)

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
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- With `w = W (strictEventIndex rho (S.a r))`, if `v`'s record in `w` locks `T` at height `H`,
    then `H` is less than the running height maximum of every node state of `v`'s round-`r` action
    read from `w`. -/
theorem recordLockHeight_lt_actionHMax_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) {H : Height} {T : BlockId}
    (hlock : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy.lock H =
      some T) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    H < n.st.core.h_max :=
  recordLock_any₅₁ facts S hf.sorted hf.tickIndexUnique v r _
    (mem_stateBeforeTime_along₅₁ hf.sorted hf.onePath _) hlock

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
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- With `w = W (strictEventIndex rho (S.a r))`, for every node state `n` of `v`'s round-`r` action
    read from `w` and every outcome `D` of `v`'s attestation duty on `n`, if the own lock of `v`'s
    record in `w` at height `H`, read against `D`'s finality pair, is some block, then `H` is less
    than `n`'s running height maximum. -/
theorem ownLockHeight_lt_actionHMax_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) {H : Height} {locked : BlockId} :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    M.own_lock
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy H
      D.2.2.finality_pair = some locked →
    H < n.st.core.h_max := by
  intro n hn D hD hlock
  cases hfp : D.2.2.finality_pair with
  | none =>
      apply Restated.recordLockHeight_lt_actionHMax_namedOn facts S Hs Xb hf v r (T := locked) _ n hn
      rw [hfp, facts.vc.own_lock_none] at hlock
      exact hlock
  | some p =>
      rcases p with ⟨h, target⟩
      by_cases hh : h = H
      · subst h
        have ht : target = locked := by
          rw [hfp, facts.vc.own_lock_some_self] at hlock
          exact Option.some.inj hlock
        subst target
        exact Restated.roundActionFinalityHeight_lt_actionHMax_namedOn facts
          S Hs Xb hf v r n hn D hD hfp
      · apply Restated.recordLockHeight_lt_actionHMax_namedOn facts S Hs Xb hf v r (T := locked) _ n hn
        rw [hfp, facts.vc.own_lock_some_of_ne _ _ (p := ⟨h, target⟩) hh] at hlock
        exact hlock

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
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- If `v ∈ Xb`, `n` is a node state of the round-`r` action read of `v`'s node state in
    `W (strictEventIndex rho (S.a r))`, and `D` is a body of `n`, then `D` is a run block read
    through `Xb` along `W`. -/
theorem actionBody_runBlock_coverageOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlockOn facts S Hs Xb hf hv hn hD

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
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- If `i` is in the set for `t`, emits along `W` the attestation `a` at `t`, and holds the body `C`
    in its store in `W (strictEventIndex rho t)`, then `a` is not among the attestations of `C`'s
    named chain. -/
theorem emittedAttestation_not_mem_named_chain_beforeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {i : V} {a : NamedAttestation V} {t : Time} {C : NamedBlock V}
    (hi : i ∈ Hs t)
    (hemit : Restated.Vocabulary.Execution.Run.emits M S rho W i (Object.attest a) t)
    (hC : C ∈ (W (strictEventIndex rho t) i).st.bodies) :
    a ∉ Protocol.named_chain_attestations C := by
  have hW := hf.onePath
  intro haC
  have hshape := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemit
  have haHon : a.val_index ∈ Hs t := by
    rw [hshape.1]
    exact hi
  obtain ⟨A, hAC, hrow⟩ :=
    (priv% Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage
      DecoupledConsensusModel.Proofs.HealingSurface.namedChain_row_ancestor) haC
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M
      (W (strictEventIndex rho t) i).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ i _
      (hW (strictEventIndex rho t)).1).1.1.1.2.2.1
  have hAbefore := namedAncestor_mem₅₁ hpc hC hAC
  rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S rho i W hW _ A hAbefore with
    hgen | ⟨j, e, hj, hje, hproc⟩
  · subst A
    rw [named_genesis_attestations] at hrow
    simp at hrow
  · have hjt : e.time < t := time_lt_of_lt_strict₅₁ hf.sorted hje hj
    obtain ⟨hle, -⟩ :=
      Restated.carriedArePastEmissions_of_admissibleCoreOn facts S Hs Xb hf hproc hrow
        (hHs _ _ hjt.le haHon)
    have htime : (Restated.Vocabulary.Execution.Setup.a M S a.round) < t := hle.trans_lt hjt
    rw [← hshape.2] at htime
    exact lt_irrefl t htime

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
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- With `w = W (strictEventIndex rho (proposal_time s))`, if `a`'s signer is in the set for slot
    `s`'s proposal instant, emitted `a` along `W` at `a`'s action instant, and `a`'s erasure is
    among the processed attestations of the proposer's staged core store in `w`, then `a` is among
    the named processed rows of the proposer's store in `w` with its clock set to that instant. -/
theorem exactRow_mem_namedProcessedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} {a : NamedAttestation V}
    (haHon : a.val_index ∈ Hs (M.proposal_time S.E s))
    (hemit : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index (Object.attest a)
      ((Restated.Vocabulary.Execution.Setup.a M S a.round)))
    (hprocessed : a.erase ∈
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s)).processed_attestations S.hc) :
    a ∈ M.processedRows S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) := by
  have hFpre := facts.dt.processed_rows_erasure
  have hW := hf.onePath
  have hwmem := mem_stateBeforeTime_along₅₁ hf.sorted hW (M.proposal_time S.E s)
  have hPool : ∀ r,
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)).core.sg_votes r =
      ((M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)).sg_rows r).map NamedAttestation.erase :=
    (facts.hd.invariant_clock S.E S.cfg _ (M.proposal_time S.E s)
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        (M.proposal_time S.E s) (S.E.proposer s) _ hwmem).1).1.1.2.2.2.1
  have hmap := hFpre S.hc _ hPool
  have hcore : (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core =
      Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s) := by
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  have hmemMap : a.erase ∈
      (M.processedRows S.hc
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))).map NamedAttestation.erase := by
    rw [hmap, hcore]
    exact hprocessed
  obtain ⟨b, hb, hberase⟩ := List.mem_map.mp hmemMap
  obtain ⟨k, hbk⟩ := facts.dt.exists_sg_rows_of_mem_processedRows S.hc _ hb
  rw [facts.hd.setClock_sg_rows] at hbk
  have hbr : b.round = k :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime facts S rho
      (M.proposal_time S.E s) (S.E.proposer s) _ hwmem k b hbk
  have hbN : b ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.sg_rows
      b.round := by
    rw [hbr]
    exact hbk
  have hT : ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho (M.proposal_time S.E s) →
      rho.events[j]? = some e → e.time ≤ M.proposal_time S.E s :=
    fun j e hj he => (time_lt_of_lt_strict₅₁ hf.sorted he hj).le
  have hbval : b.val_index = a.val_index := by
    rw [← namedAttestation_erase_val_index b, ← namedAttestation_erase_val_index a]
    exact congrArg CombinedAttestation.val_index hberase
  have hbHon : b.val_index ∈ Hs (M.proposal_time S.E s) := by
    rw [hbval]
    exact haHon
  obtain ⟨_, _, _, _, _, hbEmit⟩ :=
    Restated.heldArePastEmissions_of_admissibleCoreOn facts S Hs Xb hf hHs _ (S.E.proposer s)
      hT hbN hbHon
  have hbEmit' : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index
      (Object.attest b) ((Restated.Vocabulary.Execution.Setup.a M S b.round)) := by
    simpa only [hbval] using hbEmit
  have hround : b.round = a.round := by
    rw [← namedAttestation_erase_round b, ← namedAttestation_erase_round a]
    exact congrArg CombinedAttestation.round hberase
  have hba : b = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hbEmit' hemit hround
  rw [← hba]
  exact hb

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
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- If round `entry` is positive, `entry + 2 + delayExtra ≤ proposal`, `some B` is a value of the
    proposal of `entry`'s opening slot, the proposer of `proposal`'s opening slot can propose `Q` at
    its read from the world `wq`, and `Q`'s parent is a descendant of `B` at `B`'s derived height,
    then every parent of `Q` has its chain state's target slot plus the timeout delay at most
    `proposal`'s opening slot. -/
theorem laterOpening_timeoutMature_of_sameHeightOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {delayExtra : Nat}
    (hdelay : TimeoutDelayBound S delayExtra)
    {entry proposal : Round}
    (_hentry : 0 < entry)
    (hspace : entry + 2 + delayExtra ≤ proposal)
    {B P Q : NamedBlock V}
    (hB : some B ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho
      ((M.opening_slot S.hc entry)))
    {wq : V → M.N}
    (hwq : wq ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (M.proposal_time S.E (M.opening_slot S.hc proposal)))
    (cq : M.Cache)
    (hcq : M.onPhaseTick S.E S.hc
      (wq (S.E.proposer (M.opening_slot S.hc proposal))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc proposal))
      (wq (S.E.proposer (M.opening_slot S.hc proposal))).cache ⇢ cq)
    (hQ : M.proposal_with (M.gradeContract cq)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc proposal)))
      (M.ns_setClock S.E (wq (S.E.proposer (M.opening_slot S.hc proposal))).st
        (M.proposal_time S.E (M.opening_slot S.hc proposal))) ⇢ some Q)
    (hparent : NamedBlock.parent? Q = some P)
    (hpreceq : NamedBlock.Preceq B P)
    (hsameHeight : (M.derive_named S.E S.cfg P).h =
      (M.derive_named S.E S.cfg B).h) :
    ∀ P' : NamedBlock V, NamedBlock.parent? Q = some P' →
      (M.derive_named S.E S.cfg P').T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc proposal := by
  intro P' hP'
  have hPP' : P' = P := Option.some.inj (hP'.symm.trans hparent)
  subst P'
  have hQ' : some Q ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho
      (M.opening_slot S.hc proposal) :=
    ⟨M.mkNode (M.ns_setClock S.E (wq (S.E.proposer (M.opening_slot S.hc proposal))).st
        (M.proposal_time S.E (M.opening_slot S.hc proposal)))
      (wq (S.E.proposer (M.opening_slot S.hc proposal))).record cq,
      ⟨wq, hwq, cq, hcq, rfl⟩,
      by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
         exact hQ⟩
  obtain ⟨n, hn, hnQ⟩ := hQ'
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract n.cache) S.E
    S.hc (S.node (S.E.proposer (M.opening_slot S.hc proposal))) (M.toHealing n.st.core)
  obtain ⟨parent, hparentQ, hparentErase⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho
      ((M.opening_slot S.hc proposal)) n hn hnQ input hinput
  have hparentEq : parent = P := Option.some.inj (hparentQ.symm.trans hparent)
  subst parent
  have hparentMem := Restated.Vocabulary.Proofs.HealingSurface.proposedParent_mem facts S rho
    ((M.opening_slot S.hc proposal)) n hn input hinput
  obtain ⟨w, hw, c, -, rfl⟩ := hn
  have hTeq : (M.mkNode (M.ns_setClock S.E (w (S.E.proposer (M.opening_slot S.hc proposal))).st
      (M.proposal_time S.E (M.opening_slot S.hc proposal)))
      (w (S.E.proposer (M.opening_slot S.hc proposal))).record c).st.core.T =
      (w (S.E.proposer (M.opening_slot S.hc proposal))).st.core.T := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_T]
  rw [hTeq] at hparentMem
  have hBParent : Block.Preceq B.erase input.parent := by
    rw [← hparentErase]
    exact Proofs.NamedWire.erase_preceq hpreceq
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho _
    (S.E.proposer (M.opening_slot S.hc proposal)) w hw
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  have hBmem : B.erase ∈ (w (S.E.proposer (M.opening_slot S.hc proposal))).st.core.T :=
    Proofs.Records.mem_of_preceq hpc.2 _ _ hparentMem (preceq_eq_true_iff_Preceq.mpr hBParent)
  have htargetSlot :
      (M.derive_named S.E S.cfg B).T_h.slot ≤ B.erase.slot :=
    slot_le_of_preceq_any₅₁ facts S hf.sorted _ _ w hw _ hBmem _
      (Restated.Vocabulary.Proofs.NamedEntryHeight.entry_geometry_ancestor facts S.E S.cfg B)
  have hentrySlot : B.erase.slot = (M.opening_slot S.hc entry) := by
    rw [Proofs.NamedWire.erase_slot,
      Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho _ _ hB rfl]
  have hslot : (M.derive_named S.E S.cfg P).T_h.slot ≤
      (M.opening_slot S.hc entry) := by
    rw [← facts.cs.entry_eq_on_plateau
      S.E S.cfg hpreceq hsameHeight.symm, ← hentrySlot]
    exact htargetSlot
  calc
    (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤
        (M.opening_slot S.hc entry) + (2 + delayExtra) * S.hc.R :=
      Nat.add_le_add hslot (timeoutDelay_le_roundBound S hdelay)
    _ = (M.opening_slot S.hc (entry + (2 + delayExtra))) :=
      (facts.gr.opening_slot_add S.hc entry (2 + delayExtra)).symm
    _ ≤ (M.opening_slot S.hc proposal) := by
      exact facts.gr.opening_slot_le_of_le S.hc (by
        simpa only [Nat.add_assoc] using hspace)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `C` is in the slot-`s` vote staging of `v`'s core store in
    `W (strictEventIndex rho (vote_time s))`, then `C`'s slot is at most `s`. -/
theorem block_slot_le_of_mem_voteStore_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} {C : Block V}
    (hC : C ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T) : C.slot ≤ s := by
  have hW := hf.onePath
  rw [voteStore_T₅₁ facts] at hC
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho _ v _
      (hW _).1 hC
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW _ D hprocessed with
      hgen | ⟨i, hin, t, hacc⟩
  · rw [← hDe, hgen, erase_named_genesis, genesis_slot_inclG2]
    exact Nat.zero_le s
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    have ht : t < M.vote_time S.E s := by
      rw [← het]
      exact time_lt_of_lt_strict₅₁ hf.sorted he hin
    have hslot := Restated.proposal_time_le_of_acceptsAt_blockOn_SlotFreshness facts S Hs Xb hf hacc
    have hk := facts.sch.slot_le_slotOf_of_proposal_time_le S.E (le_of_lt (lt_of_le_of_lt hslot ht))
    rw [facts.sch.slotOf_vote_time, hDe] at hk
    exact hk

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `C` is in the slot-`s` vote staging of `v`'s core store in
    `W (strictEventIndex rho (vote_time s))` and `H` is `C`'s parent, then `H`'s slot is less than
    `C`'s. -/
theorem parent_slot_lt_of_mem_voteStore_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} {C H : Block V}
    (hC : C ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T)
    (hparent : C.parent? = some H) : H.slot < C.slot := by
  have hW := hf.onePath
  rw [voteStore_T₅₁ facts] at hC
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho _ v _
      (hW _).1 hC
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW _ D hprocessed with
      hgen | ⟨i, -, t, hacc⟩
  · exact absurd (hDe.symm.trans (by rw [hgen, erase_named_genesis]))
      (ne_genesis_of_parent?_eq_some hparent)
  · rw [← Proofs.parent_eq_of_parent? hparent]
    simpa only [hDe] using
      Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW hacc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The slot-`s` vote staging of `v`'s core store in `W (strictEventIndex rho (vote_time s))` is
    parent-closed. -/
theorem voteDutyStore_parentClosed_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (s : Slot) :
    Restated.Vocabulary.Internal.ParentClosed M
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s) := by
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
    (M.vote_time S.E s) v _ (mem_stateBeforeTime_along₅₁ _hf.sorted _hf.onePath _)
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc ⊢
  rw [facts.sto.toHealing_gs_T] at hpc ⊢
  rw [voteStore_T₅₁ facts]
  exact hpc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `B` has slot `s`, `X` is in the slot-`s` vote staging of `v`'s core store in
    `W (strictEventIndex rho (vote_time s))`, and `B ⪯ X`, then `X = B`. -/
theorem voteDutyStore_terminal_of_preceq_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} {B X : Block V}
    (hslot : B.slot = s)
    (hX : X ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T)
    (hBX : Block.Preceq B X) : X = B := by
  by_contra hne
  have hBne : B ≠ X := fun h => hne h.symm
  obtain ⟨C, hCparent, hCX⟩ :=
    Protocol.exists_child_towards X (preceq_eq_true_iff_Preceq.mpr hBX) hBne
  have hpc := Restated.voteDutyStore_parentClosed_coreOn facts S Hs Xb hf v s
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  have hCT : C ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T :=
    Proofs.Records.mem_of_preceq hpc.2 C X hX hCX
  have hle := Restated.block_slot_le_of_mem_voteStore_coreOn facts S Hs Xb hf hCT
  have hlt := Restated.parent_slot_lt_of_mem_voteStore_coreOn facts S Hs Xb hf hCT hCparent
  rw [hslot] at hlt
  exact (Nat.not_lt_of_ge hle) hlt

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The conclusion of `voteDutyStore_terminal_of_preceq_coreOn`, from the bundle's hypotheses. -/
theorem voteDutyStore_terminal_of_preceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} {B X : Block V}
    (hslot : B.slot = s)
    (hX : X ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T)
    (hBX : Block.Preceq B X) : X = B :=
  Restated.voteDutyStore_terminal_of_preceq_coreOn facts S Hs Xb hf hslot hX hBX

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades

/-- If slot `s`'s proposer is in `Xb`, the filtered block tree of the proposer's store in
    `W (strictEventIndex rho (proposal_time s))`, with its clock set to the proposal instant, is
    root-injective on ancestors. -/
theorem named_rootInjectiveBelow_source_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hprop : S.E.proposer s ∈ Xb) :
    RootInjectiveBelow (M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core).toFG) := by
  have hW := hf.onePath
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ (S.E.proposer s) _
      (hW _).1).1.1.1
  have hrun : ∀ C ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.bodies,
      Restated.RunBlockOn M S rho W Xb C := fun C hC =>
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hprop hC
  have hinj := Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hf.rootCollisionFree hrun
  rw [← hcoh.1] at hinj
  have hsub : ∀ B ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core).toFG,
      B ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
    intro B hB
    have h := facts.fc.get_filtered_block_tree_subset _ hB
    rw [facts.sto.toHealing_gs_T, facts.hd.Sts_setClock_core_T] at h
    exact h
  refine rootInjectiveBelow_intro (fun A C B₁ B₂ hB₁ hAB₁ hB₂ hCB₂ hroot => ?_)
  exact RootInjectiveBelow.eq_of_root_eq hinj (hsub B₁ hB₁) hAB₁ (hsub B₂ hB₂) hCB₂ hroot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades

/-- If `v ∈ Xb`, every outcome of the voter's filtered block tree of `v`'s slot-`s` vote-duty store,
    without `P`'s erasure, is root-injective on ancestors. -/
theorem named_rootInjectiveBelow_target_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {v : V} (hv : v ∈ Xb)
    {P : NamedBlock V} :
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)).core
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)).core.s ⇢ T →
    RootInjectiveBelow (T.erase P.erase) := by
  intro T hT
  have hW := hf.onePath
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ v _
      (hW _).1).1.1.1
  have hrun : ∀ C ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.bodies,
      Restated.RunBlockOn M S rho W Xb C := fun C hC =>
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hC
  have hinj := Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hf.rootCollisionFree hrun
  rw [← hcoh.1] at hinj
  have hsub : ∀ B ∈ T,
      B ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
    intro B hB
    have h := facts.hd.Sts_voter_filtered_block_tree_subset S.E _ _ T hT hB
    rw [facts.hd.Sts_setClock_core_T] at h
    exact h
  refine rootInjectiveBelow_intro (fun A C B₁ B₂ hB₁ hAB₁ hB₂ hCB₂ hroot => ?_)
  exact RootInjectiveBelow.eq_of_root_eq hinj (hsub B₁ (Finset.mem_of_mem_erase hB₁)) hAB₁
    (hsub B₂ (Finset.mem_of_mem_erase hB₂)) hCB₂ hroot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades

/-- With `n` `v`'s slot-`s` vote-duty read along `W`, if `P`, of slot `s`, is in an outcome `T` of
    the voter's filtered block tree of `n`'s core store, then for every outcome `A` of `n`'s anchor,
    every block `C` other than `A` with `A ⪯ C ⪯ P` is in `T`. -/
theorem named_voter_path_of_candidate_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {v : V} {P : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ c)
    (hslot : P.slot = s) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    P.erase ∈ T →
    ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
    ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C P.erase → C ∈ T := by
  intro n T hT hP A hA C hAC _hCne hCP
  have hwmem := mem_stateBeforeTime_along₅₁ _hf.sorted _hf.onePath (M.vote_time S.E s)
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)) _ := facts.nd.mkNode_st _ _ _
  obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨hPproc, -, ⟨Y, hYproc, hPY, hheight⟩, -⟩ :=
    facts.hd.voter_filtered_block_tree_cases S.E n.st.core n.st.core.s T hT hP Q hQ
  have hFJ : Block.Preceq n.st.core.F n.st.core.J := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.vote_time S.E s) v _ hwmem
  have hPmem : P.erase ∈ n.st.core.T := by
    have h := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ Q hQ hPproc
    rw [facts.sto.toHealing_gs_T] at h
    exact h
  have hpc := Restated.voteDutyStore_parentClosed_coreOn facts S Hs Xb _hf v s
  rw [voteStore_eq₅₁ facts] at hpc
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T, ← facts.nd.store_with_cache_core_T _ c, ← hnst] at hpc
  have hCT : C ∈ n.st.core.T :=
    Proofs.Records.mem_of_preceq hpc.2 C P.erase hPmem
      (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hCP)
  have hroot : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C :=
    Proofs.ModelProperties.Preceq_trans
      (Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S n _ A hA) hAC
  have hCF : Block.Preceq n.st.core.F C :=
    Proofs.ModelProperties.Preceq_trans (facts.fc.finalized_preceq_get_fg_root _ hFJ) hroot
  have hPslot : P.erase.slot = n.st.core.s := by
    rw [Proofs.NamedWire.erase_slot, hslot, hnst, facts.nd.store_with_cache_core_s,
      facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hCproc := facts.fc.mem_voter_processed_block_tree_of_proposal S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s (B := C) (P := P.erase)
    (by rw [facts.sto.toHealing_gs_T]; exact hCT) (by rw [facts.sto.toHealing_gs_T]; exact hPmem)
    hPslot hCP Q hQ
  exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E n.st.core n.st.core.s Q hQ hCproc hCF
    hYproc (Proofs.ModelProperties.Preceq_trans hCP hPY) hheight hroot T hT

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades

/-- The statement of `namedProposalWalkTransferred_of_frozenCompatiblePivot_coreOn`, assuming every
    GHOST step has an outcome. -/
private theorem namedProposalWalkTransferred_core_of_step₅₁ (facts : Record.Facts M)
    (hstepNE : ∀ (tree : Finset (Block V)) (score : Block V → ℕ) (eligible : Block V → Bool)
      (H : Block V), ∃ o : Option (Block V), M.ghost_step tree score eligible H ⇢ o)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {P : NamedBlock V} {pivot : Block V} {v : V}
    (hprop : S.E.proposer s ∈ Xb) (hv : v ∈ Xb)
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ cp)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp
    let m := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some P →
    ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T₀ →
    P.erase ∈ T₀ →
    ∀ A : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ A →
    Block.compatible A P.erase = true →
    ∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R →
    Block.Preceq R pivot →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    Block.Preceq pivot input.parent →
    (∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
     ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
     ∀ sc : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ sc B) →
     ∀ el : Block V → Bool,
      (∀ B : Block V, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) B ⇢ el B) →
     ∀ G : Block V, M.ghost A (T₀.erase P.erase) sc el ⇢ G → Block.Preceq pivot G) →
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho s pivot v P n m →
    (∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
     ∀ srcScore : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E n.st.core.T
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) B ⇢ srcScore B) →
     ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
     ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
     ∀ tgtScore : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ tgtScore B) →
     ∀ C : Block V, C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG →
       C ∈ T₀.erase P.erase → tgtScore C = srcScore C) →
    Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S rho v s m (T₀.erase P.erase)
      input.parent P := by
  intro n m hP T₀ hT₀ hcand A hA hcompat R hR hsourcePivot input hinput hpivotParent
    htargetPasses hsuffix hscore
  have hW := hf.onePath
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)) _ := facts.nd.mkNode_st _ _ _
  have hmst : m.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)) _ := facts.nd.mkNode_st _ _ _
  have hms : m.st.core.s = s := by
    rw [hmst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hnmem : n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
    ⟨W (strictEventIndex rho (M.proposal_time S.E s)),
      mem_stateBeforeTime_along₅₁ hf.sorted hW _, cp, hcp, rfl⟩
  have hslot : P.slot = s :=
    Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts S rho s (some P) ⟨n, hnmem, hP⟩
      rfl
  have hslotErase : P.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact hslot
  have hparent : P.erase.parent? = some input.parent := by
    obtain ⟨Q, hQ, hQerase⟩ := facts.dt.proposal_with_parent? (M.gradeContract n.cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) n.st P (some P) hP rfl input hinput
    simp only [Proofs.NamedWire.erase_parent_optional, hQ, Option.map_some, hQerase]
  have hPH : Block.Preceq input.parent P.erase :=
    Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (preceq_of_parent? hparent)
  have hT₀vote : ∀ Y ∈ T₀, Y ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T := by
    intro Y hY
    have h := facts.hd.Sts_voter_filtered_block_tree_subset S.E m.st.core m.st.core.s T₀ hT₀ hY
    rw [hmst] at h
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    rw [voteStore_eq₅₁ facts]
    exact h
  have hfresh : ∀ C ∈ T₀.erase P.erase, C.parent? ≠ some P.erase := by
    intro C hC hCpar
    have hCT := hT₀vote C (Finset.mem_of_mem_erase hC)
    have hle := Restated.block_slot_le_of_mem_voteStore_coreOn facts S Hs Xb hf hCT
    have hlt := Restated.parent_slot_lt_of_mem_voteStore_coreOn facts S Hs Xb hf hCT hCpar
    rw [hslotErase] at hlt
    exact (Nat.not_lt_of_ge hle) hlt
  have htreeTerminal : ∀ X ∈ T₀, Block.Preceq P.erase X → X = P.erase := fun X hX hPX =>
    Restated.voteDutyStore_terminal_of_preceq_coreOn facts S Hs Xb hf hslotErase (hT₀vote X hX) hPX
  have hanchorTerminal : Block.Preceq P.erase A → A = P.erase := by
    intro hPA
    have hwv := mem_stateBeforeTime_along₅₁ hf.sorted hW (M.vote_time S.E s)
    have hJ : m.st.core.J ∈ m.st.core.T := by
      rw [hmst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.setClock_core_J, facts.hd.Sts_setClock_core_T]
      exact Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts S rho
        _ v _ hwv
    have hF : m.st.core.F ∈ m.st.core.T := by
      rw [hmst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.setClock_core_F, facts.hd.Sts_setClock_core_T]
      exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime facts S rho
        _ v _ hwv
    have hroot : M.get_fg_root (M.toHealing m.st.core).toFG ∈ (M.toHealing m.st.core).T := by
      rcases facts.fc.get_fg_root_eq_J_or_F m.st.core with h | h
      · rw [h, Record.Model.HS.T, facts.sto.toHealing_gs_T]
        exact hJ
      · rw [h, Record.Model.HS.T, facts.sto.toHealing_gs_T]
        exact hF
    obtain ⟨G, hG, hGA⟩ := returns_map_elim₅₁ _ _ _ hA
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing m.st.core)
      (M.round_of S.hc m.st.core.s)
      (M.readFrame m.cache (M.toHealing m.st.core) (M.round_of S.hc m.st.core.s)).g1
    have hGa := facts.nd.Sts_gradeContract_read_anchor _ _ _ _ _ G hG a ha
    have hAmem : A ∈ m.st.core.T := by
      rw [← hGA, hGa, ← facts.sto.toHealing_gs_T]
      exact Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts _ _ _ _ _ hroot a ha
    have hAvote : A ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T := by
      rw [voteStore_eq₅₁ facts, ← facts.nd.store_with_cache_core_T _ cv, ← hmst]
      exact hAmem
    exact Restated.voteDutyStore_terminal_of_preceq_coreOn facts S Hs Xb hf hslotErase hAvote hPA
  have hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C input.parent →
      C ∈ T₀.erase P.erase := by
    intro C hAC hCne hCH
    have hCP : Block.Preceq C P.erase := Proofs.ModelProperties.Preceq_trans hCH hPH
    have hCfull := Restated.named_voter_path_of_candidate_coreOn facts S Hs Xb hf cv hcv hslot
      T₀ hT₀ hcand A hA C hAC hCne hCP
    rw [Finset.mem_erase]
    refine ⟨?_, hCfull⟩
    intro hEq
    subst C
    have hdepth :=
      Block.preceq_depth_le (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hCH)
    have hstrict : input.parent.depth < P.erase.depth := by
      have hparentDepth : P.erase.depth = input.parent.depth + 1 := depth_of_parent? hparent
      omega
    exact (Nat.not_lt_of_ge hdepth) hstrict
  have hsourceRoot : RootInjectiveBelow (M.get_filtered_block_tree (M.toHealing n.st.core).toFG) := by
    rw [hnst, facts.nd.store_with_cache_get_filtered_block_tree]
    exact Restated.named_rootInjectiveBelow_source_coreOn facts S Hs Xb hf hprop
  have htargetRoot : RootInjectiveBelow (T₀.erase P.erase) := by
    have hT₀' := hT₀
    rw [hmst] at hT₀'
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT₀'
    exact Restated.named_rootInjectiveBelow_target_coreOn facts S Hs Xb hf hv T₀ hT₀'
  obtain ⟨psv, hpsv⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s
  obtain ⟨Hh, hHh⟩ := facts.fc.get_head_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core)
    (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s).toFinset psv.toFinset
    ((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s - 1)
  have hparentEq : input.parent = Hh :=
    facts.dt.with_proposal_input_id_parent _ _ _ _ _ input hinput psv hpsv Hh hHh
  have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s) ⇢ R := by
    rw [facts.sto.toHealing_s]
    exact hR
  have hfc := (facts.gr.get_head_with_eq_fork_choice _ _ _ _ _ _ _ R hR' Hh).1 hHh
  rw [facts.sto.toHealing_s] at hpsv hfc
  rw [facts.sto.ModelProperties_toHealing_σ, facts.sto.ModelProperties_toHealing_h_max,
    facts.sto.toHealing_T] at hfc
  choose srcScore hsrcScore using fun B => facts.fc.goldfish_score_nonempty S.E n.st.core.T
    (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
    psv.toFinset (n.st.core.s - 1) B
  choose srcEl hsrcEl using fun B => facts.fc.goldfish_eligible_nonempty S.E n.st.core.σ
    n.st.core.h_max n.st.core.T n.st.core.s
    (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
    psv.toFinset (n.st.core.s - 1) B
  have hsrcGhost := (facts.fc.goldfish_fork_choice_eq_ghost _ _ _ _ _ R _ _ _ _ srcScore hsrcScore
    srcEl hsrcEl Hh).1 hfc
  choose step hstep using fun X => hstepNE
    (M.get_filtered_block_tree (M.toHealing n.st.core).toFG) srcScore srcEl X
  have hhead : ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
      ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
      ∀ X : Block V, M.get_head_in_tree_with_layer (M.gradeContract m.cache) S.E S.hc
        (M.toHealing m.st.core) T₀ vv vsv (m.st.core.s - 1) ⇢ X → X = P.erase := by
    intro vv hvv vsv hvsv X hX
    obtain ⟨R', hR'⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract m.cache) S.E S.hc
      (M.toHealing m.st.core) (M.round_of S.hc (M.toHealing m.st.core).toFG.toSG.toGoldfishStore.s)
    have hR'A : R' = A := by
      obtain ⟨G, hG, hGA⟩ := returns_map_elim₅₁ _ _ _ hA
      rw [← hGA]
      have hR'' := hR'
      rw [facts.sto.toHealing_s] at hR''
      exact facts.fc.get_sg_root_with_eq_read_anchor _ _ _ _ _ G hG R' hR''
    have hfcX := (facts.fc.get_head_in_tree_split_with _ _ _ _ _ _ _ _ R' hR' X).1 hX
    rw [Record.Model.HS.σ, Record.Model.HS.h_max, Record.Model.HS.T, Record.Model.HS.s,
      facts.sto.ModelProperties_toHealing_σ, facts.sto.ModelProperties_toHealing_h_max,
      facts.sto.toHealing_T, facts.sto.toHealing_s, hR'A] at hfcX
    choose sc hsc using fun B => facts.fc.goldfish_score_nonempty S.E m.st.core.T vv vsv
      (m.st.core.s - 1) B
    choose el hel using fun B => facts.fc.goldfish_eligible_nonempty S.E m.st.core.σ
      m.st.core.h_max m.st.core.T m.st.core.s vv vsv (m.st.core.s - 1) B
    have hXg := (facts.fc.goldfish_fork_choice_eq_ghost _ _ _ _ _ A _ _ _ _ sc hsc el hel X).1 hfcX
    have hforward : Block.Preceq A P.erase → Block.Preceq P.erase X := by
      intro hAP
      by_cases hEq : A = P.erase
      · rw [← hEq]
        exact facts.fc.ghost_preceq _ _ _ _ X hXg
      · have hAH : Block.Preceq A input.parent :=
          Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
            (Proofs.Optimistic.preceq_parent_of_ne hparent
              (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hAP) hEq)
        obtain ⟨G', hG'⟩ := facts.fc.ghost_nonempty A (T₀.erase P.erase) sc el
        have hpasses := htargetPasses vv hvv vsv hvsv sc hsc el hel G' hG'
        have hpersist : ∀ (Y C : Block V), Block.Preceq pivot Y → Block.Preceq Y input.parent →
            Y ≠ input.parent → step Y = some C → Block.Preceq C input.parent →
            C ∈ T₀.erase P.erase ∧ el C = true := by
          intro Y C h1 h2 h3 h4 h5
          obtain ⟨hmemC, helC⟩ := hsuffix.persist input hinput psv hpsv srcScore hsrcScore srcEl
            hsrcEl T₀ hT₀ vv hvv vsv hvsv Y C h1 h2 h3 (by rw [← h4]; exact hstep Y) h5
          exact ⟨hmemC, helC _ (hel C)⟩
        have hreflect : ∀ (Y C : Block V), Block.Preceq pivot Y → Block.Preceq Y input.parent →
            C ∈ T₀.erase P.erase → C.parent? = some Y → el C = true →
            C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG ∧ srcEl C = true := by
          intro Y C h1 h2 h3 h4 h5
          obtain ⟨hC, hsel⟩ := hsuffix.reflect input hinput psv hpsv T₀ hT₀ vv hvv vsv hvsv Y C
            h1 h2 h3 h4 (by rw [← h5]; exact hel C)
          exact ⟨hC, hsel _ (hsrcEl C)⟩
        have hscore' : ∀ C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG,
            C ∈ T₀.erase P.erase → sc C = srcScore C := fun C h1 h2 =>
          hscore psv hpsv srcScore hsrcScore vv hvv vsv hvsv sc hsc C h1 h2
        obtain ⟨hstopped, hwalk⟩ :=
          facts.fc.ghost_transport_via_bridge_of_target_passes hsourceRoot htargetRoot Hh hsrcGhost
            hparentEq.symm hsourcePivot hpivotParent hAH hpath G' hG' hpasses step hstep hpersist
            hreflect hscore'
        have hPcur : P.erase.slot = m.st.core.s := by rw [hslotErase, hms]
        obtain ⟨g, hg⟩ := facts.fc.goldfish_score_nonempty S.E m.st.core.T vv vsv
          (m.st.core.s - 1) P.erase
        have helig : el P.erase = true :=
          (facts.fc.goldfish_eligible_iff S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
            vv vsv (m.st.core.s - 1) P.erase (el P.erase) (hel P.erase) g hg).2
            (Or.inr (Or.inr hPcur))
        have hinsert := facts.fc.ghost_insert_eq hparent helig (Finset.notMem_erase _ _)
          (fun C hC hCP => hstopped C hC hCP) hfresh G' hG' hwalk X
          (by rw [Finset.insert_erase hcand]; exact hXg)
        rw [hinsert]
        exact Proofs.ModelProperties.Preceq_self _
    exact facts.fc.ghost_eq_of_compatible_anchor_and_terminal X hXg hcompat hforward
      hanchorTerminal htreeTerminal
  have htreeEq : ∀ T : Finset (Block V),
      M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T → T = T₀ := by
    intro T hT
    obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
      (M.toHealing m.st.core).toFG.toSG.toGoldfishStore (M.toHealing m.st.core).s
    have h1 := facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E m.st.core Q hQ
      T hT
    have h2 := facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E m.st.core Q hQ
      T₀ hT₀
    rw [← h1, ← h2]
  refine ⟨?_, hparent, ?_, Finset.notMem_erase _ _, hfresh, ?_⟩
  · rw [hslot, hms]
  · intro T hT
    rw [htreeEq T hT, Finset.insert_erase hcand]
  · intro T hT vv hvv vsv hvsv X hX
    rw [htreeEq T hT] at hX
    exact hhead vv hvv vsv hvsv X hX

/-- With `n` the slot-`s` proposer's read and `m` `v`'s slot-`s` vote read along `W`: if the
    proposal duty on `n` can return `P`, the proposer and `v` are in `Xb`, `P`'s erasure is in an
    outcome `T₀` of `v`'s filtered block tree at `m` and compatible with an outcome `A` of `m`'s
    anchor, `pivot` lies between an outcome of `n`'s SG root and the proposed parent `input.parent`,
    every outcome of `v`'s walk from `A` descends from `pivot`, the suffix from `pivot` transfers
    between `n` and `m`, and the two walks' scores agree on common blocks, then `m` extends
    `input.parent` by `P` over `T₀` without `P`. -/
theorem namedProposalWalkTransferred_of_frozenCompatiblePivot_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {P : NamedBlock V} {pivot : Block V} {v : V}
    (hprop : S.E.proposer s ∈ Xb) (hv : v ∈ Xb)
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ cp)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp
    let m := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some P →
    ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T₀ →
    P.erase ∈ T₀ →
    ∀ A : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ A →
    Block.compatible A P.erase = true →
    ∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R →
    Block.Preceq R pivot →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    Block.Preceq pivot input.parent →
    (∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
     ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
     ∀ sc : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ sc B) →
     ∀ el : Block V → Bool,
      (∀ B : Block V, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) B ⇢ el B) →
     ∀ G : Block V, M.ghost A (T₀.erase P.erase) sc el ⇢ G → Block.Preceq pivot G) →
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho s pivot v P n m →
    (∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
     ∀ srcScore : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E n.st.core.T
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) B ⇢ srcScore B) →
     ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
     ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
     ∀ tgtScore : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ tgtScore B) →
     ∀ C : Block V, C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG →
       C ∈ T₀.erase P.erase → tgtScore C = srcScore C) →
    Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S rho v s m (T₀.erase P.erase)
      input.parent P :=
  namedProposalWalkTransferred_core_of_step₅₁ facts facts.fc.ghost_step_nonempty S Hs Xb hf hprop hv
    cp hcp cv hcv

/-- The conclusion of `namedProposalWalkTransferred_of_frozenCompatiblePivot_coreOn`, from the
    bundle's hypotheses. -/
theorem namedProposalWalkTransferred_of_frozenCompatiblePivotOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {P : NamedBlock V} {pivot : Block V} {v : V}
    (hprop : S.E.proposer s ∈ Xb) (hv : v ∈ Xb)
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ cp)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp
    let m := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some P →
    ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T₀ →
    P.erase ∈ T₀ →
    ∀ A : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ A →
    Block.compatible A P.erase = true →
    ∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R →
    Block.Preceq R pivot →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    Block.Preceq pivot input.parent →
    (∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
     ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
     ∀ sc : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ sc B) →
     ∀ el : Block V → Bool,
      (∀ B : Block V, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) B ⇢ el B) →
     ∀ G : Block V, M.ghost A (T₀.erase P.erase) sc el ⇢ G → Block.Preceq pivot G) →
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho s pivot v P n m →
    (∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
     ∀ srcScore : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E n.st.core.T
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) B ⇢ srcScore B) →
     ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
     ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
     ∀ tgtScore : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ tgtScore B) →
     ∀ C : Block V, C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG →
       C ∈ T₀.erase P.erase → tgtScore C = srcScore C) →
    Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S rho v s m (T₀.erase P.erase)
      input.parent P :=
  Restated.namedProposalWalkTransferred_of_frozenCompatiblePivot_coreOn facts S Hs Xb hf hprop hv
    cp hcp cv hcv

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

/-! ### Helpers -/

open scoped DC

/-- The world `W (strictEventIndex rho t)` of the bundle's path is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_strict₅₁b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [Restated.stateBeforeTime_eq_stateBefore_strictEventIndexOn facts S Hs Xb hf t]
  exact (hf.onePath _).1

/-- For every outcome `c` of the cache update at slot `s`'s proposal instant on the proposer's node
    state along `W`, the node state built from its store with the clock set, its signing record and
    `c` is one of `proposerReadAt M S rho s`. -/
private theorem proposerRead_mem₅₁b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
  ⟨W (strictEventIndex rho (M.proposal_time S.E s)),
    mem_stateBeforeTime_strict₅₁b facts S hf _, c, hc, rfl⟩

/-- For every outcome `c` of the cache update at slot `s`'s proposal instant on the proposer's node
    state along `W`, every outcome of the proposal duty run with `c`'s grade contract is one of
    `proposedBlockAt M S rho s`. -/
private theorem proposedBlockAt_mem₅₁b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {o : Option (NamedBlock V)}
    (ho : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ o) :
    o ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s :=
  ⟨_, proposerRead_mem₅₁b facts S hf s c hc,
    by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
       exact ho⟩

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₁b {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_reach_le₅₁b {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {m n : Nat} (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₁b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
private theorem strictEventIndex_mono₅₁b (rho : Record.Run V) {d t : Time} (hdt : d ≤ t) :
    strictEventIndex rho d ≤ strictEventIndex rho t :=
  (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_lt_of_le he hdt)).length_le

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, every event before index `strictEventIndex rho t` is strictly before
    `t`. -/
private theorem time_lt_of_lt_strict₅₁b {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho t → rho.events[j]? = some e →
      e.time < t := by
  intro j e hj he
  by_contra hnot
  have hle : t ≤ e.time := le_of_not_gt hnot
  have hlen : (rho.events.filter (fun e => decide (e.time < t))).length ≤ j := by
    have hpre : rho.events.filter (fun e => decide (e.time < t)) =
        rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
      refine List.prefix_iff_eq_take.mp ?_
      rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
        (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
      · exact List.takeWhile_prefix _
      · intro e f hk hf
        simp only [decide_eq_true_eq] at hf ⊢
        exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
    by_contra hlt
    have hlt' : j < (rho.events.filter (fun e => decide (e.time < t))).length :=
      Nat.lt_of_not_ge hlt
    have hmem : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
      rw [hpre]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt']; exact he)
    have hp := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq] at hp
    exact absurd hp (not_lt.mpr hle)
  exact absurd hj (not_lt.mpr hlen)

/-- Every node state the round-`r` action read from `before` can give holds the bodies of `before`'s
    store. -/
private theorem actionReadFrom_bodies₅₁b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- On the path `W` of the bundle, if `0 < s` and the proposal duty at the slot-`s` proposer's read
    can return `some B`, then `B`'s parent's slot is less than `B`'s slot. -/
theorem proposedBlock_parent_slot_ltOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hs : 0 < s)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    B.erase.parent.slot < B.erase.slot := by
  have hn := proposerRead_mem₅₁b facts S hf s c hc
  have hst := facts.nd.mkNode_st
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c
  have hcache := facts.nd.mkNode_cache
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c
  generalize M.mkNode
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c = n at hn hst hcache
  have hB' : M.proposal_with (M.gradeContract n.cache)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s)) n.st ⇢ some B := by
    rw [hst, hcache, facts.dt.proposal_with_store_with_cache]
    exact hB
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing n.st.core)
  have hpar := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockErased_parent facts S rho s n
    hn hB' input hinput
  have hsslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts S rho s _ ⟨n, hn, hB'⟩ rfl
  have hmem : B.erase.parent ∈ n.st.core.T := by
    rw [hpar]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedParent_mem facts S rho s n hn input hinput
  rw [hst, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T] at hmem
  rw [hsslot]
  exact Restated.block_slot_lt_of_mem_beforeTime_of_le_proposalOn facts
    S Hs Xb hf hs (le_refl (M.proposal_time S.E s)) hmem

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

/-- On the path `W` of the bundle, if `0 < s`, the proposal duty at the slot-`s` proposer's read can
    return `some B`, and the event at index `i` is the proposer's tick at the proposal instant,
    which has an outcome and passes the grade-1 awake test, then the proposer emits `B` at that
    instant. -/
theorem proposal_emits_of_tickOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hs : 0 < s)
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
    {i : Nat}
    (hi : rho.events[i]? =
      some (.tick (S.E.proposer s) (M.proposal_time S.E s)))
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick S (S.E.proposer s) (W i (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade1 S (S.E.proposer s) (W i (S.E.proposer s)) (M.round_of S.hc s)) :
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W (S.E.proposer s) (.block B)
      (M.proposal_time S.E s) := by
  have _hr_0 : M.reachedNode (W i (S.E.proposer s)) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 (S.E.proposer s)
  have _hr_1 : M.reachedNode (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (M.proposal_time S.E s)) (W (strictEventIndex rho (M.proposal_time S.E s))) (hf.onePath (strictEventIndex rho (M.proposal_time S.E s))).1 (S.E.proposer s)
  have hsame := Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hi
  have hst : (W i (S.E.proposer s)).st =
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st := by
    rcases hsame with h | h
    · rw [h]
    · rw [h, (facts.nd.wake_st_record _).1]
  have hcache : (W i (S.E.proposer s)).cache =
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache := by
    rcases hsame with h | h
    · rw [h]
    · rw [h, facts.nd.wake_cache]
  have _hv_0 : M.runs_as (W i (S.E.proposer s)) (S.E.proposer s) :=
    facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 (S.E.proposer s)
  have hc' : M.onPhaseTick S.E S.hc (W i (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W i (S.E.proposer s)).cache ⇢ c := by
    rw [hst, hcache]; exact hc
  have hslot : S.E.slotOf (M.proposal_time S.E s) = s := facts.sch.slotOf_proposal_time S.E s
  obtain ⟨out₀, hout₀⟩ := id hneTick
  obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S (S.E.proposer s) (W i (S.E.proposer s))
    (M.proposal_time S.E s) out₀ hout₀ (by rw [hslot]; exact hs) (by rw [hslot]) (by rw [hslot])
    (by rw [hslot]; exact hrun) c hc'
  rw [← facts.nd.gradeContract_eq_frameContract] at hD
  have hD' : M.duties_propose_block_with (M.gradeContract c) S.E S.hc S.cfg (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ D := by
    rw [← hst]; exact hD
  have ho := Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_proposal_mem facts S (S.E.proposer s)
    (W i (S.E.proposer s)) s hs
    (S.node_val_index (S.E.proposer s)).symm c hc' D hD
    (facts.dt.propose_block_with_snd_of_some _ _ _ _ _ _ (some B) hB rfl D hD') hrun
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho hi (W i)
      (hf.onePath i).1 (W (i + 1)) (hf.onePath i).2 with ⟨out, hout, hw⟩ | ⟨hno, -⟩
  · refine ⟨i, hi, out, hout, hw, ho out ?_⟩
    exact hout
  · obtain ⟨out, hout⟩ := hneTick
    exact absurd hout (hno out)

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

/-- Under the hypotheses of `proposal_emits_of_tickOn`, the proposer accepts `B` at index `i`, at
    the proposal instant, along `W`. -/
theorem acceptsAt_proposedBlock_of_tickOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hs : 0 < s)
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
    {i : Nat}
    (hi : rho.events[i]? =
      some (.tick (S.E.proposer s) (M.proposal_time S.E s)))
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick S (S.E.proposer s) (W i (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade1 S (S.E.proposer s) (W i (S.E.proposer s)) (M.round_of S.hc s)) :
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i (S.E.proposer s) (.block B)
      (M.proposal_time S.E s) := by
  obtain ⟨i₁, hi₁, out, hout, hW1, hemem⟩ :=
    Restated.proposal_emits_of_tickOn facts S Hs Xb hf hs c hc hB hi hneTick hrun
  have hij : i₁ = i := tick_index_eq_of_unique hf.tickIndexUnique hi₁ hi
  subst hij
  have hadmit := Restated.proposedBlockAt_admitOn facts S Hs Xb hf s hs hi₁ c hc hB
  have hsame := Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hi₁
  have hst : (W i₁ (S.E.proposer s)).st =
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st := by
    rcases hsame with h | h
    · rw [h]
    · rw [h, (facts.nd.wake_st_record _).1]
  have hmem : B ∈ (W (i₁ + 1) (S.E.proposer s)).st.bodies := by
    obtain ⟨c', hc'⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W i₁ (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W i₁ (S.E.proposer s)).cache
    have _hr_i := facts.ndRun.stateBeforeOf_reachedNode S rho i₁ (W i₁) (hf.onePath i₁).1 (S.E.proposer s)
    have _hv_i := facts.ndRun.stateBeforeOf_runs_as S rho i₁ (W i₁) (hf.onePath i₁).1 (S.E.proposer s)
    obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S (S.E.proposer s) (W i₁ (S.E.proposer s))
      (M.proposal_time S.E s) out hout
      (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hemem).1.1
      (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hemem).1.2.1
      (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hemem).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S _ _ _ out hout hemem) c' hc'
    have hD2 : D.2 = some B :=
      (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hemem).2 c' hc' D hD
    have _hr_s1 := facts.sto.reachedStore_setClock S.E _ (M.proposal_time S.E s) (facts.nd.reachedStore_of_node _ (facts.ndRun.stateBeforeOf_reachedNode S rho i₁ (W i₁) (hf.onePath i₁).1 (S.E.proposer s)))
    have hDeq := facts.dt.propose_block_with_eq_of_snd _ _ _ _ _ _ D hD hD2
    have hdue : 0 < S.E.slotOf (M.proposal_time S.E s) ∧
        M.proposal_time S.E s = M.proposal_time S.E (S.E.slotOf (M.proposal_time S.E s)) ∧
        S.E.proposer (S.E.slotOf (M.proposal_time S.E s)) =
          (S.node (S.E.proposer s)).val_index := by
      rw [facts.sch.slotOf_proposal_time]
      exact ⟨hs, rfl, (S.node_val_index (S.E.proposer s)).symm⟩
    have hawake := facts.nd.block_mem_on_tick_emit_awake S _ _ _ out hout hemem
    have hbod :=
      ((facts.nd.tick_bodies_and_coreT_from_proposal S _ _ _ out hout).1
        ⟨hdue.1, hdue.2.1, hdue.2.2, hawake⟩ c' hc' D hD).1
    rw [hW1, hbod, hDeq, hst]
    simp only [facts.nd.store_with_cache_bodies]
    exact hadmit
  refine ⟨⟨Or.inl ⟨M.proposal_time S.E s, hi₁, out, hout, hW1, hemem⟩,
      ⟨.tick (S.E.proposer s) (M.proposal_time S.E s), hi₁, rfl, rfl⟩⟩, ?_, ?_⟩
  · simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
    rw [hst]
    intro hmemB
    have hn := proposerRead_mem₅₁b facts S hf s c hc
    have htree := (Restated.Vocabulary.Proofs.HealingSurface.proposerReadAt_invariant facts S rho s
      _ hn).1.1
    unfold Restated.Vocabulary.Proofs.NamedStore.TreeView at htree
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_bodies] at htree
    have hmemR : B ∈ (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)).bodies := by
      rw [facts.hd.ModelProperties_setClock_bodies]
      exact hmemB
    exact Restated.proposedBlockErased_fresh_at_tickOn facts S Hs Xb hf s hs c hc hB
      (htree ▸ Finset.mem_image_of_mem NamedBlock.erase hmemR)
  · simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    exact hmem

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

/-- On the path `W` of the bundle, if `0 < s`, slot `s`'s proposer is in the set for `s`'s
    confirmation instant, `lo ≤ proposal_time s ≤ horizon`, the proposer's tick at the proposal
    instant has an outcome and passes the grade-1 awake test, and the proposal duty at its read can
    return `some B`, then the proposer accepts `B` at some index, at the proposal instant. -/
theorem acceptsAt_proposedBlock_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    ∃ i : Nat, Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i (S.E.proposer s)
      (.block B) (M.proposal_time S.E s) := by
  obtain ⟨B0, -, -, i, hi, out, hout, -⟩ :=
    Restated.proposedBlockAt_emits_of_honestOn facts S Hs Xb hf hHs s hs hprop hhor hgat hneTick
      hrun c hc (some B) hB
  exact ⟨i, Restated.acceptsAt_proposedBlock_of_tickOn facts S Hs Xb hf hs c hc hB hi ⟨out, hout⟩
    (hrun i hi)⟩

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

/-- The conclusion of `acceptsAt_proposedBlock_coreOn`, from the bundle's hypotheses. -/
theorem acceptsAt_proposedBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    ∃ i : Nat, Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i (S.E.proposer s)
      (.block B) (M.proposal_time S.E s) :=
  Restated.acceptsAt_proposedBlock_coreOn facts S Hs Xb hf hHs hs hprop hhor hgat hneTick hrun c hc
    hB

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

/-- Under the hypotheses of `acceptsAt_proposedBlock_coreOn` and `hHsXb`, the proposal `B` is a run
    block read through `Xb` along `W`. -/
theorem proposedBlock_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    Restated.RunBlockOn M S rho W Xb B :=
  Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb s hs hprop hhor hgat
    hneTick hrun c hc hB

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

/-- On the path `W` of the bundle, if `p` is in the set for `max t lo` and accepts `B` (of positive
    slot) at `t`, `t < GammaIn`, `lo ≤ GammaIn`, `GammaIn + Δ = GammaOut ≤ horizon`, `w` is in the
    set for `GammaOut`, and the finalized block of `w`'s store in `W j` is an ancestor of `B` for
    every `j` up to the number of events before `GammaOut`, then `w` accepts `B` at some index, at a
    time before `GammaOut`. -/
theorem named_acceptsAt_after_cutoffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {p w : V} {i : Nat} {B : NamedBlock V} {t GammaIn GammaOut : Time}
    (hp : p ∈ Hs (max t lo)) (hw : w ∈ Hs GammaOut)
    (hBpos : 0 < B.slot)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i p (.block B) t)
    (htIn : t < GammaIn) (hgst : lo ≤ GammaIn)
    (hhop : GammaIn + S.E.Δ = GammaOut)
    (hhor : GammaOut ≤ rho.horizon)
    (hFhist : ∀ j : Nat,
      j ≤ (rho.events.filter (fun e => decide (e.time < GammaOut))).length →
        Block.Preceq (W j w).st.core.F B.erase) :
    ∃ j : Nat, ∃ t' : Time,
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j w (.block B) t' ∧
        t' < GammaOut := by
  have hinOut : GammaIn < GammaOut := by
    rw [← hhop]
    exact lt_add_of_pos_right GammaIn S.E.Δ_pos
  have hacceptCutoff : t < GammaOut := lt_trans htIn hinOut
  have hmax : max t lo ≤ GammaIn :=
    max_le (le_of_lt htIn) hgst
  have hrelayCutoff : max t lo + S.E.Δ ≤ GammaOut := by
    calc
      max t lo + S.E.Δ ≤ GammaIn + S.E.Δ := by
        simpa only [add_comm] using add_le_add_right hmax S.E.Δ
      _ = GammaOut := hhop
  have hrelayHorizon : max t lo + S.E.Δ ≤ rho.horizon :=
    le_trans hrelayCutoff hhor
  have hwRelay : w ∈ Hs (max t lo + S.E.Δ) := hHs _ _ hrelayCutoff hw
  have hearlier : ∀ {j₀ j : Nat} {t₀ : Time} {ej : Record.Event V}, j₀ < j →
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j₀ w (.block B) t₀ →
      rho.events[j]? = some ej → t₀ ≤ ej.time := by
    intro j₀ j t₀ ej hlt hacc₀ hej
    obtain ⟨-, e₀, he₀, -, ht₀⟩ := hacc₀.1
    rw [← ht₀]
    exact Restated.time_le_of_key_le
      (Restated.key_le_of_index_ltOn facts S Hs Xb hf hlt he₀ hej)
  by_cases halready : Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st (.block B) = true
  · rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho w W hf.onePath
      (i + 1) B halready with
      hgen | ⟨j, hj, t', hacc'⟩
    · exact False.elim ((Nat.ne_of_gt hBpos) (by rw [hgen]; exact named_genesis_slot))
    · obtain ⟨-, e', he', -, ht'⟩ := hacc'.1
      obtain ⟨-, e, he, -, ht⟩ := hacc.1
      have ht'le : t' ≤ t := by
        rw [← ht', ← ht]
        have hji : j ≤ i := Nat.le_of_lt_succ hj
        rcases hji.lt_or_eq with hlt | rfl
        · exact Restated.time_le_of_key_le
            (Restated.key_le_of_index_ltOn facts S Hs Xb hf hlt he' he)
        · have heq : e' = e := Option.some.inj (he'.symm.trans he)
          rw [heq]
      exact ⟨j, t', hacc', lt_of_le_of_lt ht'le hacceptCutoff⟩
  · have halreadyFalse :
        Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st (.block B) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hdmem := mem_stateBeforeTime_strict₅₁b facts S hf (max t lo + S.E.Δ)
    have hFdeadline : Block.Preceq
        (W (strictEventIndex rho (max t lo + S.E.Δ)) w).st.core.F B.erase := by
      have hFgamma : Block.Preceq (W (strictEventIndex rho GammaOut) w).st.core.F B.erase :=
        hFhist _ le_rfl
      have hFtime := Restated.Vocabulary.Proofs.stateBeforeTime_F_mono_of_le facts S rho hf.sorted
        (w := w) hrelayCutoff _ hdmem _
        (onePath_reach_le₅₁b hf.onePath (strictEventIndex_mono₅₁b rho hrelayCutoff))
      exact preceq_trans_Preceq hFtime hFgamma
    have hguard := Restated.Vocabulary.Proofs.not_excludes_of_F_preceq_later_time facts S rho
      hf.sorted (w := w) (B := B) le_rfl _ hdmem _ (onePath_reach_le₅₁b hf.onePath le_rfl)
      hFdeadline
    obtain ⟨t', htt', ht'hi, j, hproc, hslotDeliv⟩ :=
      hf.relay_block_admit p i B t hp hacc w hwRelay halreadyFalse hrelayHorizon hguard
    have ht'cutoff : t' < GammaOut := lt_of_lt_of_le ht'hi hrelayCutoff
    obtain ⟨hidx, e, hej, _, heTime⟩ := hproc
    rcases hidx with ⟨ttick, htick, out, hout, hW1, hmem⟩ | ⟨tdeliv, hdeliv⟩
    · have heTickEq : e = Record.Event.tick w ttick := Option.some.inj (hej.symm.trans htick)
      have httickEq : ttick = t' := by
        rw [heTickEq] at heTime
        exact heTime
      rw [httickEq] at htick hout
      have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (.block B) t' :=
        ⟨j, htick, out, hout, hW1, hmem⟩
      obtain ⟨-, ht'eq, hweq⟩ := Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts S
        rho W hf.onePath hemit
      subst ht'eq
      subst hweq
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E B.slot)) (S.E.proposer B.slot)).st.core.toHealing
        (M.proposal_time S.E B.slot)
        (W (strictEventIndex rho (M.proposal_time S.E B.slot)) (S.E.proposer B.slot)).cache
      obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract c) .poolAndCarried S.E S.hc
        (S.node (S.E.proposer B.slot))
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E B.slot)) (S.E.proposer B.slot)).st
          (M.proposal_time S.E B.slot))
      have hoMem := proposedBlockAt_mem₅₁b facts S hf B.slot c hc ho
      obtain ⟨B', rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts S rho
        B.slot _ hoMem
      have hawake := facts.nd.block_mem_on_tick_emit_awake S _ _ _ out hout hmem
      rw [facts.sch.slotOf_proposal_time] at hawake
      have hemit' := Restated.proposal_emits_of_tickOn facts S Hs Xb hf hBpos c hc ho htick
        ⟨out, hout⟩ hawake
      have hB'slot : B'.slot = B.slot :=
        Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho B.slot _ hoMem rfl
      have hBB' : B = B' := Restated.emits_block_uniqueOn facts S Hs Xb hf hemit hemit' hB'slot.symm
      rw [← hBB'] at ho
      exact ⟨j, _, Restated.acceptsAt_proposedBlock_of_tickOn facts S Hs Xb hf hBpos c hc ho htick
        ⟨out, hout⟩ hawake, ht'cutoff⟩
    · have heDelivEq : e = Record.Event.deliver w (.block B) tdeliv :=
        Option.some.inj (hej.symm.trans hdeliv)
      have htdelivEq : tdeliv = t' := by
        rw [heDelivEq] at heTime
        exact heTime
      rw [htdelivEq] at hdeliv
      by_cases hbefore :
          Restated.Vocabulary.Execution.Object.processed M (W j w).st (.block B) = true
      · rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho w W hf.onePath j B
          hbefore with
          hgen | ⟨j₀, hj₀, t₀, hacc₀⟩
        · exact False.elim ((Nat.ne_of_gt hBpos) (by rw [hgen]; exact named_genesis_slot))
        · have ht₀ : t₀ ≤ t' := hearlier hj₀ hacc₀ hdeliv
          exact ⟨j₀, t₀, hacc₀, lt_of_le_of_lt ht₀ ht'cutoff⟩
      · have hfresh : Restated.DeliveryFreshAt M S rho W j := by
          intro u o tu hu
          rw [hdeliv] at hu
          cases Option.some.inj hu
          exact Bool.eq_false_of_not_eq_true hbefore
        have hslot : ¬ (W j w).st.core.s < B.erase.slot :=
          Nat.not_lt.mpr (hslotDeliv hdeliv)
        have hjBound := Restated.index_succ_le_strict_filter_length rho hf.sorted GammaOut
          hdeliv (by simpa only [Record.Event.time] using ht'cutoff)
        have haccept := Restated.acceptsAt_block_of_delivery_guardsOn facts S Hs Xb hf (hHsXb _ hw)
          hfresh hdeliv hslot (hFhist j (Nat.le_trans (Nat.le_succ j) hjBound))
          (Restated.Vocabulary.Protocol.proposer_eq_of_acceptsAt_block facts S W hf.onePath hacc)
          (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
          (Restated.Vocabulary.Protocol.carried_attestations_admissible_of_acceptsAt_block facts S W
            hf.onePath hacc)
        exact ⟨j, t', haccept, ht'cutoff⟩

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

/-- On the path `W` of the bundle, if `p` is in the set for `S.a r`, `w` in the set for `S.a r + Δ`,
    `D` is a body of a node state of `p`'s round-`r` action read descending from `P` with height at
    least `h`, `lo ≤ S.a r`, `S.a r + Δ ≤ read ≤ horizon`, and the FG root of `w`'s store strictly
    before `read` is an ancestor of `P`, then `D` is a body of that store. -/
theorem actionConeWitness_visibleAtReader_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {p w : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    {P : Block V} {D : NamedBlock V} {h : Height} {read : Time}
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hDT : D ∈ n.st.bodies)
    (hPD : Block.Preceq P D.erase)
    (hheight : h ≤ (M.derive_named S.E S.cfg D).h)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hrootP : Block.Preceq
      (M.get_fg_root (W (strictEventIndex rho read) w).st.toHealing.toFG) P) :
    D ∈ (W (strictEventIndex rho read) w).st.bodies ∧
      Block.Preceq P D.erase ∧
        h ≤ (M.derive_named S.E S.cfg D).h := by
  have hD_n : D ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.bodies := by
    rw [← actionReadFrom_bodies₅₁b facts S _ r n hn]
    exact hDT
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD_n
  have hreadMem := mem_stateBeforeTime_strict₅₁b facts S hf read
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho p W hf.onePath _ D
      hprocessed with
    hgen | ⟨i, hi, t, hacc⟩
  · subst D
    have hcohTarget := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      read w _ hreadMem).1.1.1
    exact ⟨hcohTarget.2.2.1.1, hPD, hheight⟩
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have htIn : t < (Restated.Vocabulary.Execution.Setup.a M S r) := by
      simpa only [het] using time_lt_of_lt_strict₅₁b hf.sorted _ i e hi he
    have hDpos : 0 < D.slot := by
      have hparent := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W
        hf.onePath hacc
      have hslot : D.erase.slot = D.slot := Proofs.NamedWire.erase_slot D
      rw [hslot] at hparent
      exact Nat.zero_lt_of_lt hparent
    have hdeadlineHor : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon :=
      hdelay.trans hreadHor
    have hdMem := mem_stateBeforeTime_strict₅₁b facts S hf
      ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)
    have hFhist : ∀ j : Nat,
        j ≤ (rho.events.filter (fun e => decide (e.time <
          (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))).length →
        Block.Preceq (W j w).st.core.F D.erase := by
      intro j hj
      have hFj := Restated.Vocabulary.Proofs.stateBefore_F_preceq_stateBeforeTime_of_prefix facts S rho
        hf.sorted (w := w) (d := (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) hj
        (W j) (hf.onePath j).1 _ (onePath_reach_le₅₁b hf.onePath hj)
      have hFGread := Restated.Vocabulary.Proofs.stateBeforeTime_F_mono_of_le facts S rho hf.sorted
        (w := w) hdelay _ hdMem _
        (onePath_reach_le₅₁b hf.onePath (strictEventIndex_mono₅₁b rho hdelay))
      have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        facts S rho read w _ hreadMem
      have hFroot := facts.fc.finalized_preceq_get_fg_root
        (W (strictEventIndex rho read) w).st.core hFJ
      exact Proofs.ModelProperties.Preceq_trans hFj
        (Proofs.ModelProperties.Preceq_trans hFGread
          (Proofs.ModelProperties.Preceq_trans hFroot
            (Proofs.ModelProperties.Preceq_trans hrootP hPD)))
    have hpMax : p ∈ Hs (max t lo) := hHs _ _ (max_le htIn.le hpost) hp
    obtain ⟨j, t', hacc', ht'⟩ := Restated.named_acceptsAt_after_cutoffOn facts S Hs Xb hf hHs hHsXb
      hpMax hw hDpos hacc htIn hpost rfl hdeadlineHor hFhist
    have hDtarget : D ∈ (W (strictEventIndex rho read) w).st.bodies := by
      obtain ⟨-, e', he', -, he't⟩ := hacc'.1
      have htRead : e'.time < read := by
        rw [he't]
        exact lt_of_lt_of_le ht' hdelay
      have hjN : j < strictEventIndex rho read := by
        by_contra hnot
        have hnj : strictEventIndex rho read ≤ j := Nat.le_of_not_gt hnot
        have hle := Restated.le_time_of_index_geOn facts S Hs Xb hf (t := read) (j := j) (e := e')
          hnj he'
        exact (not_le_of_gt htRead) hle
      have hbodyJ : D ∈ (W (j + 1) w).st.bodies := by
        simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using
          hacc'.2.2
      exact Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho w
        (Nat.succ_le_of_lt hjN) _ (hf.onePath _).1 _
        (onePath_reach_le₅₁b hf.onePath (Nat.succ_le_of_lt hjN)) hbodyJ
    exact ⟨hDtarget, hPD, hheight⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of `named_acceptsAt_after_cutoffOn`, `w` admits `B` before `GammaOut` along
    `W`. -/
theorem block_admittedBefore_of_accepted_after_cutoff_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {p w : V} {i : Nat} {B : NamedBlock V} {t GammaIn GammaOut : Time}
    (hp : p ∈ Hs (max t lo)) (hw : w ∈ Hs GammaOut)
    (hBpos : 0 < B.slot)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i p (Object.block B) t)
    (htIn : t < GammaIn) (hgst : lo ≤ GammaIn)
    (hhop : GammaIn + S.E.Δ = GammaOut)
    (hhor : GammaOut ≤ rho.horizon)
    (hFhist : ∀ j : Nat,
      j ≤ (rho.events.filter (fun e => decide (e.time < GammaOut))).length →
        Block.Preceq (W j w).st.core.F B.erase) :
    Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w B.erase GammaOut := by
  obtain ⟨j, t', hacc', ht'⟩ := Restated.named_acceptsAt_after_cutoffOn facts S Hs Xb hf hHs hHsXb hp hw
    hBpos hacc htIn hgst hhop hhor hFhist
  exact ⟨B, rfl, j, t', hacc', ht'⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The conclusion of `block_admittedBefore_of_accepted_after_cutoff_coreOn`, from the bundle's
    hypotheses. -/
theorem block_admittedBefore_of_accepted_after_cutoffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {p w : V} {i : Nat} {B : NamedBlock V} {t GammaIn GammaOut : Time}
    (hp : p ∈ Hs (max t lo)) (hw : w ∈ Hs GammaOut)
    (hBpos : 0 < B.slot)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i p (Object.block B) t)
    (htIn : t < GammaIn) (hgst : lo ≤ GammaIn)
    (hhop : GammaIn + S.E.Δ = GammaOut)
    (hhor : GammaOut ≤ rho.horizon)
    (hFhist : ∀ j : Nat,
      j ≤ (rho.events.filter (fun e => decide (e.time < GammaOut))).length →
        Block.Preceq (W j w).st.core.F B.erase) :
    Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w B.erase GammaOut :=
  Restated.block_admittedBefore_of_accepted_after_cutoff_coreOn facts S Hs Xb hf hHs hHsXb hp hw hBpos hacc
    htIn hgst hhop hhor hFhist

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W`, if `w`'s read at `read` is a fixed-height justification root at `H` and
    `carrier` is a body of `w`'s store strictly before `read` carrying its justification, then
    `carrier`'s derived height is `H`. -/
theorem FixedHeightJustificationRootAtReadOn.carrierDerivedHeight (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {W : Nat → V → M.N} {Hs : Int → Finset V} {Xb : Finset V}
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {lo : Int} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {carrier : NamedBlock V}
    (hcarrierAt : carrier ∈ (W (strictEventIndex rho read) w).st.bodies)
    (hcarrierJust : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg carrier
      (W (strictEventIndex rho read) w).st.J (W (strictEventIndex rho read) w).st.h_j) :
    (M.derive_named S.E S.cfg carrier).h = H := by
  have hmem := mem_stateBeforeTime_strict₅₁b facts S hf read
  have hreadMem : (W (strictEventIndex rho read) w).st ∈
      Restated.Vocabulary.Execution.Run.storeBeforeTime M S rho w read :=
    ⟨_, hmem, rfl⟩
  have hOne : 1 ≤ H :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
  have hcarrierLower :
      H ≤ (M.derive_named S.E S.cfg carrier).h := by
    have hjlt :=
      (facts.cs.chainOrder_derive_named S.E S.cfg carrier).justified_below_height
    have hjEq : (M.derive_named S.E S.cfg carrier).h_j = H - 1 :=
      hcarrierJust.2.trans h.fixedTarget.justificationHeight
    rw [hjEq] at hjlt
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hOne).symm
      _ ≤ (M.derive_named S.E S.cfg carrier).h :=
        Nat.succ_le_iff.mpr hjlt
  have hcarrierUpper :
      (M.derive_named S.E S.cfg carrier).h ≤ H := by
    have hle := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts
      S rho read w _ hmem carrier hcarrierAt
    exact hle.trans (le_of_eq h.fixedTarget.frontier)
  exact Nat.le_antisymm hcarrierUpper hcarrierLower

/-- On the path `W` of the bundle, if `D` is a body of `w`'s store in
    `W (strictEventIndex rho read)`, then `D` is genesis or `w` accepted `D` along `W` at some
    index, at a time before `read`. -/
theorem carrierAcceptsBeforeStrictReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (read : Time) {D : NamedBlock V}
    (hDmem : D ∈ (W (strictEventIndex rho read) w).st.bodies) :
    D = NamedBlock.genesis ∨
      ∃ (i : Nat) (t : Time), Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i w (.block D) t ∧
        t < read := by
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho read) w).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hDmem
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho w W hf.onePath _ D
      hprocessed with
    hgen | ⟨i, hiN, t, hacc⟩
  · exact Or.inl hgen
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have heLt : e.time < read := time_lt_of_lt_strict₅₁b hf.sorted read i e hiN he
    exact Or.inr ⟨i, t, hacc, by simpa only [het] using heLt⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `v ∈ Xb`, `D` is a run block read through `Xb`, and `D`'s
    erasure is in the tree of `v`'s store in `W (strictEventIndex rho read)`, then `D` is a body of
    that store. -/
theorem namedMem_of_erasedMem_stateBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {read : Time} {D : NamedBlock V}
    (hDrun : Restated.RunBlockOn M S rho W Xb D)
    (hmem : D.erase ∈ (W (strictEventIndex rho read) v).st.core.T) :
    D ∈ (W (strictEventIndex rho read) v).st.bodies := by
  obtain ⟨E, hEmem, hEerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho read v
      _ (mem_stateBeforeTime_strict₅₁b facts S hf read) hmem
  have hErun : Restated.RunBlockOn M S rho W Xb E :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hEmem
  have hrooteq : E.root = D.root := by
    rw [← Proofs.NamedWire.erase_root E, ← Proofs.NamedWire.erase_root D, hEerase]
  have hDE : D = E :=
    hf.rootCollisionFree.root_injective D E hDrun hErun D E
      (Or.inl (Proofs.NamedAncestry.named_self D)) (Or.inr (Proofs.NamedAncestry.named_self E))
      hrooteq.symm
  rw [hDE]
  exact hEmem

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `D` is a run block read through `Xb` along `W` and `E ⪯ D`, then `E` is a run block read
    through `Xb` along `W`. -/
theorem runBlock_ancestorOn_FixedHeightRootAdmission (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} (Xb : Finset V) {D E : NamedBlock V}
    (hD : Restated.RunBlockOn M S rho W Xb D) (hED : NamedBlock.Preceq E D) :
    Restated.RunBlockOn M S rho W Xb E :=
  Restated.blockInRun_of_ancestorOn facts S rho W Xb hD hED

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `X` and `Y` are erasures of run blocks read through `Xb` with
    the same root, then `X = Y`. -/
theorem runBlockOf_root_uniqueOn_FixedHeightRootAdmission (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {X Y : Block V} (hX : Restated.RunBlockOfOn M S rho W Xb X)
    (hY : Restated.RunBlockOfOn M S rho W Xb Y)
    (hroot : X.root = Y.root) : X = Y := by
  obtain ⟨DX, hXe, hXrun⟩ := hX
  obtain ⟨DY, hYe, hYrun⟩ := hY
  have hDeq : DX = DY :=
    hf.rootCollisionFree.root_injective
      DX DY hXrun hYrun DX DY (Or.inl (Proofs.NamedAncestry.named_self DX))
      (Or.inr (Proofs.NamedAncestry.named_self DY))
      (by rw [← Proofs.NamedWire.erase_root DX, ← Proofs.NamedWire.erase_root DY, hXe, hYe];
          exact hroot)
  rw [← hXe, ← hYe, hDeq]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `v ∈ Xb`, the justified block of `v`'s store in
    `W (strictEventIndex rho read)` is the erasure of a run block read through `Xb`. -/
theorem runBlockOfJustified_atStrictReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (read : Time) :
    Restated.RunBlockOfOn M S rho W Xb (W (strictEventIndex rho read) v).st.J :=
  Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hv read
    (Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts S rho read v
      _ (mem_stateBeforeTime_strict₅₁b facts S hf read))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `w ∈ Xb` and the justification height of `w`'s store in
    `W (strictEventIndex rho read)` is not `0`, then a certificate read through `Xb` exists at that
    height for that store's justified root. -/
theorem certificateOfNamedJustification_atStrictReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time)
    (hnz : (W (strictEventIndex rho read) w).st.h_j ≠ 0) :
    Restated.CertificateOn M S rho W Xb (W (strictEventIndex rho read) w).st.h_j
      (W (strictEventIndex rho read) w).st.J.root := by
  obtain ⟨D, hD, hDJ, hDhj⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w
      _ (mem_stateBeforeTime_strict₅₁b facts S hf read)
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hD
  have hnzD : (M.derive_named S.E S.cfg D).h_j ≠ 0 := by rw [hDhj]; exact hnz
  obtain ⟨J, hJD, hJerase, Q, hQ, hwit⟩ :=
    Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg D hnzD
  have hJeraseEq : J.erase = (W (strictEventIndex rho read) w).st.J := by
    rw [hJerase]; exact hDJ
  have hroot : J.root = (W (strictEventIndex rho read) w).st.J.root := by
    rw [← Proofs.NamedWire.erase_root J, hJeraseEq]
  refine ⟨Q, (isQuorum_iff_q_le S.E Q).mp hQ, ?_⟩
  intro u hu
  obtain ⟨carrier, a, hcarrier, harow, hval, hpair⟩ := hwit u hu
  have hcarrierRun : Restated.RunBlockOn M S rho W Xb carrier :=
    Restated.runBlock_ancestorOn_FixedHeightRootAdmission facts Xb hDrun hcarrier
  have hDhjEq : (M.derive_named S.E S.cfg D).h_j = (W (strictEventIndex rho read) w).st.h_j := hDhj
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun,
      (priv% Proofs.Vocabulary.Generic.FixedHeightRootAdmission
        DecoupledConsensusModel.Proofs.HealingSurface.mem_named_chain_attestations_own) harow⟩,
    hval, ?_⟩
  rw [hpair, hDhjEq, hroot]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `w`'s read at `read` is a fixed-height justification root at
    `H` with the run block `carrier` carrying its justification, `p` is in the set for `proposal`,
    the largest `h_max` over that set in `W (inclusiveEventIndex rho proposal)` is at most `H`, and
    `i` is at most the number of events before `proposal`, then the finalized block of `p`'s store
    in `W i` is an ancestor of `carrier`. -/
theorem fixedHeightCarrier_finalizedBelowAtPrefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {carrier : NamedBlock V}
    (hcarrierRun : Restated.RunBlockOn M S rho W Xb carrier)
    (hcarrierJust : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg carrier
      (W (strictEventIndex rho read) w).st.J (W (strictEventIndex rho read) w).st.h_j)
    {p : V} {i : Nat} {proposal : Time} (hp : p ∈ Hs proposal)
    (hi : i ≤ (rho.events.filter
      (fun e => decide (e.time < proposal))).length)
    (hcap : ((Hs proposal).sup fun u =>
      (W (inclusiveEventIndex rho proposal) u).st.core.h_max) ≤ H) :
    Block.Preceq (W i p).st.core.F carrier.erase := by
  have hstrictCap : (W (strictEventIndex rho proposal) p).st.core.h_max ≤ H :=
    ((Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf p proposal).trans
      (Finset.le_sup (f := fun u => (W (inclusiveEventIndex rho proposal) u).st.core.h_max)
        hp)).trans hcap
  have hpreCap : (W i p).st.core.h_max ≤ H :=
    (Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho p hi
      (W i) (hf.onePath i).1 _ (onePath_reach_le₅₁b hf.onePath hi)).trans hstrictCap
  obtain ⟨Dst, hDstMem, hDstF, hDstBound⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho i p
      (W i) (hf.onePath i).1
  have hDrun : Restated.RunBlockOn M S rho W Xb Dst :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hp) hDstMem
  have hreadMem : (W (strictEventIndex rho read) w).st ∈
      Restated.Vocabulary.Execution.Run.storeBeforeTime M S rho w read :=
    ⟨_, mem_stateBeforeTime_strict₅₁b facts S hf read, rfl⟩
  have hcarrierLower : H ≤ (M.derive_named S.E S.cfg carrier).h := by
    have hjlt :=
      (facts.cs.chainOrder_derive_named S.E S.cfg carrier).justified_below_height
    have hjEq : (M.derive_named S.E S.cfg carrier).h_j = H - 1 :=
      hcarrierJust.2.trans h.fixedTarget.justificationHeight
    rw [hjEq] at hjlt
    have hOne : 1 ≤ H :=
      Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hOne).symm
      _ ≤ (M.derive_named S.E S.cfg carrier).h :=
        Nat.succ_le_iff.mpr hjlt
  have hcrossed : (M.derive_named S.E S.cfg Dst).h_F <
      (M.derive_named S.E S.cfg carrier).h :=
    lt_of_lt_of_le (hDstBound.trans_le hpreCap) hcarrierLower
  have hpreceq := Restated.finalized_preceq_of_height_ltOn facts S rho W Xb carrier Dst hsb
    hf.rootCollisionFree hcarrierRun hDrun hcrossed
  rwa [hDstF] at hpreceq

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `w`'s read at `read` is a fixed-height justification root at
    `H`, `p` is in the set for `target`, `lo ≤ read`, `read + Δ ≤ target ≤ horizon`, and the largest
    `h_max` over the set for `target` is at most `H`, then a carrier of the justification of `w`'s
    store strictly before `read`, a run block read through `Xb`, is a body of `p`'s store strictly
    before `target`. -/
theorem fixedHeightJustificationRootCarrier_exists_mem_laterRead_of_oneDelay_of_noRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {p : V} {target : Time} (hp : p ∈ Hs target)
    (hpost : lo ≤ read)
    (hdelay : read + S.E.Δ ≤ target)
    (hhor : target ≤ rho.horizon)
    (hcap : ((Hs target).sup fun u =>
      (W (inclusiveEventIndex rho target) u).st.core.h_max) ≤ H) :
    ∃ carrier : NamedBlock V,
      carrier ∈ (W (strictEventIndex rho read) w).st.bodies ∧
        Restated.RunBlockOn M S rho W Xb carrier ∧
        Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg carrier
          (W (strictEventIndex rho read) w).st.J
          (W (strictEventIndex rho read) w).st.h_j ∧
        carrier ∈ (W (strictEventIndex rho target) p).st.bodies := by
  have hreadMem : (W (strictEventIndex rho read) w).st ∈
      Restated.Vocabulary.Execution.Run.storeBeforeTime M S rho w read :=
    ⟨_, mem_stateBeforeTime_strict₅₁b facts S hf read, rfl⟩
  obtain ⟨carrier, hcarrierAt, hcarrierRun, hcarrierJust⟩ :=
    h.carrierExists
  have hFhist : ∀ i : Nat,
      i ≤ (rho.events.filter (fun e => decide (e.time < target))).length →
        Block.Preceq (W i p).st.core.F carrier.erase := by
    intro i hi
    exact Restated.fixedHeightCarrier_finalizedBelowAtPrefixOn facts
      S Hs Xb hf hHsXb hsb h hcarrierRun hcarrierJust hp hi hcap
  rcases Restated.carrierAcceptsBeforeStrictReadOn facts S Hs Xb hf w read hcarrierAt with
    hgen | ⟨i, t, hacc, htRead⟩
  · have hzero : H - 1 = 0 := by
      calc
        H - 1 = (W (strictEventIndex rho read) w).st.h_j :=
          h.fixedTarget.justificationHeight.symm
        _ = (M.derive_named S.E S.cfg carrier).h_j :=
          hcarrierJust.2.symm
        _ = 0 := by rw [hgen, facts.csAdded.Sts_derive_named_genesis_h_j]
    exact False.elim ((Nat.ne_of_gt h.targetHeightPositive) hzero)
  · have hcarrierPos : 0 < carrier.slot := by
      have h' := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath
        hacc
      rw [Proofs.NamedWire.erase_slot] at h'
      exact Nat.zero_lt_of_lt h'
    have htInput : t < target - S.E.Δ := by
      apply (lt_sub_iff_add_lt).2
      exact (Int.add_lt_add_right htRead S.E.Δ).trans_le hdelay
    have hpostInput : lo ≤ target - S.E.Δ := by
      apply (le_sub_iff_add_le).2
      exact (Int.add_le_add_right hpost S.E.Δ).trans hdelay
    have hhop : (target - S.E.Δ) + S.E.Δ = target :=
      sub_add_cancel target S.E.Δ
    have hwMax : w ∈ Hs (max t lo) :=
      hHs _ _ (max_le htRead.le hpost) h.readerHonest
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M
        S rho W p carrier.erase target :=
      Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hwMax hp hcarrierPos hacc htInput hpostInput
          hhop hhor hFhist
    have hcarrierTargetErased : carrier.erase ∈ (W (strictEventIndex rho target) p).st.core.T :=
      (Restated.admittedBefore_mem_and_stampOn facts S Hs Xb hf hadmit).1
    have hcarrierTarget : carrier ∈ (W (strictEventIndex rho target) p).st.bodies :=
      Restated.namedMem_of_erasedMem_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hp) hcarrierRun
        hcarrierTargetErased
    exact ⟨carrier, hcarrierAt, hcarrierRun, hcarrierJust,
      hcarrierTarget⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `w`'s read at `read` is a fixed-height justification root at
    `H`, `p ∈ Xb`, a carrier of that justification is a body of `p`'s store strictly before
    `target`, and that store's `h_max` is at most `H`, then the FG root of `p`'s store there is the
    justified block of `w`'s store strictly before `read`. -/
theorem fixedHeightJustificationRoot_laterFGRoot_eq_target_of_carrier_mem_of_hMax_leOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {p : V} (hp : p ∈ Xb)
    {target : Time} {carrier : NamedBlock V}
    (hcarrierAt : carrier ∈ (W (strictEventIndex rho read) w).st.bodies)
    (hcarrierJust : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg carrier
      (W (strictEventIndex rho read) w).st.J (W (strictEventIndex rho read) w).st.h_j)
    (hcarrierTarget : carrier ∈ (W (strictEventIndex rho target) p).st.bodies)
    (hlocalCap : (W (strictEventIndex rho target) p).st.h_max ≤ H) :
    M.get_fg_root (W (strictEventIndex rho target) p).st.toHealing.toFG =
      (W (strictEventIndex rho read) w).st.J := by
  let later := (W (strictEventIndex rho target) p).st
  have hreadMem : (W (strictEventIndex rho read) w).st ∈
      Restated.Vocabulary.Execution.Run.storeBeforeTime M S rho w read :=
    ⟨_, mem_stateBeforeTime_strict₅₁b facts S hf read, rfl⟩
  have htargetMem := mem_stateBeforeTime_strict₅₁b facts S hf target
  have hOne : 1 ≤ H :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
  have hcarrierLower :
      H ≤ (M.derive_named S.E S.cfg carrier).h := by
    have hjlt :=
      (facts.cs.chainOrder_derive_named S.E S.cfg carrier).justified_below_height
    have hjEq : (M.derive_named S.E S.cfg carrier).h_j = H - 1 :=
      hcarrierJust.2.trans h.fixedTarget.justificationHeight
    rw [hjEq] at hjlt
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hOne).symm
      _ ≤ (M.derive_named S.E S.cfg carrier).h :=
        Nat.succ_le_iff.mpr hjlt
  have hcarrierTarget' : carrier ∈ later.bodies := by
    simpa only [later] using hcarrierTarget
  have hHleLater : H ≤ later.h_max :=
    hcarrierLower.trans
      (Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts
        S rho target p _ htargetMem carrier hcarrierTarget')
  have hlaterCap : later.h_max ≤ H := by simpa only [later] using hlocalCap
  have hlaterMax : later.h_max = H := Nat.le_antisymm hlaterCap hHleLater
  have hnoHigh : Restated.Vocabulary.Internal.NamedNoHighJustifications M S.E S.cfg later :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime facts S rho
      target p _ htargetMem
  have hbelow : later.h_j < later.h_max :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime facts S rho
      target p _ htargetMem
  have hcarrierHj : (M.derive_named S.E S.cfg carrier).h_j = H - 1 :=
    hcarrierJust.2.trans h.fixedTarget.justificationHeight
  have hcarrierHjLower : H - 1 ≤ later.h_j := by
    rw [← hcarrierHj]
    exact hnoHigh carrier hcarrierTarget'
  have hlaterHj : later.h_j = H - 1 := by
    apply Nat.le_antisymm
    · exact Nat.le_sub_one_of_lt (hbelow.trans_le hlaterCap)
    · exact hcarrierHjLower
  have hHsucc : H - 1 + 1 = H := Nat.sub_add_cancel hOne
  have hlaterGate : later.h_max = later.h_j + 1 := by
    rw [hlaterMax, hlaterHj, hHsucc]
  have hlaterHjNe : later.h_j ≠ 0 := by
    rw [hlaterHj]
    exact Nat.ne_of_gt h.targetHeightPositive
  have hcertLater : Restated.CertificateOn M S rho W Xb (H - 1) later.J.root := by
    have hcert' := Restated.certificateOfNamedJustification_atStrictReadOn facts S Hs Xb hf hp target
      (by simpa only [later] using hlaterHjNe)
    have hhjRaw : (W (strictEventIndex rho target) p).st.h_j = H - 1 := hlaterHj
    rw [hhjRaw] at hcert'
    simpa only [later] using hcert'
  have hrootEq : later.J.root = (W (strictEventIndex rho read) w).st.J.root :=
    h.fixedTarget.uniqueAtHeight later.J.root hcertLater
  have htargetEq : later.J = (W (strictEventIndex rho read) w).st.J :=
    Restated.runBlockOf_root_uniqueOn_FixedHeightRootAdmission facts Hs Xb hf
      (Restated.runBlockOfJustified_atStrictReadOn facts S Hs Xb hf hp target)
      h.fixedTarget.targetBlock hrootEq
  have hrootLater :
      M.get_fg_root later.toHealing.toFG = later.J :=
    facts.fc.get_fg_root_toHealing_of_eq later.core hlaterGate
  simpa only [later] using hrootLater.trans htargetEq

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of
    `fixedHeightJustificationRootCarrier_exists_mem_laterRead_of_oneDelay_of_noRiseOn`, the FG root
    of `p`'s store strictly before `target` is the justified block of `w`'s store strictly before
    `read`, and the `h_max` of `p`'s store there is `H`. -/
theorem fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {p : V} {target : Time} (hp : p ∈ Hs target)
    (hpost : lo ≤ read)
    (hdelay : read + S.E.Δ ≤ target)
    (hhor : target ≤ rho.horizon)
    (hcap : ((Hs target).sup fun u =>
      (W (inclusiveEventIndex rho target) u).st.core.h_max) ≤ H) :
    M.get_fg_root (W (strictEventIndex rho target) p).st.toHealing.toFG =
        (W (strictEventIndex rho read) w).st.J ∧
      (W (strictEventIndex rho target) p).st.h_max = H := by
  obtain ⟨carrier, hcarrierAt, _hcarrierRun, hcarrierJust,
      hcarrierTarget⟩ :=
    Restated.fixedHeightJustificationRootCarrier_exists_mem_laterRead_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb h hp hpost hdelay hhor hcap
  have hlocalCap : (W (strictEventIndex rho target) p).st.h_max ≤ H :=
    ((Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf p target).trans
      (Finset.le_sup (f := fun u => (W (inclusiveEventIndex rho target) u).st.core.h_max)
        hp)).trans hcap
  have hroot :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_of_carrier_mem_of_hMax_leOn facts
      S Hs Xb hf h (hHsXb _ hp) hcarrierAt hcarrierJust hcarrierTarget hlocalCap
  refine ⟨hroot, ?_⟩
  have hcarrierHeight :
      (M.derive_named S.E S.cfg carrier).h = H :=
    h.carrierDerivedHeight facts hf hcarrierAt hcarrierJust
  let later := (W (strictEventIndex rho target) p).st
  have hcarrierTarget' : carrier ∈ later.bodies := by
    simpa only [later] using hcarrierTarget
  have hcarrierLocal :
      (M.derive_named S.E S.cfg carrier).h ≤ later.h_max :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts
      S rho target p _ (mem_stateBeforeTime_strict₅₁b facts S hf target) carrier hcarrierTarget'
  have hHle : H ≤ later.h_max := by
    rw [← hcarrierHeight]
    exact hcarrierLocal
  have hlaterCap : later.h_max ≤ H := by
    simpa only [later] using hlocalCap
  have hlaterMax : later.h_max = H :=
    Nat.le_antisymm hlaterCap hHle
  simpa only [later] using hlaterMax

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas
open Internal.NamedRecoveryRead
open Internal.PhaseGrades

end

end DecoupledConsensusModel.Sts.Restated
