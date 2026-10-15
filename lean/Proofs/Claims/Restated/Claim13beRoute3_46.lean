import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_30
import Proofs.Claims.Restated.Claim13beRoute3_37
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageProvenance
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockStamp
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Blocks
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Staleness
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_AdoptionTransport
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_MigrationResiduals
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecordClean
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_46
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_HMaxCore
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_Schedule_AdoptionTransport
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Vocabulary.Protocol.Schedule.CrossView
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Height bounds and run facts along a path of the run

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, most read along
the path `W` of a bundle `hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo`. They bound a
validator's own lock height and its `h_max`, show that the largest `h_max` over a set of validators
is monotone and rises by at most one per event, and state facts about emission, block and vote
acceptance, delivery, slot freshness and frame completion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ### Helpers about event lists, worlds and paths -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

omit [DecidableEq V] [Fintype V] in
/-- When the event at index `i` of `rho` is `e`, the events `i` to `i` of `rho` are the list `[e]`. -/
private theorem drop_take_succ₄₆ {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

omit [DecidableEq V] [Fintype V] in
/-- When `rho` has no event at index `i`, the events `i` to `i` of `rho` are the empty list. -/
private theorem drop_take_succ_none₄₆ {rho : Record.Run V} {i : Nat}
    (hi : rho.events[i]? = none) : (rho.events.drop i).take (i + 1 - i) = [] := by
  rw [List.getElem?_eq_none_iff] at hi
  rw [List.drop_eq_nil_of_le hi]
  exact List.take_nil

omit [DecidableEq V] [Fintype V] in
/-- For `m ≤ j ≤ n`, the elements `m` to `n - 1` of a list are the elements `m` to `j - 1` followed
    by the elements `j` to `n - 1`. -/
private theorem slice_split₄₆ {α : Type} (l : List α) {m j n : Nat} (hmj : m ≤ j) (hjn : j ≤ n) :
    (l.drop m).take (n - m) = (l.drop m).take (j - m) ++ (l.drop j).take (n - j) := by
  have h : n - m = (j - m) + (n - j) := by omega
  rw [h, List.take_add, List.drop_drop, Nat.add_sub_cancel' hmj]

/-- The worlds the one-event list `[e]` leads to from `w` are the worlds
    `Record.worldStepOf M S w e`. -/
private theorem mem_foldlM_singleton₄₆ (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

/-- A world the events `l₁ ++ l₂` lead to from `w` is one the events `l₂` lead to from a world the
    events `l₁` lead to from `w`, and conversely. -/
private theorem mem_foldlM_append₄₆ (S : Setup V) (l₁ l₂ : List (Record.Event V)) (w w₂ : V → M.N) :
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

/-- For `i ≤ j`, a world `w₂` can hold before the `j`-th event of `rho` exactly when it is reached,
    by the events `i` to `j - 1` of `rho`, from a world that can hold before the `i`-th event. -/
private theorem mem_stateBeforeOf_split₄₆ (S : Setup V) (rho : Record.Run V) {i j : Nat}
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

/-- For `m ≤ j ≤ n`, a world the events `m` to `n - 1` of `rho` lead to from `w` is one the events
    `j` to `n - 1` lead to from a world the events `m` to `j - 1` lead to from `w`, and conversely. -/
private theorem mem_slice_split₄₆ (S : Setup V) (rho : Record.Run V) {m j n : Nat} (hmj : m ≤ j)
    (hjn : j ≤ n) (w w₂ : V → M.N) :
    w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w ↔
      ∃ w' ∈ ((rho.events.drop m).take (j - m)).foldlM (Record.worldStepOf M S) w,
        w₂ ∈ ((rho.events.drop j).take (n - j)).foldlM (Record.worldStepOf M S) w' := by
  rw [slice_split₄₆ rho.events hmj hjn]
  exact mem_foldlM_append₄₆ S _ _ w w₂

/-- If the `i`-th event of `rho` is `e`, `w'` is a world `e` can lead to from `w`, `w₂` is reached
    from `w'` by the events `i + 1` to `n - 1`, and `i < n`, then `w₂` is reached from `w` by the
    events `i` to `n - 1`. -/
private theorem mem_slice_cons₄₆ (S : Setup V) (rho : Record.Run V) {i n : Nat} (hin : i < n)
    {e : Record.Event V} (hi : rho.events[i]? = some e) {w w' w₂ : V → M.N}
    (hw' : w' ∈ Record.worldStepOf M S w e)
    (hw₂ : w₂ ∈ ((rho.events.drop (i + 1)).take (n - (i + 1))).foldlM (Record.worldStepOf M S) w') :
    w₂ ∈ ((rho.events.drop i).take (n - i)).foldlM (Record.worldStepOf M S) w := by
  rw [mem_slice_split₄₆ S rho (Nat.le_succ i) hin w w₂]
  exact ⟨w', by rw [drop_take_succ₄₆ hi, mem_foldlM_singleton₄₆]; exact hw', hw₂⟩

/-- A world `w₂` reached from `w` by the events `n` to `n` of `rho` is `w` when `rho` has no event
    at index `n`, and otherwise one of the worlds the `n`-th event can lead to from `w`. -/
private theorem step_cases₄₆ (S : Setup V) (rho : Record.Run V) (n : Nat) (w w₂ : V → M.N)
    (h : w₂ ∈ ((rho.events.drop n).take (n + 1 - n)).foldlM (Record.worldStepOf M S) w) :
    (rho.events[n]? = none ∧ w₂ = w) ∨
      ∃ e, rho.events[n]? = some e ∧ w₂ ∈ Record.worldStepOf M S w e := by
  rcases hev : rho.events[n]? with _ | e
  · rw [drop_take_succ_none₄₆ hev] at h
    exact Or.inl ⟨rfl, Set.mem_singleton_iff.mp h⟩
  · rw [drop_take_succ₄₆ hev, mem_foldlM_singleton₄₆] at h
    exact Or.inr ⟨e, rfl, h⟩

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₄₆ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₄₆ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₄₆ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- In a run sorted by key, the worlds strictly before time `t` are the worlds before the event
    whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₄₆ (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world of a path `W` of the run before the event whose index is
    `strictEventIndex rho t` is a world strictly before time `t`. -/
private theorem mem_stateBeforeTime_along₄₆ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₄₆ S rho hsorted]
  exact (hW _).1

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, if the `i`-th event is `v`'s tick at `t`, the number of events with a
    time less than `t` is at most `i`. -/
private theorem strict_le_tick₄₆ {rho : Record.Run V}
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
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events has a time less
    than `t`. -/
private theorem time_lt_of_lt_strict₄₆ {rho : Record.Run V}
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

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at index `j` with a time less than `t` is among the first
    `strictEventIndex rho t` events. -/
private theorem lt_strict_of_time_lt₄₆ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time} (ht : e.time < t) :
    j < strictEventIndex rho t := by
  by_contra hnot
  exact absurd ht (not_lt.mpr
    (Restated.le_time_of_index_ge_of_sorted hsorted
      (Nat.le_of_not_gt hnot) he))

end

/-! ### Helpers about the action read -/

section
open DecoupledConsensusModel.Execution

/-- For every node state `n` the round-`r` action read computed from `before` can give, `n`'s store
    is `st` with `n`'s grade cache written into it, where `st`'s core store is an outcome of the
    confirmation write, with the grade contract of `n`'s cache, run on `before`'s core store with
    its clock set to `S.a r`, at the slot before that of `S.a r`. -/
private theorem actionReadFrom_core₄₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state the round-`r` action read computed from `before` can give has the tree of
    `before`'s core store. -/
private theorem actionReadFrom_T₄₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₆ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

/-- Every node state the round-`r` action read computed from `before` can give has the chain-state
    map of `before`'s core store. -/
private theorem actionReadFrom_σ₄₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.σ = before.st.core.σ := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₆ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_σ,
    facts.dt.update_confirmation_with_σ _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_σ]

/-- Every node state the round-`r` action read computed from `before` can give has the finalized
    block of `before`'s core store. -/
private theorem actionReadFrom_F₄₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.F = before.st.core.F := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₆ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_F,
    facts.dt.update_confirmation_with_F _ _ _ _ _ _ hX₀,
    facts.hd.setClock_core_F]

/-- Every node state the round-`r` action read computed from `before` can give has the justified
    block of `before`'s core store. -/
private theorem actionReadFrom_J₄₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.J = before.st.core.J := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₆ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_J,
    ← facts.sto.Sts_toHealing_J,
    facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ _ hX₀,
    facts.sto.Sts_toHealing_J, facts.hd.setClock_core_J]

/-- Every node state the round-`r` action read computed from `before` can give has the `h_max` of
    `before`'s core store. -/
private theorem actionReadFrom_h_max₄₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₆ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _ hX₀,
    facts.hd.setClock_toHealing_h_max]

/-- In every world strictly before `t`, every block of the tree of `v`'s core store has a
    chain-state height at most the store's `h_max`. -/
private theorem treeHeights_stateBeforeTime₄₆ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
      Restated.Vocabulary.Proofs.HealingSurface.TreeHeightsLeHMax M (w v).st.core := by
  intro w hw B hB
  obtain ⟨D, hD, rfl⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho t v w hw hB
  rw [Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho t v w hw D hD]
  exact Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts S rho t v w hw D hD

/-- In every world before the `i`-th event, every block of the tree of `v`'s core store has a
    chain-state height at most the store's `h_max`. -/
private theorem treeHeights_stateBefore₄₆ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V) :
    ∀ w ∈ Record.stateBeforeOf M S rho i,
      Restated.Vocabulary.Proofs.HealingSurface.TreeHeightsLeHMax M (w v).st.core := by
  intro w hw B hB
  obtain ⟨D, hD, rfl⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho i v w hw hB
  rw [Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho i v w hw D hD]
  exact Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho i v w hw D hD

/-- Along a path `W` of `rho`, for `m ≤ n`, every body `v` holds in `W m` it still holds in `W n`. -/
private theorem bodies_mono_path₄₆ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {m n : Nat} (hmn : m ≤ n) : (W m v).st.bodies ⊆ (W n v).st.bodies :=
  Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hmn (W m) (hW m).1
    (W n) (onePath_slice₄₆ W hW hmn)

/-- Along a path `W` of `rho`, if `reader` accepts the block `B` at index `j` at time `accepted`,
    then either that event is `reader`'s tick at `accepted` and `reader`'s stamp of `B` in
    `W (j + 1)` is `accepted`, or it is a delivery of `B` to `reader` at `accepted` and the stamp is
    `reader`'s clock in `W j`. -/
private theorem accepted_block_stamp_cases₄₆ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {j : Nat} {reader : V} {B : NamedBlock V} {accepted : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j reader (.block B) accepted) :
    (rho.events[j]? = some (.tick reader accepted) ∧
      (W (j + 1) reader).st.core.timestamp_block B.erase = some (accepted : Stamp)) ∨
    (rho.events[j]? = some (.deliver reader (.block B) accepted) ∧
      (W (j + 1) reader).st.core.timestamp_block B.erase =
        some ((W j reader).st.core.t : Stamp)) := by
  obtain ⟨⟨hproc, e, he, -, het⟩, hpre', hpost'⟩ := hacc
  have hpre : B ∉ (W j reader).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hpre'
  have hpost : B ∈ (W (j + 1) reader).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hpost'
  rcases hproc with ⟨t, htick, out, hout, hw, -⟩ | ⟨t, hdel⟩
  · obtain rfl : e = .tick reader t := Option.some.inj (he.symm.trans htick)
    have ht : t = accepted := het
    subst ht
    left
    refine ⟨htick, ?_⟩
    rw [hw] at hpost ⊢
    exact facts.nd.node_tick_body_stamp S reader (W j reader) t out hout B hpre hpost
  · obtain rfl : e = .deliver reader (.block B) t := Option.some.inj (he.symm.trans hdel)
    have ht : t = accepted := het
    subst ht
    right
    refine ⟨hdel, ?_⟩
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hdel (W j) (hW j).1
        (W (j + 1)) (hW j).2 with hproc | ⟨-, hw⟩
    · exact facts.nd.node_process_body_stamp S (W j reader) _ _ hproc B hpre hpost
    · exact absurd (hw ▸ hpost) hpre

/-- If every event of the list `l` has a time `≥ 0` and `v`'s clock in `w` is `≥ 0`, then `v`'s
    clock is `≥ 0` in every world the events of `l` lead to from `w`. -/
private theorem clock_nonneg_fold₄₆ (facts : Record.Facts M) (S : Setup V) (v : V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N), (∀ e ∈ l, 0 ≤ e.time) → 0 ≤ (w v).st.core.t →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, 0 ≤ (w₂ v).st.core.t := by
  intro l
  induction l with
  | nil =>
    intro w _ h w₂ hw₂
    rw [Set.mem_singleton_iff.mp hw₂]
    exact h
  | cons e l ih =>
    intro w hl h w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp hw₂
    refine ih w' (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) ?_ w₂ h2
    have he0 : 0 ≤ e.time := hl e (List.mem_cons_self ..)
    cases e with
    | wake u t =>
      simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw'
      subst hw'
      by_cases hv : v = u
      · subst hv
        rw [Function.update_self, (facts.nd.wake_st_record _).1]
        exact h
      · rw [Function.update_of_ne hv]
        exact h
    | tick u t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
      · by_cases hv : v = u
        · subst hv
          rw [Function.update_self, (facts.nd.tick_clock S v (w v) t out hout).1]
          exact he0
        · rw [Function.update_of_ne hv]
          exact h
      · exact h
    | deliver u o t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
      · by_cases hv : v = u
        · subst hv
          rw [Function.update_self, (facts.nd.process_clock S (w v) o n' hn').1]
          exact h
        · rw [Function.update_of_ne hv]
          exact h
      · exact h

/-- The action time of every round is a public time. -/
private theorem publicTime_a₄₆ (facts : Record.Facts M) (S : Setup V) (r : Round) :
    PublicTime S (Restated.Vocabulary.Execution.Setup.a M S r) := by
  show PublicTime S (M.a S.hc S.E.Δ r)
  rw [facts.sch.a_eq_confirmation_time]
  exact Restated.Vocabulary.Proofs.Optimistic.publicTime_confirmation_time facts S _

/-- Writing a store's clock and slot keeps its vote stamps (the field
    `sto.store_with_t_s_timestamp_vote` of `facts`). -/
private theorem store_with_t_s_timestamp_vote₄₆ (facts : Record.Facts M) (st : M.S) (t : Time)
    (s : Slot) : (M.store_with_t_s st t s).timestamp_vote = st.timestamp_vote :=
  facts.sto.store_with_t_s_timestamp_vote st t s

/-- The round-`r` action read computed from `M.wake n` can give exactly the node states it can give
    computed from `n`. -/
private theorem actionReadFrom_wake₄₆ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

/-- Every node state the round-`r` action read computed from `before` can give keeps `before`'s
    signing record. -/
private theorem actionReadFrom_record₄₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.record = before.record := by
  rintro _ ⟨c, -, st, -, rfl⟩
  exact facts.nd.mkNode_record _ _ _

/-- The round-`r` action read computed from `before` can give some node state `n`, and the
    attestation duty of the node `nd` run on `n` can return some outcome `D`. -/
private theorem actionAttestation_nonempty₄₆ (facts : Record.Facts M) (S : Setup V)
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

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₄₆ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- Every vote of every outcome of the slot-`s` confirmation numerator of `st` is in `st`'s slot-`s`
    pool. -/
private theorem confVotes_subset_pool₄₆ (E : Env V) (st : M.S) (s : Slot) :
    ∀ X, Restated.Vocabulary.Protocol.confVotes M E st s ⇢ X → X ⊆ M.store_pool st s := by
  intro X hX u hu
  obtain ⟨e, he, rfl⟩ := returns_map_elim₄₆ _ _ _ hX
  obtain ⟨τ, -, rfl⟩ := returns_map_elim₄₆ _ _ _ he
  have h := (Finset.mem_filter.mp hu).1
  rw [mem_beforeCutoff_iff] at h
  exact h.1

/-- If an outcome `out` of `v`'s tick at `t` from the node state `n` sends the attestation `a`, then
    `t` is the action time of `a`'s round, and for every node state `n'` the round's action read of
    `n` can give, every outcome `D` of the attestation duty run on `n'` has `a` as its attestation. -/
private theorem tick_attest₄₆ (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Time)
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
  rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.nd.mkNode_record,
    facts.dt.duties_attest_with_store_with_cache] at hD
  have hb := ha
  rw [facts.nd.tick_at_action_awake S v n a.round out hout c hc st hst D hD hawake] at hb
  simp only [List.mem_singleton, NamedObject.attest.injEq] at hb
  exact hb.symm

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every world `w` strictly before `S.a r`, every node state `n` that `v`'s round-`r` action
    read in `w` can give and every outcome `D` of the attestation duty run on `n`, if `D`'s
    attestation carries the finality pair `(H, T)`, then `H` is at most the justified height of
    `v`'s store in `w`. -/
private theorem seedActionFinalityPair_any₄₆ (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) {H : Height} {T : BlockId} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    D.2.2.finality_pair = some ⟨H, T⟩ →
    H ≤ (w v).st.core.h_j := by
  intro w hw n hn D hD hpair
  have hJ := Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v w hw
  have hF := Restated.Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v w hw
  have hJ' : n.st.core.J ∈ n.st.core.T := by
    rw [actionReadFrom_J₄₆ facts S (w v) r n hn, actionReadFrom_T₄₆ facts S (w v) r n hn]
    exact hJ
  have hF' : n.st.core.F ∈ n.st.core.T := by
    rw [actionReadFrom_F₄₆ facts S (w v) r n hn, actionReadFrom_T₄₆ facts S (w v) r n hn]
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
    rw [← actionReadFrom_σ₄₆ facts S (w v) r n hn, ← facts.sto.Sts_toHealing_σ]
    exact facts.vc.finality_pair_height hpair
  have hroot : M.get_fg_root (M.toHealing n.st.core).toFG ∈ (M.toHealing n.st.core).T := by
    rcases facts.fc.get_fg_root_eq_J_or_F n.st.core with h | h
    · rw [h, Record.Model.HS.T, facts.sto.toHealing_gs_T]
      exact hJ'
    · rw [h, Record.Model.HS.T, facts.sto.toHealing_gs_T]
      exact hF'
  have hHd' : Hd ∈ (w v).st.core.T := by
    rw [← actionReadFrom_T₄₆ facts S (w v) r n hn, ← facts.sto.toHealing_gs_T]
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
  have hnoHigh := Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime
    facts S rho (Restated.Vocabulary.Execution.Setup.a M S r) v w hw
  have hHeight : (M.derive_named S.E S.cfg Hn).h_j = H := by
    rw [← hsigma, hHnerase]
    exact hHdHeight
  rw [← hHeight]
  exact hnoHigh Hn hHnbody

/-- In a run sorted by key, for every world `w` before index `i`, where the `i`-th event is `v`'s
    tick at `t`, every outcome of that tick from `v`'s node state in `w` that sends an attestation
    with finality pair `(H, T)` has `H` at most `v`'s justified height in `w`. -/
private theorem seedFinalityEmission_any₄₆ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (htiu : TickIndexUnique rho)
    {i : Nat} {v : V} {t : Time} {a : NamedAttestation V}
    {H : Height} {T : BlockId}
    (hi : rho.events[i]? = some (Record.Event.tick v t))
    (hpair : a.finality_pair = some ⟨H, T⟩) :
    ∀ w ∈ Record.stateBeforeOf M S rho i,
    ∀ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v (w v) t,
    Object.attest a ∈ out.2 →
    H ≤ (w v).st.core.h_j := by
  intro w hw out hout hmem
  have _hr_w : M.reachedNode (w v) := facts.ndRun.stateBeforeOf_reachedNode S rho i w hw v
  have _hv_w : M.runs_as (w v) v := facts.ndRun.stateBeforeOf_runs_as S rho i w hw v
  obtain ⟨htime, hrow⟩ := tick_attest₄₆ facts S v (w v) t out hout a hmem
  have hle : strictEventIndex rho t ≤ i := strict_le_tick₄₆ hsorted hi
  obtain ⟨w₁, hw₁, hslice⟩ := (mem_stateBeforeOf_split₄₆ S rho hle w).mp hw
  have hw₁' : w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
    rw [stateBeforeTime_eq_strict₄₆ S rho hsorted]
    exact hw₁
  have hsame : w v = w₁ v ∨ w v = M.wake (w₁ v) :=
    Restated.Vocabulary.Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields facts S rho hsorted
      htiu hi w₁ hw₁' w hslice
  subst htime
  have hj : (w v).st.core.h_j = (w₁ v).st.core.h_j := by
    rcases hsame with h | h
    · rw [h]
    · rw [h, (facts.nd.wake_st_record _).1]
  replace hrow : ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w₁ v) a.round,
      ∀ D, M.duties_attest_with (M.gradeContract n'.cache) S.E S.hc (S.node v) n'.st n'.record ⇢ D →
        D.2.2 = a := by
    rcases hsame with h | h
    · rwa [h] at hrow
    · rwa [h, actionReadFrom_wake₄₆ facts] at hrow
  rw [hj]
  obtain ⟨n, hn, D, hD⟩ := actionAttestation_nonempty₄₆ facts S (w₁ v) a.round (S.node v)
  exact seedActionFinalityPair_any₄₆ facts S rho v a.round w₁ hw₁' n hn D hD
    (by rw [hrow n hn D hD]; exact hpair)

/-- In a run sorted by key, for every world `w` strictly before `S.a r`, if `v`'s record in `w`
    locks `T` at height `H`, then `H` is at most `v`'s justified height in `w`. -/
private theorem seedRecordLock_any₄₆ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (htiu : TickIndexUnique rho)
    (v : V) (r : Round) {H : Height} {T : BlockId} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r),
    (w v).record.legacy.lock H = some T →
    H ≤ (w v).st.core.h_j := by
  intro w hw hlock
  rw [stateBeforeTime_eq_strict₄₆ S rho hsorted] at hw
  obtain ⟨i, hi, t, a, hevent, w₁, hw₁, out, hout, hmem, hpair, hslice⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.recordLock_finalityEmission_before_migration facts S rho v
      _ w hw hlock
  have hle : H ≤ (w₁ v).st.core.h_j :=
    seedFinalityEmission_any₄₆ facts S hsorted htiu hevent hpair w₁ hw₁ out hout hmem
  have hstep : Function.update w₁ v out.1 ∈
      Record.worldStepOf M S w₁ (Record.Event.tick v t) := Or.inl ⟨out, hout, rfl⟩
  have hmono := Restated.Vocabulary.Proofs.HealingSurface.stateBefore_h_j_mono facts S rho v
    (Nat.le_of_lt hi) w₁ hw₁ w (mem_slice_cons₄₆ S rho hi hevent hstep hslice)
  exact hle.trans hmono

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- With `w = W (strictEventIndex rho (S.a r))` on the path `W` of `hf`, for every node state `n`
    that `v`'s round-`r` action read in `w` can give and every outcome `D` of the attestation duty
    run on `n`, if `own_lock` of `v`'s record in `w` and the finality pair of `D`'s attestation
    names `T` at height `H`, then `H` is at most `v`'s justified height in `w`. -/
theorem seedActionOwnLock_height_le_preJustificationOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) {H : Height} {T : BlockId} :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    M.own_lock (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy H
      D.2.2.finality_pair = some T →
    H ≤ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.h_j := by
  have hw := mem_stateBeforeTime_along₄₆ hf.sorted hf.onePath (Restated.Vocabulary.Execution.Setup.a M S r)
  generalize W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) = w at hw ⊢
  intro n hn D hD hlock
  cases hfp : D.2.2.finality_pair with
  | none =>
      have hrecord : (w v).record.legacy.lock H = some T := by
        rw [hfp, facts.vc.own_lock_none] at hlock
        exact hlock
      exact seedRecordLock_any₄₆ facts S hf.sorted hf.tickIndexUnique v r w hw hrecord
  | some p =>
      rcases p with ⟨h, target⟩
      by_cases hh : h = H
      · subst h
        have htarget : target = T := by
          rw [hfp, facts.vc.own_lock_some_self] at hlock
          exact Option.some.inj hlock
        subst target
        exact seedActionFinalityPair_any₄₆ facts S rho v r w hw n hn D hD hfp
      · have hrecord : (w v).record.legacy.lock H = some T := by
          rw [hfp, facts.vc.own_lock_some_pair_of_ne _ target hh] at hlock
          exact hlock
        exact seedRecordLock_any₄₆ facts S hf.sorted hf.tickIndexUnique v r w hw hrecord

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- With `w = W (strictEventIndex rho (S.a r))` on the path `W` of `hf`, if `v`'s justified height
    in `w` plus `2` is at most `Hm`, then for every node state `n` that `v`'s round-`r` action read
    in `w` can give and every outcome `D` of the attestation duty run on `n`, `v`'s own lock at
    height `Hm − 1`, read from `n`'s record and `D`'s attestation, is empty. -/
theorem gateOff_actionOwnLock_at_pred_noneOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) {Hm : Height} :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.h_j + 2 ≤ Hm →
    M.own_lock n.record.legacy (Hm - 1) D.2.2.finality_pair = none := by
  intro n hn D hD hgateOff
  cases hlock : M.own_lock n.record.legacy (Hm - 1) D.2.2.finality_pair with
  | none => rfl
  | some T =>
      exfalso
      have hle := Restated.seedActionOwnLock_height_le_preJustificationOn facts S Hs Xb hf v r
        n hn D hD (by
          rw [← actionReadFrom_record₄₆ facts S _ r n hn]
          exact hlock)
      have key : ∀ a b : Nat, a + 2 ≤ b → b - 1 ≤ a → False := by
        intro a b h1 h2; omega
      exact key _ _ hgateOff hle

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, two blocks `u` emits at slots that agree are the same block. -/
theorem emits_block_uniqueOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {u : V} {B B' : NamedBlock V} {t t' : Time}
    (h : Restated.Vocabulary.Execution.Run.emits M S ρ W u (Object.block B) t)
    (h' : Restated.Vocabulary.Execution.Run.emits M S ρ W u (Object.block B') t')
    (hs : B.slot = B'.slot) : B = B' := by
  have hW := hf.onePath
  have ht := (Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts S ρ W hW h).2.1
  have ht' := (Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts S ρ W hW h').2.1
  have hteq : t = t' := by rw [ht, ht', hs]
  subst hteq
  obtain ⟨i, hi, out, hout, -, hmem⟩ := h
  obtain ⟨j, hj, out', hout', -, hmem'⟩ := h'
  obtain ⟨hilt, hiv⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjlt, hjv⟩ := List.getElem?_eq_some_iff.mp hj
  have hij : i = j := hf.tickIndexUnique hiv (hiv.trans hjv.symm)
  subst hij
  have _hr_s1 := facts.ndRun.stateBeforeOf_reachedNode S ρ i (W i) (hf.onePath i).1 u
  have _hv_s2 := facts.ndRun.stateBeforeOf_runs_as S ρ i (W i) (hf.onePath i).1 u
  have heq := (Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts S u (W i u) t
    out hout hmem).2
  have _hr_s3 := facts.ndRun.stateBeforeOf_reachedNode S ρ i (W i) (hf.onePath i).1 u
  have _hv_s4 := facts.ndRun.stateBeforeOf_runs_as S ρ i (W i) (hf.onePath i).1 u
  have heq' := (Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts S u (W i u) t
    out' hout' hmem').2
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i u).st.core.toHealing t (W i u).cache
  have _hr_s5 := facts.ndRun.stateBeforeOf_reachedNode S ρ i (W i) (hf.onePath i).1 u
  have _hv_s6 := facts.ndRun.stateBeforeOf_runs_as S ρ i (W i) (hf.onePath i).1 u
  obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S u (W i u) t out' hout'
    (facts.nd.block_mem_on_tick_emit S u (W i u) t out' hout' hmem').1.1 (facts.nd.block_mem_on_tick_emit S u (W i u) t out' hout' hmem').1.2.1
    (facts.nd.block_mem_on_tick_emit S u (W i u) t out' hout' hmem').1.2.2
    (facts.nd.block_mem_on_tick_emit_awake S u (W i u) t out' hout' hmem') c hc
  have h1 := heq c hc D hD
  rw [heq' c hc D hD] at h1
  exact (Option.some_inj.mp h1).symm

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every node state `n` that the round-`r` action read computed from `v`'s node state in
    `W (strictEventIndex rho (S.a r))` can give, on the path `W` of `hf`, every block of `n`'s tree
    has a chain-state height at most `n`'s `h_max`. -/
theorem treeHeightsLeHMax_actionStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    Restated.Vocabulary.Proofs.HealingSurface.TreeHeightsLeHMax M n.st.core := by
  intro n hn
  have hpre := treeHeights_stateBeforeTime₄₆ facts S rho (Restated.Vocabulary.Execution.Setup.a M S r) v _
    (mem_stateBeforeTime_along₄₆ _hf.sorted _hf.onePath (Restated.Vocabulary.Execution.Setup.a M S r))
  exact Restated.Vocabulary.Proofs.HealingSurface.treeHeightsLeHMax_of_eq facts
    (actionReadFrom_T₄₆ facts S _ r n hn) (actionReadFrom_σ₄₆ facts S _ r n hn)
    (actionReadFrom_h_max₄₆ facts S _ r n hn) hpre

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, `v`'s `h_max` in `W (i + 1)` is at most its `h_max` in `W i` plus one. -/
theorem stateBefore_hMax_le_succOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (i : Nat) :
    (W (i + 1) v).st.core.h_max ≤ (W i v).st.core.h_max + 1 := by
  have htree := treeHeights_stateBefore₄₆ facts S rho i v (W i) (_hf.onePath i).1
  rcases step_cases₄₆ S rho i (W i) (W (i + 1)) (_hf.onePath i).2 with ⟨-, h⟩ | ⟨e, -, he⟩
  · rw [h]
    exact Nat.le_succ _
  · exact Restated.Vocabulary.Proofs.HealingSurface.worldStep_h_max_le_succ facts S (W i) e v htree
      (W (i + 1)) he

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every world `w` after `n` events and `v ∈ X`, `v`'s `h_max` in `w` is at most the largest
    `h_max` over `X` in `w`. -/
theorem localHMax_le_honestHMaxBeforeIndexOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (X : Finset V) (n : Nat) {v : V}
    (hv : v ∈ X) : ∀ w ∈ Record.stateBeforeOf M S rho n,
    (w v).st.h_max ≤ X.sup fun u => (w u).st.h_max :=
  fun w _ => Finset.le_sup (f := fun u => (w u).st.h_max) hv

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For `n ≤ m`, every world `w₁` after `n` events and every world `w₂` the events `n` to `m - 1`
    lead to from `w₁`, the largest `h_max` over `X` in `w₁` is at most the largest in `w₂`. -/
theorem honestHMaxBeforeIndex_monoOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (X : Finset V) {n m : Nat} (hnm : n ≤ m) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho n,
    ∀ w₂ ∈ ((rho.events.drop n).take (m - n)).foldlM (Record.worldStepOf M S) w₁,
    (X.sup fun u => (w₁ u).st.h_max) ≤ X.sup fun u => (w₂ u).st.h_max := by
  intro w₁ hw₁ w₂ hw₂
  apply Finset.sup_le
  intro v hv
  exact (Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v hnm w₁ hw₁ w₂ hw₂).trans
    (Finset.le_sup (f := fun u => (w₂ u).st.h_max) hv)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, the largest `h_max` over `X` in `W (i + 1)` is at most the largest in
    `W i` plus one. -/
theorem honestHMaxBeforeIndex_succ_leOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (i : Nat) :
    (X.sup fun u => (W (i + 1) u).st.h_max) ≤ (X.sup fun u => (W i u).st.h_max) + 1 := by
  apply Finset.sup_le
  intro v hv
  exact (Restated.stateBefore_hMax_le_succOn facts S Hs Xb hf v i).trans
    (Nat.add_le_add_right (Finset.le_sup (f := fun u => (W i u).st.h_max) hv) 1)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The worlds strictly before `t` are the worlds after the first `strictEventIndex rho t` events. -/
theorem stateBeforeTime_eq_stateBefore_strictEventIndexOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) :=
  stateBeforeTime_eq_strict₄₆ S rho hf.sorted t

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, for `t ≤ u` and one fixed set `X`, the largest `h_max` over `X` in
    `W (inclusiveEventIndex rho t)` is at most the largest in `W (inclusiveEventIndex rho u)`. -/
theorem honestHMaxAt_monoOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {t u : Time} (htu : t ≤ u) :
    (X.sup fun v => (W (inclusiveEventIndex rho t) v).st.core.h_max) ≤
      X.sup fun v => (W (inclusiveEventIndex rho u) v).st.core.h_max := by
  apply Finset.sup_le
  intro v hv
  exact (Restated.stateAt_h_max_monoOn facts S Hs Xb hf v htu).trans
    (Finset.le_sup (f := fun v => (W (inclusiveEventIndex rho u) v).st.core.h_max) hv)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, `v`'s `h_max` in `W (strictEventIndex rho t)` is at most its `h_max` in
    `W (inclusiveEventIndex rho t)`. -/
theorem storeBeforeTime_hMax_le_storeAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (t : Time) :
    (W (strictEventIndex rho t) v).st.core.h_max ≤ (W (inclusiveEventIndex rho t) v).st.core.h_max :=
  Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v
    (strictEventIndex_le_inclusiveEventIndex rho t) _ (hf.onePath _).1 _
    (onePath_slice₄₆ W hf.onePath (strictEventIndex_le_inclusiveEventIndex rho t))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, for `t ≤ u`, `v`'s `h_max` in `W (strictEventIndex rho t)` is at most
    its `h_max` in `W (strictEventIndex rho u)`. -/
theorem storeBeforeTime_hMax_monoOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) {t u : Time} (htu : t ≤ u) :
    (W (strictEventIndex rho t) v).st.core.h_max ≤ (W (strictEventIndex rho u) v).st.core.h_max :=
  Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v
    (strictEventIndex_mono rho htu) _ (hf.onePath _).1 _
    (onePath_slice₄₆ W hf.onePath (strictEventIndex_mono rho htu))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every world `w` after `n` events, if `H` is less than the largest `h_max` over `X` in `w`,
    some `v ∈ X` has `h_max` greater than `H` in `w`. -/
theorem exists_honest_localHMax_gt_of_lt_honestHMaxBeforeIndexOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (X : Finset V) (n : Nat) (H : Height) :
    ∀ w ∈ Record.stateBeforeOf M S rho n,
    H < (X.sup fun u => (w u).st.h_max) →
    ∃ v ∈ X, H < (w v).st.h_max := by
  intro w _ hlt
  by_contra hnone
  have hsup : (X.sup fun u => (w u).st.h_max) ≤ H := by
    apply Finset.sup_le
    intro v hv
    exact Nat.le_of_not_gt (fun hgt => hnone ⟨v, hv, hgt⟩)
  exact (Nat.not_lt_of_ge hsup) hlt

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the largest `h_max` over `X` in `W start` is at most `H` and the
    largest in `W stop`, with `stop ≥ start`, is greater than `H`, there is a least index `first` in
    `(start, stop]` at which it is greater than `H`; it is at most `H` at every index in
    `[start, first)` and exactly `H + 1` at `first`. -/
theorem exists_least_honestHMaxBeforeIndex_crossingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {H : Height}
    (hstartStop : start ≤ stop)
    (hstart : (X.sup fun u => (W start u).st.h_max) ≤ H)
    (hstop : H < X.sup fun u => (W stop u).st.h_max) :
    ∃ first : Nat,
      start < first ∧ first ≤ stop ∧
        (∀ j : Nat, start ≤ j → j < first →
          (X.sup fun u => (W j u).st.h_max) ≤ H) ∧
        (X.sup fun u => (W first u).st.h_max) = H + 1 := by
  classical
  have hne : start ≠ stop := by
    intro heq
    subst stop
    exact (Nat.not_lt_of_ge hstart) hstop
  have hstartLtStop : start < stop :=
    lt_of_le_of_ne hstartStop hne
  let P : Nat → Prop := fun k =>
    start < k ∧ k ≤ stop ∧ H < X.sup fun u => (W k u).st.h_max
  have hex : ∃ k, P k :=
    ⟨stop, hstartLtStop, le_rfl, hstop⟩
  let first : Nat := Nat.find hex
  have hspec : P first := Nat.find_spec hex
  have hbelow : ∀ j : Nat, start ≤ j → j < first →
      (X.sup fun u => (W j u).st.h_max) ≤ H := by
    intro j hstartJ hjFirst
    rcases eq_or_lt_of_le hstartJ with hEq | hstartJ'
    · subst j
      exact hstart
    · by_contra hnot
      have hgt : H < X.sup fun u => (W j u).st.h_max :=
        Nat.lt_of_not_ge hnot
      have hjFind : j < Nat.find hex := by
        simpa only [first] using hjFirst
      have hnotP : ¬ P j := Nat.find_min hex hjFind
      apply hnotP
      exact ⟨hstartJ', (Nat.le_of_lt hjFirst).trans hspec.2.1, hgt⟩
  have hfirstPos : 0 < first :=
    lt_of_le_of_lt (Nat.zero_le start) hspec.1
  have hpredStart : start ≤ first - 1 := by omega
  have hpredLt : first - 1 < first := by omega
  have hpred : (X.sup fun u => (W (first - 1) u).st.h_max) ≤ H :=
    hbelow (first - 1) hpredStart hpredLt
  have hstep :=
    Restated.honestHMaxBeforeIndex_succ_leOn facts S Hs Xb X hf (first - 1)
  have hpredSucc : first - 1 + 1 = first := by omega
  rw [hpredSucc] at hstep
  have hupper : (X.sup fun u => (W first u).st.h_max) ≤ H + 1 :=
    hstep.trans (Nat.add_le_add_right hpred 1)
  have hlower : H + 1 ≤ X.sup fun u => (W first u).st.h_max :=
    Nat.succ_le_iff.mpr hspec.2.2
  exact ⟨first, hspec.1, hspec.2.1, hbelow,
    Nat.le_antisymm hupper hlower⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every world `w` at `t` inclusive and `v ∈ Hs t`, `v`'s `h_max` in `w` is at most the largest
    `h_max` over `Hs t` in `w`. -/
theorem localHMax_le_honestHMaxAtOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (t : Time) {v : V}
    (hv : v ∈ Hs t) : ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.readAt M S rho t,
    (w v).st.core.h_max ≤ (Hs t).sup fun u => (w u).st.core.h_max :=
  fun w _ => Finset.le_sup (f := fun u => (w u).st.core.h_max) hv

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` accepts `B` at `ta`, then `B`'s proposal time is at most `ta`. -/
theorem proposal_time_le_acceptanceOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {v : V} {B : NamedBlock V} {ta : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) ta) :
    M.proposal_time S.E B.erase.slot ≤ ta :=
  Restated.Vocabulary.Proofs.NamedRelayGuards.proposal_time_le_acceptance_of_fields facts S rho hf.sorted
    hf.in_horizon W hf.onePath hacc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On every path `W` of the run, if `v ∈ Xb` does not hold the run block `B` in `W i`, `B`'s
    erasure is not in `v`'s tree in `W i`. -/
theorem no_geometry_aliasOn_RelayGuards (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Xb : Finset V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (roots : Restated.RootCollisionFreeOn M S rho W Xb) (i : Nat) (v : V)
    (hv : v ∈ Xb) (B : NamedBlock V) (hB : Restated.blockInRunOn M S rho W Xb B)
    (hnot : B ∉ (W i v).st.bodies) :
    B.erase ∉ (W i v).st.core.T := by
  intro hgeom
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v (W i)
    (hW i).1).1.1.1
  rw [hcoh.1] at hgeom
  obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hgeom
  have hCscope := Restated.blockInRun_of_directOn facts S rho W Xb
    (Restated.directBlock_of_prefixOn facts S rho W Xb hv i hC)
  have hroot : C.root = B.root :=
    (Proofs.NamedWire.erase_root C).symm.trans
      ((congrArg Block.root he).trans (Proofs.NamedWire.erase_root B))
  have hCB : C = B := roots.root_injective C B hCscope hB C B
    (Or.inl (Proofs.NamedAncestry.named_self C)) (Or.inr (Proofs.NamedAncestry.named_self B))
    hroot
  exact hnot (by simpa only [hCB] using hC)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `receiver` is in the set for `B`'s proposal time, that time is at
    least `lo`, and a delivery of `B` to `receiver` at index `j` is at a time `td` at least that
    time, then the receiver's slot in `W j` is at least `B`'s. -/
theorem receiver_slot_at_deliveryOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {j : Nat} {receiver : V} {B : NamedBlock V} {td : Time}
    (hhon : receiver ∈ Hs (M.proposal_time S.E B.erase.slot))
    (hdeliver : rho.events[j]? = some (.deliver receiver (.block B) td))
    (hlo : M.proposal_time S.E B.erase.slot ≤ td)
    (hgat : lo ≤ M.proposal_time S.E B.erase.slot) :
    B.erase.slot ≤ (W j receiver).st.core.s := by
  have hmem := List.mem_of_getElem? hdeliver
  have htk : Record.Event.tick receiver (M.proposal_time S.E B.erase.slot) ∈ rho.events :=
    hf.tick_total _ hgat receiver hhon (Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S B.erase.slot)
      (hlo.trans (hf.in_horizon _ hmem).2)
  have hclock := Restated.tick_le_clock_before_deliveryOn_RawRelay facts S rho Hs Xb hf
    hdeliver htk hlo
  have hw := (hf.onePath j).1
  generalize W j = w at hw hclock ⊢
  have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho j receiver w hw
  unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
  rw [hslot]
  exact facts.sch.slot_le_slotOf_of_proposal_time_le S.E hclock

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `source ∈ Xb` accepted `B` at `ta`, the receiver, in the set for
    `B`'s proposal time, handles `B` at index `j` at `td ≥ ta`, `B` is at slot `0` or proposed at or
    after `lo`, and the receiver's finalized block in `W j` is an ancestor of `B`, then the receiver
    holds `B` in `W (j + 1)`. -/
theorem handled_block_held_of_finalized_prefixOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {i j : Nat} {source receiver : V} {B : NamedBlock V} {ta td : Time}
    (hsource : source ∈ Xb)
    (hreceiver : receiver ∈ Hs (M.proposal_time S.E B.erase.slot))
    (hgat : B.erase.slot = 0 ∨ lo ≤ M.proposal_time S.E B.erase.slot)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.block B) ta)
    (hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j receiver (.block B) td)
    (htime : ta ≤ td)
    (hF : Block.Preceq (W j receiver).st.core.F B.erase) :
    B ∈ (W (j + 1) receiver).st.bodies := by
  have hW := hf.onePath
  have hroots : Restated.Vocabulary.Execution.NamedRootCollisionFree M S
      ({ rho with honest := Xb } : Record.Run V) W :=
    ⟨fun B C hB hC => hf.rootCollisionFree.root_injective B C hB hC⟩
  exact Restated.Vocabulary.Proofs.NamedRelayGuards.handled_block_held_of_finalized_prefix_of_fields facts S
    { rho with honest := Xb } W hW (fun i v o t hi => hf.deps i v o t hi) hroots
    hsource (hHsXb _ hreceiver) hacc hcall
    (fun hdeliver => by
      rcases hgat with h0 | hgat
      · show B.erase.slot ≤ _
        rw [h0]; exact Nat.zero_le _
      · exact Restated.receiver_slot_at_deliveryOn facts S rho Hs Xb hf hreceiver hdeliver
          ((Restated.proposal_time_le_acceptanceOn facts S rho Hs Xb hf hacc).trans htime) hgat) hF

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, every body `reader` holds in `W (strictEventIndex rho t)` has its block
    stamp there before `t`. -/
theorem held_body_stampedBefore_stateBeforeTimeOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) (t : Time)
    (B : NamedBlock V) :
    B ∈ (W (strictEventIndex rho t) reader).st.bodies →
    stampedBefore
      (W (strictEventIndex rho t) reader).st.core.timestamp_block
      t B.erase = true :=
  Restated.Vocabulary.Proofs.NamedBlockStamp.held_body_stampedBefore_stateBeforeTime_of_fields facts S rho hf.sorted
    hf.in_horizon reader t B _ (mem_stateBeforeTime_along₄₆ hf.sorted hf.onePath t)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The index of `reader`'s tick at `cut` is at most the index of any event of `reader`, other than
    a wake, at a time `≥ cut`. -/
theorem tick_index_le_target_eventOn_PublicCutBody (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {k j : Nat} {reader : V}
    {cut : Time} {e : Record.Event V}
    (htick : rho.events[k]? = some (.tick reader cut))
    (he : rho.events[j]? = some e) (hnode : e.node = reader)
    (hnwake : ∀ u t, e ≠ Record.Event.wake u t)
    (hcut : cut ≤ e.time) : k ≤ j := by
  by_contra hnot
  have hjk : j < k := Nat.lt_of_not_ge hnot
  obtain ⟨hk, hgetk⟩ := List.getElem?_eq_some_iff.mp htick
  obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp he
  have hkey := (List.pairwise_iff_getElem.mp hf.sorted) j k hj hk hjk
  rw [hgetj, hgetk] at hkey
  have htime : e.time ≤ cut := Restated.time_le_of_key_le hkey
  have heqtime : e.time = cut := le_antisymm htime hcut
  cases e with
  | wake v eventTime => exact hnwake v eventTime rfl
  | deliver v o eventTime =>
      simp only [Record.Event.node] at hnode
      simp only [Record.Event.time] at heqtime
      subst v
      subst eventTime
      simp only [Record.Event.key, Record.Event.time, Record.Event.phase,
        Prod.Lex.le_iff] at hkey
      rcases hkey with hlt | ⟨_, hphase⟩
      · exact (lt_irrefl cut) hlt
      · norm_num at hphase
  | tick v eventTime =>
      simp only [Record.Event.node] at hnode
      simp only [Record.Event.time] at heqtime
      subst v
      subst eventTime
      have hev : rho.events[j] = rho.events[k] := by
        rw [hgetj, hgetk]
      exact (ne_of_lt hjk) (hf.tickIndexUnique hgetj hev)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `reader` is in the set for the public time `cut ≥ lo` and holds `B`
    in `W (j + 1)` after one of its own events at index `j` before `cut`, then `reader` holds `B` in
    the world of `W` strictly before `cut`. -/
theorem accepted_earlier_held_at_cutOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {reader : V} {cut : Time} (hreader : reader ∈ Hs cut)
    (hpublic : PublicTime S cut) (hcutlo : lo ≤ cut) {j : Nat} {e : Record.Event V}
    (he : rho.events[j]? = some e) (_hnode : e.node = reader)
    (hearly : e.time < cut) {B : NamedBlock V}
    (hpost : B ∈ (W (j + 1) reader).st.bodies) :
    B ∈ (W (strictEventIndex rho cut) reader).st.bodies :=
  bodies_mono_path₄₆ facts S rho W hf.onePath reader (lt_strict_of_time_lt₄₆ hf.sorted he hearly) hpost

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `reader` is in the set for the public time `cut ≥ lo`, and a body it
    holds in the world of `W` strictly before `read` has its first stamp there before `cut`, then it
    holds that body in the world of `W` strictly before `cut`. -/
theorem body_mem_stateBeforeTime_of_public_stampedBeforeOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {reader : V} {cut read : Time} (hreader : reader ∈ Hs cut) (hpublic : PublicTime S cut)
    (hcutlo : lo ≤ cut)
    {B : NamedBlock V}
    (hheld : B ∈ (W (strictEventIndex rho read) reader).st.bodies)
    (hstamp : stampedBefore
      (W (strictEventIndex rho read) reader).st.core.timestamp_block
      cut B.erase = true) :
    B ∈ (W (strictEventIndex rho cut) reader).st.bodies := by
  have hW := hf.onePath
  obtain hgen | ⟨j, hj, accepted, hacc⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageProvenance.held_block_origin facts S rho
      (strictEventIndex rho read) reader W hW hheld
  · subst B
    exact bodies_mono_path₄₆ facts S rho W hW reader (Nat.zero_le _)
      (facts.hdRun.genesis_mem_stateBefore_zero S rho reader (W 0) (hW 0).1)
  · have hpost : B ∈ (W (j + 1) reader).st.bodies := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hacc.2.2
    by_contra hnotCut
    have hcutAccepted : cut ≤ accepted := by
      apply le_of_not_gt
      intro hearly
      obtain ⟨e, he, hnode, het⟩ := hacc.1.2
      apply hnotCut
      apply Restated.accepted_earlier_held_at_cutOn facts S rho Hs Xb hf hreader hpublic hcutlo he
        hnode
      · simpa only [← het] using hearly
      · exact hpost
    have htransport := Restated.Vocabulary.Proofs.NamedBlockStamp.stateBefore_body_stamp_mono facts
      S rho reader (Nat.succ_le_of_lt hj) (W (j + 1)) (hW (j + 1)).1 hpost
      (W (strictEventIndex rho read)) (onePath_slice₄₆ W hW (Nat.succ_le_of_lt hj))
    have hstampPost : stampedBefore
        (W (j + 1) reader).st.core.timestamp_block
        cut B.erase = true := by
      obtain ⟨σ, hσ, hlt⟩ := exists_stamp_of_stampedBefore hstamp
      exact stampedBefore_of_lt (by rw [← htransport.2]; exact hσ) hlt
    obtain ⟨e, he, hnode, het⟩ := hacc.1.2
    have hacceptedHorizon : accepted ≤ rho.horizon := by
      simpa only [het] using (hf.in_horizon e (List.mem_of_getElem? he)).2
    have hcutHorizon : cut ≤ rho.horizon :=
      hcutAccepted.trans hacceptedHorizon
    have htickMem := hf.tick_total cut hcutlo reader hreader hpublic hcutHorizon
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp htickMem
    have hnwake : ∀ u t, e ≠ Record.Event.wake u t := by
      rintro u t rfl
      rcases hacc.1.1 with ⟨t', htick', -⟩ | ⟨t', hdel'⟩
      · rw [he] at htick'
        cases htick'
      · rw [he] at hdel'
        cases hdel'
    have hkj := Restated.tick_index_le_target_eventOn_PublicCutBody facts S rho Hs Xb hf hk he hnode
      hnwake (by simpa only [het] using hcutAccepted)
    rcases accepted_block_stamp_cases₄₆ facts S rho W hW hacc with
      ⟨_hacceptTick, hpostStamp⟩ | ⟨hdeliver, hpostStamp⟩
    · obtain ⟨σ, hσ, hlt⟩ := exists_stamp_of_stampedBefore hstampPost
      rw [hpostStamp] at hσ
      obtain rfl := Option.some.inj hσ
      exact (not_lt_of_ge (by exact_mod_cast hcutAccepted)) hlt
    · have hkne : k ≠ j := by
        intro hEq
        subst k
        rw [hk] at hdeliver
        cases hdeliver
      have hkjStrict : k < j := lt_of_le_of_ne hkj hkne
      have hclock := Restated.tick_le_clock_before_deliveryOn_RawRelay facts S rho Hs Xb hf
        hdeliver htickMem hcutAccepted
      obtain ⟨σ, hσ, hlt⟩ := exists_stamp_of_stampedBefore hstampPost
      rw [hpostStamp] at hσ
      obtain rfl := Option.some.inj hσ
      have hclockStamp : (cut : Stamp) ≤ ((W j reader).st.core.t : Stamp) := by
        exact_mod_cast hclock
      exact (not_lt_of_ge hclockStamp) hlt

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the slot-`s` proposer is in the set for `t` and for `t'`, `v`
    processes `B` at `t` and `w` processes `B'` at `t'`, both naming that proposer and both at slot
    `s`, then `B = B'`. -/
theorem unique_slot_block_coreOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {s : Slot}
    {v w : V} {B B' : NamedBlock V} {t t' : Time}
    (hprop : S.E.proposer s ∈ Hs t) (hprop' : S.E.proposer s ∈ Hs t')
    (hB : Restated.Vocabulary.Execution.Run.processes M S ρ W v (Object.block B) t)
    (hB' : Restated.Vocabulary.Execution.Run.processes M S ρ W w (Object.block B') t')
    (hBp : B.proposer? = some (S.E.proposer s))
    (hB'p : B'.proposer? = some (S.E.proposer s))
    (hBs : B.slot = s) (hB's : B'.slot = s) : B = B' := by
  have h₁ := hf.unforgeable v _ t hB _ hprop
    (show (Object.block B).author = some (S.E.proposer s) by rw [author_block]; exact hBp)
  have h₂ := hf.unforgeable w _ t' hB' _ hprop'
    (show (Object.block B').author = some (S.E.proposer s) by rw [author_block]; exact hB'p)
  obtain ⟨t₁, -, he₁⟩ := h₁
  obtain ⟨t₂, -, he₂⟩ := h₂
  exact Restated.emits_block_uniqueOn facts S Hs Xb hf he₁ he₂ (by rw [hBs, hB's])

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, in `W i`, before a delivery to `v` at `t`, `v`'s clock is at least the
    time `p` of any tick of `v` with `p ≤ t`. -/
theorem tick_le_store_timeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {i : Nat} {v : V} {o : Object V} {t p : Time}
    (hi : ρ.events[i]? = some (Record.Event.deliver v o t)) (hmem : Record.Event.tick v p ∈ ρ.events)
    (hle : p ≤ t) : p ≤ (W i v).st.t :=
  Restated.tick_le_clock_before_deliveryOn_RawRelay facts S ρ Hs Xb hf hi hmem hle

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` is in the set for the public time `Γ ≥ lo` and, in `W i`, before
    a delivery to `v` at `t`, `v`'s clock is less than `Γ`, then `t < Γ`. -/
theorem processed_lt_of_store_time_ltOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {i : Nat} {v : V} {o : Object V} {t Γ : Time}
    (hv : v ∈ Hs Γ) (hi : ρ.events[i]? = some (Record.Event.deliver v o t))
    (hpub : PublicTime S Γ) (hΓlo : lo ≤ Γ) :
    (W i v).st.t < Γ → t < Γ := by
  intro hstamp
  by_contra hge
  have hΓt : Γ ≤ t := le_of_not_gt hge
  have hthor : t ≤ ρ.horizon := (hf.in_horizon _ (List.mem_of_getElem? hi)).2
  have htk : Record.Event.tick v Γ ∈ ρ.events :=
    hf.tick_total Γ hΓlo v hv hpub (le_trans hΓt hthor)
  have hclock := Restated.tick_le_store_timeOn facts S Hs Xb hf hi htk hΓt
  exact (not_lt_of_ge hclock) hstamp

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `X` and `B` are run blocks read through `Xb` and `X`'s erasure is an
    ancestor of `B`'s, then `X` is a named ancestor of `B`. -/
theorem namedPreceq_of_runBlock_erase_preceqOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {X B : NamedBlock V}
    (hXrun : Restated.RunBlockOn M S rho W Xb X) (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (h : Block.Preceq X.erase B.erase) :
    NamedBlock.Preceq X B := by
  obtain ⟨A, hAB, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B h
  have hArun : Restated.RunBlockOn M S rho W Xb A :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hBrun hAB
  have hrootEq : A.root = X.root := by
    rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root X, hAerase]
  have hAX : A = X :=
    hf.rootCollisionFree.root_injective
      A X hArun hXrun A X
      (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self X))
      hrootEq
  rw [← hAX]
  exact hAB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `w` is in the set for `s`'s proposal time, which is at least `lo`,
    then in `W i`, before a delivery to `w` between that time and `s`'s confirmation time, `w`'s
    slot is `s` or `s + 1`. -/
theorem delivery_store_slot_before_confirmationOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {i : Nat} {o : Object V} {s : Slot} {t : Time}
    (hw : w ∈ Hs (M.proposal_time S.E s))
    (hgat : lo ≤ M.proposal_time S.E s)
    (hi : rho.events[i]? = some (Record.Event.deliver w o t))
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.confirmation_time S.E s) :
    (W i w).st.s = s ∨ (W i w).st.s = s + 1 := by
  have htk : Record.Event.tick w (M.proposal_time S.E s) ∈ rho.events :=
    hf.tick_total _ hgat w hw (Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S s)
      (le_trans hlo (hf.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hclock : M.proposal_time S.E s ≤ (W i w).st.t :=
    Restated.tick_le_store_timeOn facts S Hs Xb hf hi htk hlo
  have hup : (W i w).st.t ≤ t := by
    simpa [Record.Event.time, Record.Event.time] using
      Restated.store_time_le_event_timeOn facts S Hs Xb hf hi w
  have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho i w (W i)
    (hf.onePath i).1
  unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
  show (W i w).st.core.s = s ∨ (W i w).st.core.s = s + 1
  rw [hslot]
  exact facts.sch.slotOf_of_proposal_before_confirmation S.E s hclock
    (lt_of_le_of_lt hup hhi)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, under the hypotheses of `delivery_store_slot_before_confirmationOn`, a
    delivered slot-`s` Goldfish vote `u` is in the late confirmation view of slot `s` of `w`'s
    confirmation store read from `W`, or its voter equivocates there. -/
theorem gfVote_delivery_settled_at_confStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {i : Nat} {u : GoldfishVote V}
    {s : Slot} {t : Time}
    (hw : w ∈ Hs (M.proposal_time S.E s))
    (hgat : lo ≤ M.proposal_time S.E s)
    (hi : rho.events[i]? = some (Record.Event.deliver w (Object.gfVote u) t))
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.confirmation_time S.E s) :
    u ∈ Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s ∨
      M.equivocates
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s)
        u.val_index = true := by
  have hW := hf.onePath
  let pre := (W i w).st.core
  have hslot : pre.s = s ∨ pre.s = s + 1 :=
    Restated.delivery_store_slot_before_confirmationOn facts S Hs Xb hf hw hgat hi hlo hhi
  have hclock : pre.t < M.confirmation_time S.E s :=
    lt_of_le_of_lt
      (Restated.store_time_le_event_timeOn facts S Hs Xb hf hi w : (W i w).st.t ≤ t)
      hhi
  have hfresh : ¬ u.slot < pre.s - 1 := by
    rcases hslot with hs | hs
    · rw [hus, hs]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    · rw [hus, hs, Nat.add_sub_cancel]
      exact Nat.lt_irrefl s
  have hfuture : ¬ pre.s < u.slot := by
    rcases hslot with hs | hs
    · rw [hus, hs]
      exact Nat.lt_irrefl s
    · rw [hus, hs]
      exact Nat.not_lt.mpr (Nat.le_add_right s 1)
  have hcommittee : u.val_index ∈ S.E.committee u.slot :=
    (hf.wire i w (Object.gfVote u) t hi).2 u rfl
  have hlocal := Restated.Vocabulary.Protocol.on_goldfish_vote_checked_beforeCutoff_or_equivocates facts
    S.E pre u (M.confirmation_time S.E s) hcommittee
    (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w i)
    hfresh hfuture hclock
  have hpost : (W (i + 1) w).st =
      M.make_grades_compatible_with_finalized
        (M.ns_with_core (W i w).st (M.on_goldfish_vote_checked S.E pre u)) := by
    rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hi (W i) (hW i).1
      (facts.nd.process_nonempty S (W i w) _ (fun _ h => by cases h)) (W (i + 1)) (hW i).2,
      facts.nd.process_gfVote]
  have hpostTV : (W (i + 1) w).st.core.timestamp_vote =
      (M.on_goldfish_vote_checked S.E pre u).timestamp_vote := by
    rw [hpost, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote,
      facts.hd.ns_with_core_core]
  have hpostPool : ∀ k, M.store_pool (W (i + 1) w).st.core k =
      M.store_pool (M.on_goldfish_vote_checked S.E pre u) k := by
    intro k
    have h := congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool
      (M.ns_with_core (W i w).st (M.on_goldfish_vote_checked S.E pre u))) k
    rw [facts.hd.ns_with_core_core] at h
    rw [hpost]
    exact h
  let Γ := M.confirmation_time S.E s
  let N := strictEventIndex rho Γ
  have hiN : i < N := lt_strict_of_time_lt₄₆ hf.sorted hi hhi
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (i + 1) w).st.core (W N w).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf w N (Nat.succ_le_of_lt hiN)
  have hlate : ∀ st : M.S, Restated.Vocabulary.Protocol.confLate M S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st Γ) s =
      beforeCutoff st.timestamp_vote Γ (M.store_pool st s) := by
    intro st
    rw [Restated.Vocabulary.Protocol.confLate, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      store_with_t_s_timestamp_vote₄₆ facts]
    exact congrArg _ (facts.sto.pool_set_clock_slot st Γ _ s)
  rw [← hpostTV, ← hpostPool] at hlocal
  rw [hus] at hlocal
  show u ∈ Restated.Vocabulary.Protocol.confLate M S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W N w).st.core Γ) s ∨
    M.equivocates (Restated.Vocabulary.Protocol.confLate M S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W N w).st.core Γ) s) u.val_index = true
  rw [hlate]
  rcases hlocal with hmem | hequiv
  · exact Or.inl (Restated.Vocabulary.Protocol.beforeCutoff_subset_of_poolCarry facts hcarry s Γ hmem)
  · apply Or.inr
    apply facts.sch.equivocates_mono _ u.val_index hequiv
    intro x hx
    exact Restated.Vocabulary.Protocol.beforeCutoff_subset_of_poolCarry facts hcarry s Γ hx

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if in `W (i + 1)`, right after the event at index `i` (before `s`'s
    view freeze), `w` has processed the slot-`s` vote `u`, then `u` is stamped before the view
    freeze in the slot-`(s + 1)` vote-duty pool of `w` read from `W`. -/
theorem gfVote_processed_after_event_at_voteDutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {i : Nat} {e : Record.Event V} {u : GoldfishVote V} {s : Slot}
    (he : rho.events[i]? = some e) (hus : u.slot = s)
    (hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (i + 1) w).st (Object.gfVote u) = true)
    (hearly : e.time < M.view_freeze S.E s) :
    u ∈ beforeCutoff
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
      (M.view_freeze S.E s)
      (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) := by
  have hmem : u ∈ (W (i + 1) w).st.gf_votes s := by
    have h : u ∈ (W (i + 1) w).st.core.gf_votes u.slot := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hprocessed
    rw [hus] at h
    exact h
  have hstamps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w (i + 1)
  obtain ⟨c, hc⟩ : ∃ c : Stamp, (W (i + 1) w).st.timestamp_vote u = some c :=
    Option.isSome_iff_exists.mp (hstamps.stamped s u hmem)
  have hclock : (W (i + 1) w).st.t ≤ e.time :=
    Restated.block_store_time_after_event_leOn facts S Hs Xb hf he w
  have hcFreeze : c < (M.view_freeze S.E s : Stamp) :=
    lt_of_le_of_lt (hstamps.bounded u c hc)
      (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock hearly))
  let Γ := M.vote_time S.E (s + 1)
  let N := strictEventIndex rho Γ
  have hiN : i < N :=
    lt_strict_of_time_lt₄₆ hf.sorted he (lt_trans hearly (facts.sch.view_freeze_lt_vote_time_succ S.E s))
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (i + 1) w).st.core (W N w).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf w N (Nat.succ_le_of_lt hiN)
  show u ∈ beforeCutoff
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)).timestamp_vote
      (M.view_freeze S.E s)
      (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)) s)
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    mem_beforeCutoff_iff, store_with_t_s_timestamp_vote₄₆ facts,
    show M.store_pool (M.store_with_t_s (W N w).st.core (M.vote_time S.E (s + 1))
        (S.E.slotOf (M.vote_time S.E (s + 1)))) s = M.store_pool (W N w).st.core s from
      facts.sto.pool_set_clock_slot _ _ _ s,
    facts.sto.mem_store_pool_iff]
  refine ⟨hcarry.mem s u hmem, ?_⟩
  exact stampedBefore_of_lt (hcarry.stamp u c hc) hcFreeze

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, every vote stamped before `s`'s view freeze in `w`'s slot-`(s + 1)`
    vote-duty pool read from `W` is in `w`'s late confirmation view of slot `s` read from `W`. -/
theorem voteDutyFrozen_subset_confLateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (s : Slot) :
    beforeCutoff
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
        (M.view_freeze S.E s)
        (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) ⊆
      Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s))
        s := by
  let Γ1 := M.vote_time S.E (s + 1)
  let Γ2 := M.confirmation_time S.E s
  let N1 := strictEventIndex rho Γ1
  let N2 := strictEventIndex rho Γ2
  have h12 : Γ1 ≤ Γ2 :=
    le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)
  have hN : N1 ≤ N2 := strictEventIndex_mono rho h12
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W N1 w).st.core (W N2 w).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf w N2 hN
  intro u hu
  have hu1 : u ∈ beforeCutoff (W N1 w).st.core.timestamp_vote (M.view_freeze S.E s)
      (M.store_pool (W N1 w).st.core s) := by
    have hu' := hu
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      store_with_t_s_timestamp_vote₄₆ facts] at hu'
    rwa [show M.store_pool (M.store_with_t_s (W N1 w).st.core Γ1 (S.E.slotOf Γ1)) s =
      M.store_pool (W N1 w).st.core s from facts.sto.pool_set_clock_slot _ _ _ s] at hu'
  have hu2 : u ∈ beforeCutoff (W N2 w).st.core.timestamp_vote (M.view_freeze S.E s)
      (M.store_pool (W N2 w).st.core s) :=
    Restated.Vocabulary.Protocol.beforeCutoff_subset_of_poolCarry facts hcarry s (M.view_freeze S.E s) hu1
  have hu3 : u ∈ beforeCutoff (W N2 w).st.core.timestamp_vote (M.confirmation_time S.E s)
      (M.store_pool (W N2 w).st.core s) :=
    beforeCutoff_mono _ (le_of_lt (facts.sch.view_freeze_lt_confirmation_time S.E s)) _ hu2
  rw [Restated.Vocabulary.Protocol.confLate, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    store_with_t_s_timestamp_vote₄₆ facts]
  rwa [show (M.store_with_t_s (W N2 w).st.core Γ2 (S.E.slotOf Γ2)).pool s =
    M.store_pool (W N2 w).st.core s from facts.sto.pool_set_clock_slot _ _ _ s]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if every acceptance by `v` along `W` of a vote of an outcome of the
    slot-`s` confirmation numerator of `v`'s confirmation store read from `W` is in
    `[proposal_time s, support_cutoff s)`, then every vote of every outcome of that numerator has
    such an acceptance along `W`. -/
theorem confirmationVotesAcceptedInWindow_of_timingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot}
    (htiming : ∀ X, Restated.Vocabulary.Protocol.confVotes M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ⇢ X →
      ∀ u ∈ X,
      ∀ i t, Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (Object.gfVote u) t →
        M.proposal_time S.E s ≤ t ∧ t < M.support_cutoff S.E s) :
    Restated.Vocabulary.Protocol.ConfirmationVotesAcceptedInWindow M S rho W v
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s))
      s := by
  have hW := hf.onePath
  intro X hX u hu
  let n := strictEventIndex rho (M.confirmation_time S.E s)
  have hupool : u ∈ M.store_pool (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
      (M.confirmation_time S.E s)) s :=
    confVotes_subset_pool₄₆ S.E _ s X hX hu
  have huprefix : u ∈ M.store_pool (W n v).st.core s := by
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
      show M.store_pool (M.store_with_t_s (W n v).st.core (M.confirmation_time S.E s)
        (S.E.slotOf (M.confirmation_time S.E s))) s = M.store_pool (W n v).st.core s from
        facts.sto.pool_set_clock_slot _ _ _ s] at hupool
    exact hupool
  have hulist : u ∈ (W n v).st.core.gf_votes s :=
    (facts.sto.mem_store_pool_iff _ s u).mp huprefix
  have hus : u.slot = s :=
    (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf v n).slot s u hulist
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n v).st (Object.gfVote u) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    rw [hus]
    exact hulist
  obtain ⟨i, -, t, hacc⟩ :=
    Restated.Vocabulary.Protocol.acceptsAt_gfVote_of_processed facts S rho v W hW n u hprocessed
  obtain ⟨hlo, hhi⟩ := htiming X hX u hu i t hacc
  exact ⟨i, t, hacc, hus, hlo, hhi⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, two Goldfish votes `v` emits for one slot are the same vote. -/
theorem emits_gfVote_uniqueOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {v : V} {u₁ u₂ : GoldfishVote V} {t₁ t₂ : Time}
    (h₁ : Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.gfVote u₁) t₁)
    (h₂ : Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.gfVote u₂) t₂)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ :=
  Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_unique_of_fields facts S hf.tickIndexUnique W h₁ h₂ hslot
    (fun i => facts.ndRun.stateBeforeOf_reachedNode S ρ i (W i) (hf.onePath i).1 v)
    (fun i => facts.ndRun.stateBeforeOf_runs_as S ρ i (W i) (hf.onePath i).1 v)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The index of an event at a time `≤ Γ` is less than the number of events at times `≤ Γ`. -/
theorem index_lt_stateAt_lengthOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {j : Nat} {e : Record.Event V} (hj : ρ.events[j]? = some e) {Γ : Time} (hle : e.time ≤ Γ) :
    j < (ρ.events.filter (fun x => decide (x.time ≤ Γ))).length := by
  by_contra hcon
  have h := Restated.filter_false_of_index_geOn facts S Hs Xb hf _ (downward_le Γ) (Nat.le_of_not_lt hcon) hj
  simp only [decide_eq_false_iff_not] at h
  exact h hle

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` is in the set for `S.a r`, `lo ≤ S.a r ≤ horizon`, `v` is awake
    for round `r` at each of its ticks at `S.a r` (`hA`), and each such tick has an outcome
    (`hneTick`), then for every node state `n` its round-`r` action read in
    `W (strictEventIndex rho (S.a r))` can give and every outcome `D` of the attestation duty run on
    `n`, `v` emits at `S.a r` the attestation of `D`. -/
theorem honest_emits_exact_actionAttestationAt_of_awakeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest D.2.2)
      (Restated.Vocabulary.Execution.Setup.a M S r) := by
  have _hr_0 : M.reachedNode (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1 v
  have _hv_0 : M.runs_as (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) v := facts.ndRun.stateBeforeOf_runs_as S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1 v
  rintro _ ⟨c, hc, st, hst, rfl⟩ D hD
  rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.nd.mkNode_record,
    facts.dt.duties_attest_with_store_with_cache] at hD
  apply Restated.emits_of_on_tick_emitOn facts S Hs Xb hf hv (publicTime_a₄₆ facts S r) hgat hhor
    hneTick
  intro j hj out hout
  have hpart : (W j v).st = (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st ∧
      (W j v).cache = (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).cache ∧
      (W j v).record = (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record := by
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj with h | h
    · rw [h]
      exact ⟨rfl, rfl, rfl⟩
    · rw [h]
      exact ⟨(facts.nd.wake_st_record _).1, facts.nd.wake_cache _, (facts.nd.wake_st_record _).2⟩
  rw [← hpart.1, ← hpart.2.1] at hc
  rw [← hpart.1] at hst
  rw [← hpart.2.2] at hD
  have _hr_s7 := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hf.onePath j).1 v
  have _hv_s8 := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hf.onePath j).1 v
  rw [facts.nd.tick_at_action_awake S v (W j v) r out hout c hc st hst D hD (hA j hj)]
  exact List.mem_singleton_self _

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` is in the set for `S.a r`, `lo ≤ S.a r ≤ horizon`, `v` is awake
    for round `r` at each of its ticks at `S.a r` (`hA`), and each such tick has an outcome
    (`hneTick`), then for every node state `n` its round-`r` action read in
    `W (strictEventIndex rho (S.a r))` can give and every outcome `D` of the attestation duty run on
    `n`, `v` emits at `S.a r` the attestation of `D`. -/
theorem honest_emits_exact_actionAttestationAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest D.2.2)
      (Restated.Vocabulary.Execution.Setup.a M S r) :=
  Restated.honest_emits_exact_actionAttestationAt_of_awakeOn facts S Hs Xb hf r hv hA hhor hgat
    hneTick

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `w` is in the set for `s`'s proposal time, which is at least `lo`,
    then in `W i`, before a delivery to `w` between that time and `s`'s view freeze, `w`'s slot is
    `s`. -/
theorem delivery_store_slot_before_freezeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {i : Nat} {o : Object V} {s : Slot} {t : Time}
    (hw : w ∈ Hs (M.proposal_time S.E s))
    (hgat : lo ≤ M.proposal_time S.E s)
    (hi : rho.events[i]? = some (Record.Event.deliver w o t))
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.view_freeze S.E s) :
    (W i w).st.s = s := by
  have htk : Record.Event.tick w (M.proposal_time S.E s) ∈ rho.events :=
    hf.tick_total _ hgat w hw (Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S s)
      (le_trans hlo (hf.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hclock : M.proposal_time S.E s ≤ (W i w).st.t :=
    Restated.tick_le_store_timeOn facts S Hs Xb hf hi htk hlo
  have hup : (W i w).st.t ≤ t :=
    (Restated.store_time_le_event_timeOn facts S Hs Xb hf hi w : (W i w).st.t ≤ t)
  have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho i w (W i)
    (hf.onePath i).1
  unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
  show (W i w).st.core.s = s
  rw [hslot]
  exact facts.sch.slotOf_of_proposal_before_freeze S.E s hclock (lt_of_le_of_lt hup hhi)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, the proposer view of the slot-`s` proposal duty's store is a valid vote
    set for the slot before that store's slot. -/
theorem proposerDutyStore_proposer_view_valid_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s)).s - 1)
      (M.proposer_view
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).s).toFinset := by
  have hs : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)).s = s := by
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.store_with_t_s_s,
      facts.sch.slotOf_proposal_time]
  rw [hs]
  show Protocol.VoteSetValid S.E (s - 1)
    (M.proposer_view (M.store_with_t_s
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s) (S.E.slotOf (M.proposal_time S.E s))).toHealing.toFG.toSG.toGoldfishStore s).toFinset
  rw [facts.fc.proposer_view_set_clock_slot]
  exact Restated.voteSetValid_proposer_view_stateBeforeTimeOn facts S Hs Xb hf
    (S.E.proposer s) (M.proposal_time S.E s) s

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, the proposer view of the slot-`s` proposal duty's store is a valid vote
    set for the slot before that store's slot. -/
theorem proposerDutyStore_proposer_view_validOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s)).s - 1)
      (M.proposer_view
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).s).toFinset :=
  Restated.proposerDutyStore_proposer_view_valid_coreOn facts S Hs Xb hf s

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every path `W` of the run along which the run blocks read through `Xb` have no root
    collision, two such run blocks with the same erased root have the same erasure. -/
theorem runBlock_eq_of_root_eqOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} (W : Nat → V → M.N) (Xb : Finset V)
    (hcf : Restated.RootCollisionFreeOn M S rho W Xb)
    {X Y : NamedBlock V} (hX : Restated.RunBlockOn M S rho W Xb X)
    (hY : Restated.RunBlockOn M S rho W Xb Y)
    (hroot : X.erase.root = Y.erase.root) : X.erase = Y.erase := by
  have hinj := Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hcf
    (T := ({X, Y} : Finset (NamedBlock V)))
    (by
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hX
      · rw [Finset.mem_singleton.mp hC]
        exact hY)
  exact RootInjectiveBelow.eq_of_root_eq hinj
    (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    (Finset.mem_image_of_mem _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hroot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On every path `W` of the run, if `v ∈ Xb` does not hold the run block `B` in `W i`, `B`'s
    erasure is not in `v`'s tree in `W i`. -/
theorem no_geometry_aliasOn_BlockAdmission (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Xb : Finset V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (roots : Restated.RootCollisionFreeOn M S rho W Xb) (i : Nat) (v : V)
    (hv : v ∈ Xb) (B : NamedBlock V) (hB : Restated.blockInRunOn M S rho W Xb B)
    (hnot : B ∉ (W i v).st.bodies) :
    B.erase ∉ (W i v).st.core.T :=
  Restated.no_geometry_aliasOn_RelayGuards facts S rho Xb W hW roots i v hv B hB hnot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, `v`'s clock in `W i` is at least `0`. -/
theorem stateBefore_store_time_nonnegOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (i : Nat) :
    0 ≤ (W i v).st.core.t := by
  refine clock_nonneg_fold₄₆ facts S v (rho.events.take i) (fun u => M.initial S u)
    (fun e he => (hf.in_horizon e ((List.take_sublist i rho.events).mem he)).1) ?_ (W i) (hf.onePath i).1
  show 0 ≤ (M.initial S v : M.N).st.core.t
  rw [facts.nd.initial_st, facts.hd.initial_core_t]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` accepts `B` at `t`, then `B`'s proposal time is at most `t`. -/
theorem proposal_time_le_of_acceptsAt_blockOn_BlockAdmission (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) t) :
    M.proposal_time S.E B.erase.slot ≤ t := by
  have hW := hf.onePath
  obtain ⟨e, he, -, ht⟩ := hacc.1.2
  rcases hacc.1.1 with ⟨t', htick, out, hout, hw, hB⟩ | ⟨t', hdeliver⟩
  · have heq : e = Record.Event.tick v t' := Option.some.inj (he.symm.trans htick)
    have ht' : t' = t := by
      rw [heq] at ht; exact ht
    have hemit : Restated.Vocabulary.Execution.Run.emits M S rho W v (.block B) t' :=
      ⟨i, htick, out, hout, hw, hB⟩
    have hshape := Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts S rho W hW hemit
    rw [Proofs.NamedWire.erase_slot]
    exact (hshape.2.1.symm.trans ht').le
  · have heq : e = Record.Event.deliver v (.block B) t' := Option.some.inj (he.symm.trans hdeliver)
    have ht' : t' = t := by
      rw [heq] at ht; exact ht
    have heDeliver : rho.events[i]? = some (Record.Event.deliver v (.block B) t) := ht' ▸ hdeliver
    have hfuture := (Restated.Vocabulary.Protocol.delivery_guards_of_acceptsAt_block facts S W hW hacc
      heDeliver).1
    have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho i v
      (W i) (hW i).1
    unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
    rw [hslot] at hfuture
    have hmono : M.proposal_time S.E B.erase.slot ≤
        M.proposal_time S.E (S.E.slotOf (W i v).st.core.t) :=
      facts.sch.proposal_time_mono S.E (Nat.not_lt.mp hfuture)
    refine le_trans hmono (le_trans
      (facts.sch.proposal_time_slotOf_le S.E
        (Restated.stateBefore_store_time_nonnegOn facts S Hs Xb hf v i)) ?_)
    exact Restated.store_time_le_event_timeOn facts S Hs Xb hf heDeliver v

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the event at index `i` delivers `B` to `v ∈ Xb`, the delivery is
    fresh (`hfresh`), and `B` passes the admission checks in `v`'s store in `W i` (slot not in the
    future, finalized ancestor, proposer, parent slot, included attestations), then `v` accepts `B`
    at index `i`. -/
theorem acceptsAt_block_of_delivery_guards_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time} (hv : v ∈ Xb)
    (hfresh : Restated.DeliveryFreshAt M S rho W i)
    (hi : rho.events[i]? = some (Record.Event.deliver v (Object.block B) t))
    (hslot : ¬ (W i v).st.core.s < B.erase.slot)
    (hF : Block.Preceq (W i v).st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparentSlot : B.erase.parent.slot < B.erase.slot)
    (hattestations : M.carried_attestations_admissible S.hc B.erase = true) :
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.block B) t := by
  have _hr_0 : M.reachedNode (W i v) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 v
  have _hr_1 : M.reachedNode (W (i + 1) v) := facts.ndRun.stateBeforeOf_reachedNode S rho (i + 1) (W (i + 1)) (hf.onePath (i + 1)).1 v
  have hW := hf.onePath
  have hparent : B.parent ∈ (W i v).st.bodies :=
    hf.deps i v (Object.block B) t hi B rfl
  have hfresh' : B ∉ (W i v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using
      hfresh v (Object.block B) t hi
  have hscope := Restated.blockInRun_of_directOn facts S rho W Xb
    (Restated.directBlock_of_deliveryOn facts S rho W Xb hi)
  have hlegacyFresh : B.erase ∉ (W i v).st.core.T :=
    Restated.no_geometry_aliasOn_BlockAdmission facts S rho Xb W hW hf.rootCollisionFree i v hv
      B hscope hfresh'
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v (W i)
    (hW i).1).1.1.1
  have hnew : B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg (W i v).st B).bodies := by
    rw [facts.hd.on_block_with_bodies_eq S .alsoCarried (W i v).st B,
      facts.hd.process_block_core_bodies_eq_commit S.E S.hc S.cfg hparent]
    refine facts.hd.mem_commitBlock_bodies_of_fresh S.E S.hc S.cfg rfl ⟨hlegacyFresh, ?_⟩
    have _hr_s9 := facts.nd.reachedStore_of_node _ (facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 v)
    rw [facts.hd.sameCore_T (facts.hd.process_block_core_of_parent_mem S.E S.hc S.cfg hparent),
      facts.hd.commit_core _ _ B
        (facts.hd.on_block_checked_using_store_part S.E S.hc S.cfg (W i v).st B)]
    have hparentTree : B.erase.parent ∈ (W i v).st.core.T := by
      rw [Proofs.NamedWire.erase_parent, hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hparent
    rw [facts.hd.on_block_checked_using_of_admissible _ S.hc (W i v).st.core hattestations]
    exact facts.hd.mem_T_on_block_using S.E (W i v).st.core B.erase _ (Nat.not_lt.mp hslot)
      hlegacyFresh hparentTree (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hF) hproposer
      hparentSlot (facts.sto.rootFresh_of_distinct _ _ (fun C hC hr => by
        rw [hcoh.1] at hC
        obtain ⟨D, hD, hDe⟩ := Finset.mem_image.mp hC
        have hDB : D = B :=
          hf.rootCollisionFree.root_injective D B
            ⟨D, Or.inr ⟨v, hv, i, hD⟩, Proofs.NamedAncestry.named_self D⟩ hscope D B
            (Or.inl (Proofs.NamedAncestry.named_self D))
            (Or.inr (Proofs.NamedAncestry.named_self B))
            (by rw [← Proofs.NamedWire.erase_root D, hDe, hr, Proofs.NamedWire.erase_root B])
        rw [← hDe, hDB]))
  refine ⟨⟨Or.inr ⟨t, hi⟩, Record.Event.deliver v (Object.block B) t, hi, rfl, rfl⟩, ?_, ?_⟩
  · simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hfresh'
  · rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hi (W i) (hW i).1
        (W (i + 1)) (hW i).2 with hproc | ⟨hnone, -⟩
    · simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
      rw [facts.nd.process_st S (W i v) _ (W (i + 1) v) hproc,
        facts.nd.make_grades_compatible_with_finalized_bodies, facts.nd.process_block]
      exact hnew
    · obtain ⟨n', hn'⟩ := hf.receipt_outcome _ _ _ _ hi
      exact absurd hn' (hnone n')

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the event at index `i` delivers `B` to `v ∈ Xb`, the delivery is
    fresh, and `B` passes the admission checks in `v`'s store in `W i`, then `v` accepts `B` at
    index `i`. -/
theorem acceptsAt_block_of_delivery_guardsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time} (hv : v ∈ Xb)
    (hfresh : Restated.DeliveryFreshAt M S rho W i)
    (hi : rho.events[i]? = some (Record.Event.deliver v (Object.block B) t))
    (hslot : ¬ (W i v).st.core.s < B.erase.slot)
    (hF : Block.Preceq (W i v).st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparentSlot : B.erase.parent.slot < B.erase.slot)
    (hattestations : M.carried_attestations_admissible S.hc B.erase = true) :
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.block B) t :=
  Restated.acceptsAt_block_of_delivery_guards_coreOn facts S Hs Xb hf hv hfresh hi hslot hF
    hproposer hparentSlot hattestations

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` accepts `u` at index `i` at `t`, then either that event is a
    delivery, `u`'s stamp in `v`'s store in `W (i + 1)` is `v`'s clock in `W i`, and `u`'s slot is
    at most `v`'s slot in `W i`; or it is `v`'s tick at `t`, the stamp is `t`, and `u`'s slot is at
    most the slot of `t`. -/
theorem acceptsAt_gfVote_time_shapeOn_Protocol (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i : Nat} {u : GoldfishVote V} {t : Time}
    (hacc : Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (Object.gfVote u) t) :
    (∃ o : Object V,
        rho.events[i]? = some (Record.Event.deliver v o t) ∧
        (W (i + 1) v).st.core.timestamp_vote u = some ((W i v).st.core.t : Stamp) ∧
        ¬ (W i v).st.core.s < u.slot) ∨
      (rho.events[i]? = some (Record.Event.tick v t) ∧
        (W (i + 1) v).st.core.timestamp_vote u = some (t : Stamp) ∧
        ¬ S.E.slotOf t < u.slot) :=
  Restated.Vocabulary.Protocol.acceptsAt_gfVote_time_shape_of_fields facts S hf.sorted hf.in_horizon W
    hf.onePath hacc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` accepts `u` at `t`, then the proposal time of `u`'s slot is at
    most `t`. -/
theorem proposal_time_le_of_acceptsAt_gfVoteOn_Protocol (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i : Nat} {u : GoldfishVote V} {t : Time}
    (hacc : Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (Object.gfVote u) t) :
    M.proposal_time S.E u.slot ≤ t := by
  rcases Restated.acceptsAt_gfVote_time_shapeOn_Protocol facts S Hs Xb hf hacc with
    ⟨o, he, -, hfuture⟩ | ⟨he, -, hfuture⟩
  · have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho i v
      (W i) (hf.onePath i).1
    unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
    have hmono : M.proposal_time S.E u.slot ≤
        M.proposal_time S.E (S.E.slotOf (W i v).st.core.t) :=
      facts.sch.proposal_time_mono S.E (by rw [← hslot]; exact Nat.le_of_not_gt hfuture)
    exact le_trans hmono (le_trans
      (facts.sch.proposal_time_slotOf_le S.E
        (Restated.stateBefore_store_time_nonnegOn facts S Hs Xb hf v i))
      (Restated.store_time_le_event_timeOn facts S Hs Xb hf he v :
        (W i v).st.t ≤ t))
  · have hmono : M.proposal_time S.E u.slot ≤
        M.proposal_time S.E (S.E.slotOf t) :=
      facts.sch.proposal_time_mono S.E (Nat.le_of_not_gt hfuture)
    exact le_trans hmono (facts.sch.proposal_time_slotOf_le S.E
      (hf.in_horizon _ (List.mem_of_getElem? he)).1)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` accepts `u` at `t` at index `i`, `i + 1 ≤ n`, `Gamma` is public
    and at least `lo`, `v` is in the set for `Gamma`, and `u`'s stamp in `v`'s store in `W n` is
    less than `Gamma`, then `t < Gamma`. -/
theorem acceptsAt_gfVote_lt_of_stamp_beforeOn_Protocol (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i n : Nat}
    {u : GoldfishVote V} {t Gamma : Time}
    (hacc : Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (Object.gfVote u) t)
    (hin : i + 1 ≤ n) (hpub : PublicTime S Gamma)
    (hv : v ∈ Hs Gamma) (hΓlo : lo ≤ Gamma)
    (hstamp : stampedBefore (W n v).st.core.timestamp_vote Gamma u = true) :
    t < Gamma := by
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (i + 1) v).st.core (W n v).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf v n hin
  rcases Restated.acceptsAt_gfVote_time_shapeOn_Protocol facts S Hs Xb hf hacc with
    ⟨o, he, hpostStamp, -⟩ | ⟨he, hpostStamp, -⟩
  · have hlater : (W n v).st.core.timestamp_vote u = some ((W i v).st.core.t : Stamp) :=
      hcarry.stamp u _ hpostStamp
    obtain ⟨σ, hσ, hσlt⟩ := exists_stamp_of_stampedBefore hstamp
    rw [hlater, Option.some_inj] at hσ
    rw [← hσ] at hσlt
    apply Restated.processed_lt_of_store_time_ltOn facts S Hs Xb hf hv he hpub hΓlo
    exact WithBot.coe_lt_coe.mp hσlt
  · have hlater : (W n v).st.core.timestamp_vote u = some (t : Stamp) :=
      hcarry.stamp u _ hpostStamp
    obtain ⟨σ, hσ, hσlt⟩ := exists_stamp_of_stampedBefore hstamp
    rw [hlater, Option.some_inj] at hσ
    rw [← hσ] at hσlt
    exact WithBot.coe_lt_coe.mp hσlt

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` is in the set for `s`'s support cutoff, which is at least `lo`,
    every acceptance along `W` by `v` of a vote of an outcome of the slot-`s` confirmation numerator
    of `v`'s confirmation store read from `W` is in `[proposal_time s, support_cutoff s)`. -/
theorem confirmationAcceptanceTiming_of_admissibleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (s : Slot) (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hΓlo : lo ≤ M.support_cutoff S.E s) :
    ∀ X, Restated.Vocabulary.Protocol.confVotes M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ⇢ X →
      ∀ u ∈ X,
      ∀ i t, Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (Object.gfVote u) t →
        M.proposal_time S.E s ≤ t ∧ t < M.support_cutoff S.E s := by
  intro X hX u hu i t hacc
  let n := strictEventIndex rho (M.confirmation_time S.E s)
  have hlo := Restated.proposal_time_le_of_acceptsAt_gfVoteOn_Protocol facts S Hs Xb hf hacc
  obtain ⟨e, he, rfl⟩ := returns_map_elim₄₆ _ _ _ hX
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₄₆ _ _ _ he
  have hearly := (Finset.mem_filter.mp hu).1
  rw [mem_beforeCutoff_iff] at hearly
  have hus : u.slot = s := by
    have huprefix : u ∈ M.store_pool (W n v).st.core s := by
      have h := hearly.1
      rwa [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.pool_set_clock_slot] at h
    have hulist : u ∈ (W n v).st.core.gf_votes s :=
      (facts.sto.mem_store_pool_iff _ s u).mp huprefix
    exact (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf v n).slot s u hulist
  have hhi : t < M.support_cutoff S.E s := by
    have hreceipt := facts.sto.stampedBefore_vote_of_tau _ τ hτ hearly.2
    have hstamp : stampedBefore (W n v).st.core.timestamp_vote (M.support_cutoff S.E s) u = true := by
      rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, store_with_t_s_timestamp_vote₄₆ facts] at hreceipt
      exact hreceipt
    have hi : i < n := by
      by_contra hnot
      have hni : n ≤ i := Nat.le_of_not_gt hnot
      have hisSome : ((W n v).st.core.timestamp_vote u).isSome = true := by
        obtain ⟨σ, hσ, -⟩ := exists_stamp_of_stampedBefore hstamp
        rw [hσ]
        rfl
      have hnmem : u ∈ (W n v).st.core.gf_votes u.slot :=
        (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf v n).pooled u hisSome
      have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W n v).st.core (W i v).st.core :=
        Restated.pool_carryOn facts S Hs Xb hf v i hni
      have himem := hcarry.mem u.slot u hnmem
      have hpre : u ∉ (W i v).st.core.gf_votes u.slot := by
        simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using
          hacc.2.1
      exact hpre himem
    exact Restated.acceptsAt_gfVote_lt_of_stamp_beforeOn_Protocol facts S Hs Xb hf hacc
      (Nat.succ_le_of_lt hi) (Restated.Vocabulary.Protocol.publicTime_support_cutoff facts S s) hv hΓlo
      hstamp
  rw [hus] at hlo
  exact ⟨hlo, hhi⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` is in the set for `s`'s support cutoff, which is at least `lo`,
    every vote of the slot-`s` confirmation numerator of `v`'s confirmation store read from `W` has
    an acceptance by `v` along `W` in `[proposal_time s, support_cutoff s)`. -/
theorem confirmationVotesAcceptedInWindow_of_admissibleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (s : Slot) (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hΓlo : lo ≤ M.support_cutoff S.E s) :
    Restated.Vocabulary.Protocol.ConfirmationVotesAcceptedInWindow M S rho W v
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s))
      s :=
  Restated.confirmationVotesAcceptedInWindow_of_timingOn facts S Hs Xb hf
    (Restated.confirmationAcceptanceTiming_of_admissibleOn facts S Hs Xb hf s hv hΓlo)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `w` is in the set for `s`'s view freeze, which is at least `lo`,
    every vote stamped before that freeze in `w`'s slot-`(s + 1)` vote-duty pool read from `W` has
    an acceptance by `w` along `W` in `[proposal_time s, view_freeze s)`. -/
theorem targetReceiptVotesAcceptedInWindow_of_admissibleOn_Protocol (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (s : Slot) (hw : w ∈ Hs (M.view_freeze S.E s))
    (hΓlo : lo ≤ M.view_freeze S.E s) :
    ∀ u ∈ beforeCutoff
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
        (M.view_freeze S.E s)
        (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s),
      ∃ (i : Nat) (t : Time),
        Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i w (Object.gfVote u) t ∧
        u.slot = s ∧ M.proposal_time S.E s ≤ t ∧ t < M.view_freeze S.E s := by
  have hW := hf.onePath
  intro u hu
  let n := strictEventIndex rho (M.vote_time S.E (s + 1))
  have huPrefix : u ∈ beforeCutoff (W n w).st.core.timestamp_vote (M.view_freeze S.E s)
      (M.store_pool (W n w).st.core s) := by
    have hu' := hu
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      store_with_t_s_timestamp_vote₄₆ facts] at hu'
    rwa [show M.store_pool (M.store_with_t_s (W n w).st.core (M.vote_time S.E (s + 1))
      (S.E.slotOf (M.vote_time S.E (s + 1)))) s = M.store_pool (W n w).st.core s from
      facts.sto.pool_set_clock_slot _ _ _ s] at hu'
  have huPool : u ∈ M.store_pool (W n w).st.core s :=
    ((mem_beforeCutoff_iff _ _ _ _).mp huPrefix).1
  have huList : u ∈ (W n w).st.core.gf_votes s :=
    (facts.sto.mem_store_pool_iff _ s u).mp huPool
  have hus : u.slot = s :=
    (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w n).slot s u huList
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n w).st (Object.gfVote u) = true :=
    by simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
       rw [hus]
       exact huList
  obtain ⟨i, hin, t, hacc⟩ :=
    Restated.Vocabulary.Protocol.acceptsAt_gfVote_of_processed facts S rho w W hW n u hprocessed
  have hlo : M.proposal_time S.E s ≤ t := by
    rw [← hus]
    exact Restated.proposal_time_le_of_acceptsAt_gfVoteOn_Protocol facts S Hs Xb hf hacc
  have hhi : t < M.view_freeze S.E s := by
    apply Restated.acceptsAt_gfVote_lt_of_stamp_beforeOn_Protocol facts S Hs Xb hf hacc
      (Nat.succ_le_of_lt hin) (Restated.Vocabulary.Protocol.publicTime_view_freeze facts S s) hw hΓlo
    exact ((mem_beforeCutoff_iff _ _ _ _).mp huPrefix).2
  exact ⟨i, t, hacc, hus, hlo, hhi⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `w` is in the set for `s`'s view freeze, which is at least `lo`,
    every vote stamped before that freeze in `w`'s slot-`(s + 1)` vote-duty pool read from `W` has
    an acceptance by `w` along `W` in `[proposal_time s, view_freeze s)`. -/
theorem targetReceiptVotesAcceptedInWindow_of_admissibleOn_WeakExecution (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (s : Slot) (hw : w ∈ Hs (M.view_freeze S.E s))
    (hΓlo : lo ≤ M.view_freeze S.E s) :
    ∀ u ∈ beforeCutoff
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
        (M.view_freeze S.E s)
        (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s),
      ∃ (i : Nat) (t : Time),
        Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i w (Object.gfVote u) t ∧
        u.slot = s ∧ M.proposal_time S.E s ≤ t ∧ t < M.view_freeze S.E s :=
  Restated.targetReceiptVotesAcceptedInWindow_of_admissibleOn_Protocol facts S Hs Xb hf s hw
    hΓlo

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if the tree of `v`'s store in `W (strictEventIndex rho t)` holds `B`
    and `X ⪯ B`, then that tree holds `X`. -/
theorem ancestor_mem_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {t : Time} {X B : Block V} :
    B ∈ (W (strictEventIndex rho t) v).st.T → Block.Preceq X B →
      X ∈ (W (strictEventIndex rho t) v).st.T := by
  intro hB hXB
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho t v _
    (mem_stateBeforeTime_along₄₆ _hf.sorted _hf.onePath t)
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  exact Proofs.Records.mem_of_preceq hpc.2 X B hB (preceq_eq_true_iff_Preceq.mpr hXB)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v`'s tree in the world of `W` strictly before `t` holds
    `B ≠ genesis`, the slot of `B`'s parent is less than `B`'s. -/
theorem parent_slot_lt_of_mem_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {t : Time} {B : Block V}
    (hB : B ∈ (W (strictEventIndex rho t) v).st.core.T)
    (hne : B ≠ Block.genesis) :
    B.parent.slot < B.slot := by
  have hW := hf.onePath
  let n := strictEventIndex rho t
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n v (W n)
      (hW n).1 hB
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n v).st (.block D) = true :=
    by simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW n D hprocessed with
      hgenesis | ⟨i, -, t', hacc⟩
  · exact absurd (hDe.symm.trans (by rw [hgenesis, erase_named_genesis])) hne
  · simpa only [hDe] using Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW hacc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v`'s tree in the world of `W` strictly before `t` holds `B` and
    `X ⪯ B`, then `X`'s slot is at most `B`'s. -/
theorem preceq_slot_le_of_mem_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {t : Time} :
    ∀ B : Block V, B ∈ (W (strictEventIndex rho t) v).st.core.T →
      ∀ X : Block V, Block.Preceq X B → X.slot ≤ B.slot := by
  have hw := mem_stateBeforeTime_along₄₆ hf.sorted hf.onePath t
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho t v _ hw
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  exact preceq_slot_le_of_parentClosed hpc.2
    (fun C hC hne => Restated.parent_slot_lt_of_mem_storeBeforeTimeOn facts S Hs Xb hf hC hne)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `v` accepts `B` at `t`, then `B`'s proposal time is at most `t`. -/
theorem proposal_time_le_of_acceptsAt_blockOn_SlotFreshness (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) t) :
    M.proposal_time S.E B.erase.slot ≤ t :=
  Restated.proposal_time_le_of_acceptsAt_blockOn_BlockAdmission facts S Hs Xb hf hacc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `0 < s` and `v`'s tree in the world of `W` strictly before `s`'s
    proposal time holds `C`, then `C`'s slot is less than `s`. -/
theorem block_slot_lt_of_mem_before_proposalOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} (hs : 0 < s) {C : Block V}
    (hC : C ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) v).st.core.T) :
    C.slot < s := by
  have hW := hf.onePath
  let n := strictEventIndex rho (M.proposal_time S.E s)
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n v (W n)
      (hW n).1 hC
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n v).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW n D hprocessed with
    hgen | hacc
  · subst D
    rw [erase_named_genesis] at hDe
    subst C
    rw [genesis_slot_inclG2]
    exact hs
  · obtain ⟨i, hin, t, haccepts⟩ := hacc
    obtain ⟨-, e, he, -, het⟩ := haccepts.1
    have ht : t < M.proposal_time S.E s := by
      rw [← het]
      exact time_lt_of_lt_strict₄₆ hf.sorted he hin
    by_contra hnot
    have hsC : s ≤ D.erase.slot := by rw [hDe]; exact Nat.le_of_not_gt hnot
    have hmono := facts.sch.proposal_time_mono S.E hsC
    have hCtime := Restated.proposal_time_le_of_acceptsAt_blockOn_SlotFreshness facts S Hs Xb hf
      haccepts
    exact (not_lt_of_ge (le_trans hmono hCtime)) ht

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `0 < s`, `t` is at most `s`'s proposal time, and `v`'s tree in the
    world of `W` strictly before `t` holds `C`, then `C`'s slot is less than `s`. -/
theorem block_slot_lt_of_mem_beforeTime_of_le_proposalOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} {t : Time} (hs : 0 < s)
    (ht : t ≤ M.proposal_time S.E s) {C : Block V}
    (hC : C ∈ (W (strictEventIndex rho t) v).st.core.T) : C.slot < s := by
  have hW := hf.onePath
  let n := strictEventIndex rho t
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n v (W n)
      (hW n).1 hC
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n v).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW n D hprocessed with
    hgen | hacc
  · subst D
    rw [erase_named_genesis] at hDe
    subst C
    rw [genesis_slot_inclG2]
    exact hs
  · obtain ⟨i, hin, time, hacc⟩ := hacc
    obtain ⟨_, e, he, _, het⟩ := hacc.1
    have htime : time < M.proposal_time S.E s := by
      rw [← het]
      exact (time_lt_of_lt_strict₄₆ hf.sorted he hin).trans_le ht
    by_contra hnot
    have hslot : s ≤ D.erase.slot := by rw [hDe]; exact Nat.le_of_not_gt hnot
    exact (not_lt_of_ge ((facts.sch.proposal_time_mono S.E hslot).trans
      (Restated.proposal_time_le_of_acceptsAt_blockOn_SlotFreshness facts S Hs Xb hf hacc))) htime

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `reader` holds `H` in the world of `W` strictly before
    `early ≤ late`, it holds `H` in the world of `W` strictly before `late`, with the same stamp. -/
theorem strict_body_stamp_carryOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) {early late : Time}
    (ht : early ≤ late) (H : NamedBlock V)
    (hH : H ∈ (W (strictEventIndex rho early) reader).st.bodies) :
    H ∈ (W (strictEventIndex rho late) reader).st.bodies ∧
      (W (strictEventIndex rho late) reader).st.core.timestamp_block H.erase =
        (W (strictEventIndex rho early) reader).st.core.timestamp_block H.erase :=
  Restated.Vocabulary.Proofs.NamedBlockStamp.stateBefore_body_stamp_mono facts S rho reader
    (strictEventIndex_mono rho ht) (W (strictEventIndex rho early)) (hf.onePath _).1 hH
    (W (strictEventIndex rho late)) (onePath_slice₄₆ W hf.onePath (strictEventIndex_mono rho ht))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if `reader ∈ Xb` holds `H` in the world of `W` strictly before `t`, its
    tree there finds `H`'s erasure at `H`'s root. -/
theorem held_find_at_strictOn_HealthyHeadReady (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) (hreader : reader ∈ Xb) (t : Time) (H : NamedBlock V)
    (hH : H ∈ (W (strictEventIndex rho t) reader).st.bodies) :
    Block.find? (W (strictEventIndex rho t) reader).st.core.T H.erase.root = some H.erase := by
  have hW := hf.onePath
  let n := strictEventIndex rho t
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n reader (W n)
    (hW n).1).1.1.1
  have hHscope := Restated.blockInRun_of_directOn facts S rho W Xb
    (Restated.directBlock_of_prefixOn facts S rho W Xb hreader n hH)
  have hHraw : H.erase ∈ (W n reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hH
  apply Proofs.Optimistic.find?_eq_some_of_unique hHraw
  intro raw hraw hroot
  rw [hcoh.1] at hraw
  obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hraw
  have hotherScope := Restated.blockInRun_of_directOn facts S rho W Xb
    (Restated.directBlock_of_prefixOn facts S rho W Xb hreader n hother)
  have hroots : other.root = H.root :=
    (Proofs.NamedWire.erase_root other).symm.trans (hroot.trans (Proofs.NamedWire.erase_root H))
  have heq : other = H := hf.rootCollisionFree.root_injective other H hotherScope hHscope other H
    (Or.inl (Proofs.NamedAncestry.named_self other)) (Or.inr (Proofs.NamedAncestry.named_self H))
    hroots
  exact congrArg NamedBlock.erase heq

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.FrameCompleted

/-! ### Frame completion -/

/-- On the path `W` of `hf`, if the `i`-th event is `v`'s tick at the phase-`p` domain time of the
    positive round `r` and that tick has an outcome (`hneTick`), then for every `t` after that
    domain time and at most `opening (r + 1)`, and every outcome `fr` of the frozen root of `v`'s
    store in the world of `W` strictly before the domain time, the phase-`p` result of the round-`r`
    frame read in the world of `W` strictly before `t` is `fr` clipped against `v`'s finalized block
    there. -/
theorem frame_phase_completed_of_tick_in_roundOn (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) (hr : 0 < r) (p : DecoupledConsensusModel.Protocol.Phase)
    (i : Nat) (he : rho.events[i]? = some (.tick v (M.domain S.E S.hc r p)))
    (t : Time) (ht : M.domain S.E S.hc r p < t) (hta : t ≤ M.opening S.E S.hc (r + 1))
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.domain S.E S.hc r p)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (M.domain S.E S.hc r p) ⇢ out) :
    ∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
    M.phaseResult (M.readFrame (W (strictEventIndex rho t) v).cache
        (M.toHealing (W (strictEventIndex rho t) v).st.core) r) p =
      some (fr.map (fun B => M.clipGrade B (W (strictEventIndex rho t) v).st.core.F)) :=
  Restated.Vocabulary.Proofs.FrameCompleted.frame_phase_completed_of_tick_in_round_of_fields facts S
    rho hf.sorted hf.tickIndexUnique W hf.onePath v r hr p i he hneTick t ht hta

/-- On the path `W` of `hf`, if `v` is in the set for the phase-`p` domain time of the positive
    round `r`, that time is at least `lo` and at most the horizon, and `v`'s tick there has an
    outcome (`hneTick`), then for every `t` after that domain time and at most `opening (r + 1)`,
    and every outcome `fr` of the frozen root of `v`'s store in the world of `W` strictly before the
    domain time, the phase-`p` result of the round-`r` frame read in the world of `W` strictly
    before `t` is `fr` clipped against `v`'s finalized block there. -/
theorem frame_phase_completed_in_roundOn (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) (hr : 0 < r) (p : DecoupledConsensusModel.Protocol.Phase)
    (hv : v ∈ Hs (M.domain S.E S.hc r p)) (t : Time)
    (ht : M.domain S.E S.hc r p < t) (hta : t ≤ M.opening S.E S.hc (r + 1))
    (htick : M.domain S.E S.hc r p ≤ rho.horizon) (hgat : lo ≤ M.domain S.E S.hc r p)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.domain S.E S.hc r p)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (M.domain S.E S.hc r p) ⇢ out) :
    ∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
    M.phaseResult (M.readFrame (W (strictEventIndex rho t) v).cache
        (M.toHealing (W (strictEventIndex rho t) v).st.core) r) p =
      some (fr.map (fun B => M.clipGrade B (W (strictEventIndex rho t) v).st.core.F)) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
    (hf.tick_total (M.domain S.E S.hc r p) hgat v hv (facts.gr.publicTime_domain S hr p) htick)
  exact frame_phase_completed_of_tick_in_roundOn facts S rho Hs Xb hf v r hr p i hi t ht hta
    hneTick

/-- The statement of `frame_phase_completed_in_roundOn` for read times `t` at most `S.a r` in place
    of `opening (r + 1)`. -/
theorem frame_phase_completedOn (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) (hr : 0 < r) (p : DecoupledConsensusModel.Protocol.Phase)
    (hv : v ∈ Hs (M.domain S.E S.hc r p)) (t : Time)
    (ht : M.domain S.E S.hc r p < t) (hta : t ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (htick : M.domain S.E S.hc r p ≤ rho.horizon) (hgat : lo ≤ M.domain S.E S.hc r p)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.domain S.E S.hc r p)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (M.domain S.E S.hc r p) ⇢ out) :
    ∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
    M.phaseResult (M.readFrame (W (strictEventIndex rho t) v).cache
        (M.toHealing (W (strictEventIndex rho t) v).st.core) r) p =
      some (fr.map (fun B => M.clipGrade B (W (strictEventIndex rho t) v).st.core.F)) := by
  have ha : Restated.Vocabulary.Execution.Setup.a M S r < M.opening S.E S.hc (r + 1) := by
    show M.a S.hc S.E.Δ r < M.opening S.E S.hc (r + 1)
    rw [facts.sch.a_eq_confirmation_time, facts.gr.opening_eq_proposal_time]
    exact facts.sch.confirmationTime_lt_proposalTime_of_two_le S.E
      (facts.gr.plusTwo_slot_le_nextOpening_l53 S r)
  exact frame_phase_completed_in_roundOn facts S rho Hs Xb hf v r hr p hv t ht
    (le_of_lt (lt_of_le_of_lt hta ha)) htick hgat hneTick

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.FrameCompleted


end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.FrameCompleted


end

/-! ## Grade-2 action blocks and the frozen G1 root -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.FrameCompleted

/-- On the path `W` of `hf`, if `p`'s round-`r` action read can give a node state `nq` that selects
    the grade-2 block `Q`, the reader `w` is in the set for `domain r .g1 ≥ lo`, `Q` is in the
    filtered tree of `w`'s node state strictly before `domain r .g1` and its grade-1 test there can
    return `true`, `Q` is in the filtered tree of `w`'s node state strictly before the vote time of
    a slot `s` of round `r` after that domain time and at most `S.a r`, and `w`'s tick at the domain
    time has an outcome (`hneTick`), then for every outcome `c` of the phase tick at that vote time,
    the round-`r` frame `w`'s vote duty reads with `c` has a frozen G1 root `R` with `Q ⪯ R`. -/
theorem selectedActionG2_preceq_frozenG1_at_readerOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) {p w : V}
    (_hp : p ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r))
    (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (hgat : lo ≤ M.domain S.E S.hc r .g1) {Q : Block V}
    (nq : M.N)
    (_hnq : nq ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (_hQ : M.grade2_block_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core) r ⇢
      some Q)
    {s : Slot} (hround : M.round_of S.hc s = r)
    (hread : M.domain S.E S.hc r .g1 < M.vote_time S.E s)
    (hta : M.vote_time S.E s ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hhor : M.domain S.E S.hc r .g1 ≤ rho.horizon)
    (hQdomain : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w))
    (hgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ true)
    (hQread : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.vote_time S.E s)) w))
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.domain S.E S.hc r .g1)) →
      ∃ out : M.N × List (NamedObject V), M.tick S w (W j w) (M.domain S.E S.hc r .g1) ⇢ out) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core)
        (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c →
      ∃ R, (M.readFrame c
          (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
            (M.vote_time S.E s)).core) r).g1 = some (some R) ∧ Block.Preceq Q R := by
  intro c hc
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hd
  set b := W (strictEventIndex rho (M.vote_time S.E s)) w with hb
  have hT : Q ∈ d.st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree facts hQdomain
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  obtain ⟨raw, hfz, hQraw⟩ := facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing d.st.core)) d.st.core.F
    S.hc.η_SG r (facts.gr.q10_early_le_late S r .g1)
    (by rw [facts.gr.Sts_gradeView_T]; exact hT) true hgrade rfl fr hfr
  have hFQ : Block.Preceq b.st.core.F Q := by
    have h := facts.fc.q10_filtered_F hQread
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  have hcompat : Block.compatible Q b.st.core.F = true :=
    compatible_of_cases (Or.inr hFQ)
  have hQclip : Block.Preceq Q (M.clipGrade raw b.st.core.F) :=
    (facts.gr.q10_retained_prefix raw b.st.core.F Q hcompat).mpr hQraw
  have hframe := Restated.frame_phase_completedOn facts S rho Hs Xb hf w r hr .g1 hw
    (M.vote_time S.E s) hread hta hhor hgat hneTick fr hfr
  rw [hfz] at hframe
  have hround' : M.round_of S.hc (S.E.slotOf (M.vote_time S.E s)) = r := by
    rw [facts.sch.slotOf_vote_time]; exact hround
  have hprepared := facts.grRun.frame_phase_prepared_eq_of_outcomes S rho w r .g1
    (M.vote_time S.E s) hround' (some (M.clipGrade raw b.st.core.F))
    (W (strictEventIndex rho (M.vote_time S.E s)))
    (mem_stateBeforeTime_along₄₆ hf.sorted hf.onePath (M.vote_time S.E s)) hframe c hc
  rw [facts.gr.phaseResult_g1] at hprepared
  exact ⟨M.clipGrade raw b.st.core.F, hprepared, hQclip⟩

/-- Under the hypotheses of `selectedActionG2_preceq_frozenG1_at_readerOn`, for an outcome `c` of
    the phase tick at the vote time of `s` and the vote-duty node state `n` built with `c`, if `Q`
    is also in the filtered tree of `n`'s store, then `Q` is an ancestor of every outcome of the
    in-tree head computed on `n`'s store with every outcome of the voter's filtered tree and of the
    two voter views. -/
theorem selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVoteOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) {p : V}
    (hp : p ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r)) {Q : Block V}
    (nq : M.N)
    (hnq : nq ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hQ : M.grade2_block_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core) r ⇢
      some Q)
    {s : Slot} (hround : M.round_of S.hc s = r)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) (hgat : lo ≤ M.domain S.E S.hc r .g1)
    (hread : M.domain S.E S.hc r .g1 < M.vote_time S.E s)
    (hta : M.vote_time S.E s ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hhor : M.domain S.E S.hc r .g1 ≤ rho.horizon)
    (hQdomain : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w))
    (hgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ true)
    (hQread : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.vote_time S.E s)) w))
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.domain S.E S.hc r .g1)) →
      ∃ out : M.N × List (NamedObject V), M.tick S w (W j w) (M.domain S.E S.hc r .g1) ⇢ out)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core)
      (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c)
    (hactiveVote : Q ∈ M.get_filtered_block_tree
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record
        c).st.core).toFG) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c
    ∀ tree : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ tree →
    ∀ votes : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ votes →
    ∀ support : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢
        support →
    ∀ X : Block V,
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        tree votes support (n.st.core.s - 1) ⇢ X →
      Block.Preceq Q X := by
  intro n tree _ votes _ support _ X hX
  obtain ⟨R, hframe, hQR⟩ := selectedActionG2_preceq_frozenG1_at_readerOn facts
    S Hs Xb hf hr hp hw hgat nq hnq hQ hround hread hta hhor hQdomain hgrade hQread hneTick c hc
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s)) c :=
    facts.nd.mkNode_st _ _ _
  have hcache : n.cache = c := facts.nd.mkNode_cache _ _ _
  have hslot : n.st.core.s = s := by
    rw [hnst, facts.nd.store_with_cache_core_s, facts.hd.Sts_setClock_core_s,
      facts.sch.slotOf_vote_time]
  have hroundVote : M.round_of S.hc n.st.core.s = r := by rw [hslot]; exact hround
  have hframe' : (M.readFrame n.cache (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s)).g1 = some (some R) := by
    rw [hroundVote, hcache, hnst, facts.nd.store_with_cache_readFrame]; exact hframe
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc n.st.core.s)
    (M.readFrame n.cache (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)).g1
  have hGa := facts.nd.ModelProperties_gradeContract_read_anchor _ _ _ _ _ G hG a ha
  obtain ⟨A, hA, hQA⟩ := facts.gr.activePrefix_covers hactiveVote hQR
  rw [hframe'] at ha
  have haA : a = A := facts.gr.anchor_of_activePrefix S.E S.hc _ _ hA a ha
  have hhead : Block.Preceq G.anchor X :=
    facts.fc.read_anchor_preceq_get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) tree votes support (n.st.core.s - 1) G
      (by rw [facts.sto.toHealing_s]; exact hG) X hX
  rw [hGa, haA] at hhead
  exact Proofs.ModelProperties.Preceq_trans hQA hhead

end

end DecoupledConsensusModel.Sts.Restated
