import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradePersistence
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecoveryTimeout
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_Evidence
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FinalityGadget_Crossing
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_FinalityPairCore
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_RecordFresh
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_50

/-!
# Vote-duty heads, action reads and recovery heights along a path

Theorems over a model `M : Record.Model V` and its facts, read along the path `W` of the bundle
`AdmissibleFieldsOn`: the vote-duty candidate trees and heads, the bodies, FG sources and
attestations of action reads, and the finality floor, locks and targets at a recovery height.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ### Helpers -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₀ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_path₅₀ (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₀ S rho hsorted t]
  exact (hW _).1

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₀ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₅₀ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₀ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
private theorem drop_take_succ₅₀ {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

omit [DecidableEq V] [Fintype V] in
private theorem drop_take_succ_none₅₀ {rho : Record.Run V} {i : Nat}
    (hi : rho.events[i]? = none) : (rho.events.drop i).take (i + 1 - i) = [] := by
  rw [List.getElem?_eq_none_iff] at hi
  rw [List.drop_eq_nil_of_le hi]
  exact List.take_nil

private theorem mem_foldlM_singleton₅₀ (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

/-- Along a path `W` of `rho`, either there is no event at index `n` and `W (n + 1) = W n`, or the
    `n`-th event `e` leads from `W n` to `W (n + 1)`. -/
private theorem path_step_cases₅₀ {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (n : Nat) :
    (rho.events[n]? = none ∧ W (n + 1) = W n) ∨
      ∃ e, rho.events[n]? = some e ∧ W (n + 1) ∈ Record.worldStepOf M S (W n) e := by
  have h := (hW n).2
  rcases hev : rho.events[n]? with _ | e
  · rw [drop_take_succ_none₅₀ hev] at h
    exact Or.inl ⟨rfl, Set.mem_singleton_iff.mp h⟩
  · rw [drop_take_succ₅₀ hev, mem_foldlM_singleton₅₀] at h
    exact Or.inr ⟨e, rfl, h⟩

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events has a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₀ {rho : Record.Run V}
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
/-- In a run sorted by key, if the `i`-th event is `e`, the number of events with a time before
    `e`'s time is at most `i`. -/
private theorem strict_le_tick₅₀ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {i : Nat} {e : Record.Event V} (hi : rho.events[i]? = some e) :
    strictEventIndex rho e.time ≤ i := by
  by_contra hnot
  have hlt : i < strictEventIndex rho e.time := Nat.lt_of_not_ge hnot
  exact lt_irrefl _ (time_lt_of_lt_strict₅₀ hsorted hi hlt)

/-- The round-`r` action read computed from `M.wake n` gives the same node states as the one
    computed from `n`. -/
private theorem actionReadFrom_wake₅₀ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

/-- The confirmation-membership invariant of a named store survives writing a grade cache into it. -/
private theorem invariant_store_with_cache₅₀ (facts : Record.Facts M) (E : Env V)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : M.NS) (c : M.Cache)
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

/-- Every node state along a path `W` of `rho` satisfies the node invariant. -/
private theorem nodeInvariant_path₅₀ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (i : Nat)
    (v : V) : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (W i v) :=
  Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v _ (hW i).1

private theorem returns_map_elim₅₀ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- The store the slot-`s` vote duty reads is the core store of `n`'s store with its clock set to
    the slot-`s` vote instant. -/
private theorem voteStore_eq₅₀ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- Every node state the round-`r` action read from `before` can give holds the bodies `before`
    holds. -/
private theorem actionReadFrom_bodies₅₀ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The round-`r` action read from `before` can give some node state. -/
private theorem actionReadFrom_nonempty₅₀ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing before.st.core)
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- The action head read under `contract` at the healing store `st` has some outcome. -/
private theorem actionHeadWith_nonempty₅₀ (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.HS) :
    ∃ H, Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M contract E hc st ⇢ H := by
  choose res hres using fun u => facts.sto.resolved_nonempty st.T u
  obtain ⟨X, hX⟩ := facts.fc.get_head_with_nonempty contract E hc st
    (st.toFG.toSG.toGoldfishStore.pool st.s)
    ((st.toFG.toSG.toGoldfishStore.pool st.s).filter (fun u => res u = true)) st.s
  exact ⟨X, res, hres, hX⟩

/-- If the FG root of the healing store `st` is in its filtered tree, every outcome of the anchor
    read at `st` from any grade-1 result is in that filtered tree. -/
private theorem anchor_mem_filtered₅₀ (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.HS) (r : Round)
    (g1 : Option (Option (Block V)))
    (hroot : M.get_fg_root st.toFG ∈ M.get_filtered_block_tree st.toFG) :
    ∀ a, M.anchor E hc st r g1 ⇢ a → a ∈ M.get_filtered_block_tree st.toFG := by
  intro a ha
  rcases facts.gr.anchor_cases E hc st r g1 a ha with h | ⟨root, A, -, hA, h⟩
  · rw [h]
    exact hroot
  · rw [h]
    exact facts.gr.activePrefix_mem _ root A hA

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of the bundle, if `w ∈ Xb`, the store of `w`'s node state in the world strictly
    before slot `d`'s vote instant, with its clock set to that instant, is parent-closed on named
    bodies, its cached chain states agree with the named derivation, and its tree is root-injective
    on ancestors. -/
theorem voteDuty_parentClosed_agrees_rootInjectiveOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (d : Slot) :
    let read := M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M read ∧
      Restated.Vocabulary.Internal.NamedDerivedStateAgrees M S.E S.cfg read ∧
      RootInjectiveBelow read.core.T := by
  intro read
  have hinv := nodeInvariant_path₅₀ facts S hf.onePath (strictEventIndex rho (M.vote_time S.E d)) w
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg read :=
    (facts.hd.invariant_clock S.E S.cfg _ _ hinv.1).1.1
  have hinj : RootInjectiveBelow (read.bodies.image NamedBlock.erase) := by
    apply Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hf.rootCollisionFree
    intro C hC
    apply Restated.runBlock_of_stateBefore_memOn facts S W Xb hw
      (i := strictEventIndex rho (M.vote_time S.E d))
    rw [facts.hd.Sts_setClock_bodies] at hC
    exact hC
  refine ⟨hcoh.2.2.1, hcoh.2.2.2.2, ?_⟩
  rw [hcoh.1]
  exact hinj

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of the bundle, with `duty` the core store of `w`'s slot-`s + 1` vote-duty read:
    if `H` is in `w`'s voter-filtered tree of `duty`, `Wt` is in its voter-processed tree, `D` is a
    child of `H` with `D ⪯ Wt`, `Wt` has height at least `duty.h_max - 1`, and `lo ≤ view_freeze s`,
    then `D` is in that voter-filtered tree. -/
theorem namedFrozenCandidate_child_towards_witnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s)) {H Wt D : Block V} :
    let duty := (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))).core
    ∀ X : Finset (Block V), M.voter_filtered_block_tree S.E duty duty.s ⇢ X → H ∈ X →
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
      (M.toHealing duty).toFG.toSG.toGoldfishStore (M.toHealing duty).s ⇢ P → Wt ∈ P →
    D.parent? = some H →
    Block.Preceq D Wt →
    duty.h_max - 1 ≤ (duty.σ Wt).h →
    lo ≤ M.view_freeze S.E s →
    D ∈ X := by
  intro duty X hX hHX P hP hWP hDparent hDW hWheight hgat
  have hstoreEq : duty = Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1) :=
    (voteStore_eq₅₀ facts S _ (s + 1)).symm
  have hgs : (M.toHealing duty).s = duty.s := facts.sto.toHealing_gs_s duty
  have hP' : M.voter_processed_block_tree S.E (M.toHealing duty).toFG.toSG.toGoldfishStore
      duty.s ⇢ P := by
    rw [← hgs]
    exact hP
  obtain ⟨-, hFH, -, hrootH⟩ :=
    facts.hd.voter_filtered_block_tree_cases S.E duty duty.s X hX hHX P hP'
  have hHD : Block.Preceq H D :=
    Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (preceq_of_parent? hDparent)
  have hFD : Block.Preceq duty.F D := Proofs.ModelProperties.Preceq_trans hFH hHD
  have hrootD : Block.Preceq (M.get_fg_root (M.toHealing duty).toFG) D :=
    Proofs.ModelProperties.Preceq_trans hrootH hHD
  have hDprocessed : D ∈ P :=
    Restated.ancestorProcessed_of_voterProcessedOn facts S Hs Xb hf hw P
      (by rw [← hstoreEq]; exact hP) hWP hgat D hDW
  exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E duty duty.s P hP' hDprocessed hFD
    hWP hDW hWheight hrootD X hX

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of the bundle, with `duty` the core store of `w`'s slot-`s + 1` vote-duty read:
    if the run block `H` read through `Xb` is in the voter-processed tree of `duty`, `C ⪯ H`, `C` is
    in the filtered tree of `duty`, `duty.h_max` is at most `H`'s height plus one, and
    `lo ≤ view_freeze s`, then `C` is in the voter candidate tree of `duty`. -/
theorem namedAncestorCandidate_of_processedDescendant_and_hMax_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s))
    {C : Block V} {H : NamedBlock V} :
    let duty := (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))).core
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
      (M.toHealing duty).toFG.toSG.toGoldfishStore (M.toHealing duty).s ⇢ P →
    H.erase ∈ P →
    Restated.RunBlockOn M S rho W Xb H →
    Block.Preceq C H.erase →
    C ∈ M.get_filtered_block_tree (M.toHealing duty).toFG →
    duty.h_max ≤ (M.derive_named S.E S.cfg H).h + 1 →
    lo ≤ M.view_freeze S.E s →
    C ∈ M.get_filtered_block_tree_from (M.toHealing duty).toFG P := by
  intro duty P hP hHprocessed hHrun hCH hCfiltered hmax hgat
  let t := M.vote_time S.E (s + 1)
  have hmem := mem_stateBeforeTime_path₅₀ S rho hf.sorted W hf.onePath t
  have hstoreEq : duty = Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho t) w).st.core (s + 1) :=
    (voteStore_eq₅₀ facts S _ (s + 1)).symm
  have hHT : H.erase ∈ (W (strictEventIndex rho t) w).st.core.T := by
    have hdata := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ P hP hHprocessed
    rw [facts.sto.toHealing_gs_T] at hdata
    have hT : duty.T = (W (strictEventIndex rho t) w).st.core.T :=
      facts.hd.Sts_setClock_core_T _ _ _
    rw [← hT]
    exact hdata
  obtain ⟨Hn, hHnbody, hHnerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho t w
      _ hmem hHT
  have hHnrun : Restated.RunBlockOn M S rho W Xb Hn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hw) hHnbody
  have hHnEq : Hn = H := by
    apply hf.rootCollisionFree.root_injective
      Hn H hHnrun hHrun Hn H (Or.inl (Proofs.NamedAncestry.named_self Hn))
      (Or.inr (Proofs.NamedAncestry.named_self H))
    rw [← Proofs.NamedWire.erase_root Hn, hHnerase, Proofs.NamedWire.erase_root]
  have hHbody : H ∈ (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t).bodies := by
    rw [facts.hd.Sts_setClock_bodies, ← hHnEq]
    exact hHnbody
  have hsigma : duty.σ H.erase = M.derive_named S.E S.cfg H :=
    (Restated.voteDuty_parentClosed_agrees_rootInjectiveOn facts S Hs Xb hf (hHsXb _ hw)
      (s + 1)).2.1 H hHbody
  have hheight : duty.h_max - 1 ≤ (duty.σ H.erase).h := by
    rw [hsigma]
    exact Nat.sub_le_iff_le_add.mpr hmax
  have hCprocessed : C ∈ P :=
    Restated.ancestorProcessed_of_voterProcessedOn facts S Hs Xb hf hw P
      (by rw [← hstoreEq]; exact hP) hHprocessed hgat C hCH
  obtain ⟨⟨⟨-, hFC⟩, -⟩, hrootC⟩ := facts.fc.parts_of_mem_get_filtered_block_tree hCfiltered
  exact facts.fc.mem_get_filtered_block_tree_from_of_parts_explicit _ hCprocessed hFC hHprocessed hCH
    (by rw [facts.sto.Sts_toHealing_h_max, facts.sto.Sts_toHealing_σ]; exact hheight) hrootC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The conclusion of `namedAncestorCandidate_of_processedDescendant_and_hMax_coreOn`, from the
    bundle's hypotheses. -/
theorem namedAncestorCandidate_of_processedDescendant_and_hMaxOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s))
    {C : Block V} {H : NamedBlock V} :
    let duty := (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))).core
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
      (M.toHealing duty).toFG.toSG.toGoldfishStore (M.toHealing duty).s ⇢ P →
    H.erase ∈ P →
    Restated.RunBlockOn M S rho W Xb H →
    Block.Preceq C H.erase →
    C ∈ M.get_filtered_block_tree (M.toHealing duty).toFG →
    duty.h_max ≤ (M.derive_named S.E S.cfg H).h + 1 →
    lo ≤ M.view_freeze S.E s →
    C ∈ M.get_filtered_block_tree_from (M.toHealing duty).toFG P :=
  Restated.namedAncestorCandidate_of_processedDescendant_and_hMax_coreOn facts
    S Hs Xb hf hHsXb hw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of the bundle, with `n` `w`'s slot-`s + 1` vote-duty read: if `C` has the vote
    inputs of a Goldfish cone at `n`, some outcome of `n`'s anchor is an ancestor of `C`, and
    `lo ≤ view_freeze s`, then every outcome of the vote head `n` computes is the erasure of a run
    block read through `Xb` whose height is at least `h_max - 1` of `w`'s slot-`s + 1` vote store. -/
theorem voteDutyHead_height_ge_frontier_sub_one_of_candidateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s)) {C : Block V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core)
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ A : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
      Block.Preceq A C →
    lo ≤ M.view_freeze S.E s →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ Vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Vv →
    ∀ Uv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Uv →
    ∀ X : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T Vv Uv (n.st.core.s - 1) ⇢ X →
    ∃ Hn : NamedBlock V,
      Hn.erase = X ∧
      Restated.RunBlockOn M S rho W Xb Hn ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max - 1 ≤
        (M.derive_named S.E S.cfg Hn).h := by
  intro n A hA hAC hgat T hT Vv hVv Uv hUv X hX
  let t := M.vote_time S.E (s + 1)
  let i := strictEventIndex rho t
  let duty := n.st.core
  have hmem := mem_stateBeforeTime_path₅₀ S rho hf.sorted W hf.onePath t
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
    ⟨W i, hmem, c, hc, rfl⟩
  have hnst₀ : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st t) c :=
    facts.nd.mkNode_st _ _ _
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st t) _ := facts.nd.mkNode_st _ _ _
  have hfacts := Restated.voteDuty_parentClosed_agrees_rootInjectiveOn facts S Hs Xb hf
    (hHsXb _ hw) (s + 1)
  have htreeT : T ⊆ duty.T := facts.hd.Sts_voter_filtered_block_tree_subset S.E duty duty.s T hT
  have hinjDuty : RootInjectiveBelow duty.T := by
    show RootInjectiveBelow n.st.core.T
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hfacts.2.2
  have hrootTree : RootInjectiveBelow T := Protocol.RootInjectiveBelow.mono hinjDuty htreeT
  have hdutyT : duty.T = (W i w).st.core.T := by
    show n.st.core.T = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hinvPath := nodeInvariant_path₅₀ facts S hf.onePath i w
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
    rw [hnst₀]
    exact invariant_store_with_cache₅₀ facts S.E S.cfg _ c
      (facts.hd.invariant_clock S.E S.cfg _ _ hinvPath.1)
  have hroot : M.get_fg_root (M.toHealing duty).toFG ∈ duty.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts n.st hinv.1.2
  have hA' := hA
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA'
  obtain ⟨G, hG, hGA⟩ := returns_map_elim₅₀ _ _ _ hA'
  have hAT : A ∈ duty.T := by
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing duty) (M.round_of S.hc duty.s)
      (M.readFrame n.cache (M.toHealing duty) (M.round_of S.hc duty.s)).g1
    have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
      (M.toHealing duty) (M.round_of S.hc duty.s)
      (M.readFrame n.cache (M.toHealing duty) (M.round_of S.hc duty.s)).g1
      (by simp only [Record.Model.HS.T, facts.sto.toHealing_gs_T]; exact hroot) a ha
    simp only [Record.Model.HS.T, facts.sto.toHealing_gs_T] at h
    rw [← hGA, facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc _ _ G hG a ha]
    exact h
  have hHT : X ∈ duty.T :=
    facts.fc.ModelProperties_get_head_in_tree_with_layer_mem _ _ _ _ _ _ _ _ G
      (by rw [facts.sto.toHealing_s]; exact hG) (by rw [hGA]; exact hAT) htreeT X hX
  have hHpre : X ∈ (W i w).st.core.T := by
    rw [← hdutyT]
    exact hHT
  obtain ⟨Hn, hHnBody, hHnErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho t w
      _ hmem hHpre
  have hHnRun : Restated.RunBlockOn M S rho W Xb Hn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hw) hHnBody
  have hHnRead : Hn ∈ (M.ns_setClock S.E (W i w).st t).bodies := by
    rw [facts.hd.Sts_setClock_bodies]
    exact hHnBody
  have hSigma : duty.σ X = M.derive_named S.E S.cfg Hn := by
    rw [← hHnErase]
    show n.st.core.σ Hn.erase = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hfacts.2.1 Hn hHnRead
  refine ⟨Hn, hHnErase, hHnRun, ?_⟩
  by_contra hnot
  have hHlow : (duty.σ X).h < duty.h_max - 1 := by
    rw [hSigma]
    have e : duty.h_max = (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W i w).st.core (s + 1)).h_max := by
      rw [voteStore_eq₅₀ facts]
      show n.st.core.h_max = _
      rw [hnst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rfl
    rw [e]
    exact Nat.lt_of_not_ge hnot
  have hT₁ : M.voter_filtered_block_tree S.E (M.ns_setClock S.E (W i w).st t).core
      (M.ns_setClock S.E (W i w).st t).core.s ⇢ T := by
    simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hT
  have hineligible : ∀ D : Block V, D ∈ T → D.parent? = some X →
      (duty.σ X).h < duty.h_max - 1 → False := by
    intro D hDT hDparent hlow
    obtain ⟨e, he⟩ := facts.fc.goldfish_eligible_nonempty S.E duty.σ duty.h_max duty.T duty.s Vv Uv
      (duty.s - 1) D
    obtain ⟨g, hg⟩ := facts.fc.goldfish_score_nonempty S.E duty.T Vv Uv (duty.s - 1) D
    have htrue : e = true := by
      rw [facts.fc.goldfish_eligible_iff _ _ _ _ _ _ _ _ D e he g hg, parent_eq_of_parent? hDparent]
      exact Or.inl hlow
    have hfalse : e = false :=
      facts.fc.goldfish_eligible_false_of_parent_head (M.gradeContract n.cache) S.E S.hc duty T Vv Uv
        (duty.s - 1) hrootTree hDT X hX hDparent e he
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing duty).toFG.toSG.toGoldfishStore duty.s
  have hP₁ : M.voter_processed_block_tree S.E
      (M.toHealing (M.ns_setClock S.E (W i w).st t).core).toFG.toSG.toGoldfishStore
      (M.toHealing (M.ns_setClock S.E (W i w).st t).core).s ⇢ P := by
    simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hP
  have stopContradiction : ∀ (Z Y : Block V),
      Z = X → Z ∈ T → Y ∈ P →
      Block.Preceq Z Y → duty.h_max - 1 ≤ (duty.σ Y).h → False := by
    intro Z Y hZH hZtree hYprocessed hZY hYheight
    subst Z
    have hHneY : X ≠ Y := by
      intro hEq
      rw [← hEq] at hYheight
      exact (Nat.not_lt_of_ge hYheight) hHlow
    obtain ⟨D, hDparent, hDY⟩ :=
      exists_child_towards Y (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hZY) hHneY
    have hYheight₁ : (M.ns_setClock S.E (W i w).st t).core.h_max - 1 ≤
        ((M.ns_setClock S.E (W i w).st t).core.σ Y).h := by
      simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hYheight
    have hDtree : D ∈ T :=
      Restated.namedFrozenCandidate_child_towards_witnessOn facts S Hs Xb hf hw T hT₁ hZtree
        P hP₁ hYprocessed hDparent
        (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hDY) hYheight₁ hgat
    exact hineligible D hDtree hDparent hHlow
  rcases facts.fc.get_head_in_tree_with_layer_anchor_or_mem (M.gradeContract n.cache) S.E S.hc
      duty T Vv Uv (duty.s - 1) G hG X hX with hHA | hHtree
  · have hHA' : X = A := hHA.trans hGA
    by_cases hACeq : A = C
    · have hHC : X = C := hHA'.trans hACeq
      have hCT : C ∈ T := hinputs.candidate T hT
      obtain ⟨-, -, ⟨Y, hYprocessed, hCY, hYheight⟩, -⟩ :=
        facts.hd.voter_filtered_block_tree_cases S.E duty duty.s T hT hCT P hP
      exact stopContradiction C Y hHC.symm hCT hYprocessed hCY hYheight
    · obtain ⟨D, hDparent, hDC⟩ :=
        exists_child_towards C (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hAC) hACeq
      have hAD : Block.Preceq A D :=
        Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (preceq_of_parent? hDparent)
      have hDneA : D ≠ A := by
        intro hEq
        subst D
        have hdepth := depth_of_parent? hDparent
        omega
      have hDtree : D ∈ T := by
        by_cases hDCeq : D = C
        · subst D
          exact hinputs.candidate T hT
        · exact hinputs.path A hA T hT D hAD hDneA
            (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hDC) hDCeq
      have hparent := hDparent
      rw [← hHA'] at hparent
      exact hineligible D hDtree hparent hHlow
  · obtain ⟨-, -, ⟨Y, hYprocessed, hHY, hYheight⟩, -⟩ :=
      facts.hd.voter_filtered_block_tree_cases S.E duty duty.s T hT hHtree P hP
    exact stopContradiction X Y rfl hHtree hYprocessed hHY hYheight

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of the bundle, with `n` `w`'s slot-`s + 1` vote-duty read: if some run block `C`
    read through `Xb` descends from `n`'s anchor, is in the voter-processed tree of `n`'s core store
    and has height at least that store's `h_max - 1`, and `lo ≤ view_freeze s`, then every outcome
    of the vote head is the erasure of a run block `Hn` read through `Xb`, the store's cached chain
    state at the head is `Hn`'s named derivation, and its height is at least `h_max - 1`. -/
theorem voteDutyHead_band_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} (s : Slot) (hw : w ∈ Hs (M.view_freeze S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core)
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    (∃ C : NamedBlock V,
      (∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A ∧ Block.Preceq A C.erase) ∧
      Restated.RunBlockOn M S rho W Xb C ∧
      (∃ P : Finset (Block V), M.voter_processed_block_tree S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s ⇢ P ∧
        C.erase ∈ P) ∧
      n.st.core.h_max ≤ (M.derive_named S.E S.cfg C).h + 1) →
    lo ≤ M.view_freeze S.E s →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ Vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Vv →
    ∀ Uv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Uv →
    ∀ X : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T Vv Uv (n.st.core.s - 1) ⇢ X →
    ∃ Hn : NamedBlock V,
      Hn.erase = X ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        n.st.core.σ X = M.derive_named S.E S.cfg Hn ∧
        n.st.core.h_max - 1 ≤ (M.derive_named S.E S.cfg Hn).h := by
  intro n hdesc hgat T hT Vv hVv Uv hUv X hX
  let t := M.vote_time S.E (s + 1)
  let i := strictEventIndex rho t
  let duty := n.st.core
  have hmem := mem_stateBeforeTime_path₅₀ S rho hf.sorted W hf.onePath t
  have hnst₀ : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st t) c :=
    facts.nd.mkNode_st _ _ _
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st t) _ := facts.nd.mkNode_st _ _ _
  have hfacts := Restated.voteDuty_parentClosed_agrees_rootInjectiveOn facts S Hs Xb hf
    (hHsXb _ hw) (s + 1)
  have htreeT : T ⊆ duty.T := facts.hd.Sts_voter_filtered_block_tree_subset S.E duty duty.s T hT
  have hinjDuty : RootInjectiveBelow duty.T := by
    show RootInjectiveBelow n.st.core.T
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hfacts.2.2
  have hrootTree : RootInjectiveBelow T := Protocol.RootInjectiveBelow.mono hinjDuty htreeT
  have hdutyT : duty.T = (W i w).st.core.T := by
    show n.st.core.T = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hrootFiltered : M.get_fg_root (M.toHealing duty).toFG ∈
      M.get_filtered_block_tree (M.toHealing duty).toFG := by
    show M.get_fg_root (M.toHealing n.st.core).toFG ∈
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_eq_store_with_t_s]
    show M.get_fg_root (M.store_with_t_s (W i w).st.core t (S.E.slotOf t)).toHealing.toFG ∈
      M.get_filtered_block_tree (M.store_with_t_s (W i w).st.core t (S.E.slotOf t)).toHealing.toFG
    rw [facts.fc.get_fg_root_set_clock_slot, facts.fc.get_filtered_block_tree_set_clock_slot]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S
      rho t w _ hmem
  have hinvPath := nodeInvariant_path₅₀ facts S hf.onePath i w
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
    rw [hnst₀]
    exact invariant_store_with_cache₅₀ facts S.E S.cfg _ c
      (facts.hd.invariant_clock S.E S.cfg _ _ hinvPath.1)
  have hroot : M.get_fg_root (M.toHealing duty).toFG ∈ duty.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts n.st hinv.1.2
  obtain ⟨C, ⟨A, hA, hAC⟩, hCrun, ⟨P, hP, hCP⟩, hmax⟩ := hdesc
  have hA' := hA
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA'
  obtain ⟨G, hG, hGA⟩ := returns_map_elim₅₀ _ _ _ hA'
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing duty) (M.round_of S.hc duty.s)
    (M.readFrame n.cache (M.toHealing duty) (M.round_of S.hc duty.s)).g1
  have hGa : G.anchor = a :=
    facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc _ _ G hG a ha
  have hAfull : A ∈ M.get_filtered_block_tree (M.toHealing duty).toFG := by
    rw [← hGA, hGa]
    exact anchor_mem_filtered₅₀ facts S.E S.hc _ _ _ hrootFiltered a ha
  have hAT : A ∈ duty.T := by
    have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
      (M.toHealing duty) (M.round_of S.hc duty.s)
      (M.readFrame n.cache (M.toHealing duty) (M.round_of S.hc duty.s)).g1
      (by simp only [Record.Model.HS.T, facts.sto.toHealing_gs_T]; exact hroot) a ha
    simp only [Record.Model.HS.T, facts.sto.toHealing_gs_T] at h
    rw [← hGA, hGa]
    exact h
  have hHT : X ∈ duty.T :=
    facts.fc.ModelProperties_get_head_in_tree_with_layer_mem _ _ _ _ _ _ _ _ G
      (by rw [facts.sto.toHealing_s]; exact hG) (by rw [hGA]; exact hAT) htreeT X hX
  have hHpre : X ∈ (W i w).st.core.T := by
    rw [← hdutyT]
    exact hHT
  obtain ⟨Hn, hHnBody, hHnErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho t w
      _ hmem hHpre
  have hHnRun : Restated.RunBlockOn M S rho W Xb Hn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hw) hHnBody
  have hHnRead : Hn ∈ (M.ns_setClock S.E (W i w).st t).bodies := by
    rw [facts.hd.Sts_setClock_bodies]
    exact hHnBody
  have hSigma : duty.σ X = M.derive_named S.E S.cfg Hn := by
    rw [← hHnErase]
    show n.st.core.σ Hn.erase = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hfacts.2.1 Hn hHnRead
  refine ⟨Hn, hHnErase, hHnRun, hSigma, ?_⟩
  by_contra hnot
  have hHlow : (duty.σ X).h < duty.h_max - 1 := by
    rw [hSigma]
    exact Nat.lt_of_not_ge hnot
  have hT₁ : M.voter_filtered_block_tree S.E (M.ns_setClock S.E (W i w).st t).core
      (M.ns_setClock S.E (W i w).st t).core.s ⇢ T := by
    simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hT
  have hP₁ : M.voter_processed_block_tree S.E
      (M.toHealing (M.ns_setClock S.E (W i w).st t).core).toFG.toSG.toGoldfishStore
      (M.toHealing (M.ns_setClock S.E (W i w).st t).core).s ⇢ P := by
    simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hP
  have hPd : M.voter_processed_block_tree S.E (M.toHealing duty).toFG.toSG.toGoldfishStore
      duty.s ⇢ P := by
    rw [show duty.s = (M.toHealing duty).s from (facts.sto.toHealing_gs_s duty).symm]
    exact hP
  have hineligible : ∀ D : Block V, D ∈ T → D.parent? = some X →
      (duty.σ X).h < duty.h_max - 1 → False := by
    intro D hDT hDparent hlow
    obtain ⟨e, he⟩ := facts.fc.goldfish_eligible_nonempty S.E duty.σ duty.h_max duty.T duty.s Vv Uv
      (duty.s - 1) D
    obtain ⟨g, hg⟩ := facts.fc.goldfish_score_nonempty S.E duty.T Vv Uv (duty.s - 1) D
    have htrue : e = true := by
      rw [facts.fc.goldfish_eligible_iff _ _ _ _ _ _ _ _ D e he g hg, parent_eq_of_parent? hDparent]
      exact Or.inl hlow
    have hfalse : e = false :=
      facts.fc.goldfish_eligible_false_of_parent_head (M.gradeContract n.cache) S.E S.hc duty T Vv Uv
        (duty.s - 1) hrootTree hDT X hX hDparent e he
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  have stopContradiction : ∀ (Z Y : Block V),
      Z = X → Z ∈ T → Y ∈ P →
      Block.Preceq Z Y → duty.h_max - 1 ≤ (duty.σ Y).h → False := by
    intro Z Y hZH hZtree hYprocessed hZY hYheight
    subst Z
    have hHneY : X ≠ Y := by
      intro hEq
      rw [← hEq] at hYheight
      exact (Nat.not_lt_of_ge hYheight) hHlow
    obtain ⟨D, hDparent, hDY⟩ :=
      exists_child_towards Y (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hZY) hHneY
    have hYheight₁ : (M.ns_setClock S.E (W i w).st t).core.h_max - 1 ≤
        ((M.ns_setClock S.E (W i w).st t).core.σ Y).h := by
      simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hYheight
    have hDtree : D ∈ T :=
      Restated.namedFrozenCandidate_child_towards_witnessOn facts S Hs Xb hf hw T hT₁ hZtree
        P hP₁ hYprocessed hDparent
        (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hDY) hYheight₁ hgat
    exact hineligible D hDtree hDparent hHlow
  rcases facts.fc.get_head_in_tree_with_layer_anchor_or_mem (M.gradeContract n.cache) S.E S.hc
      duty T Vv Uv (duty.s - 1) G hG X hX with hHA | hHtree
  · have hHA' : X = A := hHA.trans hGA
    have hAcandidate : A ∈ T := by
      have hAfull₁ : A ∈ M.get_filtered_block_tree
          (M.toHealing (M.ns_setClock S.E (W i w).st t).core).toFG := by
        simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hAfull
      have hmax₁ : (M.ns_setClock S.E (W i w).st t).core.h_max ≤
          (M.derive_named S.E S.cfg C).h + 1 := by
        simpa only [duty, hnst, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hmax
      have h := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts S Hs Xb hf
        hHsXb hw P hP₁ hCP hCrun hAC hAfull₁ hmax₁ hgat
      rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E _ P hP₁
        T hT₁] at h
      exact h
    obtain ⟨-, -, ⟨Y, hYprocessed, hAY, hYheight⟩, -⟩ :=
      facts.hd.voter_filtered_block_tree_cases S.E duty duty.s T hT hAcandidate P hPd
    exact stopContradiction A Y hHA'.symm hAcandidate hYprocessed hAY hYheight
  · obtain ⟨-, -, ⟨Y, hYprocessed, hHY, hYheight⟩, -⟩ :=
      facts.hd.voter_filtered_block_tree_cases S.E duty duty.s T hT hHtree P hPd
    exact stopContradiction X Y rfl hHtree hYprocessed hHY hYheight

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the hypotheses of `voteDutyHead_band_coreOn`, every outcome of the vote head of `w`'s
    slot-`s + 1` vote-duty read is the erasure of a run block read through `Xb` of height at least
    `h_max - 1` of that read's core store. -/
theorem voteDutyHead_height_ge_frontier_sub_one_of_anchorDescendantOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} (s : Slot) (hw : w ∈ Hs (M.view_freeze S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core)
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    (∃ C : NamedBlock V,
      (∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A ∧ Block.Preceq A C.erase) ∧
      Restated.RunBlockOn M S rho W Xb C ∧
      (∃ P : Finset (Block V), M.voter_processed_block_tree S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s ⇢ P ∧
        C.erase ∈ P) ∧
      n.st.core.h_max ≤ (M.derive_named S.E S.cfg C).h + 1) →
    lo ≤ M.view_freeze S.E s →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ Vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Vv →
    ∀ Uv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ Uv →
    ∀ X : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T Vv Uv (n.st.core.s - 1) ⇢ X →
    ∃ Hn : NamedBlock V,
      Hn.erase = X ∧
      Restated.RunBlockOn M S rho W Xb Hn ∧
        n.st.core.h_max - 1 ≤ (M.derive_named S.E S.cfg Hn).h := by
  intro n hdesc hgat T hT Vv hVv Uv hUv X hX
  obtain ⟨Hn, hErase, hRun, -, hband⟩ :=
    Restated.voteDutyHead_band_coreOn facts S Hs Xb hf hHsXb s hw c hc hdesc hgat
      T hT Vv hVv Uv hUv X hX
  exact ⟨Hn, hErase, hRun, hband⟩

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

/-- On the path `W` of the bundle, if `v ∈ Xb` and `D` is a body of a node state of `v`'s round-`r`
    action read, then `D` is a run block read through `Xb`. -/
theorem seedFresh_actionBody_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {D : NamedBlock V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D := by
  rw [actionReadFrom_bodies₅₀ facts S _ r n hn] at hD
  exact Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hD

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

/-- On the path `W` of the bundle, for every node state `n` of `v`'s round-`r` action read with
    `v ∈ Xb`: if `n`'s FG source can be `some Q`, some body `D` of `n` erases to `Q`, is a run block
    read through `Xb`, and the cached chain state of `n`'s core store at `Q` is `D`'s named
    derivation. -/
theorem seedFresh_namedSource_witnessOn (facts : Record.Facts M)
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
      (M.toHealing n.st.core).toFG.σ Q = M.derive_named S.E S.cfg D := by
  intro n hnr hsource
  have hmem := mem_stateBeforeTime_path₅₀ S rho hf.sorted W hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hn : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r := ⟨_, hmem, hnr⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hn
  have hsource' : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Q := by
    show (do
      let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s)
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some Q
    rw [hround]
    exact hsource
  obtain ⟨D, hDbody, hDerase, hσ, -⟩ :=
    Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho v r n hn Q hsource'
  have hDrun := Restated.seedFresh_actionBody_runBlockOn facts S Hs Xb hf hv n hnr hDbody
  refine ⟨D, hDbody, hDerase, hDrun, ?_⟩
  rw [facts.sto.Sts_toHealing_σ]
  exact hσ

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if the fixed-height justification root at `H` holds at `w`'s
    store before `read0` and `C` is a run block read through `Xb` erasing to that store's justified
    block, then `C`'s entry root is that justified block's root. -/
theorem namedJustification_targetRoot_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) :
    ∀ {H : Height} {w : V} {read0 : Time}
      {C : NamedBlock V},
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read0
        (W (strictEventIndex rho read0)) →
      C.erase = (W (strictEventIndex rho read0) w).st.core.J →
      Restated.RunBlockOn M S rho W Xb C →
      (M.derive_named S.E S.cfg C).h = H - 1 →
      (M.derive_named S.E S.cfg C).T_h.root =
        (W (strictEventIndex rho read0) w).st.core.J.root := by
  intro H w read0 C hfix hCerase hCrun _hheight
  obtain ⟨D, _hDbody, hDrun, hjust⟩ := hfix.carrierExists
  obtain ⟨J, hJD, hJerase, hJself⟩ := facts.cs.namedJustification_entry_ancestor S.E S.cfg D
  have hJrun : Restated.RunBlockOn M S rho W Xb J :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hDrun hJD
  have hJCerase : J.erase = C.erase :=
    hJerase.trans (hjust.1.trans hCerase.symm)
  have hJCroot : J.root = C.root := by
    rw [← Proofs.NamedWire.erase_root J, ← Proofs.NamedWire.erase_root C, hJCerase]
  have hJC : J = C :=
    hf.rootCollisionFree.root_injective J C hJrun hCrun J C
      (Or.inl (Proofs.NamedAncestry.named_self J))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hJCroot
  have hCself : (M.derive_named S.E S.cfg C).T_h = C.erase := by
    rw [← hJC]
    exact hJself
  exact congrArg Block.root (hCself.trans hCerase)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if the largest `h_max` over `X` in `W stop` is less than
    `blocked + 2`, `reader ∈ X`, `n ≤ stop`, and `reader`'s tree in `W n` holds a block of cached
    height `blocked + 1`, then `reader`'s `h_max` in `W n` is `blocked + 1`. -/
theorem localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {stop : Nat} {blocked : Height}
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2)
    {n : Nat} {reader : V} {Q : Block V}
    (hreader : reader ∈ X) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (W n reader).st.core.T)
    (hQheight : ((W n reader).st.core.σ Q).h = blocked + 1) :
    (W n reader).st.core.h_max = blocked + 1 := by
  have hmem : W n ∈ Record.stateBeforeOf M S rho n := (_hf.onePath n).1
  obtain ⟨D, hDmem, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n reader
      _ hmem hQmem
  have hagree : (W n reader).st.core.σ Q = M.derive_named S.E S.cfg D := by
    rw [← hDerase]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho n reader
      _ hmem D hDmem
  have hQle : blocked + 1 ≤ (W n reader).st.core.h_max := by
    have hbound := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S
      rho n reader _ hmem D hDmem
    rw [← hagree, hQheight] at hbound
    exact hbound
  have hfrontierN : (X.sup fun u => (W n u).st.core.h_max) < blocked + 2 :=
    (Restated.honestHMaxBeforeIndex_monoOn facts S rho X hnstop (W n) hmem (W stop)
      (onePath_slice₅₀ W _hf.onePath hnstop)).trans_lt hfrontier
  have hfrontierNle : (X.sup fun u => (W n u).st.core.h_max) ≤ blocked + 1 := by
    apply Nat.lt_succ_iff.mp
    simpa only [Nat.add_assoc] using hfrontierN
  have hupper : (W n reader).st.core.h_max ≤ blocked + 1 :=
    (Restated.localHMax_le_honestHMaxBeforeIndexOn facts S rho X n hreader (W n) hmem).trans
      hfrontierNle
  exact Nat.le_antisymm hupper hQle

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if every body a member of `X` holds in `W stop` has finalized
    height at most `hF0` and `blocked` is a recovery height for `hF0`, then for every member `v` of
    `X` and every `n ≤ stop`, the finalized block of `v`'s store in `W n` is an ancestor of every
    run block read through `Xb` at height at least `blocked`. -/
theorem finalityFloorAt_of_recoveryOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked) :
    Restated.FinalityFloorAtOn M S rho W X Xb blocked stop Block.genesis := by
  have hsb := hf.slashableBound
  intro v hv n hn X' hX hXh _
  have hmemN : W n ∈ Record.stateBeforeOf M S rho n := (hf.onePath n).1
  obtain ⟨D, hDbodies, hDF, -⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho n v (W n) hmemN
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hv) hDbodies
  have hDstop : D ∈ (W stop v).st.bodies :=
    Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hn (W n) hmemN
      (W stop) (onePath_slice₅₀ W hf.onePath hn) hDbodies
  have hcapD : (M.derive_named S.E S.cfg D).h_F ≤ hF0 :=
    hcap v hv D hDstop
  have hcrossed : (M.derive_named S.E S.cfg D).h_F <
      (M.derive_named S.E S.cfg X').h :=
    (hcapD.trans_lt ((Nat.lt_succ_self hF0).trans
      (NjGap.lt_of_recoveryHeight hrec))).trans_le hXh
  have hpre : Block.Preceq (M.derive_named S.E S.cfg D).F X'.erase :=
    Restated.finalized_preceq_of_height_ltOn facts S rho W Xb X' D hsb hf.rootCollisionFree hX hDrun
      hcrossed
  rw [hDF] at hpre
  exact hpre

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of `finalityFloorAt_of_recoveryOn`, if the largest `h_max` over `X` in
    `W stop` is less than `blocked + 2`, the height regime frame over `X` along `W` holds at
    `blocked` up to `stop`, relative to genesis and round `0`. -/
theorem heightRegimeFrame_of_recoveryOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2) :
    Restated.HeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t)) X Xb blocked stop
      Block.genesis 0 := by
  have hfloor := Restated.finalityFloorAt_of_recoveryOn facts S Hs Xb X hf hXXb hcap hrec
  refine ⟨hfloor, ?_, ?_, ?_, ?_⟩
  · change (M.cs_initial : M.CS).h ≤ blocked
    rw [facts.csAdded.chainState_initial_h]
    exact Nat.succ_le_of_lt ((Nat.zero_le (hF0 + 1)).trans_lt
      (NjGap.lt_of_recoveryHeight hrec))
  · intro v hv n hn Q hQ hQh _
    have hmem : W n ∈ Record.stateBeforeOf M S rho n := (hf.onePath n).1
    have hmax : (W n v).st.core.h_max = blocked + 1 :=
      Restated.localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontierOn facts
        S Hs Xb X hf hfrontier hv hn hQ hQh
    have hcapN : Restated.HonestPrefixFinalityCapOn M S rho W X n hF0 :=
      Restated.honestPrefixFinalityCap_of_leOn facts S Hs Xb X hf hn hcap
    have huniverse : Restated.HonestPrefixNJUniverseOn M S rho W X n blocked :=
      Restated.honestPrefixNJUniverse_of_finalityCapOn facts S Hs Xb X hf hcapN hrec
    have hne : (W n v).st.core.h_j ≠ blocked := by
      obtain ⟨D, hD, hJ, hJh⟩ :=
        Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBefore facts S rho n v
          (W n) hmem
      have hneD := (huniverse v hv D hD).2
      intro heq
      apply hneD
      exact hJh.trans heq
    have hgate : ¬ (W n v).st.core.h_max = (W n v).st.core.h_j + 1 := by
      intro hgate
      apply hne
      exact (Nat.add_right_cancel (hmax.symm.trans hgate)).symm
    show M.get_fg_root (M.toHealing (W n v).st.core).toFG ⪯ Q
    rw [facts.fc.get_fg_root_toHealing_of_ne _ hgate]
    obtain ⟨D, hD, hErase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n v
        (W n) hmem hQ
    have hDview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho n v
      (W n) hmem D hD
    have hDheight : (M.derive_named S.E S.cfg D).h = blocked + 1 := by
      rw [← hDview, hErase]
      exact hQh
    have hfloorD := hfloor v hv n hn D
      (Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hv) hD)
      (hDheight ▸ Nat.le_succ blocked)
      (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis D.erase))
    rw [hErase] at hfloorD
    exact hfloorD
  · intros
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)
  · intros
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `a`'s signer, a member of `X`, emits `a` at `ta` with a height
    pair naming `h`, then `ta` is `S.a a.round`, and for every node state `n` of the signer's action
    read of that round, `a` is the attestation computed from `n`, every outcome of `n`'s FG source
    is the erasure of a body `D` of `n` whose cached and named heights are `h`, and `a`'s height
    pair targets `D`'s entry root at `h` or is the timeout at `h`. -/
theorem honestEmittedHeightRow_exactFGSelectorWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (_haHon : a.val_index ∈ X)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index
      (NamedObject.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round,
    ta = (Restated.Vocabulary.Execution.Setup.a M S a.round) ∧
      (∀ Y, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node a.val_index) n.st
          n.record ⇢ Y → a = Y.2.2) ∧
      ∀ o : Option (Block V), Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
      ∃ D : NamedBlock V, ∃ J : Block V,
        o = some D.erase ∧
        D ∈ n.st.bodies ∧
        (n.st.core.σ D.erase).h = h ∧
        (M.derive_named S.E S.cfg D).h = h ∧
        J = (M.derive_named S.E S.cfg D).T_h ∧
        (a.height_pair.erase = HeightPair.target h J.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  intro n hnr
  have hshape := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit
  have htime : ta = (Restated.Vocabulary.Execution.Setup.a M S a.round) := hshape.2
  have haEq : ∀ Y, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node a.val_index)
      n.st n.record ⇢ Y → a = Y.2.2 :=
    ((Restated.action_run_emissionOn facts S rho Hs Xb hf a.val_index a.round a).mp
      (by rw [← htime]; exact hemit)).2.2 n hnr
  have hmem := mem_stateBeforeTime_path₅₀ S rho hf.sorted W hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S a.round)
  have hn : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho a.val_index a.round :=
    ⟨_, hmem, hnr⟩
  refine ⟨htime, haEq, ?_⟩
  intro o ho
  obtain ⟨Y, hY⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node a.val_index) n.st n.record
  have haY := haEq Y hY
  rw [haY] at hh
  generalize hp : Y.2.2.height_pair = q at hh
  cases q with
  | empty =>
      rw [namedHeightPair_erase_empty] at hh
      cases hh
  | vote h' entry timeout =>
      have hh' : h' = h := by
        rw [namedHeightPair_erase_vote_height?] at hh
        exact Option.some.inj hh
      subst h'
      obtain ⟨Cfg, rfl, hCfgHeight, hCfgRoot⟩ :=
        Restated.Vocabulary.Proofs.NamedActionSources.action_source facts S rho a.val_index a.round
          n hn h entry timeout Y hY hp o ho
      obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
        Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho a.val_index a.round
          n hn Cfg ho
      let J := (M.derive_named S.E S.cfg D).T_h
      have hheight : (n.st.core.σ D.erase).h = h := by
        rw [hDerase]
        exact hCfgHeight
      have hnamedHeight : (M.derive_named S.E S.cfg D).h = h := by
        rw [← hDderive]
        exact hCfgHeight
      have hJroot : J.root = entry := by
        show (M.derive_named S.E S.cfg D).T_h.root = entry
        rw [← hDderive]
        exact hCfgRoot
      refine ⟨D, J, by rw [hDerase], hD, hheight, hnamedHeight, rfl, ?_⟩
      cases timeout with
      | false =>
          left
          rw [haY, hp, namedHeightPair_erase_vote_false, hJroot]
      | true =>
          right
          rw [haY, hp, namedHeightPair_erase_vote_true]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if every body a member of `X` holds in `W stop` has finalized
    height at most `hF0`, `blocked` is a recovery height for `hF0`, and `v ∈ X`, then for every
    `n ≤ stop`, `v`'s record in `W n` has no lock at `blocked`. -/
theorem stateBefore_lock_none_recoveryHeight_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ X) :
    ∀ n : Nat, n ≤ stop → (W n v).record.legacy.lock blocked = none := by
  intro n
  induction n with
  | zero =>
      intro _
      have h0 : W 0 = fun v => M.initial S v := (hf.onePath 0).1
      rw [h0]
      exact facts.nd.initial_record_lock S v blocked
  | succ n ih =>
      intro hnSuccStop
      have hnStop : n ≤ stop := (Nat.le_succ n).trans hnSuccStop
      have ihN := ih hnStop
      rcases path_step_cases₅₀ hf.onePath n with ⟨-, hsame⟩ | ⟨e, hevent, hstepE⟩
      · rw [hsame]
        exact ihN
      · cases e with
        | wake u t =>
            have hupd : W (n + 1) = Function.update (W n) u (M.wake (W n u)) := hstepE
            rw [hupd]
            by_cases huv : v = u
            · subst huv
              rw [Function.update_self, (facts.nd.wake_st_record _).2]
              exact ihN
            · rw [Function.update_of_ne huv]
              exact ihN
        | deliver u o t =>
            rcases hstepE with ⟨n', hn', hupd⟩ | ⟨-, hsame⟩
            · rw [hupd]
              by_cases huv : v = u
              · subst huv
                rw [Function.update_self, facts.nd.process_record_eq S _ o n' hn']
                exact ihN
              · rw [Function.update_of_ne huv]
                exact ihN
            · rw [hsame]
              exact ihN
        | tick u t =>
            rcases hstepE with ⟨out, hout, hupd⟩ | ⟨-, hsame⟩
            · by_cases huv : v = u
              · subst huv
                have hWv : W (n + 1) v = out.1 := by
                  rw [hupd, Function.update_self]
                cases hpost : (W (n + 1) v).record.legacy.lock blocked with
                | none => rfl
                | some T =>
                    have hpostTick : out.1.record.legacy.lock blocked = some T := by
                      rw [← hWv]
                      exact hpost
                    obtain ⟨a, hemitted, hpair⟩ :=
                      facts.nd.on_tick_emit_lock_introduced S v (W n v) t ihN out hout hpostTick
                    have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v
                        (NamedObject.attest a) t :=
                      ⟨n, hevent, out, hout, hWv, hemitted⟩
                    have hshape := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W
                      hf.onePath hemit
                    have htime : t = Restated.Vocabulary.Execution.Setup.a M S a.round := hshape.2
                    have haEq := ((Restated.action_run_emissionOn facts S rho Hs Xb hf v
                      a.round a).mp (by rw [← htime]; exact hemit)).2.2
                    have hsn : strictEventIndex rho
                        (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ n := by
                      rw [← htime]
                      exact strict_le_tick₅₀ hf.sorted hevent
                    have hcapN : Restated.HonestPrefixFinalityCapOn M S rho W X
                        (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
                        hF0 :=
                      Restated.honestPrefixFinalityCap_of_leOn facts S Hs Xb X hf
                        (hsn.trans hnStop) hcap
                    have huniverse : Restated.HonestPrefixNJUniverseOn M S rho W X
                        (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
                        blocked :=
                      Restated.honestPrefixNJUniverse_of_finalityCapOn facts S Hs Xb X hf hcapN hrec
                    have hne := Restated.actionHead_h_j_ne_of_honestPrefixNJUniverseOn facts
                      S Hs Xb X hf huniverse hv rfl
                    obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty₅₀ facts S
                      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) v)
                      a.round
                    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nr.cache) S.E
                      S.hc (S.node v) nr.st nr.record
                    obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract nr.cache)
                      S.E S.hc (S.node v) (M.toHealing nr.st.core) nr.record
                    obtain ⟨Hd, hHd⟩ := actionHeadWith_nonempty₅₀ facts (M.gradeContract nr.cache)
                      S.E S.hc (M.toHealing nr.st.core)
                    rw [haEq nr hnr D hD, facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA,
                      Restated.Vocabulary.Proofs.HealingSurface.round_action_finality_pair_eq facts
                        _ _ _ _ _ _ A hA Hd hHd] at hpair
                    have hheadHeight := facts.vc.finality_pair_height hpair
                    simp only [Record.Model.HS.σ, facts.sto.Sts_toHealing_σ] at hheadHeight
                    exact absurd hheadHeight (hne nr hnr Hd hHd)
              · rw [hupd, Function.update_of_ne huv]
                exact ihN
            · rw [hsame]
              exact ihN

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

open scoped DC

omit [DecidableEq V] [Fintype V] in
private theorem drop_take_succ₅₀b {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

omit [DecidableEq V] [Fintype V] in
private theorem drop_take_succ_none₅₀b {rho : Record.Run V} {i : Nat}
    (hi : rho.events[i]? = none) : (rho.events.drop i).take (i + 1 - i) = [] := by
  rw [List.getElem?_eq_none_iff] at hi
  rw [List.drop_eq_nil_of_le hi]
  exact List.take_nil

private theorem mem_foldlM_singleton₅₀b (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

/-- A world reached from `w` by event `n` of `rho` is `w` when there is no such event, and otherwise
    one of the worlds that event leads to from `w`. -/
private theorem step_cases₅₀b (S : Setup V) (rho : Record.Run V) (n : Nat) (w w₂ : V → M.N)
    (h : w₂ ∈ ((rho.events.drop n).take (n + 1 - n)).foldlM (Record.worldStepOf M S) w) :
    (rho.events[n]? = none ∧ w₂ = w) ∨
      ∃ e, rho.events[n]? = some e ∧ w₂ ∈ Record.worldStepOf M S w e := by
  rcases hev : rho.events[n]? with _ | e
  · rw [drop_take_succ_none₅₀b hev] at h
    exact Or.inl ⟨rfl, Set.mem_singleton_iff.mp h⟩
  · rw [drop_take_succ₅₀b hev, mem_foldlM_singleton₅₀b] at h
    exact Or.inr ⟨e, rfl, h⟩

/-- The world `W (strictEventIndex rho t)` of the bundle's path is a world strictly before `t`. -/
private theorem path_mem_stateBeforeTime₅₀b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V}
    {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  have h := Restated.stateBeforeTime_eq_takeOn facts S Hs Xb hf t
  have hmem := (hf.onePath (strictEventIndex rho t)).1
  unfold strictEventIndex at hmem
  show W _ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t
  rw [h]
  exact hmem

/-- Every node state of `v`'s round-`r` action read from the bundle's path is one of `v`'s round-`r`
    action stores. -/
private theorem actionRead_mem₅₀b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r :=
  fun _ hn => ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)),
    path_mem_stateBeforeTime₅₀b facts S hf _, hn⟩

/-- Every node state the round-`r` action read from `before` can give keeps `before`'s signing
    record. -/
private theorem actionReadFrom_record₅₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.record = before.record := by
  rintro _ ⟨c, -, st, -, rfl⟩
  exact facts.nd.mkNode_record _ _ _

/-- Every node state the round-`r` action read from `before` can give holds `before`'s bodies. -/
private theorem actionReadFrom_bodies₅₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The round-`r` action read from `before` can give some node state. -/
private theorem actionReadFrom_nonempty₅₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

open scoped DC in
private theorem returns_bind_iff₅₀b {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
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

open scoped DC in
private theorem returns_map_elim₅₀b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
private theorem returns_map_intro₅₀b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨.ok a, h, rfl⟩

/-- The action FG source read at `n` can return some value. -/
private theorem actionFGSource_nonempty₅₀b (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff₅₀b _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- If an outcome of `v`'s tick at `t` from `n` sends the attestation `a`, then `t` is the action
    instant of `a`'s round and every outcome of the attestation duty on every node state of that
    round's action read of `n` is `a`. -/
private theorem tick_attest₅₀b (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Time)
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

/-- Every outcome of the early confirmation votes of `st` at slot `s` is among its late confirmation
    votes. -/
private theorem confEarly_subset_late₅₀b (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₅₀b _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- In a parent-closed named store, every named ancestor of a held body is held. -/
private theorem namedAncestor_mem₅₀b {st : M.NS}
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

/-- Under the hypotheses of `stateBefore_lock_none_recoveryHeight_namedOn`, for every `n ≤ stop`,
    `v`'s record in the world `W n` has no target at `blocked`. -/
theorem stateBefore_target_none_recoveryHeight_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ X) :
    ∀ n : Nat, n ≤ stop → (W n v).record.legacy.target blocked = none := by
  intro n
  induction n with
  | zero =>
      intro _
      have h0 : W 0 = fun v' => M.initial S v' := (hf.onePath 0).1
      rw [h0]
      exact facts.nd.initial_record_target S v blocked
  | succ n ih =>
      intro hnSuccStop
      have hnStop : n ≤ stop := (Nat.le_succ n).trans hnSuccStop
      have ihN := ih hnStop
      rcases step_cases₅₀b S rho n (W n) (W (n + 1)) (hf.onePath n).2 with
        ⟨-, heq⟩ | ⟨e, hev, hstep⟩
      · rw [heq]
        exact ihN
      cases e with
      | wake u t =>
          have hupd : W (n + 1) = Function.update (W n) u (M.wake (W n u)) := hstep
          rw [hupd]
          by_cases huv : v = u
          · subst huv
            rw [Function.update_self, (facts.nd.wake_st_record _).2]
            exact ihN
          · rw [Function.update_of_ne huv]
            exact ihN
      | deliver u o t =>
          rcases hstep with ⟨n', hn', heq⟩ | ⟨-, heq⟩
          · rw [heq]
            by_cases huv : v = u
            · subst huv
              rw [Function.update_self, facts.nd.process_record_eq S _ o n' hn']
              exact ihN
            · rw [Function.update_of_ne huv]
              exact ihN
          · rw [heq]
            exact ihN
      | tick u t =>
          rcases hstep with ⟨out, hout, heq⟩ | ⟨-, heq⟩
          · rw [heq]
            by_cases huv : v = u
            · subst huv
              rw [Function.update_self]
              cases hpost : out.1.record.legacy.target blocked with
              | none => rfl
              | some T =>
                  exfalso
                  obtain ⟨a, haOut, hpair⟩ :=
                    facts.nd.on_tick_emit_target_introduced S v (W n v) t ihN out hout hpost
                  have _hr_s1 := facts.ndRun.stateBeforeOf_reachedNode S rho n (W n) (hf.onePath n).1 v
                  have _hv_s2 := facts.ndRun.stateBeforeOf_runs_as S rho n (W n) (hf.onePath n).1 v
                  obtain ⟨htime, hrowEq⟩ := tick_attest₅₀b facts S v (W n v) t out hout a haOut
                  have hev' : rho.events[n]? =
                      some (.tick v (Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
                    rw [hev, htime]
                  have hstate2 := Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hev'
                  have hrecEq : (W n v).record = (W (strictEventIndex rho
                      (Restated.Vocabulary.Execution.Setup.a M S a.round)) v).record := by
                    rcases hstate2 with h | h
                    · rw [h]
                    · rw [h, (facts.nd.wake_st_record _).2]
                  have hreadEq : Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
                        (W n v) a.round =
                      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
                        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
                          v) a.round := by
                    rcases hstate2 with h | h
                    · rw [h]
                    · rw [h, actionReadFrom_wake₅₀ facts]
                  have hsn : strictEventIndex rho
                      (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ n :=
                    strict_le_tick₅₀ hf.sorted hev'
                  rw [hreadEq] at hrowEq
                  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty₅₀b facts S
                    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) v)
                    a.round
                  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nr.cache) S.E
                    S.hc (S.node v) nr.st nr.record
                  have hDa : D.2.2 = a := hrowEq nr hnr D hD
                  have hpairE : a.height_pair.erase = HeightPair.target blocked T := by
                    rw [← namedAttestation_erase_height_pair]
                    exact hpair
                  generalize hq : a.height_pair = q at hpairE
                  cases q with
                  | empty =>
                      rw [namedHeightPair_erase_empty] at hpairE
                      cases hpairE
                  | vote h' entry timeout =>
                      have hh' : h' = blocked := by
                        have hh := congrArg HeightPair.height? hpairE
                        rw [namedHeightPair_erase_vote_height?] at hh
                        exact Option.some.inj hh
                      subst hh'
                      have hp' : D.2.2.height_pair = NamedHeightPair.vote h' entry timeout := by
                        rw [hDa, hq]
                      obtain ⟨o, ho⟩ := actionFGSource_nonempty₅₀b facts S nr
                      obtain ⟨Cfg, rfl, hCfgHeight, -⟩ :=
                        Restated.Vocabulary.Proofs.NamedActionSources.action_source facts S rho v
                          a.round nr (actionRead_mem₅₀b facts S hf v a.round nr hnr) h' entry
                          timeout D hD hp' o ho
                      have hlock : (W n v).record.legacy.lock h' = none :=
                        Restated.stateBefore_lock_none_recoveryHeight_namedOn facts
                          S Hs Xb X hf hcap hrec hv n hnStop
                      have hvote : D.2.2.height_pair =
                          NamedHeightPair.vote h' (nr.st.core.σ Cfg).T_h.root true := by
                        cases ht : (W n v).record.legacy.timeout h' with
                        | false =>
                            have hcapN : Restated.HonestPrefixFinalityCapOn M S rho W X
                                (strictEventIndex rho
                                  (Restated.Vocabulary.Execution.Setup.a M S a.round)) hF0 :=
                              Restated.honestPrefixFinalityCap_of_leOn facts S Hs Xb X hf
                                (hsn.trans hnStop) hcap
                            have huniverse : Restated.HonestPrefixNJUniverseOn M S rho W X
                                (strictEventIndex rho
                                  (Restated.Vocabulary.Execution.Setup.a M S a.round)) h' :=
                              Restated.honestPrefixNJUniverse_of_finalityCapOn facts S Hs Xb X hf
                                hcapN hrec
                            have hfresh : Restated.Vocabulary.Proofs.HealingSurface.RecordFreshAt M
                                nr.record.legacy h' := by
                              rw [actionReadFrom_record₅₀b facts S _ _ nr hnr, ← hrecEq]
                              exact ⟨ihN, ht, hlock⟩
                            exact Restated.actionAttestationAt_height_pair_timeout_of_honestPrefixNJUniverseOn
                              facts S Hs Xb X hf huniverse hv rfl nr hnr ho hCfgHeight hfresh D hD
                        | true =>
                            exact Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_height_pair_timeout_of_recorded
                              facts S rho _ (path_mem_stateBeforeTime₅₀b facts S hf _) nr hnr ho
                              hCfgHeight (by rw [← hrecEq]; exact ht) D hD
                      rw [hp'] at hvote
                      cases hvote
                      rw [namedHeightPair_erase_vote_true] at hpairE
                      cases hpairE
            · rw [Function.update_of_ne huv]
              exact ihN
          · rw [heq]
            exact ihN

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of `stateBefore_lock_none_recoveryHeight_namedOn`, for every node state
    `nr` of `v`'s round-`r` action read, if `nr`'s action FG source can return `some Q` and `Q` has
    cached height `blocked` in `nr`'s core store, then every outcome of the attestation duty on `nr`
    carries the timeout vote at `blocked` for `Q`'s entry root. -/
theorem actionAttestationAt_height_pair_timeout_recoveryHeight_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ X) {r : Round}
    (haction : strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r)) ≤ stop)
    (nr : M.N) (hnr : nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {Q : Block V}
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ some Q)
    (hheight : (nr.st.core.σ Q).h = blocked) :
    ∀ D, M.duties_attest_with (M.gradeContract nr.cache) S.E S.hc (S.node v) nr.st nr.record ⇢ D →
      D.2.2.height_pair = NamedHeightPair.vote blocked (nr.st.core.σ Q).T_h.root true := by
  intro D hD
  let actionPrefix := strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r))
  have htarget : (W actionPrefix v).record.legacy.target blocked = none :=
    Restated.stateBefore_target_none_recoveryHeight_namedOn facts
      S Hs Xb X hf hcap hrec hv actionPrefix haction
  have hlock : (W actionPrefix v).record.legacy.lock blocked = none :=
    Restated.stateBefore_lock_none_recoveryHeight_namedOn facts
      S Hs Xb X hf hcap hrec hv actionPrefix haction
  cases ht : (W actionPrefix v).record.legacy.timeout blocked with
  | false =>
      have hcapAction : Restated.HonestPrefixFinalityCapOn M S rho W X actionPrefix hF0 :=
        Restated.honestPrefixFinalityCap_of_leOn facts S Hs Xb X hf haction hcap
      have huniverse : Restated.HonestPrefixNJUniverseOn M S rho W X actionPrefix blocked :=
        Restated.honestPrefixNJUniverse_of_finalityCapOn facts S Hs Xb X hf hcapAction hrec
      have hfresh : Restated.Vocabulary.Proofs.HealingSurface.RecordFreshAt M nr.record.legacy
          blocked := by
        rw [actionReadFrom_record₅₀b facts S _ _ nr hnr]
        exact ⟨htarget, ht, hlock⟩
      exact Restated.actionAttestationAt_height_pair_timeout_of_honestPrefixNJUniverseOn facts
        S Hs Xb X hf huniverse hv rfl nr hnr hsource hheight hfresh D hD
  | true =>
      exact Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_height_pair_timeout_of_recorded
        facts S rho _ (path_mem_stateBeforeTime₅₀b facts S hf _) nr hnr hsource hheight ht D hD

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under a finality cap over `X` up to `stop` and a recovery height `blocked`, if a member of `X`
    emits `a` along `W`, `a`'s round's action prefix is within `stop`, and `a`'s height pair targets
    `root` at `h`, then `h ≠ blocked`. -/
theorem honestEmittedTarget_height_ne_recovery_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {stop : Nat} {blocked hF0 h : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {a : NamedAttestation V} {ta : Time} {root : BlockId}
    (ha : a.val_index ∈ X)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta)
    (haction : strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ≤ stop)
    (hpair : a.height_pair.erase = HeightPair.target h root) :
    h ≠ blocked := by
  have _hr_0 : M.reachedNode (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))).1 a.val_index
  intro heq
  subst h
  obtain ⟨i, hi, out, hout, -, haOut⟩ := hemit
  have _hr_s3 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 a.val_index
  have _hv_s4 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 a.val_index
  obtain ⟨htime, hrowEq⟩ := tick_attest₅₀b facts S a.val_index (W i a.val_index) ta out hout a haOut
  have hi' : rho.events[i]? =
      some (.tick a.val_index (Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [hi, htime]
  have hreadEq : Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W i a.val_index) a.round =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
        a.round := by
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hi' with h | h
    · rw [h]
    · rw [h, actionReadFrom_wake₅₀ facts]
  rw [hreadEq] at hrowEq
  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty₅₀b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (S.node a.val_index) nr.st nr.record
  have hDa : D.2.2 = a := hrowEq nr hnr D hD
  generalize hq : a.height_pair = q at hpair
  cases q with
  | empty =>
      rw [namedHeightPair_erase_empty] at hpair
      cases hpair
  | vote h' entry timeout =>
      have hh' : h' = blocked := by
        have hh := congrArg HeightPair.height? hpair
        rw [namedHeightPair_erase_vote_height?] at hh
        exact Option.some.inj hh
      subst hh'
      have hp' : D.2.2.height_pair = NamedHeightPair.vote h' entry timeout := by
        rw [hDa, hq]
      obtain ⟨o, ho⟩ := actionFGSource_nonempty₅₀b facts S nr
      obtain ⟨Cfg, rfl, hCfgHeight, -⟩ :=
        Restated.Vocabulary.Proofs.NamedActionSources.action_source facts S rho a.val_index
          a.round nr (actionRead_mem₅₀b facts S hf a.val_index a.round nr hnr) h' entry timeout
          D hD hp' o ho
      have hvote := Restated.actionAttestationAt_height_pair_timeout_recoveryHeight_namedOn facts
        S Hs Xb X hf hcap hrec ha haction nr hnr ho hCfgHeight D hD
      rw [hp'] at hvote
      cases hvote
      rw [namedHeightPair_erase_vote_true] at hpair
      cases hpair

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read,
    and `D` is a body of `n`'s store, then `D` is a run block read through `Xb`. -/
theorem actionBody_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D := by
  rw [actionReadFrom_bodies₅₀b facts S _ _ n hn] at hD
  exact Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hD

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read,
    and `D` is a body of `n`'s store, then some body `K` of `n`'s store erases to `D`'s entry, has
    `D`'s named height, is an ancestor of `D`, and is a run block read through `Xb`. -/
theorem action_named_checkpointOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    ∃ K : NamedBlock V,
      K ∈ n.st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = (M.derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧
      Restated.RunBlockOn M S rho W Xb K := by
  obtain ⟨K, hKD, hKentry, hKh⟩ :=
    facts.cs.entry_ancestor_same_height S.E S.cfg D
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ v _
      (hf.onePath _).1).1.1.1.2.2.1
  have hK : K ∈ n.st.bodies := by
    rw [actionReadFrom_bodies₅₀b facts S _ _ n hn] at hD ⊢
    exact namedAncestor_mem₅₀b hpc hD hKD
  exact ⟨K, hK, hKentry, hKh, hKD, Restated.actionBody_runBlockOn facts S Hs Xb hf hv hn hK⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The conclusion of `honestHeightRow_confirmationWitnessOn` with three more conjuncts: `o`'s
    block, its stored chain state, and `K`'s entry. -/
private theorem heightRow_core₅₀b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ Xb)
    (hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index (Object.attest a) ta))
    (hh : a.height_pair.erase.height? = some h) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round,
    ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ o →
    ∃ D K : NamedBlock V,
      o = some D.erase ∧
      nr.st.core.σ D.erase = M.derive_named S.E S.cfg D ∧
      (M.derive_named S.E S.cfg K).T_h = K.erase ∧
      Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
        some (M.derive_named S.E S.cfg K).T_h ∧
      D ∈ nr.st.bodies ∧
      o = some D.erase ∧
      (M.derive_named S.E S.cfg D).h = h ∧
      K ∈ nr.st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h) := by
  have _hr_0 : M.reachedNode (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))) (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))).1 a.val_index
  intro nr hnr o ho
  obtain ⟨i, hi, out, hout, -, haOut⟩ := hemit
  have _hr_s5 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 a.val_index
  have _hv_s6 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 a.val_index
  obtain ⟨htime, hrowEq⟩ := tick_attest₅₀b facts S a.val_index (W i a.val_index) ta out hout a haOut
  have hi' : rho.events[i]? =
      some (.tick a.val_index (Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [hi, htime]
  have hreadEq : Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W i a.val_index) a.round =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
        a.round := by
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hi' with h | h
    · rw [h]
    · rw [h, actionReadFrom_wake₅₀ facts]
  rw [hreadEq] at hrowEq
  obtain ⟨Datt, hDatt⟩ := facts.dt.attest_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (S.node a.val_index) nr.st nr.record
  have hDa : Datt.2.2 = a := hrowEq nr hnr Datt hDatt
  rcases hq : a.height_pair with _ | ⟨h', entry, timeout⟩
  · rw [hq, namedHeightPair_erase_empty] at hh
    cases hh
  · rw [hq, namedHeightPair_erase_vote_height?] at hh
    have hh' : h' = h := Option.some.inj hh
    subst hh'
    have hp' : Datt.2.2.height_pair = NamedHeightPair.vote h' entry timeout := by
      rw [hDa, hq]
    obtain ⟨Cfg, rfl, hCfgHeight, hCfgRoot⟩ :=
      Restated.Vocabulary.Proofs.NamedActionSources.action_source facts S rho a.val_index
        a.round nr (actionRead_mem₅₀b facts S hf a.val_index a.round nr hnr) h' entry timeout
        Datt hDatt hp' o ho
    obtain ⟨D, hD, hDerase, hDderive, hfg⟩ :=
      Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho a.val_index
        a.round nr (actionRead_mem₅₀b facts S hf a.val_index a.round nr hnr) Cfg ho
    subst hDerase
    have hnamedHeight : (M.derive_named S.E S.cfg D).h = h' := by
      rw [← hDderive]
      exact hCfgHeight
    have hJroot : (M.derive_named S.E S.cfg D).T_h.root = entry := by
      rw [← hDderive]
      exact hCfgRoot
    obtain ⟨K, hK, hKentry, hKheight, hKpre, -⟩ :=
      Restated.action_named_checkpointOn facts S Hs Xb hf haHon hnr hD
    have hKheight' : (M.derive_named S.E S.cfg K).h = h' :=
      hKheight.trans hnamedHeight
    have hKtarget : (M.derive_named S.E S.cfg K).T_h = K.erase :=
      (facts.cs.entry_eq_on_plateau S.E S.cfg hKpre hKheight).trans hKentry.symm
    have hfgK : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
        some (M.derive_named S.E S.cfg K).T_h := by
      rw [hKtarget, hKentry]
      exact hfg
    have hJK : K.erase.root = entry := by
      rw [hKentry, hJroot]
    refine ⟨D, K, rfl, hDderive, hKtarget, hfgK, hD, rfl, hnamedHeight, hK, hKentry, hKheight',
      Proofs.NamedWire.erase_preceq hKpre, ?_⟩
    cases timeout with
    | false =>
        left
        rw [namedHeightPair_erase_vote_false, hJK]
    | true =>
        right
        rw [namedHeightPair_erase_vote_true]

/-- On the path `W` of the bundle, if `a`'s signer, a member of `Xb`, emits `a` at `ta` with a
    height pair naming `h`, then for every node state `nr` of the signer's round action read and
    every outcome `o` of `nr`'s action FG source, there are bodies `D` and `K` of `nr` with
    `o = some D.erase`, both of named height `h`, `K` erasing to `D`'s entry and `K ⪯ D`, the FG
    confirmation witness of `nr` can return `K`'s entry, and `a`'s height pair targets `K`'s root at
    `h` or is the timeout at `h`. -/
theorem honestHeightRow_confirmationWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ Xb)
    (hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index (Object.attest a) ta))
    (hh : a.height_pair.erase.height? = some h) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round,
    ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ o →
    ∃ D K : NamedBlock V,
      Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
        some (M.derive_named S.E S.cfg K).T_h ∧
      D ∈ nr.st.bodies ∧
      o = some D.erase ∧
      (M.derive_named S.E S.cfg D).h = h ∧
      K ∈ nr.st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h) := by
  intro nr hnr o ho
  obtain ⟨D, K, -, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    heightRow_core₅₀b facts S Hs Xb hf haHon hemit hh nr hnr o ho
  exact ⟨D, K, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `v`'s store in the world strictly before `time ≤ horizon` has
    `h_max > 1`, some signer in the set for `time` emitted an attestation `a` before `time` at
    height `h_max - 1`, and every outcome of the FG confirmation witness of every node state of its
    round action read is the entry of a body `K`, a run block read through `Xb` of named height
    `h_max - 1`. -/
theorem frontier_confirmationWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {v : V} {time : Time} (hthor : time ≤ rho.horizon)
    (hlarge : 1 < (W (strictEventIndex rho time) v).st.h_max) :
    ∃ (a : NamedAttestation V) (ta : Time),
      a.val_index ∈ Hs time ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta ∧
      ta < time ∧
      a.height_pair.erase.height? =
        some ((W (strictEventIndex rho time) v).st.core.h_max - 1) ∧
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
          a.round,
      ∀ o, Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢ o →
      ∃ D K : NamedBlock V,
        o = some (M.derive_named S.E S.cfg K).T_h ∧
        D ∈ nr.st.bodies ∧
        K ∈ nr.st.bodies ∧
        K.erase = (M.derive_named S.E S.cfg D).T_h ∧
        Restated.RunBlockOn M S rho W Xb K ∧
        (M.derive_named S.E S.cfg K).h =
          (W (strictEventIndex rho time) v).st.core.h_max - 1 := by
  obtain ⟨Wb, hWb, Q, X, a, ta, hmaxW, hQ, hXW, haW, haHon, hemit, hta,
      hheight⟩ := Restated.frontierQuorumWitness_stateBeforeTimeOn facts
    S Hs Xb hf hHs hmajority hthor hlarge
  refine ⟨a, ta, haHon, hemit, hta, hheight, ?_⟩
  intro nr hnr o ho
  unfold Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness at ho
  obtain ⟨o', ho', rfl⟩ := returns_map_elim₅₀b _ _ _ ho
  obtain ⟨D, K, rfl, hσD, hKtarget, -, hD, -, -, hK, hKentry, hKheight, -, -⟩ :=
    heightRow_core₅₀b facts S Hs Xb hf (hHsXb _ haHon) hemit hheight nr hnr o' ho'
  have hKrun := Restated.actionBody_runBlockOn facts S Hs Xb hf (hHsXb _ haHon) hnr hK
  refine ⟨D, K, ?_, hD, hK, hKentry, hKrun, hKheight⟩
  rw [Option.map_some, hσD, hKtarget, hKentry]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- A genuine confirmation of `B` by `st` at slot `s` passes the eligibility test along one outcome
    of the early confirmation votes and one choice of Goldfish scores. -/
private theorem genuine_eligible₅₀b (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
    {hc : Protocol.HealConfig} {st : M.S} {s : Slot} {B : Block V}
    (hB : Restated.Vocabulary.Protocol.GenuineConfirmationWith M contract E hc st s B) :
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
    returns_map_intro₅₀b _ _ _ htm
  have hu := returns_map_intro₅₀b
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

/-- On the path `W` of the bundle, if `v` and `w` are in the set for slot `s`'s confirmation
    instant, `lo ≤ proposal_time s`, and that confirmation instant is within the horizon, then a
    genuine confirmation of `B` by `v` and one of `C` by `w` at `s`, each under the grade contract
    of an outcome of its cache update, are compatible. -/
theorem sameSlot_genuine_compatible_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.confirmation_time S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {B C : Block V}
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ cv)
    (hB : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)) s B)
    (cw : M.Cache)
    (hcw : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ cw)
    (hC : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cw)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
        (M.confirmation_time S.E s)) s C) :
    Block.compatible B C = true := by
  have hcross := Restated.opening_frontier_crossViews_confStore_after_gstOn facts
    S Hs Xb hf hHs hHsXb hv hw hpost hhor
  obtain ⟨ev, scv, hev, huv, hscv, hltv⟩ := genuine_eligible₅₀b facts hB
  obtain ⟨ew, scw, hew, huw, hscw, hltw⟩ := genuine_eligible₅₀b facts hC
  exact facts.fc.eligible_compatible (confEarly_subset_late₅₀b facts _ _ s ev hev) rfl
    (confEarly_subset_late₅₀b facts _ _ s ew hew) rfl (hcross.1 _ huv).transfer
    (hcross.1 _ huv).resolve (hcross.2 _ huw).transfer (hcross.2 _ huw).resolve
    (scv B) (hscv B) hltv (scw C) (hscw C) hltw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If the validators outside `X` weigh less than a third and `X ⊆ Xb`, then for every path `W` of
    `rho`, named genesis is a run block read through `Xb` along `W`. -/
theorem namedGenesis_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Xb X : Finset V) (hXXb : X ⊆ Xb)
    (hbelow : Execution.BelowOneThird S X) :
    ∀ W : Nat → V → M.N, Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W →
      Restated.RunBlockOn M S rho W Xb (NamedBlock.genesis : NamedBlock V) := by
  intro W hW
  obtain ⟨v, hv⟩ : X.Nonempty := by
    by_contra hempty
    have hm := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
    unfold HonestWeightMajority at hm
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, weightOf_empty] at hm
    exact Nat.not_lt_zero _ hm
  refine ⟨NamedBlock.genesis, Or.inr ⟨v, hXXb hv, 0, ?_⟩,
    Proofs.NamedAncestry.named_self NamedBlock.genesis⟩
  exact facts.hdRun.genesis_mem_stateBefore_zero S rho v (W 0) (hW 0).1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of `heightRegimeFrame_of_recoveryOn` and a weight bound on the complement
    of `X`, the named height regime frame over `X` along `W` holds at `blocked` up to `stop`,
    relative to named genesis and any round `c0`. -/
theorem namedHeightRegimeFrame_of_recoveryOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    (hbelow : Execution.BelowOneThird S X)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2)
    (c0 : Round) :
    Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb
      blocked stop NamedBlock.genesis c0 := by
  have hraw := Restated.heightRegimeFrame_of_recoveryOn facts
    S Hs Xb X hf hXXb hcap hrec hfrontier
  refine ⟨?_, Restated.namedGenesis_runBlockOn facts S Xb X hXXb hbelow W hf.onePath, ?_, ?_, ?_⟩
  · intro v hv n hn X' hXrun hXheight hgenX
    exact hraw.floor v hv n hn X' hXrun hXheight
      (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis X'.erase))
  · rw [facts.cs.derive_named_genesis_h]
    exact Nat.succ_le_of_lt
      ((Nat.zero_le (hF0 + 1)).trans_lt (NjGap.lt_of_recoveryHeight hrec))
  · intro v hv n hn Q hQmem hQheight hgenQ
    have hmem : W n ∈ Record.stateBeforeOf M S rho n := (hf.onePath n).1
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n v
      (W n) hmem).1.1.1
    have hQraw : Q.erase ∈ (W n v).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hQmem
    have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho n v
      (W n) hmem Q hQmem
    have hQstored : ((W n v).st.core.σ Q.erase).h = blocked + 1 := by
      rw [hview, hQheight]
    exact hraw.rootBelow v hv n hn Q.erase hQraw hQstored
      (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis Q.erase))
  · intro p r hp hr hhor n hn B hBmem hsource hBheight
    exact (priv% Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBase
      DecoupledConsensusModel.Proofs.HealingSurface.namedGenesis_preceq) B

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, under the first height progress over `X` at `blocked + 1` at
    `first`, a finality cap over `X` up to `first`, a recovery height `blocked`, and the largest
    `h_max` over `X` at round `r0`'s action instant less than `blocked`, the named height regime
    base holds at `r0`, `blocked`, `first`, relative to named genesis. -/
theorem namedHeightRegimeBase_of_recoveryOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    (hbelow : Execution.BelowOneThird S X)
    {r0 : Round} {first : Nat} {blocked hF0 : Height}
    (hfirst : Restated.FirstHeightProgressAtOn M S rho W X (blocked + 1) first)
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hstart : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) <
        blocked) :
    Restated.NamedHeightRegimeBaseOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb r0
      blocked first NamedBlock.genesis := by
  refine ⟨hfirst, hstart, ?_, ?_, ?_⟩
  · exact Nat.succ_le_of_lt
      ((Nat.zero_le (hF0 + 1)).trans_lt (NjGap.lt_of_recoveryHeight hrec))
  · intro c hminimal
    exact Restated.namedHeightRegimeFrame_of_recoveryOn facts S Hs Xb X hf hXXb hbelow
      (Restated.honestPrefixFinalityCap_of_leOn facts S Hs Xb X hf (Nat.sub_le first 1) hcap)
      hrec
      (Nat.lt_succ_of_le
        (hfirst.before _ (Nat.sub_lt hfirst.positive Nat.one_pos))) c
  · intro a ta ha hemit hbefore R hRh hpair n hn hfg w hw time hfrontier hroot
      Y hYrun hYh hprev
    have hta0 : 0 ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
      have htime : ta = (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
        (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
      obtain ⟨i, hi, -⟩ := hemit
      have hin := (hf.in_horizon _ (List.mem_of_getElem? hi)).1
      simpa only [Record.Event.time, htime, Record.Event.time] using hin
    have haX : a.val_index ∈ X := hX _ hta0 ha
    exact False.elim ((Restated.honestEmittedTarget_height_ne_recovery_namedOn facts
      S Hs Xb X hf hcap hrec haX hemit hbefore.le hpair) rfl)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, every Goldfish vote included in a block of `w`'s tree in the
    world `W n` is signed by a member of its slot's committee. -/
theorem carriedVote_committee_of_mem_T_coreOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (w : V) (n : Nat)
    {B : Block V} (hB : B ∈ (W n w).st.T) :
    ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
  obtain ⟨D, hD, hDB⟩ := Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts
    S rho n w (W n) (hf.onePath n).1 hB
  have hDcommittee : ∀ u ∈ D.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S rho w W hf.onePath
        n D hD with
      rfl | ⟨j, e, -, -, hproc⟩
    · intro u hu
      rw [named_genesis_gf_votes] at hu
      exact absurd hu (by simp)
    · rcases hproc with hem | ⟨i, hi⟩
      · obtain ⟨i, hi, out, hout, -, hmem⟩ := hem
        have hproposal :=
          Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho hi (W i)
            (hf.onePath i).1 out hout hmem
        dsimp only at hproposal
        obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i w).st.core.toHealing e.time
          (W i w).cache
        have _hr_p := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
        have _hv_p := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
        obtain ⟨D₁, hD₁⟩ := facts.dt.propose_block_with_nonempty S w (W i w) e.time out hout
          (facts.nd.block_mem_on_tick_emit S w (W i w) e.time out hout hmem).1.1
          (facts.nd.block_mem_on_tick_emit S w (W i w) e.time out hout hmem).1.2.1
          (facts.nd.block_mem_on_tick_emit S w (W i w) e.time out hout hmem).1.2.2
          (facts.nd.block_mem_on_tick_emit_awake S w (W i w) e.time out hout hmem) c hc
        have hD₁eq := hproposal c hc D₁ hD₁
        obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E
          S.hc (S.node w) (M.ns_setClock S.E (W i w).st e.time)
        have hproposal' := facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _
          D₁ hD₁ (by rw [hD₁eq]) o ho
        have hgf := facts.dt.proposal_with_gf_votes _ .poolAndCarried S.E S.hc (S.node w) _
          o ho hproposal'
        intro u hu
        rw [hgf] at hu
        have hu' : u ∈ (W i w).st.core.gf_votes (S.E.slotOf e.time - 1) := by
          have h := hu
          rw [facts.hd.setClock_core_gf_votes, facts.hd.Sts_setClock_core_s] at h
          exact h
        have hslot := (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w i).slot
          (S.E.slotOf e.time - 1) u hu'
        rw [hslot]
        exact Restated.Vocabulary.Protocol.CommitteePools.stateBefore facts S rho w i (W i)
          (hf.onePath i).1 (S.E.slotOf e.time - 1) u hu'
      · have hwf := hf.wire i w (Object.block D) e.time hi
        intro u hu
        exact (hwf.1 D rfl).2.2 u hu
  intro u hu
  have hu' : u ∈ D.gf_votes := by
    rw [← Proofs.NamedWire.erase_goldfish_votes, hDB]
    exact hu
  exact hDcommittee u hu'

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
open DecoupledConsensusModel.Proofs.Optimistic

/-- On the path `W` of the bundle, if `v` is in the set for `t`, `v`'s justified height in the world
    strictly before `t` is at most `Mh - 2`, and `X` is a run block read through `Xb` of height at
    least `Mh - 1`, then `v`'s finalized block in that world is an ancestor of `X`. -/
theorem finalizedRoot_preceq_of_bandOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v : V} {t : Time} (hv : v ∈ Hs t) {Mh : Height}
    (hgate : (W (strictEventIndex rho t) v).st.h_j + 2 ≤ Mh)
    {X : NamedBlock V} (hXrun : Restated.RunBlockOn M S rho W Xb X)
    (hXh : Mh - 1 ≤ (M.derive_named S.E S.cfg X).h) :
    Block.Preceq (W (strictEventIndex rho t) v).st.core.F X.erase := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  obtain ⟨B, hBT, hBF⟩ := Restated.exists_carrier_of_FOn facts S Hs Xb hf t hv
  have hBrun : Restated.RunBlockOn M S rho W Xb B :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hBT
  have hnoHigh := Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime
    facts S rho t v _ (path_mem_stateBeforeTime₅₀b facts S hf t)
  have hhj : (M.derive_named S.E S.cfg B).h_j ≤
      (W (strictEventIndex rho t) v).st.core.h_j := by
    exact hnoHigh B hBT
  have hhF : (M.derive_named S.E S.cfg B).h_F ≤
      (M.derive_named S.E S.cfg B).h_j :=
    (facts.cs.chainOrder_derive_named S.E S.cfg B).heights_ordered
  have hlt : (M.derive_named S.E S.cfg B).h_F <
      (M.derive_named S.E S.cfg X).h := by
    have h1 : (M.derive_named S.E S.cfg B).h_F + 1 + 1 ≤ Mh :=
      (Nat.add_le_add_right (hhF.trans hhj) 2).trans hgate
    exact lt_of_lt_of_le (Nat.lt_of_succ_le (Nat.le_sub_of_add_le h1)) hXh
  have hpre := Restated.finalized_preceq_of_height_ltOn facts
    S rho W Xb X B hsb hf.rootCollisionFree hXrun hBrun hlt
  simpa only [hBF] using hpre

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `receiver` processes `B` at `t`, `a` is included in `B`, and `a`'s author is in the set for
    `t`, then `S.a a.round ≤ t` and the author emitted `a` at `S.a a.round`. -/
theorem carriedArePastEmissions_of_processesOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {receiver : V} {B : NamedBlock V} {a : NamedAttestation V} {t : Time}
    (hB : Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver (.block B) t)
    (ha : a ∈ B.attestations) (hHon : a.val_index ∈ Hs t) :
    (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ t ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a)
        ((Restated.Vocabulary.Execution.Setup.a M S a.round)) :=
  Restated.honest_carried_row_emissionOn facts S rho Hs Xb hf hB ha hHon

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The conclusion of `carriedArePastEmissions_of_processesOn`, from the bundle's hypotheses. -/
theorem carriedArePastEmissions_of_admissibleCoreOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {receiver : V} {B : NamedBlock V} {a : NamedAttestation V} {t : Time}
    (hB : Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver (.block B) t)
    (ha : a ∈ B.attestations) (hHon : a.val_index ∈ Hs t) :
    (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ t ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a)
        ((Restated.Vocabulary.Execution.Setup.a M S a.round)) :=
  Restated.carriedArePastEmissions_of_processesOn facts S rho Hs Xb hf hB ha hHon

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every event before index `i` is at a time at most `T`, `a` is in `receiver`'s round row after
    `i` events, and `a`'s author is in the set for `T`, then `receiver` accepted `a` at some index
    `j < i` and time `t ≥ S.a a.round`, and the author emitted `a` at `S.a a.round`. -/
theorem heldArePastEmissions_of_admissibleCoreOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (i : Nat) (receiver : V) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ T)
    {a : NamedAttestation V}
    (ha : a ∈ (W i receiver).st.sg_rows a.round)
    (hHon : a.val_index ∈ Hs T) :
    ∃ j : Nat, j < i ∧ ∃ t : Time,
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j receiver (.attest a) t ∧
      (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ t ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a)
        ((Restated.Vocabulary.Execution.Setup.a M S a.round)) :=
  Restated.honest_held_row_emissionOn facts S rho Hs Xb hf hHs i receiver hT ha hHon

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

/-- Under the seed cone along `W` and a run block `Tnext ⪯ Cfg0` read through `Xb`, of height
    `blocked + 1` and erasing to `Cfg0`'s entry: for a body `Cfg` of a node state of the round-`r`
    action read of `w ∈ Xb`, whose entry is compatible with `Tnext`, if `Cfg` has height
    `blocked + 1` its entry is `Tnext`, and if it has height at least `blocked + 1` its entry
    descends from `Tnext`. -/
theorem PrefixFGSelectorConeAtOn.laterFGWitness_eq_or_extends_checkpoint_of_frameN
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (_hcom : Restated.HonestCommitteesOn M S Hs)
    (_hbelow : BelowOneThirdOn S rho Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg0 : NamedBlock V} {T0 : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start first blocked i a ta Cfg0 T0)
    (_hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (_hframe : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked (first - 1) Tprev c0)
    (_hc0 : c0 ≤ a.round)
    (_ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (_hpostPrev : lo ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (_hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round)
    {Tnext : NamedBlock V}
    (hTnextCfg : NamedBlock.Preceq Tnext Cfg0)
    (hTnextRun : Restated.RunBlockOn M S rho W Xb Tnext)
    (hTnextErase : Tnext.erase = (M.derive_named S.E S.cfg Cfg0).T_h)
    (hTnextHeight : (M.derive_named S.E S.cfg Tnext).h = blocked + 1)
    {r : Round} (_hr : a.round + 1 ≤ r)
    (_hhor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {w : V} (hw : w ∈ Xb) {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    {Cfg : NamedBlock V}
    (hCfgMem : Cfg ∈ n.st.bodies)
    (_hW : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢
      some (M.derive_named S.E S.cfg Cfg).T_h)
    (hcompat : Block.compatible (M.derive_named S.E S.cfg Cfg).T_h Tnext.erase = true) :
    ((M.derive_named S.E S.cfg Cfg).h = blocked + 1 →
      (M.derive_named S.E S.cfg Cfg).T_h = Tnext.erase) ∧
    (blocked + 1 ≤ (M.derive_named S.E S.cfg Cfg).h →
      Block.Preceq Tnext.erase (M.derive_named S.E S.cfg Cfg).T_h) := by
  obtain ⟨K, _hKmem, hKerase, hKheight, hKCfg, hKrun⟩ :=
    Restated.action_named_checkpointOn facts S Hs Xb hf hw hn hCfgMem
  have hKfixed : (M.derive_named S.E S.cfg K).T_h = K.erase :=
    (facts.cs.entry_eq_on_plateau S.E S.cfg hKCfg hKheight).trans hKerase.symm
  have hTnextFixed : (M.derive_named S.E S.cfg Tnext).T_h = Tnext.erase := by
    have hplateau := facts.cs.entry_eq_on_plateau S.E S.cfg hTnextCfg
      (hTnextHeight.trans hseed.sourceDerivedHeight.symm)
    exact hplateau.trans hTnextErase.symm
  have hnamed : NamedBlock.Preceq K Tnext ∨ NamedBlock.Preceq Tnext K := by
    have hraw : Block.Preceq K.erase Tnext.erase ∨ Block.Preceq Tnext.erase K.erase := by
      rw [hKerase]
      exact compatible_cases hcompat
    rcases hraw with hKT | hTK
    · exact Or.inl
        (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hKrun hTnextRun hKT)
    · exact Or.inr
        (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTnextRun hKrun hTK)
  have heq : (M.derive_named S.E S.cfg Cfg).h = blocked + 1 →
      (M.derive_named S.E S.cfg Cfg).T_h = Tnext.erase := by
    intro hh
    have hheights : (M.derive_named S.E S.cfg K).h = (M.derive_named S.E S.cfg Tnext).h :=
      hKheight.trans (hh.trans hTnextHeight.symm)
    rcases hnamed with hKT | hTK
    · calc
        (M.derive_named S.E S.cfg Cfg).T_h = K.erase := hKerase.symm
        _ = (M.derive_named S.E S.cfg K).T_h := hKfixed.symm
        _ = (M.derive_named S.E S.cfg Tnext).T_h :=
          facts.cs.entry_eq_on_plateau S.E S.cfg hKT hheights
        _ = Tnext.erase := hTnextFixed
    · calc
        (M.derive_named S.E S.cfg Cfg).T_h = K.erase := hKerase.symm
        _ = (M.derive_named S.E S.cfg K).T_h := hKfixed.symm
        _ = (M.derive_named S.E S.cfg Tnext).T_h :=
          (facts.cs.entry_eq_on_plateau S.E S.cfg hTK hheights.symm).symm
        _ = Tnext.erase := hTnextFixed
  refine ⟨heq, ?_⟩
  intro hheight
  rcases hnamed with hKT | hTK
  · have hupper := facts.cs.derive_height_mono S.E S.cfg hKT
    have hh : (M.derive_named S.E S.cfg Cfg).h = blocked + 1 := by
      apply Nat.le_antisymm
      · exact hKheight.symm.le.trans (hupper.trans hTnextHeight.le)
      · exact hheight
    rw [heq hh]
    exact (preceq_eq_true_iff_Preceq.mp (Block.preceq_self Tnext.erase))
  · rw [← hKerase]
    exact Proofs.NamedWire.erase_preceq hTK

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the finality floor over `X` along `W`, for `reader ∈ X` and `n ≤ stop`, `reader`'s
    finalized block in the world `W n` is an ancestor of every run block read through `Xb` at height
    `blocked + 1` descending from `Tprev`. -/
theorem FinalityFloorAtOn.storeF_preceq_sourceHeightBlock (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {W : Nat → V → M.N} {X Xb : Finset V} {blocked : Height}
    {stop : Nat} {Tprev : Block V}
    (h : Restated.FinalityFloorAtOn M S rho W X Xb blocked stop Tprev)
    {n : Nat} {reader : V} (hreader : reader ∈ X)
    (hnstop : n ≤ stop) {P : NamedBlock V}
    (hPrun : Restated.RunBlockOn M S rho W Xb P)
    (hPheight : (M.derive_named S.E S.cfg P).h = blocked + 1)
    (hTP : Block.Preceq Tprev P.erase) :
    Block.Preceq (W n reader).st.F P.erase :=
  h reader hreader n hnstop P hPrun (hPheight ▸ Nat.le_succ blocked) hTP

/-- If event `i` is strictly earlier than event `j`, then `i < j`. -/
theorem eventIndex_lt_of_time_ltOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i j : Nat} {e f : Record.Event V}
    (hi : rho.events[i]? = some e)
    (hj : rho.events[j]? = some f)
    (ht : e.time < f.time) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji' | rfl
  · have hkey := Restated.key_le_of_index_ltOn facts S Hs Xb hf hji' hj hi
    exact (not_le_of_gt ht) (Restated.time_le_of_key_le hkey)
  · have heq : e = f := Option.some.inj (hi.symm.trans hj)
    exact (lt_irrefl _ (by simpa only [heq] using ht))

/-- If event `i` is a tick at `t` and event `j` delivers a block at `t`, then `i < j`. -/
theorem tickIndex_lt_delivery_sameTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i j : Nat} {u v : V} {t : Time} {B : NamedBlock V}
    (hi : rho.events[i]? = some (Record.Event.tick u t))
    (hj : rho.events[j]? = some (Record.Event.deliver v (Object.block B) t)) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji' | rfl
  · have hkey := Restated.key_le_of_index_ltOn facts S Hs Xb hf hji' hj hi
    simp [Record.Event.key, Record.Event.time, Record.Event.phase,
      Prod.Lex.toLex_le_toLex] at hkey
  · cases Option.some.inj (hj.symm.trans hi)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Along a path `W` of `rho`, every named block among `v`'s bodies in `W n` is genesis, or for some
    `j < n` the `j`-th event is a tick of `v` whose outcome along `W` sends it, or a delivery of it
    to `v`. -/
private theorem processesBlockAtIndex_of_mem_bodies₅₀ (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (v : V) (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) :
    ∀ (n : Nat) (B : NamedBlock V), B ∈ (W n v).st.bodies →
      B = NamedBlock.genesis ∨
        ∃ j : Nat, j < n ∧
          Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W j v
            (Object.block B) := by
  intro n
  induction n with
  | zero =>
    intro B hB
    exact Or.inl (facts.ndRun.stateBefore_zero_body_eq_genesis S rho v (W 0) (hW 0).1 hB)
  | succ n ih =>
    intro B hB
    by_cases hpre : B ∈ (W n v).st.bodies
    · rcases ih B hpre with h | ⟨j, hj, hproc⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hproc⟩
    · refine Or.inr ⟨n, Nat.lt_succ_self n, ?_⟩
      obtain ⟨t, hacc⟩ := Restated.Vocabulary.Proofs.NamedReceiptCalls.new_block_accepts facts S rho
        n v B W hW hpre hB
      obtain ⟨⟨hidx, e, he, -, -⟩, -, -⟩ := hacc
      rcases hidx with ⟨t', ht', hmem⟩ | ⟨t', ht'⟩
      · exact Or.inl ⟨t', ht', hmem⟩
      · exact Or.inr ⟨t', ht'⟩

/-- Along the bundle's path `W`, if every event before index `n` is at a time at most `T`, `B` is
    among `v`'s bodies in `W n`, `a` is on `B`'s chain, and `a`'s signer is in the set for `T`, then
    for some `i < n` and time `t` the `i`-th event is the signer's tick at `t`, its outcome along
    `W` sends `a`, and the signer emits `a` at `t` along `W`. -/
theorem honestCarriedAttestation_emittedBeforeIndexOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {n : Nat} {v : V} {B : NamedBlock V} {a : NamedAttestation V} {T : Int}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    (hB : B ∈ (W n v).st.bodies)
    (ha : a ∈ Protocol.named_chain_attestations B)
    (haHon : a.val_index ∈ Hs T) :
    ∃ i : Nat, ∃ t : Time,
      i < n ∧
        rho.events[i]? = some (Record.Event.tick a.val_index t) ∧
        (∃ out : M.N × List (NamedObject V),
          M.tick S a.val_index (W i a.val_index) t ⇢ out ∧ W (i + 1) a.val_index = out.1 ∧
            Object.attest a ∈ out.2) ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) t := by
  have _hr_0 : M.reachedNode (W n v) := facts.ndRun.stateBeforeOf_reachedNode S rho n (W n) (hf.onePath n).1 v
  have _hv_0 : M.runs_as (W n v) v := facts.ndRun.stateBeforeOf_runs_as S rho n (W n) (hf.onePath n).1 v
  obtain ⟨X, hXB, haX⟩ :=
    (priv% Proofs.Vocabulary.Generic.PrefixFGSelectorWitness
      DecoupledConsensusModel.Proofs.HealingSurface.named_mem_chain_attestations) B ha
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (W n v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n v _
      (hf.onePath n).1).1.1.1.2.2.1
  have hXT : X ∈ (W n v).st.bodies := namedAncestor_mem₅₀b hpc hB hXB
  rcases processesBlockAtIndex_of_mem_bodies₅₀ facts S rho v W hf.onePath n X hXT with
    hgen | ⟨j, hj, hprocessed⟩
  · rw [hgen, named_genesis_attestations] at haX
    simp at haX
  · rcases hprocessed with ⟨tp, hprocessTick, outp, houtp, hstepp, hblockEmit⟩ |
        ⟨tp, hprocessDeliver⟩
    · have hprocess : Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (.block X) tp :=
        Or.inl ⟨j, hprocessTick, outp, houtp, hstepp, hblockEmit⟩
      have htpT : tp ≤ T := hT j _ hj hprocessTick
      obtain ⟨ta, hta, hemit⟩ :=
        hf.carried_attest v X tp hprocess a haX (hHs _ _ htpT haHon)
      obtain ⟨i, hi, himit⟩ := id hemit
      have htaLt : ta < tp := by
        apply lt_of_le_of_ne hta
        intro hEq
        have haction : tp = M.a S.hc S.E.Δ a.round :=
          hEq.symm.trans
            (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
        have _hr_s7 := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hf.onePath j).1 v
        have _hv_s8 := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hf.onePath j).1 v
        obtain ⟨hguard, -⟩ := Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts
          S v (W j v) tp outp houtp hblockEmit
        exact (Restated.Vocabulary.Proofs.Optimistic.a_ne_proposal_time facts S haction) hguard.2.1
      have hij : i < j := Restated.eventIndex_lt_of_time_ltOn facts S Hs Xb hf hi hprocessTick htaLt
      exact ⟨i, ta, hij.trans hj, hi, himit, hemit⟩
    · have hprocess : Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (.block X) tp :=
        Or.inr ⟨j, hprocessDeliver⟩
      have htpT : tp ≤ T := hT j _ hj hprocessDeliver
      obtain ⟨ta, hta, hemit⟩ :=
        hf.carried_attest v X tp hprocess a haX (hHs _ _ htpT haHon)
      obtain ⟨i, hi, himit⟩ := id hemit
      rcases lt_or_eq_of_le hta with htaLt | htaEq
      · have hij : i < j :=
          Restated.eventIndex_lt_of_time_ltOn facts S Hs Xb hf hi hprocessDeliver htaLt
        exact ⟨i, ta, hij.trans hj, hi, himit, hemit⟩
      · subst htaEq
        have hij : i < j :=
          Restated.tickIndex_lt_delivery_sameTimeOn facts S Hs Xb hf hi hprocessDeliver
        exact ⟨i, ta, hij.trans hj, hi, himit, hemit⟩

/-- Along the bundle's path `W`, if the validators outside the set for `T` weigh less than a third,
    some member of `X` holds in `W stop` run blocks crossing from height `blocked` to `blocked + 2`,
    and no tick before index `start` of a member of the set for its time sends an attestation with a
    height pair at `blocked`, then some tick of index `i` with `start ≤ i < stop` sends an
    attestation `a` at its round's action instant whose action FG source is the erasure of a body of
    height `blocked + 1`, and `a`'s height pair targets that body's entry root at `blocked + 1` or
    is the timeout there. -/
theorem prefixHeightCrossing_exactFGSelectorWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) {T : Int}
    (hbelow : Execution.BelowOneThird S (Hs T))
    {start stop : Nat} {blocked : Height}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < stop → rho.events[j]? = some e → e.time ≤ T)
    (hcross : Restated.PrefixHeightCrossingWitnessOn M S rho W X Xb stop blocked)
    (hfresh : ∀ {i : Nat} {v : V} {t : Time} {a : NamedAttestation V},
      i < start → v ∈ Hs t → rho.events[i]? = some (Record.Event.tick v t) →
        ∀ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out → W (i + 1) v = out.1 →
          Object.attest a ∈ out.2 → a.height_pair.erase.height? ≠ some blocked) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time),
      start ≤ i ∧
        i < stop ∧
        a.val_index ∈ Hs T ∧
        rho.events[i]? = some (Record.Event.tick a.val_index ta) ∧
        (∃ out : M.N × List (NamedObject V),
          M.tick S a.val_index (W i a.val_index) ta ⇢ out ∧ W (i + 1) a.val_index = out.1 ∧
            Object.attest a ∈ out.2) ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta ∧
        ta = (Restated.Vocabulary.Execution.Setup.a M S a.round) ∧
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
          a.round,
        (∀ Y, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node a.val_index) n.st
            n.record ⇢ Y → a = Y.2.2) ∧
        ∀ o : Option (Block V),
          Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
        ∃ (B : NamedBlock V) (J : Block V),
          o = some B.erase ∧
          B ∈ n.st.bodies ∧
          (n.st.core.σ B.erase).h = blocked + 1 ∧
          (M.derive_named S.E S.cfg B).h = blocked + 1 ∧
          J = (M.derive_named S.E S.cfg B).T_h ∧
          (a.height_pair.erase = HeightPair.target (blocked + 1) J.root ∨
            a.height_pair.erase = HeightPair.timeout (blocked + 1)) := by
  rcases hcross with
    ⟨holder, hholder, carrier, anchor, hcarrier, hanchor,
      hcarrierRun, hanchorRun, hanchorCarrier, hanchorHeight, hcarrierHeight⟩
  have hblockedPos : 1 ≤ blocked := by
    rw [← hanchorHeight]
    exact facts.cs.one_le_derive_named_h S.E S.cfg anchor
  have hnextPos : 1 ≤ blocked + 1 :=
    hblockedPos.trans (Nat.le_add_right blocked 1)
  have hcarrierCross : blocked + 1 <
      (M.derive_named S.E S.cfg carrier).h := by
    rw [hcarrierHeight]
    exact Nat.lt_succ_self (blocked + 1)
  obtain ⟨X', hXcarrier, hXheight, Q, hQ, hrows⟩ :=
    facts.cs.height_crossing S.E S.cfg carrier
      (blocked + 1) hnextPos hcarrierCross
  obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbelow hQ
  obtain ⟨carrier', a, hcarrier', haCarrier, haSigner, haPair⟩ :=
    hrows signer hsignerQ
  have haHon : a.val_index ∈ Hs T := by
    rw [haSigner]
    exact hsignerHonest
  have haHeight : a.height_pair.erase.height? = some (blocked + 1) :=
    (priv% Proofs.Vocabulary.Generic.PrefixFGSelectorWitness
      DecoupledConsensusModel.Proofs.HealingSurface.named_height_of_matches) haPair
  clear haPair
  have haChain : a ∈ Protocol.named_chain_attestations carrier :=
    (priv% Proofs.Vocabulary.Generic.PrefixFGSelectorWitness
      DecoupledConsensusModel.Proofs.HealingSurface.named_row_mem_chain_of_ancestor)
      hcarrier' haCarrier
  obtain ⟨i, ta, hiStop, hiEvent, hiEmit, hemit⟩ :=
    Restated.honestCarriedAttestation_emittedBeforeIndexOn facts S Hs Xb hf hHs hT hcarrier haChain
      haHon
  have hselector := Restated.honestEmittedHeightRow_exactFGSelectorWitnessOn facts
    S Hs Xb (Hs T) hf haHon hemit haHeight
  obtain ⟨n0, hn0⟩ := actionReadFrom_nonempty₅₀ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  have hta : ta = (Restated.Vocabulary.Execution.Setup.a M S a.round) := (hselector n0 hn0).1
  have hiStart : start ≤ i := by
    by_contra hnot
    have hiBeforeStart : i < start := Nat.lt_of_not_ge hnot
    obtain ⟨o, ho⟩ := actionFGSource_nonempty₅₀b facts S n0
    obtain ⟨B, J, -, hBmem, -, hBderivedHeight, -, -⟩ := (hselector n0 hn0).2.2 o ho
    have hBAtI : B ∈ (W i a.val_index).st.bodies := by
      rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hiEvent with
        hstate | hstate
      · rw [hstate, hta, ← actionReadFrom_bodies₅₀ facts S _ _ n0 hn0]
        exact hBmem
      · rw [hstate, (facts.nd.wake_st_record _).1, hta, ← actionReadFrom_bodies₅₀ facts S _ _ n0 hn0]
        exact hBmem
    have hBcross : blocked <
        (M.derive_named S.E S.cfg B).h := by
      rw [hBderivedHeight]
      exact Nat.lt_succ_self blocked
    obtain ⟨X0, hX0B, hX0Height, Q0, hQ0, hrows0⟩ :=
      facts.cs.height_crossing S.E S.cfg B blocked
        hblockedPos hBcross
    obtain ⟨signer0, hsigner0Q, hsigner0Honest⟩ :=
      AlignedRoundLemmas.honest_member_of_quorum hbelow hQ0
    obtain ⟨carrier0, a0, hcarrier0, ha0B, ha0Signer, ha0Pair⟩ :=
      hrows0 signer0 hsigner0Q
    have ha0Hon : a0.val_index ∈ Hs T := by
      rw [ha0Signer]
      exact hsigner0Honest
    have ha0Height : a0.height_pair.erase.height? = some blocked :=
      (priv% Proofs.Vocabulary.Generic.PrefixFGSelectorWitness
        DecoupledConsensusModel.Proofs.HealingSurface.named_height_of_matches) ha0Pair
    have ha0Chain : a0 ∈ Protocol.named_chain_attestations B :=
      (priv% Proofs.Vocabulary.Generic.PrefixFGSelectorWitness
        DecoupledConsensusModel.Proofs.HealingSurface.named_row_mem_chain_of_ancestor)
        hcarrier0 ha0B
    have hTi : ∀ (j : Nat) (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ T :=
      fun j e hj he => hT j e (hj.trans hiStop) he
    obtain ⟨k, tk, hkI, hkEvent, ⟨outk, houtk, hstepk, hmemk⟩, -⟩ :=
      Restated.honestCarriedAttestation_emittedBeforeIndexOn facts S Hs Xb hf hHs hTi hBAtI
        ha0Chain ha0Hon
    have hkStart : k < start := hkI.trans hiBeforeStart
    have htkT : tk ≤ T := hT k _ (hkI.trans hiStop) hkEvent
    exact (hfresh hkStart (hHs _ _ htkT ha0Hon) hkEvent outk houtk hstepk hmemk ha0Height).elim
  exact ⟨i, a, ta, hiStart, hiStop, haHon, hiEvent, hiEmit, hemit, hta,
    fun n hn => (hselector n hn).2⟩

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

/-- Under the named frame over `X` along `W`, if the largest `h_max` over `X` in `W stop` is less
    than `blocked + 2`, `reader ∈ X`, `n ≤ stop`, and `Q` is a body of `reader`'s store in `W n` at
    height `blocked + 1` descending from `Tprev`, then that store's FG root is an ancestor of `Q`
    and `Q` is in its filtered tree. -/
theorem NamedHeightRegimeFrameOn.fgRoot_preceq_and_filteredMem (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {W : Nat → V → M.N} {Wt : Time → V → M.N}
    {X Xb : Finset V} {blocked : Height} {stop : Nat}
    {Tprev : NamedBlock V} {c0 : Round} (Hs : Int → Finset V)
    (h : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked stop Tprev c0)
    {lo : Int} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hXXb : X ⊆ Xb)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2)
    {n : Nat} {reader : V} {Q : NamedBlock V}
    (hreader : reader ∈ X) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (W n reader).st.bodies)
    (hQheight : (M.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : NamedBlock.Preceq Tprev Q) :
    Block.Preceq (M.get_fg_root (M.toHealing (W n reader).st.core).toFG) Q.erase ∧
      Q.erase ∈ M.get_filtered_block_tree (M.toHealing (W n reader).st.core).toFG := by
  have hmem : W n ∈ Record.stateBeforeOf M S rho n := (hf.onePath n).1
  have hcoh :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n reader _
      hmem).1.1.1
  have hQraw : Q.erase ∈ (W n reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hQmem
  have hQstored : ((W n reader).st.core.σ Q.erase).h = blocked + 1 := by
    rw [Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho n reader
      _ hmem Q hQmem, hQheight]
  have hmax : (W n reader).st.core.h_max = blocked + 1 :=
    Restated.localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontierOn facts
      S Hs Xb X hf hfrontier hreader hnstop hQraw hQstored
  have hrootQ := h.rootBelow reader hreader n hnstop Q hQmem hQheight hTQ
  have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hreader) hQmem
  have hFQ : Block.Preceq (W n reader).st.core.F Q.erase :=
    h.floor reader hreader n hnstop Q hQrun
      (by rw [hQheight]; exact Nat.le_succ blocked) hTQ
  have hT : (M.toHealing (W n reader).st.core).toFG.toSG.toGoldfishStore.T =
      (W n reader).st.core.T :=
    facts.sto.toHealing_gs_T _
  refine ⟨hrootQ, facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing (W n reader).st.core)
    (C := Q.erase) (W := Q.erase) ?_ ?_ ?_ (Proofs.ModelProperties.Preceq_self _) ?_ hrootQ⟩
  · rw [hT]
    exact hQraw
  · rw [facts.sto.Sts_toHealing_F]
    exact hFQ
  · rw [hT]
    exact hQraw
  · rw [facts.sto.Sts_toHealing_h_max, facts.sto.Sts_toHealing_σ, hmax, hQstored]
    exact Nat.sub_le _ _

end

end DecoupledConsensusModel.Sts.Restated
