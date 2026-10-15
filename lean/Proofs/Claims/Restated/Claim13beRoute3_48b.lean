import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_FrameForward
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalityMonotoneCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedJointOutage
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_48b

/-!
# Grade, anchor and finalization facts along a path of the run

Theorems about the action read, the vote-duty read, the grade-2 block and the anchor, and the
finalized blocks at deliveries, stated over a model `M : Record.Model V` along the path `W` of the
bundle `AdmissibleFieldsOn`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ## Helpers about event indices, paths and the action read -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events is at an
    instant before `t`. -/
private theorem time_lt_of_lt_strict₄₈b {rho : Record.Run V}
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

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₄₈b (S : Setup V) (rho : Record.Run V)
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
    a world strictly before the instant `t`. -/
private theorem mem_stateBeforeTime_path₄₈b (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₄₈b S rho hsorted t]
  exact (hW _).1

/-- The domain instant of phase `p` of round `r` is before round `r`'s action instant. -/
private theorem domain_lt_a₄₈b (facts : Record.Facts M) (S : Setup V) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) :
    M.domain S.E S.hc r p < Restated.Vocabulary.Execution.Setup.a M S r := by
  have hΔ := S.E.Δ_pos
  have h5 := facts.gr.domain_add_five_delta_le_action S r p
  show M.domain S.E S.hc r p < M.a S.hc S.E.Δ r
  linarith

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₄₈b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₄₈b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If the contract's grade read at `n` can return `G`, `n`'s anchor read can return `G`'s anchor. -/
private theorem nodeAnchor_of_read₄₈b (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ G.anchor := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₄₈b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G
    hG

/-- For every node state `n` of the round-`r` action read from `before`, `n`'s store is
    `M.store_with_cache st n.cache` for a store `st` whose core is an outcome of the confirmation
    write on `before`'s core store with its clock set to round `r`'s action instant, at the slot
    before that instant's slot, with the grade contract of `n`'s cache. -/
private theorem actionReadFrom_core₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- The cache of every node state of the round-`r` action read from `before` is an outcome of the
    phase tick at round `r`'s action instant on `before`'s cache. -/
private theorem actionReadFrom_cache₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.onPhaseTick S.E S.hc (M.toHealing before.st.core)
        (Restated.Vocabulary.Execution.Setup.a M S r) before.cache ⇢ n.cache := by
  rintro _ ⟨c, hc, st, -, rfl⟩
  rw [facts.nd.mkNode_cache]
  exact hc

/-- Every node state of the round-`r` action read from `before` has the finalized block of
    `before`'s core store. -/
private theorem actionReadFrom_F₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.F = before.st.core.F := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₈b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_F,
    facts.dt.update_confirmation_with_F _ _ _ _ _ _ hX₀,
    facts.hd.setClock_core_F]

/-- Every node state of the round-`r` action read from `before` has the grade view of `before`'s
    core store, when `before` is a node state a run reaches. -/
private theorem actionReadFrom_gradeView₄₈b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
    ∀ (hb : M.reachedNode before),
      M.gradeView (M.toHealing n.st.core) = M.gradeView (M.toHealing before.st.core) := by
  intro n hn hb
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₈b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_gradeView,
    facts.dt.update_confirmation_with_toHealing_gradeView _ _ _ _ _ _
    hX₀ (facts.nd.reachedCore_of_store _ (facts.sto.reachedStore_setClock S.E _ _
      (facts.nd.reachedStore_of_node _ hb))), facts.hd.setClock_gradeView]

/-- Every node state of the round-`r` action read from `before` has the tree of `before`'s core
    store. -/
private theorem actionReadFrom_T₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₈b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

/-- Every node state of the round-`r` action read from `before` has its slot equal to the slot of
    `S.a r`. -/
private theorem actionReadFrom_s₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.s = S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₈b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_s,
    facts.dt.update_confirmation_with_s _ _ _ _ _ _ hX₀,
    facts.hd.setClock_core_eq_store_with_t_s, facts.sto.store_with_t_s_s]

/-- Setting the clock of a node state's store leaves the filtered block tree of its core store
    unchanged. -/
private theorem setClock_filtered₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (t : Time) :
    M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E before.st t).core).toFG =
      M.get_filtered_block_tree (M.toHealing before.st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_toHealing_clock _ _ _

/-- Every node state of the round-`r` action read from `before` has the filtered block tree of
    `before`'s core store. -/
private theorem actionReadFrom_filtered₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
        M.get_filtered_block_tree (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₈b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_filtered_block_tree,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _
    hX₀]
  exact setClock_filtered₄₈b facts S before _

/-- Every node state of the round-`r` action read from `before` has the FG root of `before`'s store
    with its clock set to round `r`'s action instant. -/
private theorem actionReadFrom_fg_root₄₈b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG =
        M.get_fg_root (M.toHealing
          (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₈b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root]
  exact facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _ hX₀

/-- For every node state `n` of the round-`r` action read from `before` and every phase `p`, the
    phase-`p` result of the round-`k` frame read from `n`'s cache and store is that of the frame
    read from `n`'s cache and `before`'s store with its clock set to round `r`'s action instant. -/
private theorem actionReadFrom_readFrame₄₈b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r k : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
    ∀ p : DecoupledConsensusModel.Protocol.Phase,
      M.phaseResult (M.readFrame n.cache (M.toHealing n.st.core) k) p =
        M.phaseResult (M.readFrame n.cache (M.toHealing
          (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core) k) p :=
  by
  intro n hn p
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₄₈b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_readFrame]
  exact facts.gr.readFrame_phase_eq_of_F _ k
    (facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ _ hX₀) p

/-- For every node state `n` of the round-`r` action read from `before`, the round-`k` frames read
    from `n`'s cache at `n`'s store and at `before`'s store with its clock set to round `r`'s action
    instant have the same grade-0, grade-1 and grade-2 results. -/
private theorem actionReadFrom_readFrame_g₄₈b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r k : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      (M.readFrame n.cache (M.toHealing n.st.core) k).g0 =
          (M.readFrame n.cache (M.toHealing
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core) k).g0 ∧
        (M.readFrame n.cache (M.toHealing n.st.core) k).g1 =
          (M.readFrame n.cache (M.toHealing
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core) k).g1 ∧
        (M.readFrame n.cache (M.toHealing n.st.core) k).g2 =
          (M.readFrame n.cache (M.toHealing
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core) k).g2 := by
  intro n hn
  have h := actionReadFrom_readFrame₄₈b facts S before r k n hn
  refine ⟨?_, ?_, ?_⟩
  · rw [← facts.gr.phaseResult_g0, ← facts.gr.phaseResult_g0]; exact h .g0
  · rw [← facts.gr.phaseResult_g1, ← facts.gr.phaseResult_g1]; exact h .g1
  · rw [← facts.gr.Sts_phaseResult_g2, ← facts.gr.Sts_phaseResult_g2]; exact h .g2

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, is the core store of `n`'s
    store with its clock set to the slot-`s` vote instant. -/
private theorem voteStore_eq_setClock₄₈b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, has the tree of `n`'s core
    store. -/
private theorem voteStore_T₄₈b (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s).T = n.st.core.T := by
  rw [voteStore_eq_setClock₄₈b facts, facts.hd.Sts_setClock_core_T]

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, has the block stamps of
    `n`'s core store. -/
private theorem voteStore_timestamp_block₄₈b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (s : Slot) :
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s).timestamp_block =
      n.st.core.timestamp_block := by
  rw [voteStore_eq_setClock₄₈b facts, facts.hd.setClock_core_timestamp_block]

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

/-- Along the path `W` of the bundle, if `v` is in `Hs (domain r p)` and `lo ≤ domain r p`, then for
    every node state `n` of `v`'s action read of the positive round `r` (with `S.a r` inside the
    horizon) and every outcome `fr` of the frozen root of `v`'s store strictly before the domain
    instant, the round-`r` frame's phase-`p` slot at `n` holds `fr`, clipped against `n`'s finalized
    block. -/
theorem actionFrame_phase_completedOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (p : DecoupledConsensusModel.Protocol.Phase)
    (hv : v ∈ Hs (M.domain S.E S.hc r p))
    (hgat : lo ≤ M.domain S.E S.hc r p) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ fr : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.storeRoot M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st r p ⇢ fr →
    M.phaseResult (M.readFrame n.cache (M.toHealing n.st.core) r) p =
      some (fr.map (fun B => M.clipGrade B n.st.core.F)) := by
  intro n hn fr hfr
  have hmem := mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have h := Restated.Vocabulary.Proofs.FrameForward.frame_phase_checkpoint_eq facts S rho v r p _ _ hmem
    (Restated.frame_phase_completedOn facts S rho Hs Xb hf v r hr p hv
      (Restated.Vocabulary.Execution.Setup.a M S r)
      (domain_lt_a₄₈b facts S r p) le_rfl
      (le_trans (facts.gr.domain_le_a S r p) hhor) hgat (fun j hj => hf.tick_outcome j _ _ hj) fr hfr)
    n.cache (actionReadFrom_cache₄₈b facts S _ r n hn)
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at h
  simp only [facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_core_F] at h
  rw [← actionReadFrom_readFrame₄₈b facts S _ r r n hn p] at h
  rw [actionReadFrom_F₄₈b facts S _ r n hn]
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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- The G2 slot form of `actionFrame_phase_completedOn`: if `v` is in `Hs (domain r .g2)` and
    `lo ≤ domain r .g2`, the G2 slot of `v`'s action frame of `r` holds `v`'s own G2 freeze, clipped
    against the finalized block. -/
theorem actionFrame_g2On (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g2))
    (hgat : lo ≤ M.domain S.E S.hc r .g2) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ fr : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.storeRoot M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 ⇢ fr →
    (M.readFrame n.cache (M.toHealing n.st.core) r).g2 =
      some (fr.map (fun B => M.clipGrade B n.st.core.F)) :=
  fun n hn fr hfr => (facts.gr.Sts_phaseResult_g2 _).symm.trans
    (Restated.actionFrame_phase_completedOn facts S Hs Xb hf hr hhor .g2 hv hgat n hn fr hfr)

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

/-- The G1 slot form of `actionFrame_phase_completedOn`: if `v` is in `Hs (domain r .g1)` and
    `lo ≤ domain r .g1`, the G1 slot of `v`'s action frame of `r` holds `v`'s own G1 freeze, clipped
    against the finalized block. -/
theorem actionFrame_g1On (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g1))
    (hgat : lo ≤ M.domain S.E S.hc r .g1) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ fr : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.storeRoot M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st r .g1 ⇢ fr →
    (M.readFrame n.cache (M.toHealing n.st.core) r).g1 =
      some (fr.map (fun B => M.clipGrade B n.st.core.F)) :=
  fun n hn fr hfr => (facts.gr.phaseResult_g1 _).symm.trans
    (Restated.actionFrame_phase_completedOn facts S Hs Xb hf hr hhor .g1 hv hgat n hn fr hfr)

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

/-- The G0 slot form of `actionFrame_phase_completedOn`: if `v` is in `Hs (domain r .g0)` and
    `lo ≤ domain r .g0`, the G0 slot of `v`'s action frame of `r` holds `v`'s own G0 freeze, clipped
    against the finalized block. -/
theorem actionFrame_g0On (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (hgat : lo ≤ M.domain S.E S.hc r .g0) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ fr : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.storeRoot M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) v).st r .g0 ⇢ fr →
    (M.readFrame n.cache (M.toHealing n.st.core) r).g0 =
      some (fr.map (fun B => M.clipGrade B n.st.core.F)) :=
  fun n hn fr hfr => (facts.gr.phaseResult_g0 _).symm.trans
    (Restated.actionFrame_phase_completedOn facts S Hs Xb hf hr hhor .g0 hv hgat n hn fr hfr)

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

/-- If `v` is in `Hs (domain r .g0)` and `r`'s window opens at or after `lo`, a block `C` in the
    filtered tree of `v`'s node state strictly before `domain r .g2` whose G2 grade test there can
    return `true`, and in the filtered tree of a node state `n` of `v`'s action read of the positive
    round `r`, is an ancestor of `Q` for every outcome `some Q` of `n`'s candidate read. -/
theorem preceq_actionQ2_of_domainGradeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) {C : Block V}
    (hmem : C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v))
    (hgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 C ⇢ true)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hactive : C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) :
    ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ o →
      ∃ Q : Block V, o = some Q ∧ Block.Preceq C Q := by
  intro o ho
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hd
  have hT : C ∈ d.st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree facts hmem
  obtain ⟨fr2, hfr2⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2)
  obtain ⟨fr1, hfr1⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  obtain ⟨fr0, hfr0⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0)
  obtain ⟨raw, hfz, hCraw⟩ := facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing d.st.core)) d.st.core.F
    S.hc.η_SG r (facts.gr.q10_early_le_late S r .g2)
    (by rw [facts.gr.Sts_gradeView_T]; exact hT) true hgrade rfl fr2 hfr2
  have hFC : Block.Preceq n.st.core.F C := by
    have h := facts.fc.q10_filtered_F hactive
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  have hcompat : Block.compatible C n.st.core.F = true :=
    compatible_of_cases (Or.inr hFC)
  have hCclip : Block.Preceq C (M.clipGrade raw n.st.core.F) :=
    (facts.gr.q10_retained_prefix raw n.st.core.F C hcompat).mpr hCraw
  have h₂ : (M.readFrame n.cache (M.toHealing n.st.core) r).g2 =
        some (some (M.clipGrade raw n.st.core.F)) := by
    rw [Restated.actionFrame_g2On facts S Hs Xb hf hr hhor
      (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hv)
      (facts.gr.lo_le_domain_of_window_start S hr hlo .g2) n hn fr2 hfr2, hfz]
    rfl
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at ho
  obtain ⟨G, hG, hGo⟩ := returns_map_elim₄₈b _ _ _ ho
  obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
    (M.readFrame n.cache (M.toHealing n.st.core) r)
  obtain ⟨X, hX, hCX⟩ := facts.gr.preceq_grade2Block_of_g2
    (st := M.toHealing n.st.core)
    (Restated.actionFrame_g0On facts S Hs Xb hf hr hhor hv
      (facts.gr.lo_le_domain_of_window_start S hr hlo _) n hn fr0 hfr0)
    (Restated.actionFrame_g1On facts S Hs Xb hf hr hhor
      (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv)
      (facts.gr.lo_le_domain_of_window_start S hr hlo _) n hn fr1 hfr1)
    h₂ hactive hCclip x hx
  refine ⟨X, ?_, hCX⟩
  rw [← hGo, ← hX]
  exact facts.nd.ModelProperties_gradeContract_read_Q2 _ _ _ _ _ G hG x hx

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

/-- If `C` is formed as a G2 grade of the positive round `r` over the set, `v` is in
    `Hs (domain r .g0)`, `r`'s window opens at or after `lo`, and `C` is in the filtered tree of a
    node state `n` of `v`'s round-`r` action read, then every outcome of `n`'s candidate read is
    `some Q` for a descendant `Q` of `C`. -/
theorem namedGradeFormsAt_preceq_actionQ2On (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) {r : Round} (hr : 0 < r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) {C : Block V}
    (hforms : Restated.NamedGradeFormsAtOn M S rho Hs r C
      (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)))) {v : V}
    (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hactive : C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ o →
      ∃ Q : Block V, o = some Q ∧ Block.Preceq C Q := by
  have hvG2 : v ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hv
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hd
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) C
  have hbtrue : b = true := (hforms v hvG2).2 b hb
  subst hbtrue
  exact Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
    (hforms v hvG2).1 hb n hn hactive

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

/-- If `v` is in `Hs (domain r .g1)` and `r`'s window opens at or after `lo`, then for every node
    state `n` of `v`'s action read of the positive round `r`, a block `Q` that `n`'s candidate read
    can return is an ancestor of every outcome of `n`'s anchor read. -/
theorem actionQ2_preceq_actionAnchorOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g1))
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) :
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A →
      Block.Preceq Q A := by
  intro A hA
  set b := W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v with hb
  have hc := actionReadFrom_cache₄₈b facts S b r n hn
  have hfilt : M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
      M.get_filtered_block_tree (M.toHealing
        (M.ns_setClock S.E b.st (Restated.Vocabulary.Execution.Setup.a M S r)).core).toFG :=
    (actionReadFrom_filtered₄₈b facts S b r n hn).trans (setClock_filtered₄₈b facts S b _).symm
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hq
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim₄₈b _ _ _ hq
  obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
    (M.readFrame n.cache (M.toHealing n.st.core) r)
  have hGx := facts.nd.ModelProperties_gradeContract_read_Q2 _ _ _ _ _ G hG x hx
  have hq' : M.grade2Block
      (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (Restated.Vocabulary.Execution.Setup.a M S r))
        b.record n.cache).st.core)
      (M.readFrame (M.mkNode (M.ns_setClock S.E b.st (Restated.Vocabulary.Execution.Setup.a M S r))
          b.record n.cache).cache
        (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (Restated.Vocabulary.Execution.Setup.a M S r))
          b.record n.cache).st.core) r) ⇢ some Q := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.nd.mkNode_cache]
    obtain ⟨e0, e1, e2⟩ := actionReadFrom_readFrame_g₄₈b facts S b r r n hn
    refine (facts.gr.grade2Block_eq_of_phases e0 e1 e2 (some Q)).1 ?_
    refine (facts.gr.grade2Block_eq_of_filtered_eq _
      (hfilt.trans (facts.nd.store_with_cache_get_filtered_block_tree _ _).symm) (some Q)).1 ?_
    rw [← hGQ, hGx]
    exact hx
  have h := Restated.grade2_preceq_anchor_at_checkpointOn facts S rho Hs Xb hf hHs hHsXb v
    (Restated.Vocabulary.Execution.Setup.a M S r) r hv ⟨hr, le_rfl, hhor⟩ hlo n.cache hc Q hq'
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA
  obtain ⟨G', hG', hGA⟩ := returns_map_elim₄₈b _ _ _ hA
  obtain ⟨a', ha'⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r
    (M.readFrame n.cache (M.toHealing n.st.core) r).g1
  have hGa := facts.nd.ModelProperties_gradeContract_read_anchor _ _ _ _ _ G' hG' a' ha'
  have ha'' : M.anchor S.E S.hc
      (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (Restated.Vocabulary.Execution.Setup.a M S r))
        b.record n.cache).st.core) r
      (M.readFrame (M.mkNode (M.ns_setClock S.E b.st (Restated.Vocabulary.Execution.Setup.a M S r))
          b.record n.cache).cache
        (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (Restated.Vocabulary.Execution.Setup.a M S r))
          b.record n.cache).st.core) r).g1 ⇢ a' := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.nd.mkNode_cache, ← (actionReadFrom_readFrame_g₄₈b facts S b r r n hn).2.1]
    exact (facts.gr.anchor_eq_of_filtered_fg_root S.E S.hc r _
      (hfilt.trans (facts.nd.store_with_cache_get_filtered_block_tree _ _).symm)
      ((actionReadFrom_fg_root₄₈b facts S b r n hn).trans
        (facts.nd.store_with_cache_get_fg_root _ _).symm) a').1 ha'
  rw [← hGA, hGa]
  exact h a' ha''

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

/-- If `v` is in `Hs (domain r .g1)` and `r`'s window opens at or after `lo`, then for every node
    state `n` of `v`'s action read of the positive round `r` whose candidate read can return
    `some Q`, every ancestor of `Q` is an ancestor of every SG block that `n` selects. -/
theorem preceq_actionSGBlockAt_of_actionQ2On (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g1))
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) {C Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hCQ : Block.Preceq C Q) :
    let gc := M.gradeContract n.cache
    let st := M.toHealing n.st.core
    let kk := M.round_of S.hc st.s
    ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
    ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq C G := by
  intro gc st kk A2 hA2 G hG
  have hk : kk = r := by
    show M.round_of S.hc (M.toHealing n.st.core).s = r
    rw [Record.Model.HS.s, facts.sto.toHealing_s, actionReadFrom_s₄₈b facts S _ r n hn]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r
  obtain ⟨grades, hgrades⟩ := facts.gr.read_nonempty gc S.E S.hc st kk
  have heq : G = M.currentSGVote st grades :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc st kk A2 hA2 grades hgrades
      G hG
  rw [hk] at hgrades
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hq
  obtain ⟨G₀, hG₀, hG₀Q⟩ := returns_map_elim₄₈b _ _ _ hq
  obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
    (M.readFrame n.cache (M.toHealing n.st.core) r)
  have hQ2 : grades.Q2 = some Q :=
    (facts.nd.ModelProperties_gradeContract_read_Q2 _ _ _ _ _ grades hgrades x hx).trans
      ((facts.nd.ModelProperties_gradeContract_read_Q2 _ _ _ _ _ G₀ hG₀ x hx).symm.trans hG₀Q)
  have hanchor : Block.Preceq Q grades.anchor :=
    Restated.actionQ2_preceq_actionAnchorOn facts S Hs Xb hf hHs hHsXb hr hhor hv hlo n hn
      hq grades.anchor (nodeAnchor_of_read₄₈b S n r grades hgrades)
  rw [heq]
  apply facts.gr.preceq_currentSGVote_of_cases
  · exact Proofs.ModelProperties.Preceq_trans hCQ hanchor
  · intro q hq'
    rw [hQ2] at hq'
    cases hq'
    exact hCQ
  · intro hnone
    rw [hQ2] at hnone
    cases hnone

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

/-- A block `B` in the tree of `v`'s store in the world of `W` strictly before `read` is genesis, or
    a named block with erasure `B` was accepted by `v` along `W` at some index and instant
    `t < read`. -/
theorem block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (read : Time) {B : Block V}
    (hB : B ∈ (W (strictEventIndex rho read) v).st.core.T) :
    B = Block.genesis ∨
      ∃ (D : NamedBlock V) (i : Nat) (t : Time),
        D.erase = B ∧ Restated.Vocabulary.Execution.Run.acceptsAt M S rho W i v (.block D) t ∧
          t < read := by
  set N := strictEventIndex rho read with hN
  obtain ⟨D, hDbodies, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho N v
      (W N) (hf.onePath N).1 hB
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W N v).st (.block D) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hDbodies
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hf.onePath N D
      hprocessed with hgen | ⟨i, hiN, t, hacc⟩
  · exact Or.inl (by rw [← hDerase, hgen]; exact erase_named_genesis)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have heLt : e.time < read := time_lt_of_lt_strict₄₈b hf.sorted he hiN
    exact Or.inr ⟨D, i, t, hDerase, hacc, by simpa only [het] using heLt⟩

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- If `w` is in `Hs (S.a q)` and `S.a q` is inside the horizon, a vote `u` of an outcome of `w`'s
    raw inputs at any cutoff, read from the grade view of a node state of `v`'s action read of `q`,
    has its round in `q`'s window and confirms the root of every SG block that `w`'s action read of
    `u.round` selects. -/
theorem honestRawInput_confirmed_eq_actionCarrier_rootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {q : Round} (hhor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    {cutoff : Time} {v w : V}
    (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)))
    {u : Protocol.SGVote V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q)
    (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs (M.gradeView (M.toHealing n.st.core)) S.hc.η_SG q cutoff w ⇢ X)
    (hu : u ∈ X) :
    u.round ∈ M.latest_window S.hc.η_SG q ∧
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S u.round)) w) u.round,
        let gc := M.gradeContract n'.cache
        let st := M.toHealing n'.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G →
          u.confirmed = some G.root := by
  rw [actionReadFrom_gradeView₄₈b facts S _ q n hn
    (facts.ndRun.stateBeforeOf_reachedNode S rho _ (W _) (hf.onePath _).1 v)] at hX
  obtain ⟨a, -, hround, hproj, hwindow, hlt, hemit⟩ :=
    Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (Restated.Vocabulary.Execution.Setup.a M S q)
      cutoff v S.hc.η_SG q w hw X hX hu
  refine ⟨hwindow, ?_⟩
  have haEq := ((Restated.action_run_emissionOn facts S rho Hs Xb hf w a.round a).mp hemit).2.2
  have hconfU : u.confirmed = a.confirmed := by
    rw [← hproj]
    exact facts.sto.sgVote_confirmed a
  rw [← hround]
  intro n' hn' gc st kk A2 hA2 G hG
  have hnmem : n' ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho w a.round :=
    ⟨_, mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath _, hn'⟩
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n'.cache) S.E S.hc (S.node w)
    n'.st n'.record
  have hconfA := (Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho w
    a.round n' hnmem D hD A2 hA2 G hG).2.2
  rw [hconfU, haEq n' hn' D hD]
  exact hconfA

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- If `v` is in `Xb`, `w` is in `Hs (S.a q)` and `S.a q` is inside the horizon, a vote `u` of an
    outcome of `w`'s raw inputs, read from a node state `n` of `v`'s action read of `q`, whose
    confirmed root resolves to `head` in `n`'s tree has its round in `q`'s window, and `head` is
    every SG block that `w`'s action read of `u.round` selects. -/
theorem honestWindowInput_head_eq_actionCarrierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} (hhor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    {cutoff : Time} {v w : V}
    (hv : v ∈ Xb) (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)))
    {u : Protocol.SGVote V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q)
    (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs (M.gradeView (M.toHealing n.st.core)) S.hc.η_SG q cutoff w ⇢ X)
    (hu : u ∈ X)
    {head : Block V} (hconf : u.confirmed = some head.root)
    (hfind : Block.find? (M.gradeView (M.toHealing n.st.core)).T head.root = some head) :
    u.round ∈ M.latest_window S.hc.η_SG q ∧
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S u.round)) w) u.round,
        let gc := M.gradeContract n'.cache
        let st := M.toHealing n'.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G →
          head = G := by
  obtain ⟨hwindow, hcarrierAll⟩ :=
    Restated.honestRawInput_confirmed_eq_actionCarrier_rootOn facts S Hs Xb hf hHs hhor hw n
      hn X hX hu
  refine ⟨hwindow, ?_⟩
  intro n' hn' gc st kk A2 hA2 G hG
  have hcarrier := hcarrierAll n' hn' A2 hA2 G hG
  have hroot := Option.some.inj (hconf.symm.trans hcarrier)
  have hheadMem : head ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T, actionReadFrom_T₄₈b facts S _ q n hn] at h
    exact h
  obtain ⟨H, hHerase, hHrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hv
      (Restated.Vocabulary.Execution.Setup.a M S q) hheadMem
  have hcarrierMem := Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime
    facts S rho w u.round _ (mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath _) n' hn'
    A2 hA2 G hG
  obtain ⟨D, hDerase, hDrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
      (Restated.Vocabulary.Execution.Setup.a M S u.round) hcarrierMem
  have hrootEq : H.erase.root = D.erase.root := by
    rw [hHerase, hDerase]
    exact hroot
  have hHD : H.erase = D.erase :=
    Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHrun hDrun hrootEq
  rw [← hHerase, ← hDerase]
  exact hHD

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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- If `S.a q` is inside the horizon and every SG block of the round-`(q − 1)` action read of every
    member of `Hs (S.a q)` is an ancestor of `Can`, then for every reader `v` in `Xb` and author `w`
    in `Hs (S.a q)` whose round-`(q − 1)` vote is among the interpreted inputs of `v`'s action read
    of `q`, the head of the latest such input, when it resolves in `v`'s tree, is an ancestor of
    `Can`. -/
theorem nextActionBatchAligned_preceq_of_carriersPreceq_at_latestOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} (hhor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon) {Can : Block V}
    (hcarriers : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
        let gc := M.gradeContract n'.cache
        let st := M.toHealing n'.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq G Can) :
    ∀ v ∈ Xb, ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w) (q - 1),
      ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.gradeContract n'.cache) S.E S.hc (S.node w) n'.st n'.record ⇢ D →
      ∀ Y : Finset (Protocol.SGVote V),
        M.interpretedInputs (M.gradeView (M.toHealing n.st.core)) n.st.core.F S.hc.η_SG q
          (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc q) w ⇢ Y →
      M.sgVote D.2.2.erase ∈ Y →
      ∀ u ∈ Y, (∀ x ∈ Y, x.round ≤ u.round) →
        ∀ head : Block V, u.confirmed = some head.root →
          Block.find? (M.gradeView (M.toHealing n.st.core)).T head.root = some head →
          Block.Preceq head Can := by
  intro v hv w hw n hn n' hn' D hD Y hY hprev u hu hmax head hconf hfind
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing n.st.core)) S.hc.η_SG q
    (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc q) w
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing n.st.core)) n.st.core.F
    (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc q) u
  have hraw : u ∈ R := ((facts.gr.mem_interpretedInputs_iff Y hY R hR b hb).mp hu).1
  obtain ⟨hwindow, hheadAll⟩ :=
    Restated.honestWindowInput_head_eq_actionCarrierOn facts S Hs Xb hf hHs hHsXb hhor hv hw
      n hn R hR hraw hconf hfind
  have hnmem : n' ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho w (q - 1) :=
    ⟨_, mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath _, hn'⟩
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n'.cache) S.E S.hc
    (M.toHealing n'.st.core) (M.round_of S.hc (M.toHealing n'.st.core).s)
  obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n'.cache) S.E S.hc
    (M.toHealing n'.st.core) (M.round_of S.hc (M.toHealing n'.st.core).s) A2
  have hge : q - 1 ≤ u.round := by
    have hle := hmax _ hprev
    have hround : (M.sgVote D.2.2.erase).round = q - 1 := by
      rw [facts.sto.sgVote_round]
      exact (Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho w (q - 1)
        n' hnmem D hD A2 hA2 G hG).2.1
    rwa [hround] at hle
  have hlt : u.round < q := (facts.fc.window_bounds hwindow).2
  have hround : u.round = q - 1 :=
    Nat.le_antisymm (Nat.le_sub_one_of_lt hlt) hge
  have hhead := hheadAll
  rw [hround] at hhead
  rw [hhead n' hn' A2 hA2 G hG]
  exact hcarriers w hw n' hn' A2 hA2 G hG

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

/-- If `w` is in `Hs (view_freeze s)` and `lo ≤ view_freeze s`, then for every outcome `Q` of `w`'s
    voter-processed tree of the store its slot-`(s + 1)` vote duty reads, every ancestor of a block
    of `Q` is in `Q`. -/
theorem ancestorProcessed_of_voterProcessedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s)) {B : Block V}
    (Q : Finset (Block V))
    (hQ : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ Q)
    (hBmem : B ∈ Q)
    (hgat : lo ≤ M.view_freeze S.E s) :
    ∀ C : Block V, Block.Preceq C B → C ∈ Q := by
  set kv := strictEventIndex rho (M.vote_time S.E (s + 1)) with hkv
  set kf := strictEventIndex rho (M.view_freeze S.E s) with hkf
  set duty := Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W kv w).st.core (s + 1) with hduty
  have hmemV := mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath (M.vote_time S.E (s + 1))
  have hmemF := mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath (M.view_freeze S.E s)
  have hslot : (M.toHealing duty).s = s + 1 := by
    rw [Record.Model.HS.s, facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.Optimistic.voteDutyStore_slot facts S rho w (s + 1) duty
      ⟨(W kv w).st, ⟨W kv, hmemV, rfl⟩, rfl⟩
  have hdutyT : duty.T = (W kv w).st.core.T := voteStore_T₄₈b facts S _ _
  have hdutyStamp : duty.timestamp_block = (W kv w).st.core.timestamp_block :=
    voteStore_timestamp_block₄₈b facts S _ _
  have hpcV := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
    (M.vote_time S.E (s + 1)) w (W kv) hmemV
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpcV
  rw [facts.sto.toHealing_gs_T] at hpcV
  intro C hCB
  rw [hslot] at hQ
  have hcases := facts.fc.voter_processed_block_tree_cases S.E _ _ Q hQ hBmem
  rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_T, facts.sto.toHealing_gs_timestamp_block]
    at hcases
  rcases hcases with ⟨hBT, hstamp | ⟨P, hP, hPs, hBP⟩⟩
  · rw [hdutyT] at hBT
    rw [hdutyStamp] at hstamp
    obtain ⟨Bn, hBn, hBnErase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
        (M.vote_time S.E (s + 1)) w (W kv) hmemV hBT
    have hstampBn : stampedBefore (W kv w).st.core.timestamp_block
        (M.view_freeze S.E s) Bn.erase = true := by
      simpa only [hBnErase] using hstamp
    have hBnFreeze :=
      Restated.body_mem_stateBeforeTime_of_public_stampedBeforeOn facts S rho Hs Xb hf hw
        (Restated.Vocabulary.Protocol.publicTime_view_freeze facts S s) hgat hBn hstampBn
    have hcohFreeze := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.view_freeze S.E s) w (W kf) hmemF).1.1.1
    have hBfreeze : B ∈ (W kf w).st.core.T := by
      rw [hcohFreeze.1]
      exact Finset.mem_image.mpr ⟨Bn, hBnFreeze, hBnErase⟩
    have hpcF := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.view_freeze S.E s) w (W kf) hmemF
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpcF
    rw [facts.sto.toHealing_gs_T] at hpcF
    have hCfreeze : C ∈ (W kf w).st.core.T :=
      Proofs.Records.mem_of_preceq hpcF.2 C B hBfreeze (preceq_eq_true_iff_Preceq.mpr hCB)
    obtain ⟨Cn, hCn, hCnErase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
        (M.view_freeze S.E s) w (W kf) hmemF hCfreeze
    have hCnStamp := Restated.held_body_stampedBefore_stateBeforeTimeOn facts
      S rho Hs Xb hf w (M.view_freeze S.E s) Cn hCn
    have hcarry := Restated.q10_strict_body_carryOn facts S rho Hs Xb hf
      w (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)) hCn
    have hcohDuty := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.vote_time S.E (s + 1)) w (W kv) hmemV).1.1.1
    have hCtree : C ∈ (W kv w).st.core.T := by
      rw [hcohDuty.1]
      exact Finset.mem_image.mpr ⟨Cn, hcarry.1, hCnErase⟩
    have hCstampTime : stampedBefore (W kv w).st.core.timestamp_block
        (M.view_freeze S.E s) C = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hCnStamp ⊢
      rw [← hCnErase, hcarry.2]
      exact hCnStamp
    have hCstamp : stampedBefore (M.toHealing duty).toFG.toSG.toGoldfishStore.timestamp_block
        (M.view_freeze S.E (s + 1 - 1)) C = true := by
      rw [facts.sto.toHealing_gs_timestamp_block, Nat.add_sub_cancel, hdutyStamp]
      exact hCstampTime
    exact facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _
      (by rw [facts.sto.toHealing_gs_T, hdutyT]; exact hCtree) hCstamp Q hQ
  · rw [hdutyT] at hP
    have hCP : Block.Preceq C P := preceq_trans_Preceq hCB hBP
    have hCT : C ∈ (W kv w).st.core.T :=
      Proofs.Records.mem_of_preceq hpcV.2 C P hP (preceq_eq_true_iff_Preceq.mpr hCP)
    exact facts.fc.mem_voter_processed_block_tree_of_proposal S.E _ _
      (by rw [facts.sto.toHealing_gs_T, hdutyT]; exact hCT)
      (by rw [facts.sto.toHealing_gs_T, hdutyT]; exact hP) hPs hCP Q hQ

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

/-- If `w` is in `Hs (view_freeze s)` with `lo ≤ view_freeze s`, `C` is an ancestor of a block `D`
    of `w`'s voter-processed tree at slot `s + 1`'s vote duty, and at the vote-duty read `n` the
    stored height of `D` is at least `n`'s `h_max − 1` and `n`'s FG root is an ancestor of `C`, then
    `C`, and every block strictly between every outcome of `n`'s anchor read and `C`, is in every
    outcome of the voter's filtered tree of `n`'s store. -/
theorem namedCandidatePath_of_processedBandDescendant_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s)) {C D : Block V}
    (hCD : Block.Preceq C D)
    (Q : Finset (Block V))
    (hQ : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ Q)
    (hDprocessed : D ∈ Q)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core)
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hband : (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core.h_max - 1 ≤
      ((M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core.σ D).h)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core).toFG) C)
    (hgat : lo ≤ M.view_freeze S.E s) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ Y : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Y →
      C ∈ Y ∧
        ∀ A : Block V,
          Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
          ∀ B : Block V, Block.Preceq A B → B ≠ A → Block.Preceq B C → B ≠ C → B ∈ Y := by
  intro read Y hY
  set kv := strictEventIndex rho (M.vote_time S.E (s + 1)) with hkv
  have hmemV := mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath (M.vote_time S.E (s + 1))
  have hreadSt : read.st = M.store_with_cache
      (M.ns_setClock S.E (W kv w).st (M.vote_time S.E (s + 1))) c := facts.nd.mkNode_st _ _ _
  have hQr : M.voter_processed_block_tree S.E
      (M.toHealing read.st.core).toFG.toSG.toGoldfishStore read.st.core.s ⇢ Q := by
    rw [hreadSt, facts.nd.store_with_cache_core_s,
      facts.nd.store_with_cache_voter_processed_block_tree, ← voteStore_eq_setClock₄₈b facts,
      ← facts.sto.toHealing_gs_s]
    exact hQ
  have hancestor : ∀ B : Block V, Block.Preceq B D → B ∈ Q := fun B hBD =>
    Restated.ancestorProcessed_of_voterProcessedOn facts S Hs Xb hf hw (s := s) (B := D) Q hQ
      hDprocessed hgat B hBD
  have hFroot : Block.Preceq read.st.core.F
      (M.get_fg_root (M.toHealing read.st.core).toFG) := by
    have hFJ : Block.Preceq (M.toHealing read.st.core).toFG.F
        (M.toHealing read.st.core).toFG.J := by
      show Block.Preceq (M.toHealing (M.mkNode _ _ c).st.core).toFG.F
        (M.toHealing (M.mkNode _ _ c).st.core).toFG.J
      rewrite [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
      exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
        S rho (M.vote_time S.E (s + 1)) w (W kv) hmemV
    have h := facts.fc.preceq_get_fg_root_of_F (st := (M.toHealing read.st.core).toFG)
      (preceq_eq_true_iff_Preceq.mpr hFJ)
    rw [preceq_eq_true_iff_Preceq, facts.sto.Sts_toHealing_F] at h
    exact h
  have hmem : ∀ B : Block V,
      Block.Preceq (M.get_fg_root (M.toHealing read.st.core).toFG) B →
      Block.Preceq B C → B ∈ Y := by
    intro B hrootB hBC
    exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E read.st.core read.st.core.s Q hQr
      (hancestor B (preceq_trans_Preceq hBC hCD)) (preceq_trans_Preceq hFroot hrootB)
      hDprocessed (preceq_trans_Preceq hBC hCD) hband hrootB Y hY
  refine ⟨hmem C hroot (Proofs.ModelProperties.Preceq_self C), ?_⟩
  intro A hA B hAB _ hBC _
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA
  obtain ⟨G, hG, hGA⟩ := returns_map_elim₄₈b _ _ _ hA
  obtain ⟨a', ha'⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing read.st.core)
    (M.round_of S.hc read.st.core.s)
    (M.readFrame read.cache (M.toHealing read.st.core) (M.round_of S.hc read.st.core.s)).g1
  have hGa := facts.nd.ModelProperties_gradeContract_read_anchor _ _ _ _ _ G hG a' ha'
  have hrootAnchor : Block.Preceq (M.get_fg_root (M.toHealing read.st.core).toFG) A := by
    rw [← hGA, hGa]
    exact Restated.Vocabulary.Proofs.NamedOutageClosure.fg_root_preceq_anchor facts S.E S.hc
      (M.toHealing read.st.core) (M.round_of S.hc read.st.core.s) _ a' ha'
  exact hmem B (preceq_trans_Preceq hrootAnchor hAB) hBC

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

/-- The same conclusion as `namedCandidatePath_of_processedBandDescendant_coreOn`, under the same
    hypotheses. -/
theorem namedCandidatePath_of_processedBandDescendantOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s)) {C D : Block V}
    (hCD : Block.Preceq C D)
    (Q : Finset (Block V))
    (hQ : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ Q)
    (hDprocessed : D ∈ Q)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core)
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hband : (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core.h_max - 1 ≤
      ((M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core.σ D).h)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core).toFG) C)
    (hgat : lo ≤ M.view_freeze S.E s) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ Y : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Y →
      C ∈ Y ∧
        ∀ A : Block V,
          Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
          ∀ B : Block V, Block.Preceq A B → B ≠ A → Block.Preceq B C → B ≠ C → B ∈ Y :=
  Restated.namedCandidatePath_of_processedBandDescendant_coreOn facts
    S Hs Xb hf hw hCD Q hQ hDprocessed c hc hband hroot hgat

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

/-- Along the path `W` of the bundle, if more than half of every slot's committee is in the set for
    the slot's confirmation instant, and every committee member of slot `s` in the set for `s`'s
    vote instant voted at slot `s` for a run block that is a descendant of `T1`, and also for one
    that is a descendant of `T2`, then `T1` and `T2` are compatible. -/
theorem sgTargetCompatible_of_honestVotesConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) {s : Slot} {T1 T2 : Block V}
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hT1 : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq T1 X))
    (hT2 : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq T2 X)) :
    Block.compatible T1 T2 = true := by
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hxcommittee, hxconf⟩ := Finset.mem_inter.mp hx
  have hxhonest : x ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hxconf
  obtain ⟨X1, hT1X1, hX1, he1⟩ := hT1 x hxhonest hxcommittee
  obtain ⟨X2, hT2X2, hX2, he2⟩ := hT2 x hxhonest hxcommittee
  have huv :
      (⟨x, s, X1.erase.root⟩ : GoldfishVote V) = ⟨x, s, X2.erase.root⟩ :=
    Restated.emits_gfVote_uniqueOn facts S Hs Xb hf he1 he2 rfl
  have hroot : X1.erase.root = X2.erase.root :=
    congrArg (fun u : GoldfishVote V => u.head) huv
  have hrootN : X1.root = X2.root :=
    (Proofs.NamedWire.erase_root X1).symm.trans (hroot.trans (Proofs.NamedWire.erase_root X2))
  have hX12 : X1 = X2 :=
    hf.rootCollisionFree.root_injective X1 X2 hX1 hX2 X1 X2
      (Or.inl (Proofs.NamedAncestry.named_self X1))
      (Or.inr (Proofs.NamedAncestry.named_self X2)) hrootN
  rw [← hX12] at hT2X2
  exact compatible_of_common_honest_goldfish_head hT1X1 hT2X2

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

/-- Along the path `W` of the bundle, if `w` is in `Xb`, `X` is a run block read through `Xb` along
    `W`, and `X`'s erasure is in the tree of the store `w`'s slot-`s` vote duty reads, with any
    cache `c`, then that store holds `X`'s erasure at `X`'s derived height. -/
theorem storedHeight_of_runBlock_mem_voteDutyReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) {s : Slot} {X : NamedBlock V}
    (hXrun : Restated.RunBlockOn M S rho W Xb X) (c : M.Cache)
    (hXmem : X.erase ∈
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record
        c).st.core.T) :
    ((M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record
        c).st.core.σ X.erase).h =
      (M.derive_named S.E S.cfg X).h := by
  rewrite [facts.nd.mkNode_st] at hXmem; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hXmem; rw [facts.hd.Sts_setClock_core_T] at hXmem
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_σ]
  have hmem := mem_stateBeforeTime_path₄₈b S rho hf.sorted W hf.onePath (M.vote_time S.E s)
  obtain ⟨X', hX', hX'erase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.vote_time S.E s) w _ hmem hXmem
  have hX'run : Restated.RunBlockOn M S rho W Xb X' :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hX'
  have hX'eq : X' = X :=
    hf.rootCollisionFree.root_injective
      X' X hX'run hXrun X' X (Or.inl (Proofs.NamedAncestry.named_self X'))
        (Or.inr (Proofs.NamedAncestry.named_self X)) (by
          rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root X, hX'erase])
  have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (M.vote_time S.E s) w _ hmem X (by simpa only [hX'eq] using hX')
  exact congrArg (fun st => st.h) hview

end

end DecoupledConsensusModel.Sts.Restated
