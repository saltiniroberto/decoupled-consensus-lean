import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# Honest Goldfish votes at the slot after a confirmation

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, read along a path
`W` of the run: the vote heads visible at the next vote duty, membership in a filtered tree, and the
honest Goldfish votes of slot `s + 1` descending from a block eligible at an honest confirmation of
slot `s`, with the second-slot cone of a round as a consequence.
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
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₇₇ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₇₇ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₇₇ S rho hsorted]
  exact (hW _).1

/-- `W (m + k)` is among the worlds the events `m` to `m + k - 1` of `rho` lead to from `W m`. -/
private theorem onePath_reach₇₇ {S : Setup V} {rho : Record.Run V}
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

/-- For `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of `rho` lead to from `W m`. -/
private theorem onePath_slice₇₇ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₇₇ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W`, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an ancestor
    of the one in `W n`. -/
private theorem F_mono_along₇₇ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₇₇ W hW hjn)

/-- On a path `W` of a run sorted by key, the finalized block of `v`'s core store in
    `W (strictEventIndex rho t)` is an ancestor of that store's FG root. -/
private theorem F_preceq_fgRoot_along₇₇ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
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
          S rho t v _ (mem_stateBeforeTime_along₇₇ hsorted hW t)))
  rw [facts.sto.Sts_toHealing_F] at hFroot
  exact preceq_eq_true_iff_Preceq.mp hFroot

/-- The core of a store with its clock set to `t` is the store `tickStore` stages from its core at
    `t`. -/
private theorem setClock_core_eq_tickStore₇₇ (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    (M.ns_setClock S.E st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S st.core t :=
  facts.hd.setClock_core_eq_store_with_t_s S.E st t

/-- The core of `n`'s store with its clock set to `t` is the store `tickStore` stages from `n`'s
    core store at `t`. -/
private theorem setClock_core_tickStore₇₇ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The store `tickStore` stages at `t` from `n`'s core store has the `h_max` of `n`'s core store. -/
private theorem tickStore_h_max₇₇ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [← setClock_core_eq_tickStore₇₇ facts S n.st t, facts.hd.setClock_core_h_max]

/-- The store `tickStore` stages at `t` from `n`'s core store has the FG root of `n`'s core store. -/
private theorem tickStore_fgRoot₇₇ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_fg_root (M.toHealing n.st.core).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store `tickStore` stages at `t` from `n`'s core store has the filtered block tree of `n`'s
    core store. -/
private theorem tickStore_filtered₇₇ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_filtered_block_tree
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
  facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- On a path `W` of a run sorted by key, the node state staged at `t` from `v`'s node state in
    `W (strictEventIndex rho t)`, with an outcome `c` of the cache update there, is one of `v`'s
    confirmation reads at `t`. -/
private theorem mkNode_mem_confirmationReadAt₇₇ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (t : Time) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) v).st.core.toHealing t
      (W (strictEventIndex rho t) v).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) v).st t)
        (W (strictEventIndex rho t) v).record c ∈
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v t :=
  ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₇₇ hsorted hW t, c, hc, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₇₇ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₇₇ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- For every node state `n`, the voter's filtered block tree at `n`'s slot, its two vote views and
    the in-tree head computed from them each have an outcome. -/
private theorem voterHead_outcome₇₇ (facts : Record.Facts M) (S : Setup V) (n : M.N) :
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
private theorem nodeAnchor_outcome₇₇ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  exact ⟨G.anchor, returns_map_intro₇₇ (fun g : Protocol.GradeRead V => g.anchor) _ G hG⟩

/-- Writing a grade cache `c` into a store preserves the confirmation-membership invariant. -/
private theorem invariant_store_with_cache₇₇ (facts : Record.Facts M) (E : Env V)
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

/-- For a world `x` before the `i`-th event of a run, every head the in-tree head computation can
    return at the node state staged at `t` from `v`'s node state in `x` with the cache `c` is in the
    tree of `v`'s core store in `x`. -/
private theorem head_mem_core_T₇₇ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (i : Nat) (x : V → M.N) (hx : x ∈ Record.stateBeforeOf M S rho i) (v : V) (t : Time)
    (c : M.Cache) :
    let n := M.mkNode (M.ns_setClock S.E (x v).st t) (x v).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
    H ∈ (x v).st.core.T := by
  intro n T hT L hL L' hL' H hH
  have hnst₀ : n.st = M.store_with_cache (M.ns_setClock S.E (x v).st t) c := facts.nd.mkNode_st _ _ _
  have hstT : n.st.core.T = (x v).st.core.T := by
    rw [hnst₀, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T]
  have hinvPre := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v
    x hx).1
  have hinv0 := facts.hd.invariant_clock S.E S.cfg (x v).st t hinvPre
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
    rw [hnst₀]
    exact invariant_store_with_cache₇₇ facts S.E S.cfg _ c hinv0
  have hrootMem : M.get_fg_root (M.toHealing n.st.core).toFG ∈ n.st.core.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts n.st hinv.1.2
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
  have hRmem : R ∈ n.st.core.T := by
    have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
      (M.toHealing n.st.core) _ _
      (by
        show M.get_fg_root (M.toHealing n.st.core).toFG ∈
          (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T
        rw [facts.sto.toHealing_gs_T]
        exact hrootMem) R
      ((facts.nd.gradeContract_sgRoot_eq_frameAnchor _ _ _ _ _ _).mp hR)
    have h' : R ∈ (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T := h
    rw [facts.sto.toHealing_gs_T] at h'
    exact h'
  have hHmem := facts.fc.Sts_get_head_in_tree_with_layer_mem _ S.E S.hc _ T L L' _ R hR hRmem
    (facts.hd.Sts_voter_filtered_block_tree_subset S.E n.st.core n.st.core.s T hT) H hH
  rw [hstT] at hHmem
  exact hHmem

/-- If `GenuineConfirmation` holds for `B` at `st`, slot `s` and the contract `contract`, then some
    outcome of the confirmation votes of `st` at `s` and some choice `sc` of a Goldfish score
    outcome per block make the count of the late voters less than twice `sc B`. -/
private theorem genuine_eligible₇₇ (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
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
    returns_map_intro₇₇ _ _ _ htm
  have hu := returns_map_intro₇₇
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

/-- The Goldfish vote instant of slot `s + 1` is at or before the confirmation instant of slot `s`. -/
theorem vote_time_succ_le_confirmation_time_l77 (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E (s + 1) ≤ M.confirmation_time S.E s :=
  (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
    (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)

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

/-- Along the path `W` of `hf`, if `u` is in the set `Hs` for `vote_time s`, `w` in the set for
    `view_freeze s`, `lo ≤ proposal_time s`, slot `s`'s confirmation instant is in the horizon, and
    the FG root of `w`'s vote store at `s + 1` is an ancestor of `B`, then every head `H` of `u`'s
    vote duty at `s` with `B ⪯ H` is in the tree of `w`'s store in
    `W (strictEventIndex rho (vote_time (s + 1)))`, stamped there before `view_freeze s`. -/
theorem voteHeadVisible_at_nextDuty_confOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {u w : V} {s : Slot} (hu : u ∈ Hs (M.vote_time S.E s))
    (hw : w ∈ Hs (M.view_freeze S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) B)
    (cu : M.Cache)
    (hcu : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) u).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) u).cache ⇢ cu) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
    Block.Preceq B H →
      H ∈ (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.T ∧
      stampedBefore
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.timestamp_block
        (M.view_freeze S.E s) H = true := by
  intro n T hT L hL L' hL' H hH hBhead
  have hinst := facts.sch.slot_instants_l55 S.E s
  have hΔ := S.E.Δ_pos
  have hHVpreU : H ∈ (W (strictEventIndex rho (M.vote_time S.E s)) u).st.core.T :=
    head_mem_core_T₇₇ facts S (strictEventIndex rho (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s))) (hf.onePath _).1 u (M.vote_time S.E s) cu
      T hT L hL L' hL' H hH
  rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts S Hs Xb hf u
      (M.vote_time S.E s) hHVpreU with
    hgen | ⟨D, i, t, hDeq, hacc, ht⟩
  · rw [hgen]
    exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
      (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot D]
      exact Nat.zero_lt_of_lt
        (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
    have hBD : Block.Preceq B D.erase := by
      rw [hDeq]
      exact hBhead
    have htSupport : t < M.support_cutoff S.E s := by
      linarith [hinst.1, hinst.2.1]
    have hgstCut : lo ≤ M.support_cutoff S.E s := by
      linarith [hinst.2.1]
    have hfreezeVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
      (facts.sch.view_freeze_lt_vote_time_succ S.E s).le
    have hfreezeHor : M.view_freeze S.E s ≤ rho.horizon :=
      hfreezeVote.trans
        ((Restated.vote_time_succ_le_confirmation_time_l77 facts S s).trans hhor)
    have hproposalVote : M.proposal_time S.E s ≤ M.vote_time S.E s :=
      (facts.sch.proposal_time_lt_vote_time S.E s).le
    have huSrc : u ∈ Hs (max t lo) := hHs _ _ (max_le ht.le (hpost.trans hproposalVote)) hu
    have hrootW : Block.Preceq
        (M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG) B := by
      have h := hroot
      rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₇₇ facts] at h
      exact h
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w D.erase
        (M.view_freeze S.E s) := by
      apply Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb huSrc hw hDpos hacc htSupport hgstCut
          (by linarith [hinst.2.1, hinst.2.2.1]) hfreezeHor
      intro j hj
      have hjw : j ≤ strictEventIndex rho (M.vote_time S.E (s + 1)) :=
        hj.trans (strict_filter_length_mono rho hfreezeVote)
      exact preceq_trans_Preceq (F_mono_along₇₇ facts S hf.onePath w hjw)
        (preceq_trans_Preceq (F_preceq_fgRoot_along₇₇ facts S hf.sorted hf.onePath w _)
          (preceq_trans_Preceq hrootW hBD))
    have hvis := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hfreezeVote
    rw [hDeq] at hvis
    exact hvis

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

/-- If `w ∈ Xb` holds `X` in its store in `W (strictEventIndex rho read)`, `X` erases the run block
    `Xn`, `C ⪯ X`, that store's `h_max` is at most `h(Xn) + 1`, and its FG root is an ancestor of
    `C`, then `C` is in that store's filtered tree. -/
theorem filtered_of_viableDescendantOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) {read : Time}
    {C X : Block V} {Xn : NamedBlock V}
    (hX : X ∈ (W (strictEventIndex rho read) w).st.T)
    (hXerase : Xn.erase = X) (hXrun : Restated.RunBlockOn M S rho W Xb Xn)
    (hCX : Block.Preceq C X)
    (hmax : (W (strictEventIndex rho read) w).st.h_max ≤
      (M.derive_named S.E S.cfg Xn).h + 1)
    (hrootC : Block.Preceq
      (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) C) :
    C ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG := by
  have hmem := mem_stateBeforeTime_along₇₇ hf.sorted hf.onePath read
  set wd := W (strictEventIndex rho read) with hwd
  have hX' : X ∈ (wd w).st.core.T := hX
  have hmax' : (wd w).st.core.h_max ≤ (M.derive_named S.E S.cfg Xn).h + 1 := hmax
  have hCT : C ∈ (wd w).st.core.T :=
    Restated.ancestor_mem_storeBeforeTimeOn facts S Hs Xb hf hX hCX
  have hFroot : Block.Preceq (wd w).st.core.F
      (M.get_fg_root (M.toHealing (wd w).st.core).toFG) :=
    F_preceq_fgRoot_along₇₇ facts S hf.sorted hf.onePath w read
  obtain ⟨D', hD'mem, hD'erase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho read w
      wd hmem hX'
  have hD'run : Restated.RunBlockOn M S rho W Xb D' :=
    Restated.runBlockOf_of_stateBeforeTime_memOn_HeightProgressSeedRegime facts S Hs Xb hf hw read
      hD'mem
  have hDeq : D' = Xn :=
    Restated.runBlock_unique_of_erase_eqOn_HeightProgressSeedRegime facts hf hD'run hXrun
      (hD'erase.trans hXerase.symm)
  have hview :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho read w wd hmem
      D' hD'mem
  rw [hD'erase, hDeq] at hview
  exact facts.fc.mem_get_filtered_block_tree_of_parts _
    (by rw [facts.sto.toHealing_T]; exact hCT)
    (by rw [facts.sto.ModelProperties_toHealing_F]; exact preceq_trans_Preceq hFroot hrootC)
    (by rw [facts.sto.toHealing_T]; exact hX') hCX
    (by
      rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ, hview]
      exact Nat.sub_le_iff_le_add.mpr hmax')
    hrootC

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

/-- Along the path `W` of `hf`, if `T` is eligible at `v`'s confirmation of slot `s`, `T ⪯ C ⪯ Hn`
    for a run block `Hn` erasing to `u`'s vote-duty head at `s`, and `w`'s vote store at `s + 1` has
    `h_max ≤ h(Hn) + 1`, an FG root that is an ancestor of `T` and an anchor compatible with `T`,
    then some run block `X` read through `Xb` descends from `T` and `w` emits at `vote_time (s + 1)`
    the slot-`(s + 1)` Goldfish vote for `X`'s root. The validators `v`, `u` and `w` are in the sets
    `Hs` of their duty instants, and `w` is in slot `s + 1`'s committee. -/
theorem baseConeVoteWitness_of_supporter_hMaxOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v u w : V}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hu : u ∈ Hs (M.vote_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hwcommittee : w ∈ S.E.committee (s + 1))
    {T C : Block V} {Hn : NamedBlock V}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s))
      s ⇢ votes)
    {g : ℕ}
    (hg : M.goldfish_score S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).T votes votes s T ⇢ g)
    (heligible : M.voters_count S.E
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
            (M.confirmation_time S.E s)) s) s < 2 * g)
    (hTC : Block.Preceq T C)
    (cu : M.Cache)
    (hcu : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) u).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) u).cache ⇢ cu)
    {Tu : Finset (Block V)} {Lu Lu' : Finset (GoldfishVote V)} {Hu : Block V}
    (hTu : M.voter_filtered_block_tree S.E
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Tu)
    (hLu : M.voter_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Lu)
    (hLu' : M.voter_support_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Lu')
    (hHu : M.get_head_in_tree_with_layer
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).cache) S.E S.hc
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core) Tu Lu Lu'
      ((M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s - 1) ⇢ Hu)
    (hHerase : Hn.erase = Hu)
    (hHrun : Restated.RunBlockOn M S rho W Xb Hn)
    (hCH : Block.Preceq C Hn.erase)
    (hmax : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max ≤
      (M.derive_named S.E S.cfg Hn).h + 1)
    (hrootT : Block.Preceq (M.get_fg_root
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) T)
    (cw : M.Cache)
    (hcw : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ cw)
    {A : Block V}
    (hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cw)
      (M.round_of S.hc (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cw).st.core.s) ⇢ A)
    (hanchor : Block.compatible A T = true)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    ∃ X : NamedBlock V, Block.Preceq T X.erase ∧ Restated.RunBlockOn M S rho W Xb X ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote ⟨w, s + 1, X.erase.root⟩)
        (M.vote_time S.E (s + 1)) := by
  set iw := strictEventIndex rho (M.vote_time S.E (s + 1)) with hiw
  set nw := M.mkNode (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1)))
    (W iw w).record cw with hnw
  have hinst := facts.sch.slot_instants_l55 S.E s
  have hΔ := S.E.Δ_pos
  have hread : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    (Restated.vote_time_succ_le_confirmation_time_l77 facts S s).trans hhor
  have hfreezeVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
    (facts.sch.view_freeze_lt_vote_time_succ S.E s).le
  have hwFreeze : w ∈ Hs (M.view_freeze S.E s) := hHs _ _ hfreezeVote hw
  have hloFreeze : lo ≤ M.view_freeze S.E s := by
    linarith [hinst.2.2.1]
  have hloVote : lo ≤ M.vote_time S.E (s + 1) := hloFreeze.trans hfreezeVote
  have hTH : Block.Preceq T Hn.erase := preceq_trans_Preceq hTC hCH
  have hTHead : Block.Preceq T Hu := by
    rw [← hHerase]
    exact hTH
  have hvisible := Restated.voteHeadVisible_at_nextDuty_confOn facts S Hs Xb hf hHs hHsXb hu
    hwFreeze hpost hhor hrootT cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu hTHead
  have hvisT : Hu ∈ (W iw w).st.core.T := hvisible.1
  have hvisStamp : stampedBefore (W iw w).st.core.timestamp_block (M.view_freeze S.E s) Hu = true :=
    hvisible.2
  have hdutyEq : (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core =
      Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W iw w).st.core (s + 1) :=
    setClock_core_eq_tickStore₇₇ facts S _ _
  have hs1 : (M.toHealing (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core).s =
      s + 1 :=
    (facts.sto.toHealing_s _).trans
      ((facts.hd.Sts_setClock_core_s S.E _ _).trans (facts.sch.slotOf_vote_time S.E (s + 1)))
  obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core).toFG.toSG.toGoldfishStore
    (M.toHealing (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core).s
  have hHprocessed : Hn.erase ∈ P := by
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T, facts.hd.Sts_setClock_core_T, hHerase]
      exact hvisT
    · rw [hs1, Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block,
        facts.hd.setClock_core_timestamp_block, hHerase]
      exact hvisStamp
  have hmaxW : (W iw w).st.core.h_max ≤ (M.derive_named S.E S.cfg Hn).h + 1 := by
    have h := hmax
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₇₇ facts] at h
    exact h
  have hrootW : Block.Preceq (M.get_fg_root (M.toHealing (W iw w).st.core).toFG) T := by
    have h := hrootT
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₇₇ facts] at h
    exact h
  have hTfilteredPre : T ∈ M.get_filtered_block_tree (M.toHealing (W iw w).st.core).toFG :=
    Restated.filtered_of_viableDescendantOn facts S Hs Xb hf (hHsXb _ hw)
      hvisible.1 hHerase hHrun hTHead hmaxW hrootW
  have hTfiltered : T ∈ M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core).toFG := by
    rw [hdutyEq, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_filtered₇₇ facts]
    exact hTfilteredPre
  have hmax' : (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core.h_max ≤
      (M.derive_named S.E S.cfg Hn).h + 1 := by
    rw [facts.hd.setClock_core_h_max]
    exact hmaxW
  have hcand := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts S Hs Xb hf
    hHsXb hwFreeze P hP hHprocessed hHrun hTH hTfiltered hmax' hloFreeze
  rw [hdutyEq] at hP hcand
  have hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W iw w).st.core (s + 1))) ⇢
      M.get_filtered_block_tree_from
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W iw w).st.core
          (s + 1))).toFG P := by
    unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
    exact (returns_bind_iff₇₇ _ _ _).mpr ⟨P, hP, (Record.returns_pure _ _).2 rfl⟩
  have hnmem : nw ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
    mkNode_mem_confirmationReadAt₇₇ hf.sorted hf.onePath w (M.vote_time S.E (s + 1)) cw hcw
  have h3 := Restated.nextVoteAdoption_of_recovery_after_gst_compatibleOn facts S Hs Xb hf
    hHs hHsXb hv hw hpost hhor cw hcw hrootT hA hanchor hK hcand hrun
  rcases h3 with hbelow | hd
  · obtain ⟨Tr, L, L', H, hT, hL, hL', hH⟩ := voterHead_outcome₇₇ facts S nw
    have hAH := Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts S rho
      w (s + 1) nw hnmem A hA Tr hT L hL L' hL' H hH
    obtain ⟨X, hXerase, hXrun⟩ := Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf
      (hHsXb _ hw) (s + 1) cw hcw Tr hT L hL L' hL' H hH
    refine ⟨X, ?_, hXrun, ?_⟩
    · rw [hXerase]
      exact preceq_trans_Preceq hbelow hAH
    · rw [hXerase]
      exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos s)
        hwcommittee hread hloVote cw hcw hrun Tr hT L hL L' hL' H hH
  · exact Restated.honestVoteWitness_of_nextVoteAdoptionOn facts S rho W Hs Xb _ s T nw hnmem
      hvotes hg heligible hw hwcommittee hd

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

/-- Along the path `W` of `hf`, if `GenuineConfirmation` holds for `C` at `v`'s confirmation store
    and slot `s`, `T ⪯ C`, some member `u` of the set for `vote_time s` has a vote-duty head named
    by a run block `Hn` with `C ⪯ Hn`, and every member `w` of the set for `vote_time (s + 1)` has
    an FG root comparable with `T` (with `h_max ≤ h(Hn) + 1` when that root is an ancestor of `T`)
    and an anchor compatible with `T`, then every member of slot `s + 1`'s committee in that set
    emits a vote for the root of a run block descending from `T`. -/
theorem baseCone_succ_of_genuineSupporter_hMaxOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v : V} (hv : v ∈ Hs (M.confirmation_time S.E s))
    {T C : Block V}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s)
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ cv)
    (hC : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s))
      s C)
    (hTC : Block.Preceq T C)
    {u : V} (hu : u ∈ Hs (M.vote_time S.E s))
    (cu : M.Cache)
    (hcu : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) u).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) u).cache ⇢ cu)
    {Tu : Finset (Block V)} {Lu Lu' : Finset (GoldfishVote V)} {Hu : Block V}
    (hTu : M.voter_filtered_block_tree S.E
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Tu)
    (hLu : M.voter_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Lu)
    (hLu' : M.voter_support_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Lu')
    (hHu : M.get_head_in_tree_with_layer
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).cache) S.E S.hc
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core) Tu Lu Lu'
      ((M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s - 1) ⇢ Hu)
    {Hn : NamedBlock V}
    (hHerase : Hn.erase = Hu) (hHrun : Restated.RunBlockOn M S rho W Xb Hn)
    (hCH : Block.Preceq C Hn.erase)
    (hroot : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      Block.Preceq (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) T ∨
        Block.Preceq T (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG))
    (hmax : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      Block.Preceq (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) T →
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max ≤
          (M.derive_named S.E S.cfg Hn).h + 1)
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ cw →
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cw)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cw).st.core.s) ⇢ A →
        Block.compatible A T = true)
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun X => Block.Preceq T X) := by
  intro w hw hwcommittee
  set iw := strictEventIndex rho (M.vote_time S.E (s + 1)) with hiw
  obtain ⟨cw, hcw⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W iw w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W iw w).cache
  set nw := M.mkNode (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1)))
    (W iw w).record cw with hnw
  have hinst := facts.sch.slot_instants_l55 S.E s
  have hΔ := S.E.Δ_pos
  have hread : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    (Restated.vote_time_succ_le_confirmation_time_l77 facts S s).trans hhor
  have hloVote : lo ≤ M.vote_time S.E (s + 1) := by
    linarith [hinst.2.2.2.2.1]
  rcases hroot w hw with hcase1 | hcase2
  · obtain ⟨A, hA⟩ := nodeAnchor_outcome₇₇ facts S nw (M.round_of S.hc nw.st.core.s)
    obtain ⟨early, sc, hearly, hvotes, hsc, helig⟩ := genuine_eligible₇₇ facts
      (⟨hC.selected, hC.genuine⟩ : Restated.Vocabulary.Protocol.GenuineConfirmation M
        (contract := M.gradeContract cv) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)) s C)
    have hle := facts.fc.goldfish_score_le_of_Preceq S.E _ _ _ s hTC (sc C) (hsc C) (sc T) (hsc T)
    exact Restated.baseConeVoteWitness_of_supporter_hMaxOn facts S Hs Xb hf hHs hHsXb hv hu
      hw hwcommittee hpost hhor hvotes (hsc T) (lt_of_lt_of_le helig (Nat.mul_le_mul_left 2 hle))
      hTC cu hcu hTu hLu hLu' hHu hHerase hHrun hCH (hmax w hw hcase1)
      hcase1 cw hcw hA (hanchor w hw cw hcw A hA) (hrun w hwcommittee hw)
  · obtain ⟨Tr, L, L', H, hT, hL, hL', hH⟩ := voterHead_outcome₇₇ facts S nw
    have hnmem : nw ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
      mkNode_mem_confirmationReadAt₇₇ hf.sorted hf.onePath w (M.vote_time S.E (s + 1)) cw hcw
    have hstV : nw.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
    have hTX : Block.Preceq T H := by
      refine preceq_trans_Preceq ?_
        (Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts S rho w (s + 1)
          nw hnmem Tr hT L hL L' hL' H hH)
      rw [hstV]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rw [setClock_core_tickStore₇₇ facts S]
      exact hcase2
    obtain ⟨X, hXerase, hXrun⟩ := Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf
      (hHsXb _ hw) (s + 1) cw hcw Tr hT L hL L' hL' H hH
    refine ⟨X, ?_, hXrun, ?_⟩
    · show Block.Preceq T X.erase
      rw [hXerase]
      exact hTX
    · rw [hXerase]
      exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos s)
        hwcommittee hread hloVote cw hcw (hrun w hwcommittee hw) Tr hT L hL L' hL' H hH

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

/-- Along the path `W` of `hf`, if `1 ≤ c`, `v`'s live confirmation at its round-`c` action store
    satisfies `GenuineConfirmation` for the opening slot `o = opening_slot c`, `v`'s round-`c` SG
    block `G` is an ancestor of it, and the voters of slot `o + 1` have FG roots comparable with
    `G`, anchors compatible with it and the height bound `hmax`, then every member of slot `o + 1`'s
    committee in the set for its vote instant emits a vote for the root of a run block descending
    from `G`. -/
theorem secondSlotCone_of_clearGenuine_atBaseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {c : Round} (hc : 1 ≤ c)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hlive : ∃ C : Block V,
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc c)))
        (M.opening_slot S.hc c) C ∧
      C = n.live_confirmed)
    (hroot : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      Block.Preceq (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
            ((M.opening_slot S.hc c) + 1))).toFG) G ∨
        Block.Preceq G (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
            ((M.opening_slot S.hc c) + 1))).toFG))
    (hmax : ∀ u ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c))),
      ∀ cu : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) u).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc c))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) u).cache ⇢ cu →
      let nu := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) u).st
          (M.vote_time S.E (M.opening_slot S.hc c)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) u).record cu
      ∀ Tu : Finset (Block V), M.voter_filtered_block_tree S.E nu.st.core nu.st.core.s ⇢ Tu →
      ∀ Lu : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore nu.st.core.s ⇢ Lu →
      ∀ Lu' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore nu.st.core.s ⇢ Lu' →
      ∀ Hu : Block V, M.get_head_in_tree_with_layer (M.gradeContract nu.cache) S.E S.hc
          (M.toHealing nu.st.core) Tu Lu Lu' (nu.st.core.s - 1) ⇢ Hu →
      ∀ Hn : NamedBlock V,
      Hn.erase = Hu → Restated.RunBlockOn M S rho W Xb Hn →
      Block.Preceq n.live_confirmed Hn.erase →
      ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
        Block.Preceq (M.get_fg_root
            (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
              (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
              ((M.opening_slot S.hc c) + 1))).toFG) G →
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core
            ((M.opening_slot S.hc c) + 1)).h_max ≤
            (M.derive_named S.E S.cfg Hn).h + 1)
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st.core.toHealing
          (M.vote_time S.E ((M.opening_slot S.hc c) + 1))
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).cache ⇢ cw →
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc c) + 1)))
            (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc c) + 1))) w).record cw).st.core.s) ⇢ A →
        Block.compatible A G = true)
    (hclear : Block.Preceq G n.live_confirmed) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq G X) := by
  have hoPos : 0 < (M.opening_slot S.hc c) := facts.gr.opening_slot_pos_of_round_pos S.hc hc
  have hSc := Restated.a_eq_confirmation_opening_l58 facts S c
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have hpredProp : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
      M.proposal_time S.E ((M.opening_slot S.hc c)) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S hpredLt
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
  have hpostProp : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) :=
    hpost.trans hpredProp
  have hpostVoteO : lo ≤ M.vote_time S.E ((M.opening_slot S.hc c)) :=
    hpostProp.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _))
  have hcutO_le : M.support_cutoff S.E ((M.opening_slot S.hc c)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S c) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hconfOHor : M.confirmation_time S.E ((M.opening_slot S.hc c)) ≤ rho.horizon := by
    rw [← hSc]
    exact hhor
  have hvCut : v ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc c)) := hHs _ _ hcutO_le hv
  have hvConf : v ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc c)) := by
    rw [← hSc]
    exact hv
  obtain ⟨C, hgen, hCeq⟩ := hlive
  obtain ⟨cc, hcc, st, -, rfl⟩ := hn
  rw [facts.nd.mkNode_cache] at hgen
  rw [hSc] at hcc hgen
  have hclearC : Block.Preceq G C := by
    rw [hCeq]
    exact hclear
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
  have hrunO1 : ∀ w ∈ S.E.committee (M.opening_slot S.hc c + 1),
      w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc c + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc c + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc c + 1)) := by
    intro w _ hw j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc c + 1)) .g1 - S.E.Δ := by
      rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc c]
      exact hwinC
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  obtain ⟨x, hx, _hxCommittee, hCx⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts S Hs Xb hf hHs
      hHsXb hcom hvCut hoPos hpostVoteO hconfOHor cc hcc hgen hrunO
  have hxVote : x ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hx
  obtain ⟨cx, hcx⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) x).st.core.toHealing
    (M.vote_time S.E (M.opening_slot S.hc c))
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) x).cache
  obtain ⟨Tx, Lx, Lx', Hx, hTx, hLx, hLx', hHx⟩ := voterHead_outcome₇₇ facts S
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) x).st
        (M.vote_time S.E (M.opening_slot S.hc c)))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) x).record cx)
  have hCHx : Block.Preceq C Hx := hCx cx hcx Tx hTx Lx hLx Lx' hLx' Hx hHx
  obtain ⟨Hn, hHnErase, hHnRun⟩ :=
    Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hxVote)
      ((M.opening_slot S.hc c)) cx hcx Tx hTx Lx hLx Lx' hLx' Hx hHx
  have hCHn : Block.Preceq C Hn.erase := by
    rw [hHnErase]
    exact hCHx
  exact Restated.baseCone_succ_of_genuineSupporter_hMaxOn facts S Hs Xb hf hHs hHsXb
    hvConf hpostProp hconfOHor cc hcc hgen hclearC hxVote cx hcx hTx hLx hLx' hHx hHnErase hHnRun
    hCHn hroot
    (fun w hw hr => hmax x hxVote cx hcx Tx hTx Lx hLx Lx' hLx' Hx hHx Hn hHnErase hHnRun
      (by rw [← hCeq]; exact hCHn) w hw hr)
    hanchor hrunO1

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

end DecoupledConsensusModel.Sts.Restated
