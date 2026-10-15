import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_OpeningActiveCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Vocabulary.Protocol.Schedule.RecoveryHandoffCore
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Vote-duty heads, the base cone and the opening proposal

Theorems over a model `M : Record.Model V` and its facts, read along a path `W` of a run with the
admissible fields `hf`. A validator's read at a time `t` is the node state staged at `t` from its
node state in `W (strictEventIndex rho t)` with an outcome `c` of the cache update `M.onPhaseTick`
there. The theorems place a vote-duty head in the next duty's store, give the votes of slot
`s + 1`'s committee for run blocks descending from a confirmed block `T`, and show that a round's
opening proposal has a parent of height at least `Mh − 1` and is admitted and held by the members of
the set for its slot's vote time.
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

/-- In a run sorted by key, the worlds strictly before the time `t` are the worlds before the event
    of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₅b (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₅b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₅b S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₅b {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₆₅b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₅b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W`, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an ancestor
    of the one in `W n`. -/
private theorem F_mono_along₆₅b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₆₅b W hW hjn)

/-- On a path `W` of a run sorted by key, the finalized block of `v`'s core store in
    `W (strictEventIndex rho t)` is an ancestor of that store's FG root. -/
private theorem F_preceq_fgRoot_along₆₅b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
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
          S rho t v _ (mem_stateBeforeTime_along₆₅b hsorted hW t)))
  rw [facts.sto.Sts_toHealing_F] at hFroot
  exact preceq_eq_true_iff_Preceq.mp hFroot

/-- The core store of `st` with its clock set to `t` is the store `tickStore` stages from `st`'s
    core store at `t`. -/
private theorem setClock_core_eq_tickStore₆₅b (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    (M.ns_setClock S.E st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S st.core t :=
  facts.hd.setClock_core_eq_store_with_t_s S.E st t

/-- The store a tick at `t` stages from `n`'s core store has the tree of `n`'s core store. -/
private theorem tickStore_T₆₅b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [← setClock_core_eq_tickStore₆₅b facts S n.st t, facts.hd.Sts_setClock_core_T]

/-- The store a tick at `t` stages from `n`'s core store has the `h_max` of `n`'s core store. -/
private theorem tickStore_h_max₆₅b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [← setClock_core_eq_tickStore₆₅b facts S n.st t, facts.hd.setClock_core_h_max]

/-- The store a tick at `t` stages from `n`'s core store has the `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₆₅b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [← setClock_core_eq_tickStore₆₅b facts S n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

/-- The store a tick at `t` stages from `n`'s core store has the FG root of `n`'s core store. -/
private theorem tickStore_fgRoot₆₅b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_fg_root (M.toHealing n.st.core).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store a tick at `t` stages from `n`'s core store has the filtered block tree of `n`'s core
    store. -/
private theorem tickStore_filtered₆₅b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_filtered_block_tree
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
  facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- On a path `W` of a run sorted by key, the node state staged at `t` from `v`'s node state in
    `W (strictEventIndex rho t)`, with an outcome `c` of the cache update there, is one of `v`'s
    reads at `t`. -/
private theorem mkNode_mem_confirmationReadAt₆₅b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (t : Time) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) v).st.core.toHealing t
      (W (strictEventIndex rho t) v).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) v).st t)
        (W (strictEventIndex rho t) v).record c ∈
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v t :=
  ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₆₅b hsorted hW t, c, hc, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₅b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₅b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₆₅b {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- The voter candidate tree of the core store of `st` with the cache `c` written in can return `K`
    exactly when the voter candidate tree of `st`'s own core store can. -/
private theorem candidateTree_store_with_cache₆₅b (facts : Record.Facts M) (E : Env V) (st : M.NS)
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
  rw [returns_bind_iff₆₅b, returns_bind_iff₆₅b]
  constructor
  · rintro ⟨P, hP1, hK⟩
    have hP0 := (hP P).1 hP1
    exact ⟨P, hP0, by rw [← hfrom P hP0]; exact hK⟩
  · rintro ⟨P, hP0, hK⟩
    exact ⟨P, (hP P).2 hP0, by rw [hfrom P hP0]; exact hK⟩

/-- For every node state `n`, the voter's filtered block tree of `n`'s core store, its two vote
    views and the in-tree head computed from them can each return a value. -/
private theorem voterHead_outcome₆₅b (facts : Record.Facts M) (S : Setup V) (n : M.N) :
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
private theorem nodeAnchor_outcome₆₅b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  exact ⟨G.anchor, returns_map_intro₆₅b (fun g : Protocol.GradeRead V => g.anchor) _ G hG⟩

/-- Every block the SG root under the grade contract of `n`'s cache can return at round `r` is the
    block `A` the anchor of `n` at `r` can return. -/
private theorem sgRoot_eq_nodeAnchor₆₅b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (r : Round) {A R : Block V}
    (hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A)
    (hR : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ R) :
    R = A := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA
  obtain ⟨G, hG, hGA⟩ := returns_map_elim₆₅b _ _ _ hA
  have ha := (facts.nd.gradeContract_sgRoot_eq_frameAnchor _ _ _ _ _ _).mp hR
  have h := facts.nd.ModelProperties_gradeContract_read_anchor _ _ _ _ _ G hG R ha
  exact h.symm.trans hGA

/-- If the store `st` satisfies the confirmation-membership invariant, so does `st` with the grade
    cache `c` written into it. -/
private theorem invariant_store_with_cache₆₅b (facts : Record.Facts M) (E : Env V)
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
private theorem head_mem_core_T₆₅b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
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
    exact invariant_store_with_cache₆₅b facts S.E S.cfg _ c hinv0
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

/-- Every outcome of the early confirmation votes of `st` at slot `s` is a subset of the late
    confirmation votes. -/
private theorem confEarly_subset_late₆₅b (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₆₅b _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- Every outcome `votes` of the counted confirmation votes of `st` at slot `s` comes with an
    outcome `early` of the early confirmation votes such that `early`, the late confirmation votes
    and `votes` have the numerator's shape. -/
private theorem confNumerator₆₅b (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot)
    (votes : Finset (GoldfishVote V))
    (hvotes : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ votes) :
    ∃ early, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ early ∧
      Restated.Vocabulary.Protocol.Numerator M early
        (Restated.Vocabulary.Protocol.confLate M E st s) votes := by
  obtain ⟨e, he, rfl⟩ := returns_map_elim₆₅b _ _ _ hvotes
  exact ⟨e, he, ⟨confEarly_subset_late₆₅b facts E st s e he, rfl⟩⟩

/-- If `GenuineConfirmation` holds for `B` at `st` and slot `s` under `contract`, there are an
    outcome `early` of the early confirmation votes and a choice `sc` of one Goldfish score outcome
    per block, over the votes of `early` with no second vote in the late votes, such that those
    votes are an outcome of the confirmation votes and the count of the late voters is less than
    twice `sc B`. -/
private theorem genuine_eligible₆₅b (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
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
    returns_map_intro₆₅b _ _ _ htm
  have hu := returns_map_intro₆₅b
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

/-- If the source's early, late and counted votes have the numerator's shape, the transport from the
    source tree to the target tree holds for `B`, `g` is an outcome of `B`'s Goldfish score over the
    source votes with the late voter count less than `2 * g`, the target support votes are among the
    target votes, `A` is compatible with `B`, and every block strictly between `A` and `B` is in
    `tree` when `A ⪯ B`, then `B` is an ancestor of every outcome of the Goldfish fork choice from
    `A`. -/
private theorem captures_of_confirmation_one₆₅b (facts : Record.Facts M)
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

/-- The round-`r` action read from any node state `before` has a node state. -/
private theorem actionReadFrom_nonempty₆₅b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

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

/-- Along the path `W`, for the node state `n` staged at `vote_time s` from `v`'s node state in
    `W (strictEventIndex rho (vote_time s))` with an outcome `c` of the cache update there (`hc`),
    every head the in-tree head computation at `n` can return is in the tree of the store
    `voteStore` stages at slot `s` from `v`'s core store in that world. -/
theorem voteDutyHead_mem_voteDutyStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (s : Slot)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ c) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) v).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      H ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T := by
  intro n T hT L hL L' hL' H hH
  have hHmem := head_mem_core_T₆₅b facts S (strictEventIndex rho (M.vote_time S.E s))
    (W (strictEventIndex rho (M.vote_time S.E s))) (hf.onePath _).1 v (M.vote_time S.E s) c
    T hT L hL L' hL' H hH
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_T₆₅b facts]
  exact hHmem

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

/-- Along the path `W` with the admissible fields `hf`: if `u` is in the set for `vote_time s`, `w`
    is in the set for `view_freeze s`, `lo ≤ proposal_time s`, slot `s + 1`'s confirmation time is
    in the horizon, and the FG root of the store `voteStore` stages at `s + 1` from `w`'s core store
    in `W (strictEventIndex rho (vote_time (s + 1)))` is an ancestor of `B` (`hroot`), then every
    head `H` with `B ⪯ H` that the in-tree head computation can return at `u`'s vote read of slot
    `s` is in the tree of `w`'s store in that world and stamped there before `view_freeze s`. -/
theorem voteHeadVisible_at_nextDutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {u w : V} {s : Slot} (hu : u ∈ Hs (M.vote_time S.E s))
    (hw : w ∈ Hs (M.view_freeze S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E (s + 1) ≤ rho.horizon)
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
    head_mem_core_T₆₅b facts S (strictEventIndex rho (M.vote_time S.E s))
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
        ((facts.sch.Protocol_vote_time_le_confirmation_time S.E (s + 1)).trans hhor)
    have hproposalVote : M.proposal_time S.E s ≤ M.vote_time S.E s :=
      (facts.sch.proposal_time_lt_vote_time S.E s).le
    have huSrc : u ∈ Hs (max t lo) := hHs _ _ (max_le ht.le (hpost.trans hproposalVote)) hu
    have hrootW : Block.Preceq
        (M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG) B := by
      have h := hroot
      rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₅b facts] at h
      exact h
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w D.erase
        (M.view_freeze S.E s) := by
      apply Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb huSrc hw hDpos hacc htSupport hgstCut
          (by linarith [hinst.2.1, hinst.2.2.1]) hfreezeHor
      intro j hj
      have hjw : j ≤ strictEventIndex rho (M.vote_time S.E (s + 1)) :=
        hj.trans (strict_filter_length_mono rho hfreezeVote)
      exact preceq_trans_Preceq (F_mono_along₆₅b facts S hf.onePath w hjw)
        (preceq_trans_Preceq (F_preceq_fgRoot_along₆₅b facts S hf.sorted hf.onePath w _)
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

/-- Along the path `W` with the admissible fields `hf`: if `v` is in the set for
    `confirmation_time s`, `w` is in the set for `vote_time (s + 1)`, `lo ≤ proposal_time s`,
    `confirmation_time s` is in the horizon, the FG root of `w`'s vote-duty store at `s + 1` is an
    ancestor of `B` (`hroot`), an outcome `A` of the anchor read at `w`'s vote read `n` of slot
    `s + 1` is compatible with `B` (`hanchor`), `B` is in an outcome `K` of the voter candidate tree
    of that store, and `w` passes the grade-1 awake test at its ticks at `vote_time (s + 1)`
    (`hrun`), then `B` is an ancestor of `A`, or `w` adopts `B` at `n` from `v`'s confirmation store
    at `s`. -/
theorem nextVoteAdoption_of_recovery_after_gst_compatibleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) B)
    {A : Block V}
    (hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
      (M.round_of S.hc (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ A)
    (hanchor : Block.compatible A B = true)
    {K : Finset (Block V)}
    (hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))) ⇢ K)
    (hcandidate : B ∈ K)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let cw := Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)
    Block.Preceq B A ∨
    ((∀ votes : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M S.E cw s ⇢ votes →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      Restated.Vocabulary.Protocol.AdoptionTransport M cw.T n.st.core.T votes
        (Restated.Vocabulary.Protocol.confLate M S.E cw s) L L' B) ∧
    (∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      L' ⊆ L) ∧
    (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ R →
      R.compatible B = true) ∧
    (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ R →
      R ⪯ B →
        ∀ C : Block V, R ⪯ C → C ≠ R → C ⪯ B →
          ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
            C ∈ T) ∧
    (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      ∃ C : NamedBlock V, C.erase = H ∧ Restated.RunBlockOn M S rho W Xb C) ∧
    (∀ u : GoldfishVote V,
      ∀ D : M.NS × Option (GoldfishVote V),
        M.duties_goldfish_vote_with (M.gradeContract n.cache) S.E S.hc (S.node w) n.st ⇢ D →
      D.2 = some u →
        Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.gfVote u)
          (M.vote_time S.E (s + 1)))) := by
  intro n cw
  have hstV : n.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  rcases compatible_cases hanchor with habove | hbelow
  · have hroot' : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) B := by
      rw [hstV]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rw [setClock_core_eq_tickStore₆₅b facts S]
      exact hroot
    have hanchor' : ∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) ⇢ R → Block.Preceq R B := by
      intro R hR
      rw [sgRoot_eq_nodeAnchor₆₅b facts S n _ hA hR]
      exact habove
    have hK' : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
        (M.toHealing n.st.core) ⇢ K := by
      rw [hstV]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rw [setClock_core_eq_tickStore₆₅b facts S]
      rw [candidateTree_store_with_cache₆₅b facts, setClock_core_eq_tickStore₆₅b facts S]
      exact hK
    exact Or.inr (Restated.nextVoteAdoption_of_recovery_after_gstOn facts
      S Hs Xb hf hHs hHsXb hv hw hpost hhor c hc hroot' hanchor' hK' hcandidate hrun)
  · exact Or.inl hbelow

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

/-- If `n` is one of `w`'s vote reads of slot `s + 1` (`hn`), `votes` is an outcome of `source`'s
    slot-`s` counted confirmation votes (`hvotes`), `T`'s Goldfish score over `votes` has an outcome
    `g` with the late voter count less than `2 * g` (`heligible`), `w` is in slot `s + 1`'s
    committee, and `w` adopts `T` at `n` from `source` (`hd`), then some run block `X` read along
    `W` through `Xb` descends from `T`, and `w` emits along `W` at `vote_time (s + 1)` the
    slot-`(s + 1)` Goldfish vote for `X`'s root. -/
theorem honestVoteWitness_of_nextVoteAdoptionOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (source : M.S)
    (s : Slot) (T : Block V) {w : V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1))
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E source s ⇢ votes)
    {g : ℕ} (hg : M.goldfish_score S.E source.T votes votes s T ⇢ g)
    (heligible : M.voters_count S.E (Restated.Vocabulary.Protocol.confLate M S.E source s) s < 2 * g)
    (_hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hwcommittee : w ∈ S.E.committee (s + 1))
    (hd :
      (∀ votes' : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M S.E source s ⇢ votes' →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        Restated.Vocabulary.Protocol.AdoptionTransport M source.T n.st.core.T votes'
          (Restated.Vocabulary.Protocol.confLate M S.E source s) L L' T) ∧
      (∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        L' ⊆ L) ∧
      (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc n.st.core.s) ⇢ R →
        R.compatible T = true) ∧
      (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc n.st.core.s) ⇢ R →
        R ⪯ T →
          ∀ C : Block V, R ⪯ C → C ≠ R → C ⪯ T →
            ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
              C ∈ Tr) ∧
      (∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        ∃ C : NamedBlock V, C.erase = H ∧ Restated.RunBlockOn M S rho W Xb C) ∧
      (∀ u : GoldfishVote V,
        ∀ D : M.NS × Option (GoldfishVote V),
          M.duties_goldfish_vote_with (M.gradeContract n.cache) S.E S.hc (S.node w) n.st ⇢ D →
        D.2 = some u →
          Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.gfVote u)
            (M.vote_time S.E (s + 1)))) :
    ∃ X : NamedBlock V, Block.Preceq T X.erase ∧ Restated.RunBlockOn M S rho W Xb X ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote ⟨w, s + 1, X.erase.root⟩)
        (M.vote_time S.E (s + 1)) := by
  obtain ⟨htransport, hsub, hanchorCompat, hpath, hrun, hemit⟩ := hd
  have hslot : n.st.core.s = s + 1 :=
    Restated.Vocabulary.Proofs.Optimistic.voteDutyRead_slot facts S rho w (s + 1) n hn
  have hprev : n.st.core.s - 1 = s := by
    rw [hslot]
    simp
  have hcommittee : (S.node w).val_index ∈ S.E.committee n.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hwcommittee
  obtain ⟨Tr, L, L', H, hT, hL, hL', hH⟩ := voterHead_outcome₆₅b facts S n
  obtain ⟨early, -, hN⟩ := confNumerator₆₅b facts S.E source s votes hvotes
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  have hs : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s n.st.core
  have hTn : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_T n.st.core
  have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R := by
    rw [hs] at hR
    exact hR
  have hX := (facts.fc.get_head_in_tree_split_with (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) R hR H).1 hH
  rw [hprev] at hX
  have hhead : Block.Preceq T H :=
    captures_of_confirmation_one₆₅b facts S.E (M.toHealing n.st.core).σ
      (M.toHealing n.st.core).h_max source.T (M.toHealing n.st.core).T Tr (M.toHealing n.st.core).s
      early (Restated.Vocabulary.Protocol.confLate M S.E source s) votes L L' s hN
      (by rw [hTn]; exact htransport votes hvotes L hL L' hL')
      g hg heligible (hsub L hL L' hL') (hanchorCompat R hR')
      (fun hRB C hRC hCR hCB => hpath R hR' hRB C hRC hCR hCB Tr hT) H hX
  obtain ⟨C, hCH, hCrun⟩ := hrun Tr hT L hL L' hL' H hH
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node w) n.st
  have hDvote := facts.fc.goldfish_vote_with_snd_of_mem_committee (M.gradeContract n.cache) S.E
    S.hc (S.node w) n.st hcommittee D hD Tr hT L hL L' hL' H hH
  have hem := hemit _ D hD hDvote
  refine ⟨C, ?_, hCrun, ?_⟩
  · rw [hCH]
    exact hhead
  · rw [← hCH, hslot] at hem
    simpa only [S.node_val_index] using hem

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

/-- Along the path `W` with the admissible fields `hf`: if `v` is in the set for
    `confirmation_time s`, `u` in the set for `vote_time s`, `w` in the set for `vote_time (s + 1)`
    and in slot `s + 1`'s committee, `lo ≤ proposal_time s`, slot `s + 1`'s confirmation time is in
    the horizon, `T` passes the eligibility test at `v`'s confirmation store of `s`, `T ⪯ C`, `Hn`
    is a run block of height at least `Mh − 1` erasing to a vote-duty head of `u` at `s` with
    `C ⪯ Hn`, `w`'s vote-duty store at `s + 1` has `h_max = Mh`, `h_j + 2 ≤ Mh` and an FG root that
    is an ancestor of `T`, `w`'s prepared anchor there is compatible with `T`, and `w` passes the
    grade-1 awake test at its ticks at `vote_time (s + 1)` (`hrun`), then some run block `X` read
    along `W` through `Xb` descends from `T`, and `w` emits at `vote_time (s + 1)` the
    slot-`(s + 1)` Goldfish vote for `X`'s root. -/
theorem baseConeVoteWitness_of_supporterOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {s : Slot} {v u w : V}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hu : u ∈ Hs (M.vote_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hwcommittee : w ∈ S.E.committee (s + 1))
    {T C : Block V} {Hn : NamedBlock V}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E (s + 1) ≤ rho.horizon)
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
    (hHthin : Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
    (hfrontier : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh)
    (hgate : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_j + 2 ≤ Mh)
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
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E (s + 1)).trans hhor
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
  have hvisible := Restated.voteHeadVisible_at_nextDutyOn facts S Hs Xb hf hHs hHsXb hu hwFreeze
    hpost hhor hrootT cu hcu Tu hTu Lu hLu Lu' hLu' Hu hHu hTHead
  have hvisT : Hu ∈ (W iw w).st.core.T := hvisible.1
  have hvisStamp : stampedBefore (W iw w).st.core.timestamp_block (M.view_freeze S.E s) Hu = true :=
    hvisible.2
  have hdutyEq : (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core =
      Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W iw w).st.core (s + 1) :=
    setClock_core_eq_tickStore₆₅b facts S _ _
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
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hfrontierW : (W iw w).st.core.h_max = Mh := by
    have h := hfrontier
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₅b facts] at h
    exact h
  have hgateW : (W iw w).st.core.h_j + 2 ≤ Mh := by
    have h := hgate
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₆₅b facts] at h
    exact h
  have hM : 1 ≤ Mh :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans ((Nat.le_add_left 2 _).trans hgateW)
  have hrootW : Block.Preceq (M.get_fg_root (M.toHealing (W iw w).st.core).toFG) T := by
    have h := hrootT
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₆₅b facts] at h
    exact h
  have hTfilteredPre : T ∈ M.get_filtered_block_tree (M.toHealing (W iw w).st.core).toFG :=
    Restated.frontierAncestor_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) hread
      hvisible.1 hHerase hHrun hTHead hHthin hM hfrontierW hgateW hrootW
  have hTfiltered : T ∈ M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core).toFG := by
    rw [hdutyEq, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_filtered₆₅b facts]
    exact hTfilteredPre
  have hmax : (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1))).core.h_max ≤
      (M.derive_named S.E S.cfg Hn).h + 1 := by
    rw [facts.hd.setClock_core_h_max, hfrontierW]
    exact Nat.sub_le_iff_le_add.mp hHthin
  have hcand := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts S Hs Xb hf
    hHsXb hwFreeze P hP hHprocessed hHrun hTH hTfiltered hmax hloFreeze
  rw [hdutyEq] at hP hcand
  have hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W iw w).st.core (s + 1))) ⇢
      M.get_filtered_block_tree_from
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W iw w).st.core
          (s + 1))).toFG P := by
    unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
    exact (returns_bind_iff₆₅b _ _ _).mpr ⟨P, hP, (Record.returns_pure _ _).2 rfl⟩
  have hhor' : M.confirmation_time S.E s ≤ rho.horizon :=
    (facts.sch.confirmation_time_mono S (Nat.le_succ s)).trans hhor
  have hnmem : nw ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
    mkNode_mem_confirmationReadAt₆₅b hf.sorted hf.onePath w (M.vote_time S.E (s + 1)) cw hcw
  have h3 := Restated.nextVoteAdoption_of_recovery_after_gst_compatibleOn facts S Hs Xb hf
    hHs hHsXb hv hw hpost hhor' cw hcw hrootT hA hanchor hK hcand hrun
  rcases h3 with hbelow | hd
  · obtain ⟨Tr, L, L', H, hT, hL, hL', hH⟩ := voterHead_outcome₆₅b facts S nw
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

/-- Along the path `W` with the admissible fields `hf`: if `v` is in the set for
    `confirmation_time s`, `lo ≤ proposal_time s`, slot `s + 1`'s confirmation time is in the
    horizon, `v` confirms `C` at slot `s` (`hC`), `T ⪯ C`, `T` is the erasure of a run block, every
    member of the set for `vote_time (s + 1)` has at its vote-duty store at `s + 1` `h_max = Mh`,
    `h_j + 2 ≤ Mh` and an FG root comparable with `T` (`hframe`), some member of the set for
    `vote_time s` has a vote-duty head at `s` that is the erasure of a run block descending from `C`
    of height at least `Mh − 1` (`hsupp`), the prepared anchor at `s + 1` of every member of the set
    for `vote_time (s + 1)` is compatible with `T` (`hanchor`), and the committee members of `s + 1`
    pass the grade-1 awake test at their vote ticks (`hrun`), then every member of slot `s + 1`'s
    committee in the set for `vote_time (s + 1)` emits at that time a vote for the root of a run
    block descending from `T`. -/
theorem baseCone_succ_of_genuineSupporter_rootComparableOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {s : Slot} {v : V} (hv : v ∈ Hs (M.confirmation_time S.E s))
    {T C : Block V}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E (s + 1) ≤ rho.horizon)
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
    (hTrun : ∃ Tn : NamedBlock V, Tn.erase = T ∧ Restated.RunBlockOn M S rho W Xb Tn)
    (hframe : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh ∧
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_j + 2 ≤ Mh ∧
      (Block.Preceq (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) T ∨
        Block.Preceq T (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG)))
    (hsupp : ∃ u ∈ Hs (M.vote_time S.E s), ∃ cu : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) u).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) u).cache ⇢ cu ∧
      ∃ (Tu : Finset (Block V)) (Lu Lu' : Finset (GoldfishVote V)) (Hu : Block V),
        M.voter_filtered_block_tree S.E
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Tu ∧
        M.voter_view S.E
          (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core).toFG.toSG.toGoldfishStore
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Lu ∧
        M.voter_support_view S.E
          (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core).toFG.toSG.toGoldfishStore
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s ⇢ Lu' ∧
        M.get_head_in_tree_with_layer
          (M.gradeContract (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).cache) S.E S.hc
          (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core) Tu Lu Lu'
          ((M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record cu).st.core.s - 1) ⇢ Hu ∧
        ∃ Hn : NamedBlock V,
          Hn.erase = Hu ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
            Block.Preceq C Hn.erase ∧
            Mh - 1 ≤ (M.derive_named S.E S.cfg Hn).h)
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
  obtain ⟨u, hu, cu, hcu, Tu, Lu, Lu', Hu, hTu, hLu, hLu', hHu, Hn, hHerase, hHrun, hCH, hHthin⟩ :=
    hsupp
  intro w hw hwcommittee
  set iw := strictEventIndex rho (M.vote_time S.E (s + 1)) with hiw
  obtain ⟨cw, hcw⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W iw w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W iw w).cache
  set nw := M.mkNode (M.ns_setClock S.E (W iw w).st (M.vote_time S.E (s + 1)))
    (W iw w).record cw with hnw
  have hinst := facts.sch.slot_instants_l55 S.E s
  have hΔ := S.E.Δ_pos
  have hread : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E (s + 1)).trans hhor
  have hloVote : lo ≤ M.vote_time S.E (s + 1) := by
    linarith [hinst.2.2.2.2.1]
  rcases (hframe w hw).2.2 with hcase1 | hcase2
  · obtain ⟨A, hA⟩ := nodeAnchor_outcome₆₅b facts S nw (M.round_of S.hc nw.st.core.s)
    obtain ⟨early, sc, hearly, hvotes, hsc, helig⟩ := genuine_eligible₆₅b facts
      (⟨hC.selected, hC.genuine⟩ : Restated.Vocabulary.Protocol.GenuineConfirmation M
        (contract := M.gradeContract cv) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)) s C)
    have hle := facts.fc.goldfish_score_le_of_Preceq S.E _ _ _ s hTC (sc C) (hsc C) (sc T) (hsc T)
    exact Restated.baseConeVoteWitness_of_supporterOn facts S Hs Xb hf hHs hHsXb hv hu hw
      hwcommittee hpost hhor hvotes (hsc T) (lt_of_lt_of_le helig (Nat.mul_le_mul_left 2 hle))
      hTC cu hcu hTu hLu hLu' hHu hHerase hHrun hCH hHthin (hframe w hw).1 (hframe w hw).2.1
      hcase1 cw hcw hA (hanchor w hw cw hcw A hA) (hrun w hwcommittee hw)
  · obtain ⟨Tr, L, L', H, hT, hL, hL', hH⟩ := voterHead_outcome₆₅b facts S nw
    have hnmem : nw ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
      mkNode_mem_confirmationReadAt₆₅b hf.sorted hf.onePath w (M.vote_time S.E (s + 1)) cw hcw
    have hstV : nw.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
    have hTX : Block.Preceq T H := by
      refine preceq_trans_Preceq ?_
        (Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts S rho w (s + 1)
          nw hnmem Tr hT L hL L' hL' H hH)
      rw [hstV]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rw [setClock_core_eq_tickStore₆₅b facts S]
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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic

/-- Along the path `W` with the admissible fields `hf`, if slot `s`'s proposer is in `Xb`, the tree
    of its store in `W (strictEventIndex rho (proposal_time s))`, with the clock set to
    `proposal_time s`, is root-injective on ancestors. -/
theorem rootInjective_proposerReadAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hprop : S.E.proposer s ∈ Xb) :
    RootInjectiveBelow (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core.T := by
  have hrun : ∀ C ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.bodies,
      Restated.RunBlockOn M S rho W Xb C :=
    fun C hC => Restated.runBlock_of_stateBefore_memOn facts S W Xb hprop hC
  have hinj := Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hf.rootCollisionFree hrun
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
    (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s) _ (hf.onePath _).1).1.1.1
  rw [facts.hd.Sts_setClock_core_T, hcoh.1]
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic

/-- Along the path `W` with the admissible fields `hf`: if `P` is a proposal slot `s`'s proposer's
    duty can return at its read with the cache `c` (`hc`, `hP`), the proposer is in `Xb`, and the
    store `tickStore` stages at its proposal time from its core store has `h_max = Mh`
    (`hfrontier`), then `P`'s parent has height at least `Mh − 1`. -/
theorem seedOpeningParentHeight_of_frontierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {Mh : Height} {s : Slot} {P : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P)
    (hprop : S.E.proposer s ∈ Xb)
    (hfrontier : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)).h_max = Mh) :
    Mh - 1 ≤ (M.derive_named S.E S.cfg P.parent).h := by
  set ip := strictEventIndex rho (M.proposal_time S.E s) with hip
  set p := S.E.proposer s with hp
  set tp := M.proposal_time S.E s with htp
  set nst₀ := M.ns_setClock S.E (W ip p).st tp with hnst₀
  set nst := M.store_with_cache nst₀ c with hnst
  have hT : nst.core.T = (W ip p).st.core.T := by
    rw [hnst, facts.nd.store_with_cache_core_T, hnst₀, facts.hd.Sts_setClock_core_T]
  -- the outcomes the proposal input is computed from
  obtain ⟨Ls, hLs⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing nst.core).toFG.toSG.toGoldfishStore
    (M.toHealing nst.core).toFG.toSG.toGoldfishStore.s
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing nst.core) (M.round_of S.hc (M.toHealing nst.core).toFG.toSG.toGoldfishStore.s)
  obtain ⟨H, hH⟩ := facts.fc.get_head_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing nst.core)
    (M.proposer_view (M.toHealing nst.core).toFG.toSG.toGoldfishStore
      (M.toHealing nst.core).toFG.toSG.toGoldfishStore.s).toFinset
    Ls.toFinset ((M.toHealing nst.core).toFG.toSG.toGoldfishStore.s - 1)
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node p) (M.toHealing nst.core)
  have hIH : I.parent = H :=
    facts.dt.with_proposal_input_id_parent _ S.E S.hc (S.node p) (M.toHealing nst.core) I hI
      Ls hLs H hH
  have hHfc := (facts.gr.get_head_with_eq_fork_choice (M.gradeContract c) S.E S.hc
    (M.toHealing nst.core) _ _ _ R hR H).1 hH
  -- the head is in the filtered tree
  have hnmem : M.mkNode nst₀ (W ip p).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
    mkNode_mem_confirmationReadAt₆₅b hf.sorted hf.onePath p tp c hc
  have hHfiltered : H ∈ M.get_filtered_block_tree (M.toHealing nst.core).toFG := by
    have h := Restated.Vocabulary.Proofs.HealingSurface.selectedOpeningProposedParent_mem_filtered
      facts S s _ hnmem I (by rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st]; exact hI)
    rewrite [facts.nd.mkNode_st, hIH] at h
    exact h
  have hrootTree : RootInjectiveBelow (M.get_filtered_block_tree (M.toHealing nst.core).toFG) := by
    have hroot := Restated.rootInjective_proposerReadAtOn facts S Hs Xb hf hprop
    have hsub := facts.fc.get_filtered_block_tree_subset (M.toHealing nst.core).toFG
    rw [facts.sto.toHealing_T, hnst, facts.nd.store_with_cache_core_T] at hsub
    exact Protocol.RootInjectiveBelow.mono hroot hsub
  have hFH : Block.Preceq nst.core.F H := by
    have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hHfiltered
    rwa [facts.sto.ModelProperties_toHealing_F] at h
  have hrootH : Block.Preceq (M.get_fg_root (M.toHealing nst.core).toFG) H :=
    preceq_eq_true_iff_Preceq.1 (facts.fc.preceq_get_fg_root_of_mem_filtered hHfiltered)
  obtain ⟨Wb, hWT, hHW, hWheight⟩ :=
    facts.fc.viable_witness_of_mem_get_filtered_block_tree hHfiltered
  rw [facts.sto.toHealing_T] at hWT
  rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ] at hWheight
  have hbound : nst.core.h_max ≤ (nst.core.σ H).h + 1 := by
    by_contra hnot
    have hHlt : (nst.core.σ H).h + 1 < nst.core.h_max := Nat.lt_of_not_ge hnot
    have hHneW : H ≠ Wb := by
      intro hEq
      subst hEq
      have key : ∀ a b : Nat, a - 1 ≤ b → b + 1 < a → False := by omega
      exact key _ _ hWheight hHlt
    obtain ⟨C, hCparent, hCW⟩ :=
      Protocol.exists_child_towards Wb (preceq_eq_true_iff_Preceq.2 hHW) hHneW
    have hHC : Block.Preceq H C :=
      preceq_eq_true_iff_Preceq.1 (Protocol.preceq_of_parent? hCparent)
    have hCT : C ∈ nst.core.T := by
      rw [hT]
      have hWT' : Wb ∈ (W ip p).st.core.T := by
        rw [← hT]
        exact hWT
      exact Restated.ancestor_mem_storeBeforeTimeOn facts S Hs Xb hf hWT'
        (preceq_eq_true_iff_Preceq.1 hCW)
    have hFC : Block.Preceq nst.core.F C := preceq_trans_Preceq hFH hHC
    have hrootC : Block.Preceq (M.get_fg_root (M.toHealing nst.core).toFG) C :=
      preceq_trans_Preceq hrootH hHC
    have hCfiltered : C ∈ M.get_filtered_block_tree (M.toHealing nst.core).toFG := by
      refine facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing nst.core) (W := Wb) ?_ ?_ ?_
        (preceq_eq_true_iff_Preceq.1 hCW) ?_ hrootC
      · rw [facts.sto.toHealing_T]; exact hCT
      · rw [facts.sto.ModelProperties_toHealing_F]; exact hFC
      · rw [facts.sto.toHealing_T]; exact hWT
      · rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
        exact hWheight
    have hHlow : (nst.core.σ H).h < nst.core.h_max - 1 := by
      have key : ∀ a b : Nat, a + 1 < b → a < b - 1 := by omega
      exact key _ _ hHlt
    obtain ⟨e, he⟩ := facts.fc.goldfish_eligible_nonempty S.E (M.toHealing nst.core).toFG.σ
      (M.toHealing nst.core).toFG.h_max (M.toHealing nst.core).toFG.toSG.toGoldfishStore.T
      (M.toHealing nst.core).toFG.toSG.toGoldfishStore.s
      (M.proposer_view (M.toHealing nst.core).toFG.toSG.toGoldfishStore
        (M.toHealing nst.core).toFG.toSG.toGoldfishStore.s).toFinset
      Ls.toFinset ((M.toHealing nst.core).toFG.toSG.toGoldfishStore.s - 1) C
    obtain ⟨gC, hgC⟩ := facts.fc.goldfish_score_nonempty S.E
      (M.toHealing nst.core).toFG.toSG.toGoldfishStore.T
      (M.proposer_view (M.toHealing nst.core).toFG.toSG.toGoldfishStore
        (M.toHealing nst.core).toFG.toSG.toGoldfishStore.s).toFinset
      Ls.toFinset ((M.toHealing nst.core).toFG.toSG.toGoldfishStore.s - 1) C
    have hCeligible : e = true := by
      refine (facts.fc.goldfish_eligible_iff S.E _ _ _ _ _ _ _ C e he gC hgC).2 (Or.inl ?_)
      rw [parent_eq_of_parent? hCparent, facts.sto.ModelProperties_toHealing_σ,
        facts.sto.ModelProperties_toHealing_h_max]
      exact hHlow
    have hCfalse : e = false :=
      facts.fc.goldfish_eligible_eq_false_of_parent_fork_choice hrootTree hCfiltered H hHfc
        hCparent e he
    rw [hCfalse] at hCeligible
    exact Bool.noConfusion hCeligible
  -- the proposal's parent is the head
  obtain ⟨Lsel, hLsel⟩ := facts.dt.select_nonempty Protocol.ProposalRowSource.poolAndCarried S.hc nst
  have _hr_pay : M.reachedStore nst := by
    have h := facts.nd.reachedStore_of_node _ (facts.nd.reachedNode_confirmationRead S.E S.hc (W ip p) tp c hc
      (facts.ndRun.stateBeforeOf_reachedNode S rho ip (W ip) (hf.onePath ip).1 p))
    rw [facts.nd.mkNode_st] at h
    exact h
  have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts (M.gradeContract c)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node p) nst P
    (by rw [hnst, facts.dt.proposal_with_store_with_cache]; exact hP) I hI Lsel hLsel
  have hinv := facts.hd.invariant_clock S.E S.cfg (W ip p).st tp
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho ip p (W ip)
      (hf.onePath ip).1).1
  have hview : nst.core.σ P.parent.erase = M.derive_named S.E S.cfg P.parent := by
    have h1 := hpay.1
    try simp only [hnst, facts.nd.store_with_cache_bodies] at h1
    rw [hnst, facts.nd.store_with_cache_core_σ]
    exact hinv.1.1.2.2.2.2 P.parent h1
  have hparentErase : P.parent.erase = H := hpay.2.1.trans hIH
  have hbound' : nst.core.h_max ≤ (M.derive_named S.E S.cfg P.parent).h + 1 := by
    rw [← hview, hparentErase]
    exact hbound
  have hfrontier' : nst.core.h_max = Mh := by
    have h := hfrontier
    rw [tickStore_h_max₆₅b facts] at h
    rw [hnst, facts.nd.store_with_cache_core_h_max, hnst₀, facts.hd.setClock_core_h_max]
    exact h
  rw [hfrontier'] at hbound'
  exact Nat.sub_le_iff_le_add.mpr hbound'

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

/-- Along the path `W` with the admissible fields `hf` and the slashable bound `hsb`: if `P` is a
    run block of height at least `Mh − 1` and every member of the set for `vote_time s` has
    `h_max = Mh` and `h_j + 2 ≤ Mh` in `W (strictEventIndex rho (vote_time s))`, then for every such
    member `v` and every `i` up to the number of events before `vote_time s`, the finalized block of
    `v`'s store in `W i` is an ancestor of `P`'s block. -/
theorem seedOpeningProposal_finalizedBelow_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {s : Slot} {P : NamedBlock V}
    (c : M.Cache)
    (_hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    (_hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P)
    (hPrun : Restated.RunBlockOn M S rho W Xb P)
    (hPthin : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h)
    (hvoteFrontier : ∀ v ∈ Hs (M.vote_time S.E s),
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.h_max = Mh)
    (hvoteGate : ∀ v ∈ Hs (M.vote_time S.E s),
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.h_j + 2 ≤ Mh) :
    ∀ v ∈ Hs (M.vote_time S.E s),
      ∀ i : Nat, i ≤ (rho.events.filter (fun e => decide (e.time < M.vote_time S.E s))).length →
        Block.Preceq (W i v).st.core.F P.erase := by
  intro v hv i hi
  exact Restated.seedBase_thinBlock_finalizedBelowOn facts S Hs Xb hf hsb hPrun hPthin (hHsXb _ hv)
    (hvoteFrontier v hv) (hvoteGate v hv) i hi

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

/-- Along the path `W` with the admissible fields `hf`: if `0 < s`, slot `s`'s proposer is in the
    set for slot `s`'s confirmation time, `lo ≤ proposal_time s`, `vote_time s` is in the horizon,
    `P` is a proposal the proposer's duty can return at its read with the cache `c`, for every
    member `v` of the set for `vote_time s` and every `i` up to the number of events before
    `vote_time s` the finalized block of `v`'s store in `W i` is an ancestor of `P`'s block
    (`hFhist`), and the proposer passes the grade-1 awake test at its proposal ticks (`hrun`), then
    every member of the set for `vote_time s` admits `P` along `W` before `vote_time s`. -/
theorem proposedBlock_admittedBefore_vote_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P)
    (hFhist : ∀ v ∈ Hs (M.vote_time S.E s),
      ∀ i : Nat, i ≤ (rho.events.filter (fun e => decide (e.time < M.vote_time S.E s))).length →
        Block.Preceq (W i v).st.core.F P.erase)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s)) :
    ∀ v ∈ Hs (M.vote_time S.E s),
      Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v P.erase (M.vote_time S.E s) := by
  set p := S.E.proposer s with hp_def
  set tp := M.proposal_time S.E s with htp_def
  have hinst := facts.sch.slot_instants_l55 S.E s
  have hproposalVote : tp + S.E.Δ = M.vote_time S.E s := hinst.1.symm
  have hproposalLeVote : tp ≤ M.vote_time S.E s :=
    le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)
  have hproposalConf : tp ≤ M.confirmation_time S.E s :=
    hproposalLeVote.trans (facts.sch.Protocol_vote_time_le_confirmation_time S.E s)
  have hproposalHor : tp ≤ rho.horizon := hproposalLeVote.trans hvoteHor
  have hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p tp) →
      ∃ out : M.N × List (NamedObject V), M.tick S p (W j p) tp ⇢ out :=
    fun j hj => hf.tick_outcome j _ _ hj
  obtain ⟨B0, hB0, hB0slot, hemit0⟩ :=
    Restated.proposedBlockAt_emits_of_honestOn facts S Hs Xb hf hHs s hs hprop hproposalHor
      hpost hneTick hrun c hc (some P) hP
  cases hB0
  have hBslot : P.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact hB0slot
  have hBpos : 0 < P.slot := by
    rw [hB0slot]
    exact hs
  obtain ⟨i0, hacc0⟩ := Restated.acceptsAt_proposedBlockOn facts S Hs Xb hf hHs hs hprop
    hproposalHor hpost hneTick hrun c hc hP
  intro v hv
  have hdeadline : tp + S.E.Δ ≤ rho.horizon := by
    rw [hproposalVote]
    exact hvoteHor
  have hguard : ∀ B' : NamedBlock V, Object.block P = .block B' →
      Block.compatible (W (strictEventIndex rho (tp + S.E.Δ)) v).st.core.F B'.erase = true := by
    intro B' hB'
    cases hB'
    rw [hproposalVote]
    exact compatible_of_cases (Or.inl (hFhist v hv _ le_rfl))
  have hpropP : p ∈ Hs tp := hHs _ _ hproposalConf hprop
  have hvRecv : v ∈ Hs (tp + S.E.Δ) := by
    rw [hproposalVote]
    exact hv
  obtain ⟨t, hlo, hhi, j, hcall⟩ :=
    hf.broadcast p _ _ hpropP hemit0 v hvRecv hpost hdeadline hguard
  have hbeforeVote : t < M.vote_time S.E s := by
    rw [← hproposalVote]
    exact hhi
  obtain ⟨e, hej, -, heTime⟩ := hcall.2
  have hjBound : j + 1 ≤ strictEventIndex rho (M.vote_time S.E s) :=
    index_succ_le_strict_filter_length rho hf.sorted (M.vote_time S.E s) hej
      (by rw [heTime]; exact hbeforeVote)
  have hFj : Block.Preceq (W j v).st.core.F P.erase :=
    hFhist v hv j ((Nat.le_succ j).trans hjBound)
  have hvProp : v ∈ Hs (M.proposal_time S.E P.erase.slot) := by
    rw [hBslot]
    exact hHs _ _ hproposalLeVote hv
  have hheld := Restated.handled_block_held_of_finalized_prefixOn facts S rho Hs Xb hf hHsXb
    (hHsXb _ hpropP) hvProp (Or.inr (by rw [hBslot]; exact hpost)) hacc0 hcall hlo hFj
  obtain ⟨j', t', hacc', ht'⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.acceptsAt_before_of_processed_after_event facts S rho
      hf.sorted (w := v) hBpos hej (by rw [heTime]; exact hbeforeVote) W hf.onePath
      (by simp only [Restated.Vocabulary.Execution.Object.processed]; exact decide_eq_true hheld)
  exact ⟨P, rfl, j', t', hacc', ht'⟩

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

/-- Along the path `W` with the admissible fields `hf` and the slashable bound `hsb`: if `0 < s`,
    slot `s`'s proposer is in the set for slot `s`'s confirmation time, `lo ≤ proposal_time s`,
    `vote_time s` is in the horizon, `P` is a proposal the proposer's duty can return at its read
    with the cache `c`, `P` is a run block of height at least `Mh − 1`, every member of the set for
    `vote_time s` has `h_max = Mh` and `h_j + 2 ≤ Mh` there, and the proposer passes the grade-1
    awake test at its proposal ticks (`hrun`), then every such member has `P`'s block in the tree of
    its store in `W (strictEventIndex rho read)` for every `read` from `vote_time s` on. -/
theorem seedOpeningProposal_mem_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P)
    (hPrun : Restated.RunBlockOn M S rho W Xb P)
    (hPthin : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h)
    (hvoteFrontier : ∀ v ∈ Hs (M.vote_time S.E s),
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.h_max = Mh)
    (hvoteGate : ∀ v ∈ Hs (M.vote_time S.E s),
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.h_j + 2 ≤ Mh)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s)) :
    ∀ v ∈ Hs (M.vote_time S.E s), ∀ read : Time, M.vote_time S.E s ≤ read →
      P.erase ∈ (W (strictEventIndex rho read) v).st.T := by
  intro v hv read hread
  have hadmit := Restated.proposedBlock_admittedBefore_vote_after_gstOn facts S Hs Xb hf hHs
    hHsXb hs hprop hpost hvoteHor c hc hP
    (Restated.seedOpeningProposal_finalizedBelow_of_gateOffOn facts S Hs Xb hf hHsXb hsb c hc hP
      hPrun hPthin hvoteFrontier hvoteGate) hrun v hv
  exact (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hread).1

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

/-- Along the path `W` with the admissible fields `hf`: if `t_GST ≤ S.a base`, `base + 2 ≤ q`,
    `S.a (q + 1)` is in the horizon, the proposer of round `q`'s opening slot `s` is in the set for
    `s`'s confirmation time, `P` is a proposal its duty can return with the cache `c`, every member
    of the set for each time from `S.a base` to `S.a (q + 1)` has `h_j + 2 ≤ Mh` and `h_max = Mh`
    there (`hwindow`), and `lo ≤ S.a base`, then: `0 < q`; `t_GST` is at most `S.a (q − 1)`,
    `proposal_time (s − 1)` and `vote_time s`; round `q`'s cutoff `Γ_neg1` and `S.a (q + 1)` are in
    the horizon; `P`'s parent has height at least `Mh − 1`; the proposer's duty store has
    `h_max = Mh` and `h_j + 2 ≤ Mh`; and the vote-duty stores at `s`, the confirmation stores at `s`
    and the stores before `S.a (q + 1)` of the members of the matching sets have `h_max = Mh`,
    `h_j + 2 ≤ Mh` and `P`'s block in their tree. -/
theorem gateOffOpeningWindow_of_windowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {base q : Round}
    (hpostBase : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hbaseq : base + 2 ≤ q)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P)
    (hwindow : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S base) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hloBase : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base)) :
    0 < q ∧
    S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ∧
    S.E.t_GST ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1) ∧
    S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc q)) ∧
    Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon ∧
    (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon ∧
    Mh - 1 ≤ (M.derive_named S.E S.cfg P.parent).h ∧
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc q))).h_max = Mh ∧
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc q))).h_j + 2 ≤ Mh ∧
    (∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).h_max = Mh) ∧
    (∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).h_j + 2 ≤ Mh) ∧
    (∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      P.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).T) ∧
    (∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q))).h_max = Mh) ∧
    (∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q))).h_j + 2 ≤ Mh) ∧
    (∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
      P.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q))).T) ∧
    (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
        v).st.core).h_max = Mh) ∧
    (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
        v).st.core).h_j + 2 ≤ Mh) ∧
    (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      P.erase ∈ (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) v).st.core).T) := by
  set s := M.opening_slot S.hc q with hs_def
  set p := S.E.proposer s with hp_def
  set tp := M.proposal_time S.E s with htp_def
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have keyR : ∀ b q : Nat, b + 2 ≤ q →
      0 < q ∧ b ≤ q - 1 ∧ b ≤ q - 2 ∧ q - 1 + 1 = q ∧ q - 2 < q - 1 ∧ b ≤ q + 1 := by
    intro b q h
    omega
  obtain ⟨hqpos, hbasePred, hbasePred2, hqPred, hq21, hbaseSucc⟩ := keyR base q hbaseq
  have hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred)
  have hpostPrev2 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred2)
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans hhor
  have hconfEq : M.confirmation_time S.E s = Restated.Vocabulary.Execution.Setup.a M S q :=
    Restated.confirmation_time_opening_slot facts S q
  have hproposalConf : tp ≤ M.confirmation_time S.E s :=
    facts.sch.proposal_time_le_confirmation_time S.E _
  have hproposalHi : tp ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    rw [← hconfEq]
    exact hproposalConf
  have hproposalLo : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤ tp := by
    refine Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S ?_
    have key : ∀ q : Nat, 0 < q → q - 1 < q := by
      intro q h
      omega
    exact key q hqpos
  have hpostProposal : S.E.t_GST ≤ tp :=
    hpostPrev.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hproposalLo)
  have hpostVote : S.E.t_GST ≤ M.vote_time S.E s :=
    hpostProposal.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _))
  have hvoteConf : M.vote_time S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E _
  have hvoteHi : M.vote_time S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    rw [← hconfEq]
    exact hvoteConf
  have hvoteHor : M.vote_time S.E s ≤ rho.horizon := hvoteHi.trans hactionHor
  have hproposalHor : tp ≤ rho.horizon := hproposalHi.trans hactionHor
  have hopenPos : 0 < s := facts.gr.opening_slot_pos_of_round_pos S.hc hqpos
  have hend : ∀ {read : Time}, (Restated.Vocabulary.Execution.Setup.a M S base) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S q) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh := by
    intro read hlo hhi w hw
    exact hwindow read hlo
      (hhi.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q))) w hw
  have hbaseProposal : (Restated.Vocabulary.Execution.Setup.a M S base) ≤ tp :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred).trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hproposalLo)
  have hloProposal : lo ≤ tp := hloBase.trans hbaseProposal
  have hproposerRead := fun w hw => hend hbaseProposal hproposalHi w hw
  have hvoteRead := fun w hw =>
    hend (hbaseProposal.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s))) hvoteHi w hw
  have hconfRead := fun w hw =>
    hend (hbaseProposal.trans hproposalConf) (le_of_eq hconfEq) w hw
  have hnextRead := fun w hw =>
    hwindow ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseSucc) (le_refl _) w hw
  have hpropP : p ∈ Hs tp := hHs _ _ hproposalConf hprop
  have hproposerFrontier : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho tp) p).st.core tp).h_max = Mh := by
    rw [tickStore_h_max₆₅b facts]
    exact (hproposerRead p hpropP).2
  have hproposerGate : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho tp) p).st.core tp).h_j + 2 ≤ Mh := by
    rw [tickStore_h_j₆₅b facts]
    exact (hproposerRead p hpropP).1
  have hparentHeight : Mh - 1 ≤ (M.derive_named S.E S.cfg P.parent).h :=
    Restated.seedOpeningParentHeight_of_frontierOn facts S Hs Xb hf c hc hP (hHsXb _ hprop)
      hproposerFrontier
  -- The opening proposer passes the grade-1 awake test at its proposal ticks.
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p tp) →
      M.awake_for_grade1 S p (W j p) (M.round_of S.hc s) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ := by
      rw [hs_def, facts.gr.round_of_opening_slot_eq S.hc q]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
        (show base < q from Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right Nat.two_pos) hbaseq)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q
      have h3 : lo ≤ M.a S.hc S.E.Δ base := hloBase
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj hpropP hwin
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlock_runBlockOn facts S Hs Xb hf hHs hHsXb hopenPos hprop hproposalHor
      hloProposal (fun j hj => hf.tick_outcome j _ _ hj) hrunP c hc hP
  have hnmem : M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
      (W (strictEventIndex rho tp) p).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
    mkNode_mem_confirmationReadAt₆₅b hf.sorted hf.onePath p tp c hc
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node p) (M.toHealing (M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp) c).core)
  obtain ⟨parent, hparent, -, hheight⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_height facts S rho s (B := P) _ hnmem
      (by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact hP) I
      (by rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st]; exact hI)
  have hparentEq : P.parent = parent := by
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hparent
    | node parent' slot root votes support rows proposer =>
        rw [Proofs.ModelProperties.named_parent_node]
        simpa only [NamedBlock.parent?, Option.some.injEq] using hparent
  subst hparentEq
  have hPthin : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h := by
    rcases hheight with hsucc | hsame
    · rw [hsucc]
      exact hparentHeight.trans (Nat.le_add_right _ _)
    · rwa [hsame]
  have hmem := Restated.seedOpeningProposal_mem_of_gateOffOn facts S Hs Xb hf hHs hHsXb hsb
    hopenPos hprop hloProposal hvoteHor c hc hP hPrun hPthin
    (fun w hw => (hvoteRead w hw).2) (fun w hw => (hvoteRead w hw).1) hrunP
  have hvoteNext : M.vote_time S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    hvoteHi.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q))
  have hpostFrozen : S.E.t_GST ≤ M.proposal_time S.E (s - 1) := by
    refine hpostPrev2.trans ?_
    refine (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans ?_
    refine (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S (r := q - 2) (q := q - 1) hq21).trans ?_
    refine facts.sch.proposal_time_mono S.E ?_
    have hsucc : s = (M.opening_slot S.hc (q - 1)) + S.hc.R := by
      have h := facts.gr.opening_slot_succ_eq S.hc (q - 1)
      rw [hqPred] at h
      exact h
    rw [hsucc]
    have key2 : ∀ a R : Nat, 2 ≤ R → a ≤ a + R - 1 := by
      intro a R h
      omega
    exact key2 _ _ S.hc.R_ge_two
  have hcutHor : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon := by
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    have h6 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc q)
    have hΔ := S.E.Δ_pos
    linarith
  refine ⟨hqpos, hpostPrev, hpostFrozen, hpostVote, hcutHor, hhor, hparentHeight,
    hproposerFrontier, hproposerGate, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₆₅b facts]
    exact (hvoteRead v hv).2
  · intro v hv
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₆₅b facts]
    exact (hvoteRead v hv).1
  · intro v hv
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_T₆₅b facts]
    exact hmem v hv (M.vote_time S.E s) (le_refl _)
  · intro v hv
    rw [tickStore_h_max₆₅b facts]
    exact (hconfRead v hv).2
  · intro v hv
    rw [tickStore_h_j₆₅b facts]
    exact (hconfRead v hv).1
  · intro v hv
    rw [tickStore_T₆₅b facts]
    exact hmem v (hHs _ _ hvoteConf hv) (M.confirmation_time S.E s) hvoteConf
  · intro v hv
    exact (facts.sto.Sts_toHealing_h_max _).trans (hnextRead v hv).2
  · intro v hv
    show (M.toHealing _).toFG.h_j + 2 ≤ Mh
    rw [facts.sto.toHealing_h_j]
    exact (hnextRead v hv).1
  · intro v hv
    show P.erase ∈ (M.toHealing _).toFG.toSG.toGoldfishStore.T
    rw [facts.sto.toHealing_gs_T]
    exact hmem v (hHs _ _ hvoteNext hv) ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
      hvoteNext

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

/-- Along the path `W` with the admissible fields `hf`, if slot `s`'s proposer is in `Xb` and `P` is
    a proposal its duty can return at its read with the cache `c`, then `P`'s parent is a run block
    read through `Xb` along `W`. -/
theorem proposedParent_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hprop : S.E.proposer s ∈ Xb)
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
    Restated.RunBlockOn M S rho W Xb P.parent := by
  have _hr_0 : M.reachedNode (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (M.proposal_time S.E s)) (W (strictEventIndex rho (M.proposal_time S.E s))) (hf.onePath (strictEventIndex rho (M.proposal_time S.E s))).1 (S.E.proposer s)
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node (S.E.proposer s))
    (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core)
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty Protocol.ProposalRowSource.poolAndCarried S.hc
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
  have _hr_pay : M.reachedStore (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s)) :=
    facts.sto.reachedStore_setClock S.E _ _ (facts.nd.reachedStore_of_node _ _hr_0)
  have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts (M.gradeContract c)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s)) _ P hP I hI L hL
  have hmem : P.parent ∈
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.bodies := by
    have h := hpay.1
    rw [facts.hd.Sts_setClock_bodies] at h
    exact h
  exact Restated.runBlock_of_stateBefore_memOn facts S W Xb hprop hmem

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

/-- Along the path `W` with the admissible fields `hf` and the honest committees `hcom`: let `P` and
    `P'` be proposals of the opening slots of rounds `q` and `q'` with `q + 2 ≤ q'`, `P` a run block
    of height `Mh`, graded 2 at round `q' − 1` by every member of the set for that round's grade-2
    domain time and in the filtered tree of every round-`(q' − 1)` action read, every
    round-`(q' − 1)` action carrier an ancestor of the parent of every proposal input of round
    `q'`'s opening proposer, `P'`'s parent of height at most `Mh` (`hparentCap`), and
    `lo ≤ opening (q' − 1 − η_SG)`. Then `P` is graded 2 at round `q' − 1` by those members, `P` is
    an ancestor of `P'`'s parent, and the two have the same height. -/
theorem seedExactOpening_gradePackageOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q q' : Round} {C' P P' : NamedBlock V}
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
    (c' : M.Cache)
    (hc' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
        (S.E.proposer (M.opening_slot S.hc q'))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q'))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
        (S.E.proposer (M.opening_slot S.hc q'))).cache ⇢ c')
    (hP' : M.proposal_with (M.gradeContract c')
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q')))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
        (S.E.proposer (M.opening_slot S.hc q'))).st
        (M.proposal_time S.E (M.opening_slot S.hc q'))) ⇢ some P')
    (hcarrier' : Restated.ProposerCarrierAtOn M S Hs q')
    (_hceiling' : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb
      Mh q' C')
    (_hgradeNext : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) Phase.g2),
      P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) Phase.g2)) v).st (q + 1) Phase.g2
            P.erase ⇢ b → b = true)
    (hPrun : Restated.RunBlockOn M S rho W Xb P)
    (hexact : (M.derive_named S.E S.cfg P).h = Mh)
    (_hM : 1 ≤ Mh)
    (hqq' : q + 2 ≤ q')
    (_hpostNext : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
    (hhorPrev : (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)) ≤ rho.horizon)
    (_hactionFrontier : ∀ k, q + 1 ≤ k → k ≤ q' - 1 →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w) k,
      n.st.core.h_max = Mh)
    (_hactionGate : ∀ k, q + 1 ≤ k → k ≤ q' - 1 →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w) k,
      n.st.core.h_j + 2 ≤ Mh)
    (_of_namedGradeFormsAt_persists_through_gateOffActionWindow :
      (∀ v ∈ Hs (M.domain S.E S.hc (q' - 1) Phase.g2),
        P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v).st (q' - 1) Phase.g2
              P.erase ⇢ b → b = true) ∧
        ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
          ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) w) (q' - 1),
          P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (_of_openingAnchorsAligned_of_roundCeiling :
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) w) (q' - 1),
      ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
      ∀ G : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c') S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q')))
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
              (S.E.proposer (M.opening_slot S.hc q'))).st
            (M.proposal_time S.E (M.opening_slot S.hc q')))
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
              (S.E.proposer (M.opening_slot S.hc q'))).record c').st.core) ⇢ I →
        Block.Preceq G I.parent)
    (hparentCap : (M.derive_named S.E S.cfg P'.parent).h ≤ Mh)
    (hlo : lo ≤ M.opening S.E S.hc (q' - 1 - S.hc.η_SG)) :
    (∀ v ∈ Hs (M.domain S.E S.hc (q' - 1) Phase.g2),
      P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) Phase.g2)) v).st (q' - 1) Phase.g2
            P.erase ⇢ b → b = true) ∧
      NamedBlock.Preceq P P'.parent ∧
      (M.derive_named S.E S.cfg P'.parent).h =
        (M.derive_named S.E S.cfg P).h := by
  have hspan : q + 1 ≤ q' - 1 := by
    have key : ∀ a b : Nat, a + 2 ≤ b → a + 1 ≤ b - 1 := by
      intro a b h
      omega
    exact key q q' hqq'
  have hroundPos : 0 < q' - 1 :=
    Nat.zero_lt_of_lt (lt_of_lt_of_le (Nat.lt_succ_self q) hspan)
  have hforms := _of_namedGradeFormsAt_persists_through_gateOffActionWindow.1
  obtain ⟨x, hx⟩ : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1)))).Nonempty := by
    have h := Restated.honest_nonempty_of_committeesOn facts S Hs hcom ((M.opening_slot S.hc (q' - 1)))
    rwa [Restated.confirmation_time_opening_slot facts S (q' - 1)] at h
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₅b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) x) (q' - 1)
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c') S.E S.hc
    (S.node (S.E.proposer (M.opening_slot S.hc q')))
    (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
        (S.E.proposer (M.opening_slot S.hc q'))).st
      (M.proposal_time S.E (M.opening_slot S.hc q')))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
        (S.E.proposer (M.opening_slot S.hc q'))).record c').st.core)
  have hPG : Block.Preceq P.erase G :=
    (priv% Proofs.Claims.Restated.Claim13beRoute3_54
      DecoupledConsensusModel.Sts.Restated.formsW_preceq_actionSGBlockAt₅₄s) facts S Hs Xb hf
      hHs hHsXb hroundPos hhorPrev hforms (hHs _ _ (facts.gr.domain_le_a S (q' - 1) .g0) hx) n hn
      (_of_namedGradeFormsAt_persists_through_gateOffActionWindow.2 x hx n hn) hlo A2 hA2 G hG
  have hGI : Block.Preceq G I.parent :=
    _of_openingAnchorsAligned_of_roundCeiling x hx n hn A2 hA2 G hG I hI
  have hI' : M.with_proposal_input (M.gradeContract c') S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q')))
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).st
        (M.proposal_time S.E (M.opening_slot S.hc q'))) c').core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  obtain ⟨parent, hparent, hparentErase⟩ :=
    facts.dt.proposal_with_parent? _ _ _ _ _ _ P' _
      (by rw [facts.dt.proposal_with_store_with_cache]; exact hP') rfl I hI'
  have hparentEq : P'.parent = parent := by
    cases P' with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hparent
    | node parent' slot root votes support rows proposer =>
        rw [Proofs.ModelProperties.named_parent_node]
        simpa only [NamedBlock.parent?, Option.some.injEq]
          using hparent
  subst hparentEq
  have hbelow' : Block.Preceq P.erase P'.parent.erase := by
    rw [hparentErase]
    exact preceq_trans_Preceq hPG hGI
  obtain ⟨A, hAparent, hAerase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift P'.parent hbelow'
  have hprop' : S.E.proposer ((M.opening_slot S.hc q')) ∈ Xb := by
    have h := hcarrier' 0 (by decide)
    simp only [Nat.add_zero] at h
    exact hHsXb _ h
  have hparentRun : Restated.RunBlockOn M S rho W Xb P'.parent :=
    Restated.proposedParent_runBlockOn facts S Hs Xb hf hprop' c' hc' hP'
  have hArun : Restated.RunBlockOn M S rho W Xb A :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hparentRun hAparent
  have hPA : P = A := by
    apply hf.rootCollisionFree.root_injective P A hPrun hArun P A
      (Or.inl (Proofs.NamedAncestry.named_self P))
      (Or.inr (Proofs.NamedAncestry.named_self A))
    rw [← Proofs.NamedWire.erase_root P, ← Proofs.NamedWire.erase_root A, hAerase]
  have hnamed : NamedBlock.Preceq P P'.parent := by
    rw [hPA]
    exact hAparent
  refine ⟨hforms, hnamed, ?_⟩
  have hlower : Mh ≤ (M.derive_named S.E S.cfg P'.parent).h := by
    rw [← hexact]
    exact facts.cs.derive_height_mono S.E S.cfg hnamed
  rw [hexact]
  exact Nat.le_antisymm hparentCap hlower

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
