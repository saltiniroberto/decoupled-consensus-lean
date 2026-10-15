import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Views_VoteSetValidityCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Pool
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Goldfish vote cones along one path

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`, read along the path
`W` of the bundle `AdmissibleFieldsOn`: the votes blocks carry and the votes visible to a validator,
vote-duty heads as run blocks and their emission, the availability of committee heads before the
support cutoff, the eligibility of the cone path at the next vote duty, and the step that carries a
Goldfish vote cone from slot `s` to slot `s + 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₅₇ {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
    (hb : b % Δ = 0) (hab : a < b) : a + Δ ≤ b := by
  obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero ha
  obtain ⟨l, rfl⟩ := Int.dvd_of_emod_eq_zero hb
  have hkl : k < l := by
    by_contra h
    have h' : l ≤ k := not_lt.mp h
    have : Δ * l ≤ Δ * k := Int.mul_le_mul_of_nonneg_left h' (le_of_lt hΔ)
    omega
  have h1 : k + 1 ≤ l := hkl
  have h2 : Δ * (k + 1) ≤ Δ * l := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hΔ)
  rw [Int.mul_add, Int.mul_one] at h2
  exact h2

/-- A slot's vote time plus one delay is at most the slot's support cutoff. -/
private theorem vote_time_add_delta_le_support_cutoff₅₇ (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.vote_time S.E s + S.E.Δ ≤ M.support_cutoff S.E s :=
  add_delta_le_of_lt_emod₅₇ S.E.Δ_pos (facts.sch.vote_time_emod_delta S s)
    (facts.sch.support_cutoff_emod_delta S s) (Restated.vote_time_lt_support_cutoff_l49 facts S s)

/-- For a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of `rho`
    lead to from `W m`. -/
private theorem onePath_reach₅₇ {S : Setup V} {rho : Record.Run V}
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

/-- For a path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₅₇ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₇ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₇ (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world of a path `W` before the event at index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₅₇ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₇ S rho hsorted]
  exact (hW _).1

/-- On a path `W` of a run sorted by key, the node state staged at `t` from `v`'s node state in
    `W (strictEventIndex rho t)` with a cache update outcome is in `confirmationReadAt` for `v` at
    `t`. -/
private theorem mkNode_mem_confirmationReadAt₅₇ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (t : Time) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) v).st.core.toHealing t
      (W (strictEventIndex rho t) v).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) v).st t)
        (W (strictEventIndex rho t) v).record c ∈
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v t :=
  ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₅₇ hsorted hW t, c, hc, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₇ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events has a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₇ {rho : Record.Run V}
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

/-- Writing a cache into a store keeps the confirmation-membership invariant. -/
private theorem invariant_store_with_cache₅₇ (facts : Record.Facts M) (E : Env V)
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

/-- If `votes` with the support votes `support` give cone support for the descendants of `B` over
    `Hon` at slot `k` in the tree `T`, and `votes` is a valid vote set for `k`, then every outcome
    of `B`'s supporter set has more than half of the voters counted in `votes` at `k`. -/
private theorem supporterMajority_of_cone₅₇ (facts : Record.Facts M) (E : Env V)
    {T : Finset (Block V)} {votes support : Finset (GoldfishVote V)} {k : Slot} {Hon : Finset V}
    {B : Block V}
    (hcone : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M E T votes support votes k Hon
      (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E k votes) :
    ∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M E T votes support k B ⇢ sup →
      M.voters_count E votes k < 2 * sup.card := by
  intro sup hsup
  obtain ⟨t, ht⟩ : ∃ t : GoldfishVote V → Bool, ∀ u, M.targets_under T B u ⇢ t u :=
    ⟨fun u => (facts.fc.targets_under_nonempty T B u).choose,
      fun u => (facts.fc.targets_under_nonempty T B u).choose_spec⟩
  have hsub : (E.committee k) ∩ Hon ⊆ sup := by
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨u, hu, hux, hus, X, hfind, hXslot, hBX⟩ := hcone.vote x hx.1 hx.2
    refine (facts.fc.mem_supporters_iff (_E := E) sup hsup t ht).2
      ⟨hcone.no_equiv x hx.1 hx.2, u, ?_, hus, ?_⟩
    · exact (facts.sch.mem_votes_by_iff support x u).2 ⟨hu, hux⟩
    · exact (facts.fc.targets_under_iff (t u) (ht u)).2
        ⟨X, hfind, hXslot, preceq_eq_true_iff_Preceq.mpr hBX⟩
  have hcard := Finset.card_le_card hsub
  have hcount := facts.fc.voters_count_le_committee E votes k hvalid
  have hmaj := hcone.majority
  omega

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the bundle's path `W`, every support vote carried by a block of the tree of `w`'s store in
    `W n` is among the Goldfish votes that block carries. -/
theorem coreCarriedSupportSubsetOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (W n w).st.core.T) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes :=
  Restated.carried_support_subset_of_mem_T_coreOn facts S Hs Xb hf w n hB

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the bundle's path `W`, every Goldfish vote carried by a block of the tree of `w`'s store
    in `W n` is signed by a member of its slot's committee. -/
theorem coreCarriedVoteCommitteeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (W n w).st.T) :
    ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot :=
  Restated.carriedVote_committee_of_mem_T_coreOn facts S Hs Xb hf w n hB

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if every event before index `n` is at a time at most `T`, `u` is in
    some slot's list of `w`'s store in `W n` or is included in a block of that store's tree, and
    `u`'s sender is in `Hs T`, then that sender emitted `u` along `W`. -/
theorem coreEmitsOfVoteVisibleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u : GoldfishVote V}
    (hu : (∃ k : Slot, u ∈ (W n w).st.gf_votes k) ∨ ∃ B ∈ (W n w).st.core.T, u ∈ B.gf_votes)
    (hx : u.val_index ∈ Hs T) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (Object.gfVote u) t := by
  rcases hu with ⟨k, hk⟩ | ⟨B, hB, hmem⟩
  · exact Restated.named_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT (Or.inl ⟨k, hk⟩) hx
  · obtain ⟨B', hB', hB'eq⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n w
        (W n) (hf.onePath n).1 hB
    have hmem' : u ∈ B'.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes, hB'eq]
      exact hmem
    exact Restated.named_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT
      (Or.inr ⟨B', hB', hmem'⟩) hx

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if every event before index `n` is at a time at most `T`, two votes
    visible in `w`'s store in `W n` with the same slot and the same sender in `Hs T` are the same
    vote. -/
theorem coreVoteVisibleUniqueOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u₁ u₂ : GoldfishVote V}
    (h₁ : (∃ k : Slot, u₁ ∈ (W n w).st.gf_votes k) ∨ ∃ B ∈ (W n w).st.core.T, u₁ ∈ B.gf_votes)
    (h₂ : (∃ k : Slot, u₂ ∈ (W n w).st.gf_votes k) ∨ ∃ B ∈ (W n w).st.core.T, u₂ ∈ B.gf_votes)
    (hx : u₁.val_index ∈ Hs T)
    (hval : u₂.val_index = u₁.val_index)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨t₁, he₁⟩ := Restated.coreEmitsOfVoteVisibleOn facts S Hs Xb hf hHs w n hT h₁ hx
  obtain ⟨t₂, he₂⟩ := Restated.coreEmitsOfVoteVisibleOn facts S Hs Xb hf hHs w n hT h₂ (by
    rw [hval]
    exact hx)
  rw [hval] at he₂
  exact Restated.emits_gfVote_uniqueOn facts S Hs Xb hf he₁ he₂ hslot

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if every event before index `n` is at a time at most `T`, `gst`'s
    lists and tree are contained in those of `w`'s store in `W n`, and `x ∈ Hs T`, then `x` does not
    equivocate in any outcome of `gst`'s slot-`s` voter view. -/
theorem coreVoterViewNoHonestEquivocationOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    (gst : M.GS)
    (hgf : ∀ (k : Slot) (u : GoldfishVote V), u ∈ gst.gf_votes k →
      u ∈ (W n w).st.gf_votes k)
    (hTree : ∀ B ∈ gst.T, B ∈ (W n w).st.core.T)
    {x : V} (hx : x ∈ Hs T) (s : Slot) :
    ∀ Y : Finset (GoldfishVote V), M.voter_view S.E gst s ⇢ Y →
      M.equivocates Y x = false := by
  intro Y hY
  have hview : ∀ u ∈ Y,
      ((∃ k : Slot, u ∈ (W n w).st.gf_votes k) ∨ ∃ B ∈ (W n w).st.core.T, u ∈ B.gf_votes) ∧
        u.slot = s - 1 := by
    intro u hu
    rcases facts.fc.voter_view_cases_beforeCutoff S.E gst s Y hY hu with hu | ⟨B, hBT', -, hmem, hus⟩
    · rw [mem_beforeCutoff_iff, facts.sto.mem_goldfishStore_pool_iff] at hu
      have hmem := hgf (s - 1) u hu.1
      exact ⟨Or.inl ⟨s - 1, hmem⟩,
        (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w n).slot _ u hmem⟩
    · exact ⟨Or.inr ⟨B, hTree B hBT', hmem⟩, hus⟩
  apply facts.sch.equivocates_eq_false_of_card_le_one
  refine Finset.card_le_one.mpr ?_
  intro u₁ hu₁ u₂ hu₂
  rw [facts.sch.mem_votes_by_iff] at hu₁ hu₂
  obtain ⟨hv₁, hs₁⟩ := hview u₁ hu₁.1
  obtain ⟨hv₂, hs₂⟩ := hview u₂ hu₂.1
  exact Restated.coreVoteVisibleUniqueOn facts S Hs Xb hf hHs w n hT hv₁ hv₂
    (by rw [hu₁.2]; exact hx)
    (by rw [hu₂.2, hu₁.2]) (by rw [hs₁, hs₂])

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the bundle's path `W`, with `st` the core store of `w`'s store in
    `W (strictEventIndex rho (vote_time s))` staged to `vote_time s`, every outcome of the voter
    view of `st` at its slot is a valid vote set for the slot before. -/
theorem corePreparedVoteViewValidOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (s : Slot) :
    let st := (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
      (M.vote_time S.E s)).core
    ∀ Y : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ Y →
      Protocol.VoteSetValid S.E (st.s - 1) Y := by
  intro st Y hY
  set i := strictEventIndex rho (M.vote_time S.E s) with hi_def
  have hs : st.s = s := by
    show (M.ns_setClock S.E (W i w).st (M.vote_time S.E s)).core.s = s
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hcore : st = M.store_with_t_s (W i w).st.core (M.vote_time S.E s)
      (S.E.slotOf (M.vote_time S.E s)) :=
    facts.hd.setClock_core_eq_store_with_t_s _ _ _
  rw [hs] at hY ⊢
  rw [hcore] at hY
  have hY' := (facts.fc.voter_view_set_clock_slot S.E (W i w).st.core _ _ s Y).mp hY
  have hpool := Restated.voteSetValid_pool_stateBeforeOn facts S Hs Xb hf w i (s - 1)
  have hcarried : ∀ B ∈ (W i w).st.core.T,
      ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    intro B hB u hu
    exact Restated.coreCarriedVoteCommitteeOn facts S Hs Xb hf w i hB u hu
  exact Restated.Vocabulary.Protocol.voteSetValid_voter_view_of_carried facts
    (E := S.E) (st := (W i w).st.core) s hpool hcarried Y hY'

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `w ∈ Xb`, every head the in-tree head computation can return at
    `w`'s node state staged at `vote_time d` with the cache outcome `c` is in the tree of that node
    state's core store and is the erasure of a run block read through `Xb` along `W`. -/
theorem coreVoterHeadRunBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (d : Slot)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
      (M.vote_time S.E d)
      (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
      (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
    ∃ H : NamedBlock V, H.erase = Hd ∧ Hd ∈ n.st.core.T ∧
      Restated.blockInRunOn M S rho W Xb H := by
  intro n T hT L hL L' hL' Hd hHd
  set i := strictEventIndex rho (M.vote_time S.E d) with hi_def
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E d)) c :=
    facts.nd.mkNode_st _ _ _
  have hstT : n.st.core.T = (W i w).st.core.T := by
    rw [hnst, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T]
  have hinvPre := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i w
    (W i) (hf.onePath i).1).1
  have hinv := invariant_store_with_cache₅₇ facts S.E S.cfg _ c
    (facts.hd.invariant_clock S.E S.cfg (W i w).st (M.vote_time S.E d) hinvPre)
  rw [← hnst] at hinv
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
    (facts.hd.Sts_voter_filtered_block_tree_subset S.E n.st.core n.st.core.s T hT) Hd hHd
  have hHpre : Hd ∈ (W i w).st.core.T := by
    rw [← hstT]
    exact hHmem
  obtain ⟨H, hHerase, hHrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hw (M.vote_time S.E d) hHpre
  exact ⟨H, hHerase, hHmem, hHrun⟩

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `x ∈ Xb`, `C` is a run block read through `Xb`, and `x` emitted
    at `vote_time s` the Goldfish vote with head `C`, then `C.erase` is in the tree of `x`'s store
    in `W (strictEventIndex rho (vote_time s))` staged to `vote_time s`. -/
theorem coreEmittedHeadMemOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {x : V} (hx : x ∈ Xb) {s : Slot} {C : NamedBlock V}
    (hCrun : Restated.blockInRunOn M S rho W Xb C)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W x
      (.gfVote ⟨x, s, C.erase.root⟩) (M.vote_time S.E s)) :
    C.erase ∈ (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st
      (M.vote_time S.E s)).core.T := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing (M.vote_time S.E s)
    (W (strictEventIndex rho (M.vote_time S.E s)) x).cache
  have h := Restated.named_emittedHead_mem_voteDutyReadOn facts S Hs Xb hf hx hCrun hemit c hc
  rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `x ∈ Xb`, `C` is a run block read through `Xb` and `C.erase` is
    in the tree of `x`'s store before `vote_time s` staged to `vote_time s`, then looking up `C`'s
    root in that tree finds `C.erase`. -/
theorem coreFindEmittedHeadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {x : V} (hx : x ∈ Xb) {s : Slot} {C : NamedBlock V}
    (hCrun : Restated.blockInRunOn M S rho W Xb C)
    (hmem : C.erase ∈ (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st
      (M.vote_time S.E s)).core.T) :
    Block.find? (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st
      (M.vote_time S.E s)).core.T C.erase.root = some C.erase := by
  apply find?_eq_some_of_unique hmem
  intro Y hY hroot
  have hYpre : Y ∈ (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.T := by
    rw [facts.hd.Sts_setClock_core_T] at hY
    exact hY
  obtain ⟨D, hDerase, hDrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hx (M.vote_time S.E s) hYpre
  have hrootNamed : D.root = C.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root C, hDerase]
    exact hroot
  have hDC : D = C :=
    hf.rootCollisionFree.root_injective D C hDrun hCrun D C
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hrootNamed
  rw [← hDerase, hDC]

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `w ∈ Hs (vote_time s)`, `0 < s`, `w` is on `s`'s committee,
    `vote_time s` is inside the horizon, `lo ≤ vote_time s`, and `w`'s ticks at `vote_time s` pass
    the grade-1 awake test, then every head the in-tree head computation can return at `w`'s node
    state staged at `vote_time s` is the erasure of a run block `C` read through `Xb`, and `w` emits
    at `vote_time s` the Goldfish vote of slot `s` for `C`'s root. -/
theorem coreVoterHeadEmitsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.vote_time S.E s))
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.vote_time S.E s)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
    ∃ C : NamedBlock V, C.erase = Hd ∧
      Restated.blockInRunOn M S rho W Xb C ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (M.vote_time S.E s) := by
  intro n T hT L hL L' hL' Hd hHd
  obtain ⟨C, hChead, -, hCrun⟩ :=
    Restated.coreVoterHeadRunBlockOn facts S Hs Xb hf (hHsXb _ hw) s c hc T hT L hL L' hL' Hd hHd
  have hem := Restated.voterHead_emits_of_coreOn facts S Hs Xb hf hw hs hcommittee hhor hgat
    c hc hrun T hT L hL L' hL' Hd hHd
  refine ⟨C, hChead, hCrun, ?_⟩
  rw [hChead]
  exact hem

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `p ∈ Hs (max t lo)`, `w ∈ Hs GammaOut`, `p` accepts the
    non-genesis block `B` at `t < GammaIn`, `lo ≤ GammaIn`, `GammaOut = GammaIn + Δ` is inside the
    horizon, and the finalized block of `w`'s store in every world of `W` up to `GammaOut` is an
    ancestor of `B`, then `w` admits `B` along `W` before `GammaOut`. -/
theorem coreBlockAdmittedAfterCutoffOn (facts : Record.Facts M)
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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `v ∈ Hs (support_cutoff s)`, `lo ≤ vote_time s`, the support
    cutoff is inside the horizon, the FG root of `v`'s store before `vote_time (s + 1)` staged to
    that time is an ancestor of `B`, and every committee member of `s` in `Hs (vote_time s)` voted a
    run block descending from `B`, then every head voted by a committee member of `s` in
    `Hs (confirmation_time s)` is genesis or admitted by `v` before the support cutoff. -/
theorem coreHonestHeadsAvailableOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st
          (M.vote_time S.E (s + 1))).core).toFG) B)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    ∀ X : Block V, Restated.HonestHeadOn M S rho W Hs Xb s X →
      X = Block.genesis ∨ Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v X
        (M.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  have hxvote : x ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hx
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hxvote hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hYemit rfl
  have hrootEq : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hCY : C = Y := by
    apply hf.rootCollisionFree.root_injective C Y hCrun hYrun
      C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y))
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootEq
  have hBX : Block.Preceq B X := by
    simpa only [← hCY, hCX] using hBY
  have hXemit' : Restated.Vocabulary.Execution.NamedRun.emits M S rho W x
      (.gfVote ⟨x, s, C.erase.root⟩) (M.vote_time S.E s) := by
    simpa only [hCX] using hXemit
  have hmem := Restated.coreEmittedHeadMemOn facts S Hs Xb hf (hHsXb _ hx) hCrun hXemit'
  have hmemPre : C.erase ∈ (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.T := by
    rw [facts.hd.Sts_setClock_core_T] at hmem
    exact hmem
  rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts S Hs Xb hf
      x (M.vote_time S.E s) hmemPre with
    hgenC | ⟨D, i, ta, hDeq, hacc, hta⟩
  · have hXgen : X = Block.genesis := by
      rw [← hCX, hgenC]
    exact False.elim (hgen hXgen)
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot D]
      exact Nat.zero_lt_of_lt (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W
        hf.onePath hacc)
    have hDX : D.erase = X := hDeq.trans hCX
    have hroot' : Block.Preceq
        (M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core).toFG) B := by
      have h := hroot
      rw [facts.hd.setClock_core_eq_store_with_t_s] at h
      exact (congrArg (fun Z => Block.Preceq Z B) (facts.fc.get_fg_root_set_clock_slot
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core
        (M.vote_time S.E (s + 1)) (S.E.slotOf (M.vote_time S.E (s + 1))))).mp h
    have hFhist : ∀ j : Nat,
        j ≤ (rho.events.filter (fun e => decide (e.time < M.support_cutoff S.E s))).length →
          Block.Preceq (W j v).st.core.F D.erase := by
      intro j hj
      have hjVote : j ≤ (rho.events.filter
          (fun e => decide (e.time < M.vote_time S.E (s + 1)))).length :=
        hj.trans (Restated.strict_filter_length_mono rho
          ((facts.sch.Sts_support_cutoff_lt_view_freeze S.E s).le.trans
            (facts.sch.view_freeze_lt_vote_time_succ S.E s).le))
      have hFD := Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts
        S rho hf.sorted hjVote (W j) (hf.onePath j).1
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))))
        (onePath_slice₅₇ W hf.onePath hjVote) hroot'
      rw [hDX]
      exact preceq_trans_Preceq hFD hBX
    have hcutIn : M.vote_time S.E s ≤ M.support_cutoff S.E s - S.E.Δ :=
      le_sub_iff_add_le.mpr (vote_time_add_delta_le_support_cutoff₅₇ facts S s)
    have hxmax : x ∈ Hs (max ta lo) :=
      hHs _ _ (max_le (le_of_lt hta) hpost) hxvote
    have hadmit := Restated.coreBlockAdmittedAfterCutoffOn facts S Hs Xb hf hHs hHsXb hxmax hv hDpos
      hacc (hta.trans_le hcutIn) (hpost.trans hcutIn) (sub_add_cancel _ _) hhor hFhist
    rw [hDX] at hadmit
    exact hadmit

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- `coreVoterHeadEmitsOn`: a committee member's vote-duty head is a run block and is the head it
    votes for at `vote_time s`. -/
theorem voterHead_runBlock_and_emitsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.vote_time S.E s))
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.vote_time S.E s)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
    ∃ C : NamedBlock V, C.erase = Hd ∧
      Restated.blockInRunOn M S rho W Xb C ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (M.vote_time S.E s) :=
  Restated.coreVoterHeadEmitsOn facts S Hs Xb hf hHsXb hw hs hcommittee hhor hgat c hc hrun

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- The cone support for `C`'s descendants, the supporter majority for `C` and the validity of the
    voter view at `w`'s vote-duty node state of slot `s + 1`, under the hypotheses of
    `coreGoldfishConePathEligible_of_transportOn` without its vote inputs. -/
private theorem coneSupport_and_majority₅₇ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Xb)
    (havailable : Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s w
      (M.support_cutoff S.E s))
    (hcutoff : ∀ {x : V}, x ∈ Hs (M.confirmation_time S.E s) → ∀ {X : NamedBlock V},
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W x
        (.gfVote ⟨x, s, X.erase.root⟩) (M.vote_time S.E s) →
      (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ beforeCutoff
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.timestamp_vote
        (M.view_freeze S.E s)
        ((W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.pool s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let st := n.st.core
    ∀ votes : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ votes →
    ∀ support : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ support →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T votes support votes (st.s - 1)
        (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) ∧
      (∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M S.E st.T votes support
          (st.s - 1) C ⇢ sup →
        M.voters_count S.E votes (st.s - 1) < 2 * sup.card) ∧
      Protocol.VoteSetValid S.E (st.s - 1) votes := by
  intro n st votes hvotesV support hsupp
  set i := strictEventIndex rho (M.vote_time S.E (s + 1)) with hi_def
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) _ := facts.nd.mkNode_st _ _ _
  have hslot : st.s = s + 1 := by
    show n.st.core.s = s + 1
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hstT : st.T = (W i w).st.core.T := by
    show n.st.core.T = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hTst : (M.toHealing st).toFG.toSG.toGoldfishStore.T = (W i w).st.core.T := by
    rw [facts.sto.toHealing_gs_T]
    exact hstT
  have hgfst : ∀ k : Slot, (M.toHealing st).toFG.toSG.toGoldfishStore.gf_votes k
      = (W i w).st.core.gf_votes k := by
    intro k
    rw [facts.sto.toHealing_gs_gf_votes]
    show n.st.core.gf_votes k = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_gf_votes]
  have hpoolst : ∀ k : Slot, (M.gs_pool (M.toHealing st).toFG.toSG.toGoldfishStore k)
      = M.store_pool (W i w).st.core k := by
    intro k
    rw [facts.sto.toHealing_gs_pool]
    show M.store_pool n.st.core k = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_pool]
  have htvst : (M.toHealing st).toFG.toSG.toGoldfishStore.timestamp_vote
      = (W i w).st.core.timestamp_vote := by
    rw [facts.sto.toHealing_gs_timestamp_vote]
    show n.st.core.timestamp_vote = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_timestamp_vote]
  have htbst : (M.toHealing st).toFG.toSG.toGoldfishStore.timestamp_block
      = (W i w).st.core.timestamp_block := by
    rw [facts.sto.toHealing_gs_timestamp_block]
    show n.st.core.timestamp_block = _
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_timestamp_block]
  have hT : ∀ (j : Nat) (e : Record.Event V), j < i → rho.events[j]? = some e →
      e.time ≤ M.confirmation_time S.E s := by
    intro j e hj he
    exact le_of_lt (lt_of_lt_of_le (time_lt_of_lt_strict₅₇ hf.sorted he hj)
      (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
        (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)))
  have hcone : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T votes support votes
      (st.s - 1) (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) := by
    apply Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts
      (by simp only [hslot, Nat.add_sub_cancel]; exact hcom s)
      (subset_refl _)
      (facts.fc.voter_support_view_subset S.E _ _
        (fun B hB => Restated.coreCarriedSupportSubsetOn facts S Hs Xb hf w i (hTst ▸ hB))
        support hsupp votes hvotesV)
    · intro x hxCommittee hxHonest
      exact Restated.coreVoterViewNoHonestEquivocationOn facts S Hs Xb hf hHs w i hT
        (M.toHealing st).toFG.toSG.toGoldfishStore
        (fun k u hu => (congrArg (u ∈ ·) (hgfst k)).mp hu)
        (fun B hB => hTst ▸ hB) hxHonest st.s votes hvotesV
    · intro x hxCommittee hxHonest
      have hxCommittee' : x ∈ S.E.committee s := by
        simpa only [hslot, Nat.add_sub_cancel] using hxCommittee
      have hxvote : x ∈ Hs (M.vote_time S.E s) :=
        hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hxHonest
      obtain ⟨X, hCX, hXrun, hXemit⟩ := hvotes x hxvote hxCommittee'
      have hhead : Restated.HonestHeadOn M S rho W Hs Xb s X.erase :=
        ⟨x, hxHonest, hxCommittee', ⟨X, rfl, hXrun⟩, hXemit⟩
      have hvisible : X.erase ∈ (W i w).st.T ∧
          stampedBefore (W i w).st.timestamp_block (M.view_freeze S.E s) X.erase = true := by
        rcases havailable X.erase hhead with hgen | hadmit
        · rw [hgen]
          exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
            (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
        · have hvis := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit
            (facts.sch.support_cutoff_le_vote_time_succ S.E s)
          refine ⟨hvis.1, ?_⟩
          rw [stampedBefore_eq_occurrenceBefore] at hvis ⊢
          exact occurrenceBefore_mono
            (le_of_lt (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s)) hvis.2
      have hXmem : X.erase ∈ (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))).core.T := by
        rw [facts.hd.Sts_setClock_core_T]
        exact hvisible.1
      have hfind := Restated.coreFindEmittedHeadOn facts S Hs Xb hf hw hXrun hXmem
      have hcut := hcutoff hxHonest hXemit
      have hXslot : X.erase.slot ≤ s :=
        Restated.emitted_vote_head_slot_le_of_store_memOn facts S Hs Xb hf
          (hHsXb _ hxHonest) hw hXemit rfl hvisible.1 (by rfl)
      have hfindst : Block.find? st.T X.erase.root = some X.erase := by
        show Block.find? n.st.core.T X.erase.root = some X.erase
        rw [hnst]
        try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
        exact hfind
      refine ⟨X.erase, hCX, by rw [hslot, Nat.add_sub_cancel]; exact hXslot, ?_, hfindst⟩
      rw [mem_beforeCutoff_iff] at hcut
      have hpool : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈
          (M.toHealing st).toFG.toSG.toGoldfishStore.pool s := by
        show _ ∈ M.gs_pool _ s
        rw [hpoolst]
        exact hcut.1
      obtain ⟨τ, hτ, hτlt⟩ := exists_stamp_of_stampedBefore hcut.2
      obtain ⟨σ, hσ, hσlt⟩ := exists_stamp_of_stampedBefore hvisible.2
      rw [hslot, Nat.add_sub_cancel]
      exact facts.sch.mem_voter_support_view_of_pool S.E _ s hpool
        (by rw [htvst]; exact hτ) hτlt
        (by rw [hTst.trans hstT.symm]; exact hfindst) hXslot
        (by rw [htbst]; exact hσ) hσlt support (by rw [← hslot]; exact hsupp)
  have hvotesV' : M.voter_view S.E
      (M.toHealing (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))).core).toFG.toSG.toGoldfishStore
      (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))).core.s ⇢ votes := by
    simpa only [st, n, hnst, facts.nd.mkNode_st, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hvotesV
  have hvalid : Protocol.VoteSetValid S.E (st.s - 1) votes := by
    have h := Restated.corePreparedVoteViewValidOn facts S Hs Xb hf w (s + 1) votes hvotesV'
    show Protocol.VoteSetValid S.E (n.st.core.s - 1) votes
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact h
  exact ⟨hcone, supporterMajority_of_cone₅₇ facts S.E hcone hvalid, hvalid⟩

/-- The conclusions of `coneSupport_and_majority₅₇`, with the heads' availability from
    `coreHonestHeadsAvailableOn` and the votes' arrival from `gfVote_in_cutoff_view_after_gstOn`. -/
private theorem coneSupport_and_majority_of_root₅₇ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) C)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let st := n.st.core
    ∀ votes : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ votes →
    ∀ support : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ support →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T votes support votes (st.s - 1)
        (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) ∧
      (∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M S.E st.T votes support
          (st.s - 1) C ⇢ sup →
        M.voters_count S.E votes (st.s - 1) < 2 * sup.card) ∧
      Protocol.VoteSetValid S.E (st.s - 1) votes := by
  have hwcut : w ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hw
  refine coneSupport_and_majority₅₇ facts S Hs Xb hf hHs hHsXb hcom hs hvotes (hHsXb _ hw)
    (Restated.coreHonestHeadsAvailableOn facts S Hs Xb hf hHs hHsXb hwcut hpost
      ((facts.sch.Sts_support_cutoff_le_confirmation_time S.E s).trans hhor) hroot hvotes)
    ?_ c hc
  intro x hx X hXemit
  exact Restated.gfVote_in_cutoff_view_after_gstOn facts S Hs Xb hf hHs
    (hHs _ _ (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hx) hs hpost
    hXemit rfl hwcut
    (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
    (facts.sch.support_cutoff_le_vote_time_succ S.E s)
    (le_of_lt (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s))
    ((facts.sch.Sts_support_cutoff_le_confirmation_time S.E s).trans hhor)

/-- Under the bundle along `W` and the committee majority, if `0 < s`, every committee member of `s`
    in `Hs (vote_time s)` voted a run block descending from `C`, `w ∈ Xb` has every head of `s`'s
    committee available before the support cutoff and their votes in its slot-`s` pool before the
    freeze, and `w` has the cone's vote inputs at `C`, then at `w`'s vote-duty node state of slot
    `s + 1` the voter views give cone support for `C`'s descendants over `Hs (confirmation_time s)`,
    `C`'s supporters are a majority, and every block from `w`'s anchor (exclusive) to `C`
    (inclusive) is in the candidate tree and passes the score and eligibility tests. -/
theorem coreGoldfishConePathEligible_of_transportOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Xb)
    (havailable : Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s w
      (M.support_cutoff S.E s))
    (hcutoff : ∀ {x : V}, x ∈ Hs (M.confirmation_time S.E s) → ∀ {X : NamedBlock V},
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W x
        (.gfVote ⟨x, s, X.erase.root⟩) (M.vote_time S.E s) →
      (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ beforeCutoff
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.timestamp_vote
        (M.view_freeze S.E s)
        ((W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.pool s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let st := n.st.core
    ∀ votes : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ votes →
    ∀ support : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ support →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T votes support votes (st.s - 1)
        (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) ∧
      (∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M S.E st.T votes support
          (st.s - 1) C ⇢ sup →
        M.voters_count S.E votes (st.s - 1) < 2 * sup.card) ∧
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc st.s) ⇢ A →
      ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C →
        (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E st st.s ⇢ T → D ∈ T) ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            ∀ g : Nat, M.goldfish_score S.E st.T votes support (st.s - 1) D ⇢ g →
              M.voters_count S.E votes (st.s - 1) < 2 * g) ∧
          ∀ b : Bool, M.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D ⇢ b → b = true := by
  intro n st votes hvotesV support hsupp
  obtain ⟨hcone, hmajority, hvalid⟩ := coneSupport_and_majority₅₇ facts S Hs Xb hf hHs hHsXb hcom
    hs hvotes hw havailable hcutoff c hc votes hvotesV support hsupp
  have hn : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
    mkNode_mem_confirmationReadAt₅₇ hf.sorted hf.onePath w (M.vote_time S.E (s + 1)) c hc
  refine ⟨hcone, hmajority, ?_⟩
  intro A hA D hAD hDne hDC
  have hDmajority : ∀ g : Nat, M.goldfish_score S.E st.T votes support (st.s - 1) D ⇢ g →
      M.voters_count S.E votes (st.s - 1) < 2 * g :=
    facts.fc.ConeSupport_eligible S.E st.T votes support votes (st.s - 1)
      (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) hcone.majority hcone.counted
      hcone.sub hcone.no_equiv hcone.vote hvalid
      (fun X hX => preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hDC hX))
  refine ⟨?_, Or.inr hDmajority, ?_⟩
  · intro T hT'
    by_cases hEq : D = C
    · subst D
      exact hinputs.candidate T hT'
    · exact hinputs.path A hA T hT' D hAD hDne hDC hEq
  · intro b hb
    obtain ⟨g, hg⟩ := facts.fc.goldfish_score_nonempty S.E st.T votes support (st.s - 1) D
    exact (facts.fc.goldfish_eligible_iff S.E st.σ st.h_max st.T st.s votes support (st.s - 1) D
      b hb g hg).2 (Or.inr (Or.inl (hDmajority g hg)))


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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, every committee member of `s` in `Hs (vote_time s)`
    voted a run block descending from `C`, and `w ∈ Hs (vote_time (s + 1))` has the cone's vote
    inputs at `C`, then the conclusions of `coreGoldfishConePathEligible_of_transportOn` hold at
    `w`. -/
theorem coreGoldfishConePathEligibleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let st := n.st.core
    ∀ votes : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ votes →
    ∀ support : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ support →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T votes support votes (st.s - 1)
        (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) ∧
      (∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M S.E st.T votes support
          (st.s - 1) C ⇢ sup →
        M.voters_count S.E votes (st.s - 1) < 2 * sup.card) ∧
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc st.s) ⇢ A →
      ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C →
        (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E st st.s ⇢ T → D ∈ T) ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            ∀ g : Nat, M.goldfish_score S.E st.T votes support (st.s - 1) D ⇢ g →
              M.voters_count S.E votes (st.s - 1) < 2 * g) ∧
          ∀ b : Bool, M.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D ⇢ b → b = true := by
  have hwcut : w ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hw
  have hn := mkNode_mem_confirmationReadAt₅₇ hf.sorted hf.onePath w (M.vote_time S.E (s + 1)) c hc
  have hroot := hinputs.root
  rewrite [facts.nd.mkNode_st] at hroot; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hroot
  refine Restated.coreGoldfishConePathEligible_of_transportOn facts S Hs Xb hf hHs hHsXb hcom hs
    hvotes (hHsXb _ hw)
    (Restated.coreHonestHeadsAvailableOn facts S Hs Xb hf hHs hHsXb hwcut hpost
      ((facts.sch.Sts_support_cutoff_le_confirmation_time S.E s).trans hhor) hroot hvotes)
    ?_ c hc hinputs
  intro x hx X hXemit
  exact Restated.gfVote_in_cutoff_view_after_gstOn facts S Hs Xb hf hHs
    (hHs _ _ (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hx) hs hpost
    hXemit rfl hwcut
    (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
    (facts.sch.support_cutoff_le_vote_time_succ S.E s)
    (le_of_lt (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s))
    ((facts.sch.Sts_support_cutoff_le_confirmation_time S.E s).trans hhor)

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, every committee member of `s` in `Hs (vote_time s)`
    voted a run block descending from `C`, and `w ∈ Hs (vote_time (s + 1))` has the cone's root-side
    vote inputs at `C`, then `C` is an ancestor of every head the in-tree head computation can
    return at `w`'s vote-duty node state of slot `s + 1`. -/
theorem goldfishCone_stepOn'_WeakGoldfishCone (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq C H := by
  intro n T hT L hL L' hL' H hH
  have hn := mkNode_mem_confirmationReadAt₅₇ hf.sorted hf.onePath w (M.vote_time S.E (s + 1)) c hc
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1))) _ := facts.nd.mkNode_st _ _ _
  have hround : M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s =
      M.round_of S.hc n.st.core.s := by
    rw [facts.sto.toHealing_gs_s]
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
  have hRG : R = G.anchor := facts.fc.get_sg_root_with_eq_read_anchor _ _ _ _ _ G hG R hR
  have hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ R := by
    rw [hRG, ← hround]
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₅₇ (fun g : Protocol.GradeRead V => g.anchor) _ G hG
  have hHf := (facts.fc.get_head_in_tree_split_with _ S.E S.hc _ T L L' _ R hR H).1 hH
  rcases hinputs.rootSide R hA T hT with ⟨hrootC, hCT, hpath⟩ | hbelow
  · have hroot' : Block.Preceq
        (M.get_fg_root
          (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core).toFG) C := by
      simpa only [hnst, facts.nd.mkNode_st, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hrootC
    obtain ⟨hcone, hmaj, -⟩ := coneSupport_and_majority_of_root₅₇ facts S Hs Xb hf hHs hHsXb
      hcom hs hpost hhor hvotes hw hroot' c hc L hL L' hL'
    obtain ⟨sup, hsup⟩ := facts.fc.raw_supporters_nonempty n.st.core.T L L' (n.st.core.s - 1) C
    have hTeq : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_gs_T _
    rw [hTeq] at hHf
    exact facts.fc.goldfish_fork_choice_captures_supporter_majority _ _ _ _ _ _ _ _ _ hcone.sub
      sup hsup (hmaj sup hsup) (hinputs.anchor R hA)
      (fun _ D hRD hDne hDC => by
        by_cases hEq : D = C
        · rw [hEq]
          exact hCT
        · exact hpath D hRD hDne hDC hEq) H hHf
  · exact preceq_trans_Preceq hbelow
      (facts.fc.fgRoot_Preceq_get_head_in_tree_with_layer_gradeContract n.cache S.E S.hc
        (M.toHealing n.st.core) T L L' _ H hH)

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `lo ≤ vote_time s`, `confirmation_time s` is inside the horizon,
    every committee member of `s` in `Hs (vote_time s)` voted a run block descending from `C`, `H`
    is a head of a committee member of `s` in `Hs (confirmation_time s)`,
    `w ∈ Hs (support_cutoff s)`, and the FG root of `w`'s store before `vote_time (s + 1)` staged to
    that time is an ancestor of `C`, then `H` is in every outcome of the voter's processed block
    tree of `w`'s vote-duty store of `s + 1`. -/
theorem coreHonestHeadProcessedAtNextDutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C H : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    (hH : Restated.HonestHeadOn M S rho W Hs Xb s H)
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) C) :
    let duty := Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
      (M.toHealing duty).toFG.toSG.toGoldfishStore (M.toHealing duty).s ⇢ P → H ∈ P := by
  intro duty P hP
  set i := strictEventIndex rho (M.vote_time S.E (s + 1)) with hi_def
  have hdutyCore : duty = (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))).core := by
    show Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W i w).st.core (M.vote_time S.E (s + 1)) = _
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  have hdutyT : duty.T = (W i w).st.core.T := by
    rw [hdutyCore, facts.hd.Sts_setClock_core_T]
  have hdutyStamp : duty.timestamp_block = (W i w).st.core.timestamp_block := by
    rw [hdutyCore, facts.hd.setClock_core_timestamp_block]
  have hcutHor : M.support_cutoff S.E s ≤ rho.horizon :=
    (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s).trans hhor
  have havailable := Restated.coreHonestHeadsAvailableOn facts S Hs Xb hf hHs hHsXb hw hpost hcutHor
    hroot hvotes
  have hslot : (M.toHealing duty).s = s + 1 := by
    show (M.toHealing duty).toFG.toSG.toGoldfishStore.s = s + 1
    rw [facts.sto.toHealing_gs_s, hdutyCore, facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  rw [hslot] at hP
  rcases havailable H hH with hgen | hadmit
  · subst H
    have hgenesis := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
      (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T, hdutyT]
      exact hgenesis.1
    · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hdutyStamp]
      exact hgenesis.2
  · have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit
      (le_trans (le_of_lt (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s))
        (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)))
    have hstampCut : stampedBefore (M.toHealing duty).toFG.toSG.toGoldfishStore.timestamp_block
        (M.support_cutoff S.E s) H = true := by
      rw [facts.sto.toHealing_gs_timestamp_block, hdutyStamp]
      exact hvisible.2
    have hstampFreeze :
        stampedBefore (M.toHealing duty).toFG.toSG.toGoldfishStore.timestamp_block
          (M.view_freeze S.E s) H = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s)) hstampCut
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T, hdutyT]
      exact hvisible.1
    · rw [Nat.add_sub_cancel]
      exact hstampFreeze

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

end

/-! ## Frontier witnesses and the slot step from them -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the bundle's path `W`, if `X` and `B` are run blocks read through `Xb` and `X`'s erasure
    is an ancestor of `B`'s, then `X` is a named ancestor of `B`. -/
theorem coreNamedPreceq_of_runBlock_erase_preceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {X B : NamedBlock V} (hXrun : Restated.RunBlockOn M S rho W Xb X)
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (h : Block.Preceq X.erase B.erase) :
    NamedBlock.Preceq X B :=
  Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hXrun hBrun h

/-- Under the bundle along `W`, if `v`'s store before `time ≤ horizon` has `h_max > 1`, some signer
    in `Hs time` emitted along `W` before `time` an attestation `a` at height `h_max − 1` such that,
    for every node state of its round action read and every outcome `o` of its FG confirmation
    witness, `o` is the entry of a run block `K` read through `Xb`, of named height `h_max − 1`,
    whose entry is its own erasure. -/
theorem coreFrontierConfirmationWitnessOn (facts : Record.Facts M)
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
          (W (strictEventIndex rho time) v).st.core.h_max - 1 ∧
        (M.derive_named S.E S.cfg K).T_h = K.erase := by
  obtain ⟨a, ta, haHon, hemit, hta, hheight, hall⟩ :=
    Restated.frontier_confirmationWitnessOn facts S Hs Xb hf hHs hHsXb hmajority hthor hlarge
  refine ⟨a, ta, haHon, hemit, hta, hheight, ?_⟩
  intro nr hnr o ho
  obtain ⟨D, K, ho', hD, hK, hKentry, hKrun, hKheight⟩ := hall nr hnr o ho
  obtain ⟨K', hK', hK'entry, hK'height, hK'D, hK'run⟩ :=
    Restated.action_named_checkpoint_coreOn facts S Hs Xb hf (hHsXb _ haHon) hnr hD
  have hKK : K' = K :=
    hf.rootCollisionFree.root_injective K' K hK'run hKrun K' K
      (Or.inl (Proofs.NamedAncestry.named_self K'))
      (Or.inr (Proofs.NamedAncestry.named_self K)) (by
        rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'entry, hKentry])
  subst hKK
  exact ⟨D, K', ho', hD, hK, hKentry, hKrun, hKheight,
    (facts.cs.entry_eq_on_plateau S.E S.cfg hK'D hK'height).trans hKentry.symm⟩

/-- Under the bundle along `W`, if `w ∈ Xb`, `X` is a run block read through `Xb` and `X.erase` is
    in the tree of `w`'s vote-duty node state of `s` built with the cache `c`, then that node
    state's stored height of `X.erase` is `X`'s named height. -/
theorem coreStoredHeightAtVoteDutyOn (facts : Record.Facts M)
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
      (M.derive_named S.E S.cfg X).h :=
  Restated.storedHeight_of_runBlock_mem_voteDutyReadOn facts S Hs Xb hf hw hXrun c hXmem

/-- Under the bundle along `W`, if `w ∈ Hs (view_freeze s)`, `lo ≤ view_freeze s`, `C` is an
    ancestor of a block `D` of an outcome of `w`'s voter-processed tree of slot `s + 1`, and at
    `w`'s vote-duty node state `n` of `s + 1` the stored height of `D` is at least `h_max − 1` and
    the FG root is an ancestor of `C`, then `C`, and every block strictly between an outcome of
    `n`'s anchor and `C`, is in every outcome of the voter's filtered tree of `n`'s store. -/
theorem coreCandidatePathOfBandDescendantOn (facts : Record.Facts M)
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
  Restated.namedCandidatePath_of_processedBandDescendant_coreOn facts S Hs Xb hf hw hCD Q hQ
    hDprocessed c hc hband hroot hgat

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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open scoped DC

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₅₇w {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
    (hb : b % Δ = 0) (hab : a < b) : a + Δ ≤ b := by
  obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero ha
  obtain ⟨l, rfl⟩ := Int.dvd_of_emod_eq_zero hb
  have hkl : k < l := by
    by_contra h
    have h' : l ≤ k := not_lt.mp h
    have : Δ * l ≤ Δ * k := Int.mul_le_mul_of_nonneg_left h' (le_of_lt hΔ)
    omega
  have h1 : k + 1 ≤ l := hkl
  have h2 : Δ * (k + 1) ≤ Δ * l := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hΔ)
  rw [Int.mul_add, Int.mul_one] at h2
  exact h2

/-- A slot's support cutoff plus one delay is at most the slot's view freeze. -/
private theorem support_cutoff_add_delta_le_view_freeze₅₇w (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s := by
  obtain ⟨k, hk⟩ := (facts.sch.publicTime_iff S (M.view_freeze S.E s)).mpr
    ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩
  have hb : M.view_freeze S.E s % S.E.Δ = 0 := by
    rw [hk]
    exact Int.mul_emod_left _ _
  exact add_delta_le_of_lt_emod₅₇w S.E.Δ_pos (facts.sch.support_cutoff_emod_delta S s) hb
    (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)

/-- If `S.a r < vote_time (s + 1)`, then `S.a r ≤ support_cutoff s`. -/
private theorem action_le_support_cutoff₅₇w (facts : Record.Facts M) (S : Setup V) {r : Round}
    {s : Slot}
    (h : Restated.Vocabulary.Execution.Setup.a M S r < M.vote_time S.E (s + 1)) :
    Restated.Vocabulary.Execution.Setup.a M S r ≤ M.support_cutoff S.E s := by
  have heq : Restated.Vocabulary.Execution.Setup.a M S r =
      M.support_cutoff S.E (M.opening_slot S.hc r + 1) :=
    (facts.sch.a_eq_confirmation_time S.hc S.E r).trans
      (facts.sch.confirmation_time_eq_support_cutoff_succ S.E _)
  have hk : M.opening_slot S.hc r + 1 ≤ s := by
    by_contra hn
    have hs : s + 1 ≤ M.opening_slot S.hc r + 1 := Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
    have hvote := Restated.vote_time_lt_support_cutoff_l49 facts S (s + 1)
    have hmono := facts.sch.support_cutoff_mono S.E hs
    rw [heq] at h
    exact absurd (lt_of_le_of_lt hmono h) (not_lt_of_gt hvote)
  rw [heq]
  exact facts.sch.support_cutoff_mono S.E hk

/-- For a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of `rho`
    lead to from `W m`. -/
private theorem onePath_reach₅₇w {S : Setup V} {rho : Record.Run V}
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

/-- For a path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₅₇w {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₇w W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Every node state of the round-`r` action read from `before` holds `before`'s bodies. -/
private theorem actionReadFrom_bodies₅₇w (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The round-`r` action read from `before` has some node state. -/
private theorem actionReadFrom_nonempty₅₇w (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₅₇w {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
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

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₇w {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- The FG confirmation witness read at any node state can return some value. -/
private theorem fgConfirmationWitness_nonempty₅₇w (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o :=
    (returns_bind_iff₅₇w _ _ _).2 ⟨A2, hA2, ho⟩
  exact ⟨_, returns_map_intro₅₇w _ _ o hsrc⟩

/-- Under the bundle along `W`, if `u ∈ Hs (support_cutoff s)`, `w ∈ Hs (view_freeze s)`, `T` is a
    body of a node state of `u`'s round-`r` action read, `S.a r < vote_time (s + 1)`,
    `lo ≤ support_cutoff s`, `vote_time (s + 1)` is inside the horizon, and the FG root of `w`'s
    store before `vote_time (s + 1)` staged to that time is an ancestor of `T`'s erasure, then that
    erasure is in every outcome of the voter's processed block tree of `w`'s vote-duty store of
    `s + 1`. -/
theorem coreActionBlockProcessedAtNextDutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {u w : V} {s : Slot} (hu : u ∈ Hs (M.support_cutoff S.E s))
    (hw : w ∈ Hs (M.view_freeze S.E s))
    {r : Round} {T : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (hmem : T ∈ n.st.bodies)
    (haction : (Restated.Vocabulary.Execution.Setup.a M S r) < M.vote_time S.E (s + 1))
    (hpost : lo ≤ M.support_cutoff S.E s)
    (hhor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) T.erase) :
    let duty := Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
      (M.toHealing duty).toFG.toSG.toGoldfishStore (M.toHealing duty).s ⇢ P → T.erase ∈ P := by
  intro duty P hP
  set kv := strictEventIndex rho (M.vote_time S.E (s + 1)) with hkv
  set ka := strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) with hka
  have hdutyCore : duty = (M.ns_setClock S.E (W kv w).st (M.vote_time S.E (s + 1))).core := by
    show Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W kv w).st.core (M.vote_time S.E (s + 1)) = _
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  have hdutyT : duty.T = (W kv w).st.core.T := by
    rw [hdutyCore, facts.hd.Sts_setClock_core_T]
  have hdutyStamp : duty.timestamp_block = (W kv w).st.core.timestamp_block := by
    rw [hdutyCore, facts.hd.setClock_core_timestamp_block]
  have hslot : (M.toHealing duty).s = s + 1 := by
    show (M.toHealing duty).toFG.toSG.toGoldfishStore.s = s + 1
    rw [facts.sto.toHealing_gs_s, hdutyCore, facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  rw [hslot] at hP
  have hbodies := actionReadFrom_bodies₅₇w facts S (W ka u) r n hn
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho ka u
    (W ka) (hf.onePath ka).1).1.1.1
  have hpre : T.erase ∈ (W ka u).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase (hbodies ▸ hmem)
  have hcut := action_le_support_cutoff₅₇w facts S haction
  have hfreezeVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
    le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)
  have hcutFreeze : M.support_cutoff S.E s ≤ M.view_freeze S.E s - S.E.Δ :=
    le_sub_iff_add_le.mpr (support_cutoff_add_delta_le_view_freeze₅₇w facts S s)
  have hrelay : T.erase = Block.genesis ∨
      Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w T.erase (M.view_freeze S.E s) := by
    rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts S Hs Xb hf
        u (Restated.Vocabulary.Execution.Setup.a M S r) hpre with
      hgen | ⟨D, i, t, hDeq, hacc, ht⟩
    · exact Or.inl hgen
    · right
      have hroot' : Block.Preceq
          (M.get_fg_root (M.toHealing (W kv w).st.core).toFG) D.erase := by
        have h := hroot
        rw [facts.hd.setClock_core_eq_store_with_t_s] at h
        rw [hDeq]
        exact (congrArg (fun Z => Block.Preceq Z T.erase) (facts.fc.get_fg_root_set_clock_slot
          (W kv w).st.core (M.vote_time S.E (s + 1))
          (S.E.slotOf (M.vote_time S.E (s + 1))))).mp h
      have hFhist : ∀ j : Nat,
          j ≤ (rho.events.filter (fun e => decide (e.time < M.view_freeze S.E s))).length →
            Block.Preceq (W j w).st.core.F D.erase := by
        intro j hj
        have hjVote : j ≤ (rho.events.filter
            (fun e => decide (e.time < M.vote_time S.E (s + 1)))).length :=
          hj.trans (Restated.strict_filter_length_mono rho hfreezeVote)
        exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts
          S rho hf.sorted hjVote (W j) (hf.onePath j).1
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))))
          (onePath_slice₅₇w W hf.onePath hjVote) hroot'
      have htcut : t < M.support_cutoff S.E s := ht.trans_le hcut
      have humax : u ∈ Hs (max t lo) := hHs _ _ (max_le (le_of_lt htcut) hpost) hu
      have hDpos : 0 < D.slot := by
        rw [← Proofs.NamedWire.erase_slot D]
        exact Nat.zero_lt_of_lt (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W
          hf.onePath hacc)
      have hadmit := Restated.coreBlockAdmittedAfterCutoffOn facts S Hs Xb hf hHs hHsXb humax hw
        hDpos hacc (htcut.trans_le hcutFreeze) (hpost.trans hcutFreeze) (sub_add_cancel _ _)
        (hfreezeVote.trans hhor) hFhist
      rw [hDeq] at hadmit
      exact hadmit
  rcases hrelay with hgen | hadmit
  · have hgenesis := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
      (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T, hdutyT, hgen]
      exact hgenesis.1
    · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hdutyStamp, hgen]
      exact hgenesis.2
  · have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hfreezeVote
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ P hP
    · rw [facts.sto.toHealing_gs_T, hdutyT]
      exact hvisible.1
    · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hdutyStamp]
      exact hvisible.2

/-- Under the bundle along `W`, the committee majority and the weight majority, if every committee
    member of `s` in `Hs (vote_time s)` voted a run block descending from `C`, `w ∈ Xb`, `P` is an
    outcome of the voter's processed block tree of `w`'s vote-duty store of `s + 1` holding every
    committee head and every earlier action body of the signers in `Hs (vote_time (s + 1))`, the
    frontier witnesses are compatible with `C`, the FG root of `w`'s staged store is an ancestor of
    `C`, and `vote_time (s + 1)` is inside the horizon, then some descendant of `C` is in `P` with
    stored height at least `h_max − 1`. -/
theorem coreConeBandDescendant_of_processedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {s : Slot} {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Xb)
    (P : Finset (Block V))
    (hP : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ P)
    (hwitnesses : ∀ {C' : NamedBlock V}, C'.erase = C →
      (M.derive_named S.E S.cfg C').h <
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.h_max - 1 →
      Restated.RunBlockOn M S rho W Xb C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ Hs (M.vote_time S.E (s + 1)) →
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
        ta < M.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max - 1) →
        ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
          a.round,
        Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
          some (M.derive_named S.E S.cfg K).T_h →
        Restated.RunBlockOn M S rho W Xb K →
        Block.compatible C'.erase
          (M.derive_named S.E S.cfg K).T_h = true))
    (hheadProcessed : ∀ {X : Block V}, Restated.HonestHeadOn M S rho W Hs Xb s X → X ∈ P)
    (hblockProcessed : ∀ {u : V}, u ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ {r : Round} {T : NamedBlock V} {n : M.N},
      n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r →
      T ∈ n.st.bodies →
      (Restated.Vocabulary.Execution.Setup.a M S r) < M.vote_time S.E (s + 1) →
      Block.Preceq
        (M.get_fg_root
          (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core).toFG)
        T.erase →
      T.erase ∈ P)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) C)
    (hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon) :
    ∃ D : Block V, Block.Preceq C D ∧ D ∈ P ∧
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.h_max - 1 ≤
        ((M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.σ D).h := by
  set kv := strictEventIndex rho (M.vote_time S.E (s + 1)) with hkv
  set stN := M.ns_setClock S.E (W kv w).st (M.vote_time S.E (s + 1)) with hstN
  have hdutyCore : Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W kv w).st.core (s + 1) =
      stN.core := by
    show Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W kv w).st.core (M.vote_time S.E (s + 1)) = _
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  have hhmax : stN.core.h_max = (W kv w).st.core.h_max := facts.hd.setClock_core_h_max _ _ _
  rw [hdutyCore] at hP hwitnesses
  have hstored : ∀ {X : NamedBlock V}, Restated.RunBlockOn M S rho W Xb X → X.erase ∈ P →
      (stN.core.σ X.erase).h = (M.derive_named S.E S.cfg X).h := by
    intro X hXrun hXP
    have hXmem : X.erase ∈ stN.core.T := by
      have hmem := facts.fc.mem_T_of_mem_voter_processed_block_tree S.E _ _ P hP hXP
      rw [facts.sto.toHealing_gs_T] at hmem
      exact hmem
    have hheight := Restated.coreStoredHeightAtVoteDutyOn facts S Hs Xb hf hw (s := s + 1) hXrun
      (W kv w).cache (by rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; exact hXmem)
    rewrite [facts.nd.mkNode_st] at hheight; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hheight
    exact hheight
  have hpositive : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    have hc := hcom s
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  have huHon : u ∈ Hs (M.confirmation_time S.E s) := (Finset.mem_inter.mp hu).2
  have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
  obtain ⟨X, hCX, hXrun, hXemit⟩ :=
    hvotes u (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) huHon) huCommittee
  obtain ⟨Cn, hCnX, hCnErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hCX
  have hCnrun : Restated.RunBlockOn M S rho W Xb Cn :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hXrun hCnX
  by_cases hband : stN.core.h_max - 1 ≤ (M.derive_named S.E S.cfg Cn).h
  · have hhead : Restated.HonestHeadOn M S rho W Hs Xb s X.erase :=
      ⟨u, huHon, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hprocessed := hheadProcessed hhead
    refine ⟨X.erase, hCX, hprocessed, ?_⟩
    rw [hstored hXrun hprocessed]
    exact hband.trans (facts.cs.derive_height_mono S.E S.cfg hCnX)
  · have hhigh : (M.derive_named S.E S.cfg Cn).h < stN.core.h_max - 1 := Nat.lt_of_not_ge hband
    have hlarge : 1 < (W kv w).st.h_max := by
      show 1 < (W kv w).st.core.h_max
      by_contra hn
      have hz : stN.core.h_max - 1 = 0 := by
        rw [hhmax]
        exact Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hn)
      rw [hz] at hhigh
      exact Nat.not_lt_zero _ hhigh
    obtain ⟨a, ta, ha, hemit, hta, hrow, hall⟩ :=
      Restated.coreFrontierConfirmationWitnessOn facts S Hs Xb hf hHs hHsXb hmajority hvoteHor hlarge
    obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty₅₇w facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
    obtain ⟨o, ho⟩ := fgConfirmationWitness_nonempty₅₇w facts S nr
    obtain ⟨D, K, hoK, hDmem, hKmem, hKentry, hKrun, hKheight, hKtarget⟩ := hall nr hnr o ho
    rw [hoK] at ho
    have hrawCompatible : Block.compatible Cn.erase K.erase = true := by
      have h := hwitnesses hCnErase hhigh hCnrun a ta K ha hemit hta
        (by rw [hrow, hhmax]) nr hnr ho hKrun
      rw [hKtarget] at h
      exact h
    have hcompatible : NamedBlock.compatible Cn K = true := by
      have hcases : Block.Preceq Cn.erase K.erase ∨ Block.Preceq K.erase Cn.erase :=
        compatible_cases hrawCompatible
      rcases hcases with hCK | hKC
      · exact namedBlock_compatible_of_cases (Or.inl
          (Restated.coreNamedPreceq_of_runBlock_erase_preceqOn facts S Hs Xb hf hCnrun hKrun hCK))
      · exact namedBlock_compatible_of_cases (Or.inr
          (Restated.coreNamedPreceq_of_runBlock_erase_preceqOn facts S Hs Xb hf hKrun hCnrun hKC))
    have hCnK : NamedBlock.Preceq Cn K := by
      have hcases : NamedBlock.Preceq Cn K ∨ NamedBlock.Preceq K Cn :=
        namedBlock_compatible_cases hcompatible
      rcases hcases with hCK | hKC
      · exact hCK
      · have hmono := facts.cs.derive_height_mono S.E S.cfg hKC
        rw [hKheight, ← hhmax] at hmono
        exact False.elim ((Nat.not_le_of_gt hhigh) hmono)
    have hCK : Block.Preceq C K.erase := by
      rw [← hCnErase]
      exact Proofs.NamedWire.erase_preceq hCnK
    have hprocessed : K.erase ∈ P := hblockProcessed ha hnr hKmem
      (by
        rw [← (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2]
        exact hta)
      (preceq_trans_Preceq hroot hCK)
    refine ⟨K.erase, hCK, hprocessed, ?_⟩
    rw [hstored hKrun hprocessed, hKheight, hhmax]

/-- Under the bundle along `W`, the committee majority and the weight majority, if
    `lo ≤ vote_time s`, `confirmation_time s` is inside the horizon, every committee member of `s`
    in `Hs (vote_time s)` voted a run block descending from `C`, `w ∈ Hs (vote_time (s + 1))`, `P`
    is an outcome of the voter's processed block tree of `w`'s vote-duty store of `s + 1`, the
    frontier witnesses are compatible with `C`, and the FG root of `w`'s staged store is an ancestor
    of `C`, then some descendant of `C` is in `P` with stored height at least `h_max − 1`. -/
theorem coreConeBandDescendant_of_runFrontierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {s : Slot} {C : Block V}
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (P : Finset (Block V))
    (hP : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ P)
    (hwitnesses : ∀ {C' : NamedBlock V}, C'.erase = C →
      (M.derive_named S.E S.cfg C').h <
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.h_max - 1 →
      Restated.RunBlockOn M S rho W Xb C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ Hs (M.vote_time S.E (s + 1)) →
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
        ta < M.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max - 1) →
        ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
          a.round,
        Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
          some (M.derive_named S.E S.cfg K).T_h →
        Restated.RunBlockOn M S rho W Xb K →
        Block.compatible C'.erase
          (M.derive_named S.E S.cfg K).T_h = true))
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) C) :
    ∃ D : Block V, Block.Preceq C D ∧ D ∈ P ∧
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.h_max - 1 ≤
        ((M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.σ D).h := by
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon := by
    exact le_trans (le_of_lt (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hwcut : w ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hw
  have hwfreeze : w ∈ Hs (M.view_freeze S.E s) :=
    hHs _ _ (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)) hw
  have hpostSupport : lo ≤ M.support_cutoff S.E s :=
    hpost.trans (le_of_lt (Restated.vote_time_lt_support_cutoff_l49 facts S s))
  refine Restated.coreConeBandDescendant_of_processedOn facts
    S Hs Xb hf hHs hHsXb hcom hmajority hvotes (hHsXb _ hw) P hP hwitnesses ?_ ?_ hroot hvoteHor
  · intro X hhead
    exact Restated.coreHonestHeadProcessedAtNextDutyOn facts S Hs Xb hf hHs hHsXb hpost hhor
      hvotes hhead hwcut hroot P hP
  · intro u hu r T n hn hmem haction hrootT
    exact Restated.coreActionBlockProcessedAtNextDutyOn facts S Hs Xb hf hHs hHsXb
      (hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hu) hwfreeze hn hmem haction
      hpostSupport hvoteHor hrootT P hP

/-- Under the bundle along `W`, the committee majority and the weight majority, if `0 < s`,
    `lo ≤ vote_time s`, `confirmation_time s` is inside the horizon, every committee member of `s`
    in `Hs (vote_time s)` voted a run block descending from `C`, every member of
    `Hs (vote_time (s + 1))` has frontier witnesses, FG root and anchors compatible with `C`, and
    the committee members of `s + 1` pass the grade-1 awake test at their vote ticks, then `C` is an
    ancestor of every vote-duty head of those members at `s + 1`, and every committee member of
    `s + 1` in `Hs (vote_time (s + 1))` voted a run block descending from `C`. -/
theorem goldfishCone_succ_of_runFrontierWitnessesOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {s : Slot} {C : Block V} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    (hwitnesses : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ {C' : NamedBlock V},
      C'.erase = C →
      (M.derive_named S.E S.cfg C').h <
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.h_max - 1 →
      Restated.RunBlockOn M S rho W Xb C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ Hs (M.vote_time S.E (s + 1)) →
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
        ta < M.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max - 1) →
        ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
          a.round,
        Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
          some (M.derive_named S.E S.cfg K).T_h →
        Restated.RunBlockOn M S rho W Xb K →
        Block.compatible C'.erase
          (M.derive_named S.E S.cfg K).T_h = true))
    (hroots : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), Block.compatible
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) C = true)
    (hanchors : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
          (M.round_of S.hc
            (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
              (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ A →
        Block.compatible A C = true)
    (hrun : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), w ∈ S.E.committee (s + 1) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq C H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1)
        (fun X => Block.Preceq C X) := by
  have hfreezeLe : lo ≤ M.view_freeze S.E s :=
    hpost.trans (facts.sch.vote_time_le_view_freeze S.E s)
  have hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' M S rho s C w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c) := by
    intro w hw c hc
    refine { rootSide := ?_, anchor := hanchors w hw c hc }
    intro A hA T hT
    have hcases := compatible_cases (hroots w hw)
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rcases hcases with hroot | habove
    · obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s
      obtain ⟨D, hCD, hprocessed, hband⟩ :=
        Restated.coreConeBandDescendant_of_runFrontierOn facts S Hs Xb hf hHs hHsXb hcom hmajority
          hpost hhor hvotes hw P hP (hwitnesses w hw) hroot
      have hpath := Restated.coreCandidatePathOfBandDescendantOn facts S Hs Xb hf
        (hHs _ _ (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)) hw) hCD P hP hprocessed
        c hc (by rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; exact hband) (by rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; exact hroot)
        hfreezeLe T hT
      exact Or.inl ⟨hroot, hpath.1, fun B hAB hne hBC hne' => hpath.2 A hA B hAB hne hBC hne'⟩
    · exact Or.inr habove
  have hheads : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq C H := fun w hw c hc =>
    Restated.goldfishCone_stepOn'_WeakGoldfishCone facts S Hs Xb hf hHs hHsXb hcom hs hpost
      hhor hvotes hw c hc (hinputs w hw c hc)
  refine ⟨hheads, ?_⟩
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon := by
    exact le_trans (le_of_lt (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hvoteLo : lo ≤ M.vote_time S.E (s + 1) :=
    hpost.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s))
  intro w hw hcommittee
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
    (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c with hn
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    Restated.coreVoterHeadEmitsOn facts S Hs Xb hf hHsXb hw (Nat.succ_pos s)
      hcommittee hvoteHor hvoteLo c hc (hrun w hw hcommittee) T hT L hL L' hL' Hd hHd
  exact ⟨X, hXe ▸ hheads w hw c hc T hT L hL L' hL' Hd hHd, hXrun, hXemit⟩

end

end DecoupledConsensusModel.Sts.Restated
