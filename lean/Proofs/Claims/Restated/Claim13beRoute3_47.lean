import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_OutageProvenance
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockStamp
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Blocks
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_GoldfishVotePool
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Pool
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Proposer
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_47

/-!
# Vote-duty stores, emitted votes and relayed heads along a path of the run

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, read along the
path `W` of a bundle `hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo`. They state when blocks
and votes were accepted relative to a vote duty, what an emitted Goldfish vote names, that votes and
slot blocks are unique, that a source's head reaches a later reader, and that two Goldfish scores of
a candidate agree.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ### Helpers about event indices, worlds and stores -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The tree of the vote-duty store staged from the node state `n` for slot `s` is the tree of `n`'s
    core store. -/
private theorem voteStore_T₄₇ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s, facts.hd.Sts_setClock_core_T]

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events has a time less
    than `t`. -/
private theorem time_lt_of_lt_strict₄₇ {rho : Record.Run V}
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
private theorem lt_strict_of_time_lt₄₇ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time} (ht : e.time < t) :
    j < strictEventIndex rho t := by
  by_contra hnot
  exact absurd ht (not_lt.mpr
    (Restated.le_time_of_index_ge_of_sorted hsorted
      (Nat.le_of_not_gt hnot) he))

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₄₇ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₄₇ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₄₇ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- If the node state `n` satisfies the node invariant, then for every cache `c`, with `m` the node
    state `M.mkNode (M.ns_setClock S.E n.st t) n.record c`, every outcome of the in-tree head
    computed on `m`'s store, from every outcome of its voter's filtered tree and all vote sets `L`
    and `L'`, under the grade contract of `c`, is in the tree of `n`'s core store. -/
private theorem voteDutyHead_mem₄₇ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (hinvPre : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) (t : Time) (c : M.Cache) :
    let m := M.mkNode (M.ns_setClock S.E n.st t) n.record c
    ∀ T, M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
    ∀ L L' H, M.get_head_in_tree_with_layer (M.gradeContract m.cache) S.E S.hc
        (M.toHealing m.st.core) T L L' (m.st.core.s - 1) ⇢ H →
    H ∈ n.st.core.T := by
  intro m T hT L L' H hH
  have hmst : m.st = M.store_with_cache (M.ns_setClock S.E n.st t) _ := facts.nd.mkNode_st _ _ _
  have hmc : m.cache = c := facts.nd.mkNode_cache _ _ _
  rw [hmst] at hT hH
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT hH
  rw [hmc] at hH
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg
      (M.ns_setClock S.E n.st t) :=
    facts.hd.invariant_clock S.E S.cfg _ _ hinvPre.1
  have hroot : M.get_fg_root (M.toHealing (M.ns_setClock S.E n.st t).core).toFG ∈
      (M.ns_setClock S.E n.st t).core.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts _ hinv.1.2
  obtain ⟨R, hR⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing (M.ns_setClock S.E n.st t).core)
    (M.round_of S.hc (M.toHealing (M.ns_setClock S.E n.st t).core).toFG.toSG.toGoldfishStore.s)
    (M.readFrame c (M.toHealing (M.ns_setClock S.E n.st t).core)
      (M.round_of S.hc (M.toHealing (M.ns_setClock S.E n.st t).core).toFG.toSG.toGoldfishStore.s)).g1
  have hRT : R ∈ (M.ns_setClock S.E n.st t).core.T := by
    have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
      (M.toHealing (M.ns_setClock S.E n.st t).core) _ _
      (by rw [Record.Model.HS.T, facts.sto.toHealing_gs_T]; exact hroot) R hR
    rw [Record.Model.HS.T, facts.sto.toHealing_gs_T] at h
    exact h
  have hR' := (facts.nd.gradeContract_sgRoot_eq_frameAnchor c S.E S.hc _ _ R).2 hR
  have hHmem := facts.fc.Sts_get_head_in_tree_with_layer_mem (M.gradeContract c) S.E S.hc
    (M.toHealing (M.ns_setClock S.E n.st t).core) T L L' _ R hR' hRT
    (facts.hd.Sts_voter_filtered_block_tree_subset S.E _ _ T hT) H hH
  rw [facts.hd.Sts_setClock_core_T] at hHmem
  exact hHmem

/-- When the `i`-th event of `rho` is a wake of `v`, `v`'s store in every world that event leads to
    from `w₁` is `v`'s store in `w₁`. -/
private theorem stateBefore_wake_st₄₇ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.wake v t)) (w₁ w₂ : V → M.N)
    (hw₂ : w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁) :
    (w₂ v).st = (w₁ v).st := by
  have hl : (rho.events.drop i).take (i + 1 - i) = [Record.Event.wake v t] := by
    rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
    rfl
  rw [hl, List.foldlM_cons, Set.bind_def] at hw₂
  obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp hw₂
  have h2' : w₂ = w' := h2
  subst h2'
  have hw : w₂ = Function.update w₁ v (M.wake (w₁ v)) := hw'
  rw [hw, Function.update_self, (facts.nd.wake_st_record _).1]

/-- For every path `W` of `rho`, if the vote `u` is in the slot-`k` list of `v`'s core store in
    `W i`, then at some event `j < i` of `rho` `v` processes `u` along `W`, or processes along `W` a
    block that includes `u`. -/
private theorem processes_gfVote_of_mem_pool₄₇ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (v : V) (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) :
    ∀ (i : Nat) (k : Slot) (u : GoldfishVote V), u ∈ (W i v).st.core.gf_votes k →
      ∃ (j : Nat) (e : Record.Event V), j < i ∧ rho.events[j]? = some e ∧
        (Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (Object.gfVote u) e.time ∨
          ∃ B : NamedBlock V,
            Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (Object.block B) e.time ∧
              u ∈ B.gf_votes) := by
  intro i
  induction i with
  | zero =>
    intro k u hu
    exfalso
    have h0 : W 0 = fun u => M.initial S u := (hW 0).1
    rw [h0] at hu
    change u ∈ (M.initial S v : M.N).st.core.gf_votes k at hu
    rw [facts.nd.initial_st] at hu
    exact facts.hd.initial_core_not_mem_pool k u ((facts.sto.mem_store_pool_iff _ _ _).mpr hu)
  | succ n ih =>
    intro k u hu
    have lift : u ∈ (W n v).st.core.gf_votes k →
        ∃ (j : Nat) (e : Record.Event V), j < n + 1 ∧ rho.events[j]? = some e ∧
          (Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (Object.gfVote u) e.time ∨
            ∃ B : NamedBlock V,
              Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (Object.block B) e.time ∧
                u ∈ B.gf_votes) := by
      intro h
      obtain ⟨j, e, hj, hje, hp⟩ := ih k u h
      exact ⟨j, e, Nat.lt_succ_of_lt hj, hje, hp⟩
    obtain ⟨hn, hstep⟩ := hW n
    cases hev : rho.events[n]? with
    | none =>
      have hlen : rho.events.length ≤ n := List.getElem?_eq_none_iff.mp hev
      rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
      have hsame : W (n + 1) = W n := hstep
      rw [hsame] at hu
      exact lift hu
    | some e =>
      by_cases hv : v = e.node
      · cases e with
        | wake u' t' =>
          change v = u' at hv
          subst hv
          rw [stateBefore_wake_st₄₇ facts S rho hev (W n) (W (n + 1)) hstep] at hu
          exact lift hu
        | tick u' t' =>
          change v = u' at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho hev (W n) hn
              (W (n + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
          · rw [hw] at hu
            have hcase : u ∈ (W n v).st.core.gf_votes k ∨ NamedObject.gfVote u ∈ out.2 ∨
                ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧ u ∈ B.gf_votes :=
              facts.stoRun.tick_gf_votes_mem S v (W n v) t' k out hout hu
            rcases hcase with h | h | ⟨B, hB, hBu⟩
            · exact lift h
            · exact ⟨n, .tick v t', Nat.lt_succ_self n, hev,
                Or.inl (Or.inl ⟨n, hev, out, hout, hw, h⟩)⟩
            · exact ⟨n, .tick v t', Nat.lt_succ_self n, hev,
                Or.inr ⟨B, Or.inl ⟨n, hev, out, hout, hw, hB⟩, hBu⟩⟩
          · rw [hw] at hu
            exact lift hu
        | deliver u' o' t' =>
          change v = u' at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hev (W n) hn
              (W (n + 1)) hstep with hproc | ⟨-, hw⟩
          · have hcase : u ∈ (W n v).st.core.gf_votes k ∨ o' = NamedObject.gfVote u ∨
                ∃ B : NamedBlock V, o' = NamedObject.block B ∧ u ∈ B.gf_votes :=
              facts.stoRun.process_gf_votes_mem S (W n v) o' k (W (n + 1) v) hproc hu
            rcases hcase with h | h | ⟨B, hB, hBu⟩
            · exact lift h
            · subst h
              exact ⟨n, .deliver v (Object.gfVote u) t', Nat.lt_succ_self n, hev,
                Or.inl (Or.inr ⟨n, hev⟩)⟩
            · subst hB
              exact ⟨n, .deliver v (Object.block B) t', Nat.lt_succ_self n, hev,
                Or.inr ⟨B, Or.inr ⟨n, hev⟩, hBu⟩⟩
          · rw [hw] at hu
            exact lift hu
      · have hw := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho hev v hv (W n) hn
          (W (n + 1)) hstep
        rw [hw] at hu
        exact lift hu

/-- Along a path `W` of `rho`, if `reader` accepts the block `B` at index `j` at time `accepted`,
    then either that event is `reader`'s tick at `accepted` and `reader`'s stamp of `B` in
    `W (j + 1)` is `accepted`, or it is a delivery of `B` to `reader` at `accepted` and the stamp is
    `reader`'s clock in `W j`. -/
private theorem accepted_block_stamp_cases₄₇ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
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

/-- Slot `s`'s vote time is less than its support cutoff. -/
private theorem vote_time_lt_support_cutoff₄₇ (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s < M.support_cutoff S.E s := by
  rcases lt_or_gt_of_ne (facts.sch.support_cutoff_ne_vote_time S.E s) with h | h
  · exfalso
    have h1 := facts.sch.support_cutoff_lt_vote_time_imp_lt_proposal_time S.E h
    have h2 := facts.sch.proposal_time_slotOf_le S.E (le_of_lt (facts.sch.support_cutoff_pos S s))
    rw [facts.sch.slotOf_support_cutoff] at h2
    exact absurd h1 (not_lt.mpr h2)
  · exact h

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₄₇ {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
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

/-- Under `CandidateScorePreservingViewExtension` from the source views to the target views, every
    outcome of the Goldfish score of the candidate `C` over the source views equals every outcome of
    its score over the target views. -/
private theorem candidateScore_eq₄₇ (facts : Record.Facts M) {sourceTree targetTree : Finset (Block V)}
    {sourceRaw sourceSupport targetRaw targetSupport : Finset (GoldfishVote V)} {C : Block V}
    (h : Restated.Vocabulary.Protocol.CandidateScorePreservingViewExtension M sourceTree targetTree
      sourceRaw sourceSupport targetRaw targetSupport C)
    (E : Env V) (s : Slot) :
    ∀ g, M.goldfish_score E sourceTree sourceRaw sourceSupport s C ⇢ g →
      ∀ g', M.goldfish_score E targetTree targetRaw targetSupport s C ⇢ g' → g = g' := by
  have heq : ∀ x : V, M.equivocates sourceRaw x = M.equivocates targetRaw x := by
    intro x
    cases hs : M.equivocates sourceRaw x with
    | true => exact (facts.sch.equivocates_mono h.raw_subset x hs).symm
    | false =>
      cases ht : M.equivocates targetRaw x with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u₁, hu₁, u₂, hu₂, hne, h₁, h₂⟩ := (facts.sch.equivocates_eq_true_iff targetRaw x).mp ht
        by_cases hs₁ : u₁ ∈ sourceRaw
        · by_cases hs₂ : u₂ ∈ sourceRaw
          · have h' := (facts.sch.equivocates_eq_true_iff sourceRaw x).mpr ⟨u₁, hs₁, u₂, hs₂, hne, h₁, h₂⟩
            rw [hs] at h'
            exact Bool.false_ne_true h'
          · have h' := h.raw_extra_equiv u₂ hu₂ hs₂
            rw [h₂, hs] at h'
            exact Bool.false_ne_true h'
        · have h' := h.raw_extra_equiv u₁ hu₁ hs₁
          rw [h₁, hs] at h'
          exact Bool.false_ne_true h'
  intro g hg g' hg'
  let t : GoldfishVote V → Bool := fun u =>
    Classical.choose (facts.fc.targets_under_nonempty sourceTree C u)
  have ht : ∀ u, M.targets_under sourceTree C u ⇢ t u := fun u =>
    Classical.choose_spec (facts.fc.targets_under_nonempty sourceTree C u)
  let t' : GoldfishVote V → Bool := fun u =>
    Classical.choose (facts.fc.targets_under_nonempty targetTree C u)
  have ht' : ∀ u, M.targets_under targetTree C u ⇢ t' u := fun u =>
    Classical.choose_spec (facts.fc.targets_under_nonempty targetTree C u)
  refine facts.fc.goldfish_score_eq_of_iff E s C heq t ht t' ht' ?_ g hg g' hg'
  intro w hw
  have hwt : M.equivocates targetRaw w = false := by rw [← heq]; exact hw
  constructor
  · rintro ⟨u, hu, huw, hus, htar⟩
    rcases h.forward u hu (t u) (ht u) htar with ⟨hu', htar'⟩ | hequiv
    · exact ⟨u, hu', huw, hus, htar' (t' u) (ht' u)⟩
    · rw [huw, hwt] at hequiv
      exact absurd hequiv Bool.false_ne_true
  · rintro ⟨u, hu, huw, hus, htar⟩
    rcases h.backward u hu (t' u) (ht' u) htar with ⟨hu', htar'⟩ | hequiv
    · exact ⟨u, hu', huw, hus, htar' (t u) (ht u)⟩
    · rw [huw, hw] at hequiv
      exact absurd hequiv Bool.false_ne_true

/-- If the pool of `st'` keeps that of `st` (`PoolCarry`), every vote of slot `k` stamped before `Γ`
    in `st` is stamped before `Γ` in `st'`. -/
private theorem beforeCutoff_subset_of_poolCarry₄₇ (facts : Record.Facts M) {st st' : M.S}
    (h : Restated.Vocabulary.Protocol.PoolCarry M st st') (k : Slot) (Γ : Time) :
    ∀ x ∈ beforeCutoff st.timestamp_vote Γ (M.store_pool st k),
      x ∈ beforeCutoff st'.timestamp_vote Γ (M.store_pool st' k) := by
  intro x hx
  rw [mem_beforeCutoff_iff] at hx ⊢
  obtain ⟨hp, hs⟩ := hx
  obtain ⟨σ, hσ, hlt⟩ := exists_stamp_of_stampedBefore hs
  exact ⟨(facts.sto.mem_store_pool_iff _ _ _).mpr (h.mem k x ((facts.sto.mem_store_pool_iff _ _ _).mp hp)),
    stampedBefore_of_lt (h.stamp x σ hσ) hlt⟩

/-- Along a path `W` of `rho`, for `m ≤ n`, every body `v` holds in `W m` it still holds in `W n`. -/
private theorem bodies_mono_path₄₇ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {m n : Nat} (hmn : m ≤ n) : (W m v).st.bodies ⊆ (W n v).st.bodies :=
  Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hmn (W m) (hW m).1
    (W n) (onePath_slice₄₇ W hW hmn)

/-- In a run sorted by key, the worlds strictly before time `t` are the worlds before the event
    whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₄₇ (S : Setup V) (rho : Record.Run V)
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

/-- On the path `W` of `hf`, if a block `B` of positive slot is in the tree of `w`'s slot-`k`
    vote-duty store read from `W`, some named block `C` with erasure `B` was accepted by `w` along
    `W` at a time `t` at least `B`'s proposal time and less than `k`'s vote time. -/
theorem acceptsAt_carrier_before_vote_of_mem_voteDutyStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {k : Slot} {B : Block V} (hBpos : 0 < B.slot)
    (hB : B ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E k)) w).st.core k).T) :
    ∃ (C : NamedBlock V) (i : Nat) (t : Time), C.erase = B ∧
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i w (.block C) t ∧
      M.proposal_time S.E B.slot ≤ t ∧
      t < M.vote_time S.E k := by
  have hW := hf.onePath
  rw [voteStore_T₄₇ facts] at hB
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed_erased facts S rho w W hW _ hB with
    hgen | ⟨C, hCerase, i, hin, t, hacc⟩
  · exfalso
    apply Nat.ne_of_gt hBpos
    rw [hgen, genesis_slot_inclG2]
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    refine ⟨C, i, t, hCerase, hacc, ?_, ?_⟩
    · rw [← hCerase]
      exact Restated.proposal_time_le_of_acceptsAt_blockOn_SlotFreshness facts S Hs Xb hf hacc
    · rw [← het]
      exact time_lt_of_lt_strict₄₇ hf.sorted he hin

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

/-- On the path `W` of `hf`, if `v, w ∈ Xb`, `v`'s tree in `W (strictEventIndex rho t1)` finds `X`
    at `root` and `w`'s tree in `W (strictEventIndex rho t2)` finds `Y` at `root`, then `X = Y`. -/
theorem find_agreeOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v w : V) (hv : v ∈ Xb) (hw : w ∈ Xb) (t1 t2 : Time)
    (root : BlockId) {X Y : Block V}
    (hX : Block.find? (W (strictEventIndex rho t1) v).st.core.T root = some X)
    (hY : Block.find? (W (strictEventIndex rho t2) w).st.core.T root = some Y) :
    X = Y := by
  have hW := hf.onePath
  have hXroot := Proofs.HealingLemmas.find?_root hX
  have hYroot := Proofs.HealingLemmas.find?_root hY
  have hXmem := Proofs.HealingLemmas.find?_mem hX
  have hYmem := Proofs.HealingLemmas.find?_mem hY
  have hcoh1 : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho t1) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ v _
      (hW (strictEventIndex rho t1)).1).1.1.1
  have hcoh2 : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W (strictEventIndex rho t2) w).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ w _
      (hW (strictEventIndex rho t2)).1).1.1.1
  rw [hcoh1.1] at hXmem
  rw [hcoh2.1] at hYmem
  obtain ⟨Xn, hXn, hXe⟩ := Finset.mem_image.mp hXmem
  obtain ⟨Yn, hYn, hYe⟩ := Finset.mem_image.mp hYmem
  have hXscope := Restated.blockInRun_of_directOn facts S rho W Xb
    (Restated.directBlock_of_prefixOn facts S rho W Xb hv _ hXn)
  have hYscope := Restated.blockInRun_of_directOn facts S rho W Xb
    (Restated.directBlock_of_prefixOn facts S rho W Xb hw _ hYn)
  have hroots : Xn.root = Yn.root := by
    rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Yn, hXe, hYe, hXroot,
      hYroot]
  have := hf.rootCollisionFree.root_injective Xn Yn hXscope hYscope Xn Yn
    (Or.inl (Proofs.NamedAncestry.named_self Xn)) (Or.inr (Proofs.NamedAncestry.named_self Yn)) hroots
  rw [← hXe, ← hYe, this]

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

/-- If more than half of every slot's committee is in the set for the slot's confirmation time and
    the family `Hs` shrinks as time grows, then every value of the largest `h_max` over `Hs t` at
    `t` is at least `1`. -/
theorem one_le_honestHMaxAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hcom : Restated.HonestCommitteesOn M S Hs) (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (t : Time) :
    ∀ x ∈ Restated.honestHMaxAtOn M S rho Hs t, 1 ≤ x := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨s, hs⟩ := facts.sch.exists_confirmation_time_ge S t
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    omega
  obtain ⟨v, hvmem⟩ := Finset.card_pos.mp hpos
  have hv : v ∈ Hs t := hHs _ _ hs (Finset.mem_inter.mp hvmem).2
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateAt facts S rho t v w hw
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  obtain ⟨D, hD, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateAt facts S rho t v w hw hpc.1
  have hbound := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateAt facts S rho t v w hw D hD
  have hDgen : D = NamedBlock.genesis := by
    exact eq_named_genesis_of_erase_eq_genesis hDerase
  have hheight : (M.derive_named S.E S.cfg D).h = 1 := by
    rw [hDgen, facts.cs.derive_named_genesis_h]
  have hlocal : 1 ≤ (w v).st.core.h_max :=
    calc
      1 = (M.derive_named S.E S.cfg D).h := hheight.symm
      _ ≤ (w v).st.core.h_max := hbound
  exact hlocal.trans (Restated.localHMax_le_honestHMaxAtOn facts S rho Hs t hv w hw)

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

/-- On the path `W` of `hf`, for `c ≤ d`, the reader's finalized block in
    `W (strictEventIndex rho c)` is an ancestor of, or equal to, its finalized block in
    `W (strictEventIndex rho d)`. -/
theorem incl_strict_F_monoOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (reader : V) {c d : Time} (hcd : c ≤ d) :
    Block.Preceq (W (strictEventIndex rho c) reader).st.core.F
      (W (strictEventIndex rho d) reader).st.core.F := by
  have hW := hf.onePath
  have hcd' : strictEventIndex rho c ≤ strictEventIndex rho d :=
    Restated.strict_lengths_mono rho hcd
  exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho reader hcd'
    _ (hW _).1 _ (onePath_slice₄₇ W hW hcd')

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

/-- On the path `W` of `hf`, every block in the tree of `v`'s slot-`s` vote-duty store read from `W`
    has slot at most `s`. -/
theorem block_slot_le_of_mem_voteDutyStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} {C : Block V}
    (hC : C ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T) : C.slot ≤ s := by
  have hW := hf.onePath
  rw [voteStore_T₄₇ facts] at hC
  obtain hgen | ⟨D, hDe, i, hin, t, hacc⟩ :=
    Restated.Vocabulary.Protocol.acceptsAt_block_of_processed_erased facts S rho v W hW _ hC
  · subst C
    rw [genesis_slot_inclG2]
    exact Nat.zero_le s
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    have ht : t < M.vote_time S.E s := by
      rw [← het]
      exact time_lt_of_lt_strict₄₇ hf.sorted he hin
    have hslot := Restated.proposal_time_le_of_acceptsAt_blockOn_SlotFreshness facts S Hs Xb hf hacc
    have hslot' : M.proposal_time S.E C.slot ≤ t := by
      simpa only [hDe] using hslot
    have hk := facts.sch.slot_le_slotOf_of_proposal_time_le S.E (le_of_lt (lt_of_le_of_lt hslot' ht))
    rwa [facts.sch.slotOf_vote_time] at hk

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

/-- On the path `W` of `hf`, if `x` emits the vote `u` at `t`, then for every outcome `c` of the
    phase tick at `x`'s node state `w` in `W (strictEventIndex rho (vote_time u.slot))`, with `n`
    the node state staged from `w` at the vote time with the cache `c`, and for every outcome `T` of
    the voter's filtered tree, `L` and `L'` of the two voter views of `n`'s store at its slot, and
    `H` of the head computed from them under the grade contract of `c`, `u`'s head is the root of
    `H`. -/
theorem emitted_vote_head_eq_voterHeadAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {x : V} {u : GoldfishVote V} {t : Time}
    (hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W x (Object.gfVote u) t)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E u.slot)) x).st.core.toHealing
        (M.vote_time S.E u.slot) (W (strictEventIndex rho (M.vote_time S.E u.slot)) x).cache ⇢ c →
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E u.slot)) x).st
      (M.vote_time S.E u.slot)) (W (strictEventIndex rho (M.vote_time S.E u.slot)) x).record c
    ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        n.st.core.s ⇢ L' →
    ∀ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        T L L' (n.st.core.s - 1) ⇢ H →
    u.head = H.root := by
  intro c hc n T hT L hL L' hL' H hH
  obtain ⟨-, ht, -, hus⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
  have ht' : t = M.vote_time S.E u.slot := by
    rw [hus]
    exact ht
  subst ht'
  obtain ⟨i, hi, out, hout, -, ho⟩ := hemit
  have hparts : (W i x).st = (W (strictEventIndex rho (M.vote_time S.E u.slot)) x).st ∧
      (W i x).cache = (W (strictEventIndex rho (M.vote_time S.E u.slot)) x).cache := by
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hi with hsame | hsame
    · rw [hsame]; exact ⟨rfl, rfl⟩
    · rw [hsame]; exact ⟨(facts.nd.wake_st_record _).1, facts.nd.wake_cache _⟩
  set w := W i x with hw
  have _hr_w : M.reachedNode w := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 x
  have _hv_w : M.runs_as w x := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 x
  obtain ⟨hpos, -, hduty, -, hslot⟩ :=
    facts.nd.gfVote_emitted_shape S x w (M.vote_time S.E u.slot) out hout u ho
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E u.slot)) x).st (M.vote_time S.E u.slot)) _ := facts.nd.mkNode_st _ _ _
  have hncache : n.cache = c := facts.nd.mkNode_cache _ _ _
  rw [hnst] at hT hL hL' hH
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT hL hL' hH
  rw [← hparts.1] at hT hL hL' hH
  rw [hncache] at hH
  rw [← hparts.1, ← hparts.2] at hc
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.frameContract c) S.E S.hc (S.node x)
    (M.ns_setClock S.E w.st (M.vote_time S.E u.slot))
  obtain ⟨Hf, hHf⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.frameContract c) S.E S.hc
    (M.toHealing (M.ns_setClock S.E w.st (M.vote_time S.E u.slot)).core) T L L'
    ((M.ns_setClock S.E w.st (M.vote_time S.E u.slot)).core.s - 1)
  obtain ⟨hcom, -⟩ := facts.fc.namedDuties_goldfish_vote_with_snd_eq_some (M.frameContract c)
    S.E S.hc (S.node x) _ D hD (hduty c hc D hD) T hT L hL L' hL' Hf hHf
  obtain ⟨D', hD'⟩ := facts.dt.goldfish_vote_with_nonempty (M.gradeContract c) S.E S.hc (S.node x)
    (M.ns_setClock S.E w.st (M.vote_time S.E u.slot))
  have hD'u := facts.fc.goldfish_vote_with_snd_of_mem_committee (M.gradeContract c) S.E S.hc
    (S.node x) _ hcom D' hD' T hT L hL L' hL' H hH
  have hs : 0 < u.slot := by rw [hslot]; exact hpos
  have hg1 : M.awake_for_grade1 S x w (M.round_of S.hc u.slot) := by
    have h := facts.nd.gfVote_mem_on_tick_emit_awake S x w (M.vote_time S.E u.slot) out hout ho
    rw [← hslot] at h
    exact h
  have hmem := facts.nd.on_tick_emit_vote_mem_of_outcomes S x w u.slot hs c hc D' hD' hD'u out hout
    hg1
  have hdup := Restated.Vocabulary.Proofs.Optimistic.gfVote_emitted_unique facts S x w
    (M.vote_time S.E u.slot) out hout ho hmem
  rw [hdup]

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

/-- On the path `W` of `hf`, if `x, v ∈ Xb`, `x` emits the slot-`s` vote `u` at `s`'s vote time, and
    `v`'s tree in `W (strictEventIndex rho t)` holds `H` with `u`'s head as root, then `H`'s slot is
    at most `u`'s slot. -/
theorem emitted_vote_head_slot_le_of_store_memOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {x v : V} (hx : x ∈ Xb) (hv : v ∈ Xb)
    {s : Slot} {u : GoldfishVote V}
    (hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W x (Object.gfVote u) (M.vote_time S.E s)))
    (hus : u.slot = s) {t : Time} {H : Block V}
    (hH : H ∈ (W (strictEventIndex rho t) v).st.core.T)
    (hroot : H.root = u.head) : H.slot ≤ u.slot := by
  have hW := hf.onePath
  subst hus
  set w := W (strictEventIndex rho (M.vote_time S.E u.slot)) x with hw
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc w.st.core.toHealing
    (M.vote_time S.E u.slot) w.cache
  set m := M.mkNode (M.ns_setClock S.E w.st (M.vote_time S.E u.slot)) w.record c with hm
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E m.st.core m.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract m.cache) S.E
    S.hc (M.toHealing m.st.core) T L L' (m.st.core.s - 1)
  have hhead : u.head = Hd.root :=
    Restated.emitted_vote_head_eq_voterHeadAtOn facts S Hs Xb hf hemit c hc T hT L hL L' hL' Hd hHd
  have hinv := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
    (strictEventIndex rho (M.vote_time S.E u.slot)) x _ (hW _).1
  have hheadMem : Hd ∈ w.st.core.T :=
    voteDutyHead_mem₄₇ facts S _ hinv (M.vote_time S.E u.slot) c T hT L L' Hd hHd
  have hheadSlot := Restated.block_slot_le_of_mem_voteDutyStoreOn facts S Hs Xb hf
    (by rw [voteStore_T₄₇ facts]; exact hheadMem)
  obtain ⟨C, hCbody, hCrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hx
      (M.vote_time S.E u.slot) hheadMem
  obtain ⟨D, hDbody, hDrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hv t hH
  have hCroot : C.root = u.head := by
    rw [← Proofs.NamedWire.erase_root C, hCbody]
    exact hhead.symm
  have hDroot : D.root = u.head := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = H.root := congrArg Block.root hDbody
      _ = u.head := hroot
  have hDC : D = C :=
    hf.rootCollisionFree.root_injective D C hDrun hCrun D C
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self C)) (hDroot.trans hCroot.symm)
  have hslot : H.slot = C.erase.slot := by
    rw [← hDbody, hDC]
  rw [hslot, hCbody]
  exact hheadSlot

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

/-- On the path `W` of `hf`, if `w`, in the set for slot `s`'s vote time `≥ lo`, is delivered a
    Goldfish vote at index `i` at a time `t'` at least that vote time and less than the support
    cutoff, then `w`'s slot in `W i` is `s`. -/
theorem delivery_store_slot_coreOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {i : Nat} {u : GoldfishVote V} {s : Slot} {t' : Time}
    (hw : w ∈ Hs (M.vote_time S.E s)) (hgat : lo ≤ M.vote_time S.E s)
    (hi : rho.events[i]? = some (.deliver w (Object.gfVote u) t'))
    (hlo : M.vote_time S.E s ≤ t')
    (hhi : t' < M.support_cutoff S.E s) :
    (W i w).st.s = s := by
  have hclock : M.vote_time S.E s ≤ (W i w).st.t := by
    refine Restated.tick_le_store_timeOn facts S Hs Xb hf hi ?_ hlo
    refine hf.tick_total _ hgat w hw (Restated.Vocabulary.Proofs.Optimistic.publicTime_vote_time facts S s) ?_
    exact le_trans hlo (hf.in_horizon _ (List.mem_of_getElem? hi)).2
  have hup : (W i w).st.t ≤ t' := by
    simpa [Record.Event.time, Record.Event.time] using
      Restated.store_time_le_event_timeOn facts S Hs Xb hf hi w
  have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho i w (W i)
    (hf.onePath i).1
  unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
  show (W i w).st.core.s = s
  rw [hslot]
  exact facts.sch.slotOf_of_between S.E s hclock (lt_of_le_of_lt hup hhi)

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

/-- On the path `W` of `hf`, if `w`, in the set for slot `s`'s vote time `≥ lo`, is delivered a
    Goldfish vote at index `i` at a time `t'` at least that vote time and less than the support
    cutoff, then `w`'s slot in `W i` is `s`. -/
theorem delivery_store_slotOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {i : Nat} {u : GoldfishVote V} {s : Slot} {t' : Time}
    (hw : w ∈ Hs (M.vote_time S.E s)) (hgat : lo ≤ M.vote_time S.E s)
    (hi : rho.events[i]? = some (.deliver w (Object.gfVote u) t'))
    (hlo : M.vote_time S.E s ≤ t')
    (hhi : t' < M.support_cutoff S.E s) :
    (W i w).st.s = s :=
  Restated.delivery_store_slot_coreOn facts S Hs Xb hf hw hgat hi hlo hhi

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

/-- On the path `W` of `hf`, if every event before index `n` has a time at most `T`, `u` is in some
    slot's list of `w`'s store in `W n` or is included in a body that store holds, and `u`'s sender
    is in the set for `T`, then that sender emitted `u` along `W` at some time. -/
theorem named_emits_of_voteVisibleOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u : GoldfishVote V}
    (hu : (∃ k : Slot, u ∈ (W n w).st.core.gf_votes k) ∨ ∃ B ∈ (W n w).st.bodies, u ∈ B.gf_votes)
    (hx : u.val_index ∈ Hs T) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (Object.gfVote u) t := by
  have hW := hf.onePath
  have hblock : ∀ B : NamedBlock V, B ∈ (W n w).st.bodies →
      u ∈ B.gf_votes → ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (Object.gfVote u) t := by
    intro B hB hmem
    rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S rho w W hW n B hB with
      rfl | ⟨j, e, hj, he, hproc⟩
    · exact absurd hmem (by rw [named_genesis_gf_votes]; simp)
    · exact (hf.carried_gf w B e.time hproc u hmem (hHs _ _ (hT j e hj he) hx)).imp
        fun _ ht => ht.2
  rcases hu with ⟨k, hk⟩ | ⟨B, hB, hmem⟩
  · obtain ⟨j, e, hj, he, hproc⟩ := processes_gfVote_of_mem_pool₄₇ facts S rho w W hW n k u hk
    rcases hproc with hbare | ⟨B, hprocB, hmem⟩
    · exact (hf.unforgeable w (Object.gfVote u) e.time hbare u.val_index
        (hHs _ _ (hT j e hj he) hx) (author_gfVote u)).imp fun _ ht => ht.2
    · exact (hf.carried_gf w B e.time hprocB u hmem (hHs _ _ (hT j e hj he) hx)).imp
        fun _ ht => ht.2
  · exact hblock B hB hmem

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

/-- On the path `W` of `hf`, if every event before index `n` has a time at most `T`, two votes
    visible to `w` in `W n` with one sender, in the set for `T`, and one slot are the same vote. -/
theorem named_voteVisible_uniqueOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u₁ u₂ : GoldfishVote V}
    (h₁ : (∃ k : Slot, u₁ ∈ (W n w).st.core.gf_votes k) ∨ ∃ B ∈ (W n w).st.bodies, u₁ ∈ B.gf_votes)
    (h₂ : (∃ k : Slot, u₂ ∈ (W n w).st.core.gf_votes k) ∨ ∃ B ∈ (W n w).st.bodies, u₂ ∈ B.gf_votes)
    (hx : u₁.val_index ∈ Hs T) (hval : u₂.val_index = u₁.val_index)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨t₁, he₁⟩ := Restated.named_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT h₁ hx
  obtain ⟨t₂, he₂⟩ := Restated.named_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT h₂
    (by rw [hval]; exact hx)
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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- On the path `W` of `hf`, if every event before index `n` has a time at most `T` and `x` is in
    the set for `T`, `x` does not equivocate in the slot-`k` pool of `w`'s store in `W n`. -/
theorem pool_no_honest_equivocation_of_coreOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    (k : Slot) {x : V} (hx : x ∈ Hs T) :
    M.equivocates (M.store_pool (W n w).st.core k) x = false := by
  have hps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w n
  rw [← Bool.not_eq_true, facts.sch.equivocates_eq_true_iff]
  rintro ⟨u₁, hu₁, u₂, hu₂, hne, h₁, h₂⟩
  have hg₁ := (facts.sto.mem_store_pool_iff _ _ _).mp hu₁
  have hg₂ := (facts.sto.mem_store_pool_iff _ _ _).mp hu₂
  refine hne (Restated.named_voteVisible_uniqueOn facts S Hs Xb hf hHs w n hT (Or.inl ⟨k, hg₁⟩)
    (Or.inl ⟨k, hg₂⟩) (by rw [h₁]; exact hx) (by rw [h₂, h₁]) ?_)
  rw [hps.slot k u₁ hg₁, hps.slot k u₂ hg₂]

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

/-- On the path `W` of `hf`, if every event before index `n` has a time at most `T` and `x` is in
    the set for `T`, `x` does not equivocate in the slot-`k` pool of `w`'s store in `W n`. -/
theorem pool_no_honest_equivocationOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    (k : Slot) {x : V} (hx : x ∈ Hs T) :
    M.equivocates (M.store_pool (W n w).st.core k) x = false :=
  Restated.pool_no_honest_equivocation_of_coreOn facts S Hs Xb hf hHs w n hT k hx

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

/-- On the path `W` of `hf`, for a block `B` in `w`'s tree in `W n`, every support vote `B` includes
    is among the Goldfish votes `B` includes. -/
theorem carried_support_subset_of_mem_T_coreOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (W n w).st.core.T) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes := by
  have hW := hf.onePath
  obtain ⟨D, hD, hDB⟩ := Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
    facts S rho n w (W n) (hW n).1 hB
  have hDsub : ∀ u ∈ D.gf_support_votes, u ∈ D.gf_votes := by
    rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S rho w W hW n D hD with
      rfl | ⟨j, e, -, -, hproc⟩
    · intro u hu
      exact absurd hu (by simp [NamedBlock.gf_support_votes])
    · rcases hproc with hem | ⟨i, hi⟩
      · obtain ⟨i, hi, out, hout, -, hmem⟩ := hem
        have _hr_s1 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
        have _hv_s2 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
        obtain ⟨-, hproposal⟩ := Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts S w
          (W i w) e.time out hout hmem
        obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i w).st.core.toHealing e.time
          (W i w).cache
        have _hr_s3 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
        have _hv_s4 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
        obtain ⟨D₁, hD₁⟩ := facts.dt.propose_block_with_nonempty S w (W i w) e.time out hout
          (facts.nd.block_mem_on_tick_emit S w (W i w) e.time out hout hmem).1.1 (facts.nd.block_mem_on_tick_emit S w (W i w) e.time out hout hmem).1.2.1
          (facts.nd.block_mem_on_tick_emit S w (W i w) e.time out hout hmem).1.2.2
          (facts.nd.block_mem_on_tick_emit_awake S w (W i w) e.time out hout hmem) c hc
        obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E
          S.hc (S.node w) (M.ns_setClock S.E (W i w).st e.time)
        exact facts.dt.proposal_with_gf_support_subset _ _ _ _ _ _ o ho
          (facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D₁ hD₁
            (hproposal c hc D₁ hD₁) o ho)
      · exact ((hf.wire i w (Object.block D) e.time hi).1 D rfl).2.1
  intro u hu
  have hu' : u ∈ D.gf_support_votes := by
    rw [← Proofs.NamedWire.erase_goldfish_support, hDB]
    exact hu
  have hu'' := hDsub u hu'
  have hu''' : u ∈ D.erase.gf_votes := by
    simpa only [Proofs.NamedWire.erase_goldfish_votes] using hu''
  simpa only [hDB] using hu'''

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

/-- On the path `W` of `hf`, for a block `B` in `w`'s tree in `W n`, every support vote `B` includes
    is among the Goldfish votes `B` includes. -/
theorem carried_support_subset_of_mem_TOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If the event at index `i` is a tick of `w` at `t`, every event at an index less than `i` has a
    time at most `t`. -/
theorem time_le_of_index_lt_tickOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {w : V} {t : Time} (hi : rho.events[i]? = some (Record.Event.tick w t)) :
    ∀ (j : Nat) (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ t := by
  intro j e hji he
  have hkey := Restated.key_le_of_index_ltOn facts S Hs Xb hf hji he hi
  exact Restated.time_le_of_key_le hkey

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

/-- On the path `W` of `hf`, if `w` emits the vote `u` of slot `s > 0` at `s`'s vote time and `u`'s
    sender is in the set for that time, then at the index `i` of that tick `u` is in the slot-`s`
    list of `w`'s store in `W (i + 1)`, with a stamp at most the vote time. -/
theorem mem_pool_of_emits_coreOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w : V} {s : Slot} (hs : 0 < s) {u : GoldfishVote V}
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u) (M.vote_time S.E s))
    (hus : u.slot = s) (hval : u.val_index ∈ Hs (M.vote_time S.E s)) :
    ∃ i : Nat, rho.events[i]? = some (.tick w (M.vote_time S.E s)) ∧
      u ∈ (W (i + 1) w).st.core.gf_votes s ∧
      ∃ c : Stamp, (W (i + 1) w).st.core.timestamp_vote u = some c ∧
        c ≤ (M.vote_time S.E s : Stamp) := by
  obtain ⟨i, hi, out, hout, hWi, ho⟩ := hemit
  have hps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w i
  have hclockle : (W i w).st.core.t ≤ M.vote_time S.E s :=
    Restated.store_time_le_event_timeOn facts S Hs Xb hf hi w
  have hequiv : M.equivocates (M.store_pool (W i w).st.core s) u.val_index = false :=
    Restated.pool_no_honest_equivocation_of_coreOn facts S Hs Xb hf hHs w i
      (Restated.time_le_of_index_lt_tickOn facts S Hs Xb hf hi) s hval
  have hpooled : u ∈ out.1.st.core.gf_votes s ∧
      ∃ c : Stamp, out.1.st.core.timestamp_vote u = some c ∧ c ≤ (M.vote_time S.E s : Stamp) :=
    facts.nd.tick_vote_pooled S w (W i w) s u out hout hs ho hus
      hps.slot hps.stamped hps.pooled hps.bounded hclockle hequiv
  obtain ⟨hmem, c, hc, hle⟩ := hpooled
  rw [← hWi] at hmem hc
  exact ⟨i, hi, hmem, c, hc, hle⟩

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

/-- On the path `W` of `hf`, if `w` emits the vote `u` of slot `s > 0` at `s`'s vote time and `u`'s
    sender is in the set for that time, then at the index `i` of that tick `u` is in the slot-`s`
    list of `w`'s store in `W (i + 1)`, with a stamp at most the vote time. -/
theorem mem_pool_of_emitsOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w : V} {s : Slot} (hs : 0 < s) {u : GoldfishVote V}
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u) (M.vote_time S.E s))
    (hus : u.slot = s) (hval : u.val_index ∈ Hs (M.vote_time S.E s)) :
    ∃ i : Nat, rho.events[i]? = some (.tick w (M.vote_time S.E s)) ∧
      u ∈ (W (i + 1) w).st.core.gf_votes s ∧
      ∃ c : Stamp, (W (i + 1) w).st.core.timestamp_vote u = some c ∧
        c ≤ (M.vote_time S.E s : Stamp) :=
  Restated.mem_pool_of_emits_coreOn facts S Hs Xb hf hHs hs hemit hus hval

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

/-- On the path `W` of `hf`, if `v` admitted `H` before `Γ`, `A` is an ancestor of `H`, and
    `Γ ≤ Γ'`, then `v`'s store in `W (strictEventIndex rho Γ')` holds `A` with a block stamp less
    than `Γ`. -/
theorem admittedBefore_ancestor_mem_and_stamp_atOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {A H : Block V} {Γ Γ' : Time}
    (hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v H Γ)
    (hAH : Block.Preceq A H) (hle : Γ ≤ Γ') :
    A ∈ (W (strictEventIndex rho Γ') v).st.core.T ∧
      stampedBefore (W (strictEventIndex rho Γ') v).st.core.timestamp_block Γ A = true := by
  have hW := hf.onePath
  obtain ⟨C, hCH, i, t, hacc, hlt⟩ := hadmit
  obtain ⟨hindex, e, he, hnode, htime⟩ := hacc.1
  have hpostC : C ∈ (W (i + 1) v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hacc.2.2
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho (i + 1) v
    (W (i + 1)) (hW (i + 1)).1).1.1.1
  have hpostH : H ∈ (W (i + 1) v).st.core.T := by
    rw [hcoh.1, ← hCH]
    exact Finset.mem_image_of_mem NamedBlock.erase hpostC
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S rho (i + 1) v
    (W (i + 1)) (hW (i + 1)).1
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  have hpostA : A ∈ (W (i + 1) v).st.core.T :=
    Proofs.Records.mem_of_preceq hpc.2 A H hpostH (preceq_eq_true_iff_Preceq.mpr hAH)
  let N := strictEventIndex rho Γ'
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hΓ'e : Γ' ≤ e.time :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf (t := Γ') (j := i) (e := e) hNle he
    rw [htime] at hΓ'e
    exact (not_le_of_gt (lt_of_lt_of_le hlt hle)) hΓ'e
  have hcarry : Restated.Vocabulary.Protocol.BlockCarry M (W (i + 1) v).st.core (W N v).st.core :=
    Restated.block_carryOn facts S Hs Xb hf v N (Nat.succ_le_of_lt hiN)
  have hsource : Restated.Vocabulary.Protocol.BlockStamps M (W (i + 1) v).st.core :=
    Restated.blockStamps_stateBeforeOn facts S Hs Xb hf v (i + 1)
  obtain ⟨c, hc⟩ : ∃ c : Stamp, (W (i + 1) v).st.core.timestamp_block A = some c :=
    Option.isSome_iff_exists.mp (hsource.stamped A hpostA)
  have hcfinal : (W N v).st.core.timestamp_block A = some c :=
    hcarry.stamp A c hc
  have hclock : (W (i + 1) v).st.core.t ≤ t := by
    have ht := Restated.block_store_time_after_event_leOn facts S Hs Xb hf he v
    simpa only [htime] using ht
  have hcΓ : c < (Γ : Stamp) :=
    lt_of_le_of_lt
      (le_trans (hsource.bounded A c hc) (WithBot.coe_le_coe.mpr hclock))
      (WithBot.coe_lt_coe.mpr hlt)
  exact ⟨hcarry.mem A hpostA, stampedBefore_of_lt hcfinal hcΓ⟩

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

/-- On the path `W` of `hf`, if `v` accepted `B` at index `i` at `t`, `i + 1 ≤ n`, `v`'s block stamp
    of `B` in `W n` is less than the public time `Gamma`, `v` is in the set for `Gamma` and
    `lo ≤ Gamma`, then `t < Gamma`. -/
theorem acceptsAt_block_lt_of_stamp_before_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i n : Nat}
    {B : NamedBlock V} {t Gamma : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.block B) t)
    (hin : i + 1 ≤ n) (hpub : PublicTime S Gamma)
    (hv : v ∈ Hs Gamma) (hgat : lo ≤ Gamma)
    (hstamp : stampedBefore (W n v).st.core.timestamp_block Gamma B.erase = true) :
    t < Gamma := by
  have hW := hf.onePath
  have hpost : B ∈ (W (i + 1) v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hacc.2.2
  obtain ⟨-, hcarryStamp⟩ :=
    Restated.Vocabulary.Proofs.NamedBlockStamp.stateBefore_body_stamp_mono facts S rho v hin
      (W (i + 1)) (hW (i + 1)).1 hpost (W n) (onePath_slice₄₇ W hW hin)
  obtain ⟨σ, hσ, hσlt⟩ := exists_stamp_of_stampedBefore hstamp
  rw [hcarryStamp] at hσ
  rcases accepted_block_stamp_cases₄₇ facts S rho W hW hacc with ⟨-, hst⟩ | ⟨hdel, hst⟩
  · rw [hst] at hσ
    cases hσ
    exact WithBot.coe_lt_coe.mp hσlt
  · rw [hst] at hσ
    cases hσ
    have hclock : (W i v).st.core.t < Gamma := WithBot.coe_lt_coe.mp hσlt
    exact Restated.processed_lt_of_store_time_ltOn facts S Hs Xb hf hv hdel hpub hgat
      hclock

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

/-- On the path `W` of `hf`, if `v` accepted `B` at index `i` at `t`, `i + 1 ≤ n`, `v`'s block stamp
    of `B` in `W n` is less than the public time `Gamma`, `v` is in the set for `Gamma` and
    `lo ≤ Gamma`, then `t < Gamma`. -/
theorem acceptsAt_block_lt_of_stamp_beforeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i n : Nat}
    {B : NamedBlock V} {t Gamma : Time}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.block B) t)
    (hin : i + 1 ≤ n) (hpub : PublicTime S Gamma)
    (hv : v ∈ Hs Gamma) (hgat : lo ≤ Gamma)
    (hstamp : stampedBefore (W n v).st.core.timestamp_block Gamma B.erase = true) :
    t < Gamma :=
  Restated.acceptsAt_block_lt_of_stamp_before_coreOn facts S Hs Xb hf hacc hin hpub hv
    hgat hstamp

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

/-- On the path `W` of `hf`, if `w ∈ Xb`, a source store finds `H` at `u`'s head, and `H` is in the
    tree of `w`'s slot-`(s + 1)` vote-duty store read from `W`, then that tree finds `H` at `u`'s
    head too. -/
theorem find_voteDutyStore_of_source_find_and_memOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {source : M.S} {s : Slot} {w : V}
    (hw : w ∈ Xb) {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? source.T u.head = some H)
    (hHmem : H ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T) :
    Block.find? (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T u.head = some H := by
  have hW := hf.onePath
  rw [voteStore_T₄₇ facts] at hHmem ⊢
  have hHroot : H.root = u.head := Proofs.HealingLemmas.find?_root hfind
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ w _ (hW _).1).1.1.1
  have hrun : ∀ C ∈ (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.bodies,
      Restated.RunBlockOn M S rho W Xb C :=
    fun C hC => Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hC
  have hinj := Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hf.rootCollisionFree hrun
  rw [← hcoh.1] at hinj
  rw [← hHroot]
  apply Proofs.Optimistic.find?_eq_some_of_unique hHmem
  intro Y hY hroot
  exact RootInjectiveBelow.eq_of_root_eq hinj hY
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self Y))
    hHmem (preceq_eq_true_iff_Preceq.mp (Block.preceq_self H)) hroot

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

/-- On the path `W` of `hf`, if `u` is in the slot-`s` pool of `w`'s slot-`(s + 1)` vote-duty store
    read from `W`, then `w` accepted `u` along `W` at a time `t` at least `s`'s proposal time and
    less than `s + 1`'s vote time, and `u` is at slot `s`. -/
theorem targetPoolVoteAcceptedBeforeVoteOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} {u : GoldfishVote V}
    (hu : u ∈ M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) :
    ∃ (i : Nat) (t : Time), Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i w (Object.gfVote u) t ∧
      u.slot = s ∧ M.proposal_time S.E s ≤ t ∧
      t < M.vote_time S.E (s + 1) := by
  have hW := hf.onePath
  let N := strictEventIndex rho (M.vote_time S.E (s + 1))
  have huPool : u ∈ M.store_pool (W N w).st.core s := by
    have h := hu
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      show M.store_pool (M.store_with_t_s (W N w).st.core (M.vote_time S.E (s + 1))
          (S.E.slotOf (M.vote_time S.E (s + 1)))) s = M.store_pool (W N w).st.core s from
        facts.sto.pool_set_clock_slot _ _ _ s] at h
    exact h
  have huList : u ∈ (W N w).st.core.gf_votes s := (facts.sto.mem_store_pool_iff _ _ _).mp huPool
  have hus : u.slot = s :=
    (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w N).slot s u huList
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W N w).st
      (Object.gfVote u) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    rw [hus]
    exact huList
  obtain ⟨i, hin, t, hacc⟩ :=
    Restated.Vocabulary.Protocol.acceptsAt_gfVote_of_processed facts S rho w W hW N u hprocessed
  obtain ⟨-, e, he, -, het⟩ := hacc.1
  have hit : t < M.vote_time S.E (s + 1) := by
    rw [← het]
    exact time_lt_of_lt_strict₄₇ hf.sorted he hin
  have hlo : M.proposal_time S.E s ≤ t := by
    rw [← hus]
    exact Restated.proposal_time_le_of_acceptsAt_gfVoteOn_Protocol facts S Hs Xb hf hacc
  exact ⟨i, t, hacc, hus, hlo, hit⟩

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

/-- On the path `W` of `hf`, if `w`, in the set for slot `s + 1`'s proposal time `≥ lo`, holds the
    slot-`(s + 1)` block `B` in the tree of its slot-`(s + 1)` vote-duty store read from `W`, and
    `u` is a slot-`s` vote `B` includes, then `u` is in that store's slot-`s` pool, or that pool
    shows `u`'s sender equivocating. -/
theorem targetCarrierVote_settledInPoolOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot}
    (hw : w ∈ Hs (M.proposal_time S.E (s + 1)))
    (hgat : lo ≤ M.proposal_time S.E (s + 1)) {B : Block V}
    (hB : B ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T)
    (hBslot : B.slot = s + 1) {u : GoldfishVote V}
    (hu : u ∈ B.gf_votes) (hus : u.slot = s) :
    u ∈ M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s ∨
      M.equivocates
        (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s)
        u.val_index = true := by
  have hW := hf.onePath
  have hBpos : 0 < B.slot := by rw [hBslot]; exact Nat.zero_lt_succ s
  obtain ⟨C, i, t, hCerase, hacc, hlo, hhi⟩ :=
    Restated.acceptsAt_carrier_before_vote_of_mem_voteDutyStoreOn facts S Hs Xb hf hBpos hB
  have huC : u ∈ C.erase.gf_votes := by rw [hCerase]; exact hu
  have hCslotB : C.erase.slot = s + 1 := by rw [hCerase]; exact hBslot
  let Γ := M.vote_time S.E (s + 1)
  let N := strictEventIndex rho Γ
  have hpoolN : M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)) s =
      M.store_pool (W N w).st.core s :=
    facts.sto.pool_set_clock_slot _ _ _ s
  show u ∈ M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)) s ∨
    M.equivocates (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)) s)
      u.val_index = true
  rw [hpoolN]
  obtain ⟨⟨hindex, e, he, hnode, htime⟩, hpreProcessed, hpostProcessed⟩ := hacc
  rcases hindex with ⟨t', htick', out, hout, hwout, hem⟩ | ⟨t', hdeliver⟩
  · have heq : Record.Event.tick w t' = e := Option.some.inj (htick'.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    have _hr_s5 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
    have _hv_s6 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
    obtain ⟨⟨hs0, htProp, hpropV⟩, hpropAll⟩ :=
      Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts S w (W i w) t out hout hem
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i w).st.core.toHealing t (W i w).cache
    have _hr_s7 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
    have _hv_s8 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
    obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S w (W i w) t out hout
      (facts.nd.block_mem_on_tick_emit S w (W i w) t out hout hem).1.1 (facts.nd.block_mem_on_tick_emit S w (W i w) t out hout hem).1.2.1
      (facts.nd.block_mem_on_tick_emit S w (W i w) t out hout hem).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S w (W i w) t out hout hem) c hc
    have hpropEq := hpropAll c hc D hD
    obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E S.hc
      (S.node w) (M.ns_setClock S.E (W i w).st t)
    have hcslot : C.slot = (M.ns_setClock S.E (W i w).st t).core.s :=
      facts.dt.propose_block_with_slot _ _ _ _ _ _ D hD hpropEq
    have hcgf : C.gf_votes = (M.ns_setClock S.E (W i w).st t).core.gf_votes
        ((M.ns_setClock S.E (W i w).st t).core.s - 1) :=
      facts.dt.proposal_with_gf_votes _ _ _ _ _ _ o ho
        (facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD hpropEq o ho)
    have hcslot' : C.slot = s + 1 := (Proofs.NamedWire.erase_slot C).symm.trans hCslotB
    have hbeforeS : (M.ns_setClock S.E (W i w).st t).core.s = s + 1 := hcslot.symm.trans hcslot'
    have hu' : u ∈ C.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes]; exact huC
    rw [hcgf, hbeforeS, Nat.add_sub_cancel, facts.hd.setClock_core_gf_votes] at hu'
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hΓe : Γ ≤ (Record.Event.tick w t).time :=
        Restated.le_time_of_index_geOn facts S Hs Xb hf (t := Γ)
          (j := i) (e := Record.Event.tick w t) hNle htick'
      exact (not_le_of_gt hhi) hΓe
    have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W i w).st.core (W N w).st.core :=
      Restated.pool_carryOn facts S Hs Xb hf w N (Nat.le_of_lt hiN)
    exact Or.inl ((facts.sto.mem_store_pool_iff _ _ _).mpr (hcarry.mem s u hu'))
  · have heq : Record.Event.deliver w (Object.block C) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    have hi : rho.events[i]? = some (Record.Event.deliver w (Object.block C) t) := hdeliver
    have hstoreSlot : (W i w).st.core.s = s + 1 :=
      Restated.delivery_store_slot_before_freezeOn facts S Hs Xb hf
        (w := w) (i := i) (o := Object.block C) (s := s + 1) (t := t) hw hgat hi
        (by rw [← hBslot]; exact hlo)
        (lt_trans hhi (lt_trans (vote_time_lt_support_cutoff₄₇ facts S (s + 1))
          (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E (s + 1))))
    have hfresh : ¬ u.slot < (W i w).st.core.s - 1 := by
      rw [hus, hstoreSlot, Nat.add_sub_cancel]
      exact Nat.lt_irrefl s
    have hfuture : ¬ (W i w).st.core.s < u.slot := by
      rw [hus, hstoreSlot]
      exact Nat.not_lt.mpr (Nat.le_add_right s 1)
    have hclock : (W i w).st.core.t < Γ :=
      lt_of_le_of_lt
        (Restated.store_time_le_event_timeOn facts S Hs Xb hf hi w)
        hhi
    have hCpre : C ∉ (W i w).st.bodies := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using
        hpreProcessed
    have hpost : (W (i + 1) w).st =
        M.make_grades_compatible_with_finalized
          (M.on_block_with .alsoCarried S.E S.hc S.cfg (W i w).st C) := by
      rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hi (W i) (hW i).1
          (hf.receipt_outcome _ _ _ _ hi) (W (i + 1)) (hW i).2,
        facts.nd.process_block]
    have hCpost : C ∈
        (M.on_block_with .alsoCarried S.E S.hc S.cfg (W i w).st C).bodies := by
      have h : C ∈ (W (i + 1) w).st.bodies := by
        simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using
          hpostProcessed
      rwa [hpost, facts.nd.make_grades_compatible_with_finalized_bodies] at h
    have hcommittee : u.val_index ∈ S.E.committee u.slot :=
      ((hf.wire i w (Object.block C) t hi).1 C rfl).2.2 u
        (by rw [← Proofs.NamedWire.erase_goldfish_votes]; exact huC)
    have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (W i w).st.core :=
      Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w i
    have hlocal := Restated.Vocabulary.Proofs.Optimistic.block_carried_beforeCutoff_or_equivocates facts S
      (W i w).st C u Γ hstamps hCpre hCpost huC hcommittee hfresh hfuture hclock
    dsimp only at hlocal
    rw [hus] at hlocal
    have hpostTV : (W (i + 1) w).st.core.timestamp_vote =
        (M.on_block_with .alsoCarried S.E S.hc S.cfg (W i w).st C).core.timestamp_vote := by
      rw [hpost, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote]
    have hpostPool : M.store_pool (W (i + 1) w).st.core s =
        M.store_pool (M.on_block_with .alsoCarried S.E S.hc S.cfg (W i w).st C).core s := by
      rw [hpost]
      exact congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool _) s
    rw [← hpostTV, ← hpostPool] at hlocal
    have hiN : i < N := by
      by_contra hnot
      have hNle : N ≤ i := Nat.le_of_not_gt hnot
      have hΓt : Γ ≤ t :=
        Restated.le_time_of_index_geOn facts S Hs Xb hf (t := Γ)
          (j := i) (e := Record.Event.deliver w (Object.block C) t) hNle hi
      exact (not_le_of_gt hhi) hΓt
    have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (i + 1) w).st.core (W N w).st.core :=
      Restated.pool_carryOn facts S Hs Xb hf w N (Nat.succ_le_of_lt hiN)
    rcases hlocal with hmem | hequiv
    · exact Or.inl ((mem_beforeCutoff_iff _ _ _ _).mp
        (beforeCutoff_subset_of_poolCarry₄₇ facts hcarry s Γ u hmem)).1
    · refine Or.inr (facts.sch.equivocates_mono ?_ u.val_index hequiv)
      intro x hx
      exact ((mem_beforeCutoff_iff _ _ _ _).mp (beforeCutoff_subset_of_poolCarry₄₇ facts hcarry s Γ x hx)).1

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

/-- On the path `W` of `hf`, if `0 < s`, the slot-`s` proposer is in the set for `T`, every event
    before index `m` and every event before index `n` has a time at most `T`, and `v`'s tree in
    `W m` and `w`'s tree in `W n` hold slot-`s` blocks `B` and `B'`, then `B = B'`. -/
theorem unique_slot_block_in_store_beforeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hpos : 0 < s) {T : Time} (hprop : S.E.proposer s ∈ Hs T)
    {v w : V} {m n : Nat} {B B' : Block V}
    (hTm : ∀ (j : Nat) (e : Record.Event V), j < m → ρ.events[j]? = some e → e.time ≤ T)
    (hTn : ∀ (j : Nat) (e : Record.Event V), j < n → ρ.events[j]? = some e → e.time ≤ T)
    (hB : B ∈ (W m v).st.core.T) (hB' : B' ∈ (W n w).st.core.T)
    (hBs : B.slot = s) (hB's : B'.slot = s) : B = B' := by
  have hW := hf.onePath
  have hproc : ∀ (x : V) (k : Nat) (C : Block V),
      (∀ (j : Nat) (e : Record.Event V), j < k → ρ.events[j]? = some e → e.time ≤ T) →
      C ∈ (W k x).st.core.T →
      C.slot = s → ∃ D : NamedBlock V, D.erase = C ∧
        ∃ u : Time, u ≤ T ∧ Restated.Vocabulary.Execution.Run.processes M S ρ W x (Object.block D) u := by
    intro x k C hTk hC hCs
    obtain ⟨D, hDmem, hDerase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S ρ k x (W k) (hW k).1 hC
    rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S ρ x W hW k D hDmem with
      rfl | ⟨j, e, hj, he, hpr⟩
    · exact absurd hpos (by
        rw [← hCs, ← hDerase, erase_named_genesis, genesis_slot_inclG2]
        exact Nat.lt_irrefl _)
    · exact ⟨D, hDerase, e.time, hTk j e hj he, hpr⟩
  have hfield : ∀ (x : V) (k : Nat) (C : Block V), C ∈ (W k x).st.core.T →
      C.slot = s → C.proposer? = some (S.E.proposer s) := by
    intro x k C hC hCs
    rcases Restated.Vocabulary.Proofs.HealingSurface.proposerOk_stateBefore facts S ρ x k (W k) (hW k).1 C hC with rfl | hp
    · exact absurd hpos (by
        rw [← hCs, genesis_slot_inclG2]
        exact Nat.lt_irrefl _)
    · rw [← hCs]
      exact hp
  obtain ⟨D, hDerase, s₁, hs₁, hp₁⟩ := hproc v m B hTm hB hBs
  obtain ⟨D', hD'erase, s₂, hs₂, hp₂⟩ := hproc w n B' hTn hB' hB's
  have hDs : D.slot = s := by rw [← Proofs.NamedWire.erase_slot, hDerase, hBs]
  have hD's : D'.slot = s := by rw [← Proofs.NamedWire.erase_slot, hD'erase, hB's]
  have hDp : D.proposer? = some (S.E.proposer s) := by
    rw [← Proofs.NamedWire.erase_proposer, hDerase]; exact hfield v m B hB hBs
  have hD'p : D'.proposer? = some (S.E.proposer s) := by
    rw [← Proofs.NamedWire.erase_proposer, hD'erase]; exact hfield w n B' hB' hB's
  have hDeq : D = D' := Restated.unique_slot_block_coreOn facts S Hs Xb hf
    (hHs _ _ hs₁ hprop) (hHs _ _ hs₂ hprop) hp₁ hp₂ hDp hD'p hDs hD's
  rw [← hDerase, ← hD'erase, hDeq]

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

/-- On the path `W` of `hf`, if the source, in the set for `max sourceCut lo`, holds `H` in
    `W (strictEventIndex rho sourceCut)`, `max sourceCut lo + Δ ≤ targetEarly ≤ targetRead`,
    `targetEarly` is within the horizon, the reader is in the set for `targetEarly`, and the
    reader's finalized block in `W (strictEventIndex rho targetRead)` is an ancestor of `H`, then
    the reader holds `H` in `W (strictEventIndex rho targetEarly)`. -/
theorem head_held_at_early_after_gst_admitOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (source : V) (reader : V) (H : NamedBlock V)
    (sourceCut targetEarly targetRead : Time)
    (hsource : source ∈ Hs (max sourceCut lo)) (hreader : reader ∈ Hs targetEarly)
    (hHsource : H ∈ (W (strictEventIndex rho sourceCut) source).st.bodies)
    (hDeadline : max sourceCut lo + S.E.Δ ≤ targetEarly)
    (hOrder : targetEarly ≤ targetRead) (hCut : targetEarly ≤ rho.horizon)
    (hF : Block.Preceq (W (strictEventIndex rho targetRead) reader).st.core.F H.erase) :
    H ∈ (W (strictEventIndex rho targetEarly) reader).st.bodies := by
  have hW := hf.onePath
  by_cases hgen : H = NamedBlock.genesis
  · subst H
    exact (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ reader _
      (hW (strictEventIndex rho targetEarly)).1).1.1.1.2.2.1.1
  · rcases Restated.Vocabulary.Proofs.NamedOutageProvenance.held_block_origin facts S rho _ source W hW
        hHsource with hgen' | ⟨i, hin', ta, hacc⟩
    · exact False.elim (hgen hgen')
    · obtain ⟨eSource, heSource, _, htSource⟩ := hacc.1.2
      have hta : ta < sourceCut := by
        rw [← htSource]
        exact time_lt_of_lt_strict₄₇ hf.sorted heSource hin'
      have hmax : max ta lo ≤ max sourceCut lo :=
        max_le_max hta.le (le_refl _)
      have htaDeadline : max ta lo + S.E.Δ ≤ targetEarly :=
        (add_le_add hmax (le_refl _)).trans hDeadline
      have htaMax : ta < max ta lo + S.E.Δ := by
        exact (le_max_left _ _).trans_lt
          (lt_add_of_pos_right (max ta lo) S.E.Δ_pos)
      have htaEarly : ta < targetEarly := htaMax.trans_le htaDeadline
      have hiEarly : i + 1 ≤ strictEventIndex rho targetEarly :=
        Nat.succ_le_of_lt (lt_strict_of_time_lt₄₇ hf.sorted heSource (by rw [htSource]; exact htaEarly))
      by_cases hskip : H ∈ (W (i + 1) reader).st.bodies
      · exact bodies_mono_path₄₇ facts S rho W hW reader hiEarly hskip
      · have hmissing : Restated.Vocabulary.Execution.Object.processed M
            (W (i + 1) reader).st (.block H) = false := by
          simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
          exact hskip
        have hdr : max ta lo + S.E.Δ ≤ targetRead := htaDeadline.trans hOrder
        have hguard : Block.compatible
            (W (strictEventIndex rho (max ta lo + S.E.Δ)) reader).st.core.F H.erase = true :=
          Restated.Vocabulary.Proofs.not_excludes_of_F_preceq_later_time facts S rho hf.sorted
            (w := reader) (B := H) hdr _
            (by rw [stateBeforeTime_eq_strict₄₇ S rho hf.sorted]; exact (hW _).1) _
            (onePath_slice₄₇ W hW (Restated.strict_lengths_mono rho hdr)) hF
        have hsrc : source ∈ Hs (max ta lo) := hHs _ _ hmax hsource
        have hrd : reader ∈ Hs (max ta lo + S.E.Δ) := hHs _ _ htaDeadline hreader
        obtain ⟨td, hlo, hhi, j, hcall, hadmit⟩ := hf.relay_block_admit
          source i H ta hsrc hacc reader hrd hmissing
          (htaDeadline.trans hCut) hguard
        obtain ⟨e, he, _, het⟩ := hcall.2
        have htdEarly : td < targetEarly := hhi.trans_le htaDeadline
        have heEarly : e.time < targetEarly := by rw [het]; exact htdEarly
        have heDomain : e.time < targetRead := heEarly.trans_le hOrder
        have hindex : j + 1 ≤ strictEventIndex rho targetRead :=
          Nat.succ_le_of_lt (lt_strict_of_time_lt₄₇ hf.sorted he heDomain)
        have hFmono := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho reader
          ((Nat.le_succ j).trans hindex) (W j) (hW j).1 _
          (onePath_slice₄₇ W hW ((Nat.le_succ j).trans hindex))
        have hFcall : Block.Preceq (W j reader).st.core.F H.erase := by
          apply preceq_trans_Preceq hFmono
          exact hF
        have hroots : Restated.Vocabulary.Execution.NamedRootCollisionFree M S
            ({ rho with honest := Xb } : Record.Run V) W :=
          ⟨fun B C hB hC => hf.rootCollisionFree.root_injective B C hB hC⟩
        have hpost : H ∈ (W (j + 1) reader).st.bodies :=
          Restated.Vocabulary.Proofs.NamedRelayGuards.handled_block_held_of_finalized_prefix_of_fields facts S
            { rho with honest := Xb } W hW (fun i v o t hi => hf.deps i v o t hi) hroots
            (hHsXb _ hsource) (hHsXb _ hreader) hacc hcall hadmit hFcall
        exact bodies_mono_path₄₇ facts S rho W hW reader
          (Nat.succ_le_of_lt (lt_strict_of_time_lt₄₇ hf.sorted he heEarly)) hpost

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

/-- On the path `W` of `hf`, under the hypotheses of `head_held_at_early_after_gst_admitOn`, the
    reader holds `H` in `W (strictEventIndex rho targetRead)`, with a block stamp less than
    `targetEarly`, and its tree there finds `H` at `H`'s root. -/
theorem healthy_head_body_at_read_after_gst_admitOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (source : V) (reader : V) (H : NamedBlock V)
    (sourceCut targetEarly targetRead : Time)
    (hsource : source ∈ Hs (max sourceCut lo)) (hreader : reader ∈ Hs targetEarly)
    (hHsource : H ∈ (W (strictEventIndex rho sourceCut) source).st.bodies)
    (hDeadline : max sourceCut lo + S.E.Δ ≤ targetEarly)
    (hOrder : targetEarly ≤ targetRead) (hCut : targetEarly ≤ rho.horizon)
    (hF : Block.Preceq (W (strictEventIndex rho targetRead) reader).st.core.F H.erase) :
    H ∈ (W (strictEventIndex rho targetRead) reader).st.bodies ∧
      stampedBefore
        (W (strictEventIndex rho targetRead) reader).st.core.timestamp_block
        targetEarly H.erase = true ∧
      Block.find? (W (strictEventIndex rho targetRead) reader).st.core.T H.erase.root =
        some H.erase := by
  have hEarly := Restated.head_held_at_early_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb
    source reader H sourceCut targetEarly targetRead hsource hreader hHsource hDeadline hOrder hCut hF
  have hStamp := Restated.held_body_stampedBefore_stateBeforeTimeOn facts S rho Hs Xb hf reader targetEarly
    H hEarly
  obtain ⟨hHeld, hCarry⟩ := Restated.strict_body_stamp_carryOn facts S rho Hs Xb hf reader hOrder H
    hEarly
  refine ⟨hHeld, ?_, Restated.held_find_at_strictOn_HealthyHeadReady facts S rho Hs Xb hf reader
    (hHsXb _ hreader) targetRead H hHeld⟩
  obtain ⟨σ, hσ, hlt⟩ := exists_stamp_of_stampedBefore hStamp
  exact stampedBefore_of_lt (hCarry.trans hσ) hlt

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

/-- On the path `W` of `hf`, if `source, reader ∈ Xb`, `source`'s tree in
    `W (strictEventIndex rho sourceTime)` finds `H` at `u`'s head and `reader`'s tree in
    `W (strictEventIndex rho readerTime)` finds `K` there, then `H = K`. -/
theorem pinScoreEq_resolved_blocks_eqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {source reader : V} (hsource : source ∈ Xb)
    (hreader : reader ∈ Xb) {sourceTime readerTime : Time}
    {u : GoldfishVote V} {H K : Block V}
    (hH : Block.find? (W (strictEventIndex rho sourceTime) source).st.core.T u.head = some H)
    (hK : Block.find? (W (strictEventIndex rho readerTime) reader).st.core.T u.head = some K) :
    H = K := by
  obtain ⟨HN, hHNe, hHNrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hsource sourceTime
      (Proofs.HealingLemmas.find?_mem hH)
  obtain ⟨KN, hKNe, hKNrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hreader readerTime
      (Proofs.HealingLemmas.find?_mem hK)
  have hroot : HN.root = KN.root := by
    rw [← Proofs.NamedWire.erase_root HN, ← Proofs.NamedWire.erase_root KN, hHNe, hKNe]
    exact (Proofs.HealingLemmas.find?_root hH).trans
      (Proofs.HealingLemmas.find?_root hK).symm
  have heq := hf.rootCollisionFree.root_injective
    HN KN hHNrun hKNrun HN KN (Or.inl (Proofs.NamedAncestry.named_self HN))
      (Or.inr (Proofs.NamedAncestry.named_self KN)) hroot
  calc
    H = HN.erase := hHNe.symm
    _ = KN.erase := congrArg NamedBlock.erase heq
    _ = K := hKNe

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

/-- If the event at index `i` has a time less than `t`, then `i` is less than the number of events
    strictly before `t`. -/
theorem pinScoreEq_index_lt_strictEventIndex_of_time_ltOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {t : Time} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) (ht : e.time < t) :
    i < strictEventIndex rho t := by
  by_contra hnot
  have hle : t ≤ e.time :=
    Restated.le_time_of_index_geOn facts S Hs Xb hf (t := t) (j := i) (e := e)
      (by simpa only [strictEventIndex] using Nat.le_of_not_gt hnot) hi
  exact (not_le_of_gt ht) hle

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

/-- On the path `W` of `hf`, if the reader, in the set for the public time `cut ≥ lo`, holds `B` in
    `W (strictEventIndex rho read)` with a block stamp there less than `cut`, then it holds `B` in
    `W (strictEventIndex rho cut)`. -/
theorem pinScoreEq_body_held_at_public_cutOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {reader : V}
    {B : NamedBlock V} {cut read : Time}
    (hpublic : PublicTime S cut)
    (hreader : reader ∈ Hs cut) (hgat : lo ≤ cut)
    (hB : B ∈ (W (strictEventIndex rho read) reader).st.bodies)
    (hstamp : stampedBefore (W (strictEventIndex rho read) reader).st.core.timestamp_block
      cut B.erase = true) :
    B ∈ (W (strictEventIndex rho cut) reader).st.bodies := by
  have hW := hf.onePath
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho read) reader).st (Object.block B) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hB
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts
      S rho reader W hW _ B hprocessed with hgen | ⟨i, hi, t, haccepts⟩
  · subst B
    exact (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ reader _
      (hW (strictEventIndex rho cut)).1).1.1.1.2.2.1.1
  · have ht : t < cut :=
      Restated.acceptsAt_block_lt_of_stamp_beforeOn facts S Hs Xb hf haccepts
        (Nat.succ_le_of_lt hi) hpublic hreader hgat hstamp
    obtain ⟨⟨hindex, e, he, -, het⟩, -, hpost⟩ := haccepts
    have hiCut : i < strictEventIndex rho cut := by
      apply Restated.pinScoreEq_index_lt_strictEventIndex_of_time_ltOn facts S Hs Xb hf he
      show e.time < cut
      rw [het]
      exact ht
    have hBi : B ∈ (W (i + 1) reader).st.bodies := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hpost
    exact bodies_mono_path₄₇ facts S rho W hW reader (Nat.succ_le_of_lt hiCut) hBi

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
open DecoupledConsensusModel.Statements.Instantiation

/-- On the path `W` of `hf`, with `source` and `target` the node states staged, for every outcome
    `cs` and `ct` of the phase ticks, from the slot-`(s + 1)` proposer's node state strictly before
    `s + 1`'s proposal time and from `v`'s node state strictly before `s + 1`'s vote time: if
    `source` can propose `P`, `lo ≤ proposal_time s`, the slot-`(s + 1)` proposer is in the set for
    `s + 1`'s confirmation time, the vote and proposal times of `s + 1` are within the horizon, `v`
    is in the set for `s + 1`'s vote time, `P` is in an outcome `VT` of `target`'s voter tree, and
    every raw vote of an outcome `vv` of `target`'s voter view outside the votes `P` includes shows
    its sender equivocating in them, then on every block `C` of `source`'s filtered tree and of `VT`
    without `P`, every outcome of `target`'s Goldfish score of `C` equals every outcome of
    `source`'s Goldfish score of `C`. -/
theorem namedWalkScore_target_eq_source_of_proposalCandidateOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {P : NamedBlock V} {v : V} :
    ∀ cs : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1)))
          (S.E.proposer (s + 1))).st.core.toHealing
        (M.proposal_time S.E (s + 1))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ cs →
    ∀ ct : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).cache ⇢ ct →
    let source := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record cs
    let target := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).record ct
    M.proposal_with (M.gradeContract source.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (s + 1))) source.st ⇢ some P →
    lo ≤ M.proposal_time S.E s →
    S.E.proposer (s + 1) ∈ Hs (M.confirmation_time S.E (s + 1)) →
    M.vote_time S.E (s + 1) ≤ rho.horizon →
    M.proposal_time S.E (s + 1) ≤ rho.horizon →
    v ∈ Hs (M.vote_time S.E (s + 1)) →
    ∀ VT : Finset (Block V),
      M.voter_filtered_block_tree S.E target.st.core target.st.core.s ⇢ VT →
    P.erase ∈ VT →
    ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing target.st.core).toFG.toSG.toGoldfishStore
        target.st.core.s ⇢ vv →
    (∀ u ∈ vv, u ∉ P.erase.gf_votes.toFinset →
      M.equivocates P.erase.gf_votes.toFinset u.val_index = true) →
    ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing target.st.core).toFG.toSG.toGoldfishStore
        target.st.core.s ⇢ vsv →
    ∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing source.st.core).toFG.toSG.toGoldfishStore
        source.st.core.s ⇢ psv →
    ∀ C,
      C ∈ M.get_filtered_block_tree (M.toHealing source.st.core).toFG →
      C ∈ VT.erase P.erase →
      ∀ x, M.goldfish_score S.E target.st.core.T vv vsv (target.st.core.s - 1) C ⇢ x →
      ∀ y, M.goldfish_score S.E source.st.core.T
          (M.proposer_view (M.toHealing source.st.core).toFG.toSG.toGoldfishStore
            source.st.core.s).toFinset
          psv.toFinset (source.st.core.s - 1) C ⇢ y →
      x = y := by
  intro cs hcs ct hct source target hproposal hpostProposalSnapshot hproposerHonest hvoteHor
    hproposalHor hv VT hVT hproposalCandidate vv hvv hrawExtra vsv hvsv psv hpsv C hCsource
    hCtarget x hx y hy
  have hW := hf.onePath
  have hΔ := S.E.Δ_pos
  let Np := strictEventIndex rho (M.proposal_time S.E (s + 1))
  let Nv := strictEventIndex rho (M.vote_time S.E (s + 1))
  have hpt_le_ptsucc : M.proposal_time S.E s ≤ M.proposal_time S.E (s + 1) :=
    facts.sch.proposal_time_mono S.E (Nat.le_succ s)
  have hlo_ptsucc : lo ≤ M.proposal_time S.E (s + 1) :=
    hpostProposalSnapshot.trans hpt_le_ptsucc
  have hfreeze_delta : M.view_freeze S.E s + S.E.Δ ≤ M.proposal_time S.E (s + 1) :=
    facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E s
  have hfreeze_ptsucc : M.view_freeze S.E s ≤ M.proposal_time S.E (s + 1) := by
    linarith
  have hptsucc_delta : M.proposal_time S.E (s + 1) + S.E.Δ ≤ M.vote_time S.E (s + 1) :=
    add_delta_le_of_lt_emod₄₇ hΔ (facts.sch.proposal_time_emod_delta_inclX S.E (s + 1))
      (facts.sch.vote_time_emod_delta S (s + 1)) (facts.sch.proposal_time_lt_vote_time S.E (s + 1))
  have hptsucc_vote : M.proposal_time S.E (s + 1) ≤ M.vote_time S.E (s + 1) :=
    le_of_lt (facts.sch.proposal_time_lt_vote_time S.E (s + 1))
  have hvote_conf : M.vote_time S.E (s + 1) ≤ M.confirmation_time S.E (s + 1) :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E (s + 1)
  have hlo_freeze : lo ≤ M.view_freeze S.E s :=
    hpostProposalSnapshot.trans (le_of_lt ((facts.sch.proposal_time_lt_vote_time S.E s).trans
      ((vote_time_lt_support_cutoff₄₇ facts S s).trans
        (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s))))
  have hproposerAtProposal' : S.E.proposer (s + 1) ∈ Hs (M.proposal_time S.E (s + 1)) :=
    hHs _ _ (hptsucc_vote.trans hvote_conf) hproposerHonest
  have hproposerAtProposal :
      S.E.proposer (s + 1) ∈ Hs (max (M.proposal_time S.E (s + 1)) lo) := by
    rw [max_eq_left hlo_ptsucc]
    exact hproposerAtProposal'
  have hvFreeze : v ∈ Hs (M.view_freeze S.E s) :=
    hHs _ _ (hfreeze_ptsucc.trans hptsucc_vote) hv
  have hvFreezeMax : v ∈ Hs (max (M.view_freeze S.E s) lo) := by
    rw [max_eq_left hlo_freeze]
    exact hvFreeze
  have hloFreeze := hlo_freeze
  have hsrcSt : source.st = M.store_with_cache (M.ns_setClock S.E (W Np (S.E.proposer (s + 1))).st (M.proposal_time S.E (s + 1))) _ := facts.nd.mkNode_st _ _ _
  have htgtSt : target.st = M.store_with_cache (M.ns_setClock S.E (W Nv v).st (M.vote_time S.E (s + 1))) _ := facts.nd.mkNode_st _ _ _
  have hsrcMem : source ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (s + 1) :=
    ⟨W Np, by rw [stateBeforeTime_eq_strict₄₇ S rho hf.sorted]; exact (hW Np).1, cs, hcs, rfl⟩
  have hsourceT : source.st.core.T = (W Np (S.E.proposer (s + 1))).st.core.T := by
    rw [hsrcSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact facts.hd.Sts_setClock_core_T _ _ _
  have htargetT : target.st.core.T = (W Nv v).st.core.T := by
    rw [htgtSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact facts.hd.Sts_setClock_core_T _ _ _
  have hsourceGf : ∀ k, source.st.core.gf_votes k = (W Np (S.E.proposer (s + 1))).st.core.gf_votes k := by
    intro k
    rw [hsrcSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_gf_votes]
  have hsourceF : source.st.core.F = (W Np (S.E.proposer (s + 1))).st.core.F := by
    rw [hsrcSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_F]
  have htargetF : target.st.core.F = (W Nv v).st.core.F := by
    rw [htgtSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_F]
  have htargetTs : target.st.core.timestamp_block = (W Nv v).st.core.timestamp_block := by
    rw [htgtSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_timestamp_block]
  have hsourceSlot : source.st.core.s = s + 1 := by
    rw [hsrcSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s]
    exact facts.sch.slotOf_proposal_time S.E (s + 1)
  have htargetSlot : target.st.core.s = s + 1 := by
    rw [htgtSt]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s]
    exact facts.sch.slotOf_vote_time S.E (s + 1)
  have hPslotEq : P.slot = s + 1 :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho (s + 1) (some P)
      ⟨source, hsrcMem, hproposal⟩ rfl
  have hPtargetFiltered : P.erase ∈
      M.get_filtered_block_tree (M.toHealing target.st.core).toFG :=
    facts.fc.voter_filtered_block_tree_subset_filtered S.E target.st.core VT hVT hproposalCandidate
  have hPtargetT : P.erase ∈ target.st.core.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hPtargetFiltered
    rw [facts.sto.toHealing_gs_T] at h
    exact h
  have hnconf : ∀ (j : Nat) (e : Record.Event V), j < Nv → rho.events[j]? = some e →
      e.time ≤ M.confirmation_time S.E (s + 1) :=
    fun j e hj he => (time_lt_of_lt_strict₄₇ hf.sorted he hj).le.trans hvote_conf
  have hPprefix : P.erase ∈ (W Nv v).st.core.T := by
    rw [← htargetT]
    exact hPtargetT
  have hslots : ∀ u ∈ P.gf_votes, u.slot + 1 = P.slot := by
    intro u hu
    have huFin : u ∈ (M.store_pool source.st.core (source.st.core.s - 1)) := by
      rw [← Restated.Vocabulary.Protocol.proposedBlock_raw_eq_proposer_pool facts
        S rho (s + 1) source hsrcMem hproposal]
      exact List.mem_toFinset.mpr hu
    have huFin' : u ∈ (M.store_pool source.st.core s) := by
      simpa only [hsourceSlot, Nat.add_sub_cancel] using huFin
    have huPool : u ∈ (W Np (S.E.proposer (s + 1))).st.core.gf_votes s := by
      rw [facts.sto.mem_store_pool_iff, hsourceGf] at huFin'
      exact huFin'
    have hus := (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf
      (S.E.proposer (s + 1)) Np).slot s u huPool
    rw [hPslotEq, hus]
  have hrawSubset : P.gf_votes.toFinset ⊆ vv := by
    intro u hu
    have hPslot : P.erase.slot = target.st.core.s := by
      rw [Proofs.NamedWire.erase_slot, hPslotEq]
      exact htargetSlot.symm
    have hsub := facts.fc.carried_raw_subset_voter_view
      S.E (M.toHealing target.st.core).toFG.toSG.toGoldfishStore
      (by rw [facts.sto.toHealing_gs_T]; exact hPtargetT)
      hPslot
      (by
        intro x hx
        have hx' : x ∈ P.gf_votes := by
          simpa only [Proofs.NamedWire.erase_goldfish_votes] using hx
        simpa only [Proofs.NamedWire.erase_slot] using hslots x hx')
      vv hvv
    exact hsub (by simpa only [Proofs.NamedWire.erase_goldfish_votes] using hu)
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract source.cache)
    S.E S.hc (S.node (S.E.proposer (s + 1))) (M.toHealing source.st.core)
  have hraw : (M.proposer_view
      (M.toHealing source.st.core).toFG.toSG.toGoldfishStore
      source.st.core.s).toFinset = P.gf_votes.toFinset := by
    rw [Restated.Vocabulary.Protocol.proposedBlock_gf_votes facts S rho (s + 1) source hsrcMem hproposal
      input hinput,
      facts.dt.with_proposal_input_id_gf_votes _ _ _ _ _ input hinput, facts.sto.toHealing_s]
  have hsupp : psv.toFinset = P.gf_support_votes.toFinset := by
    rw [Restated.Vocabulary.Protocol.proposedBlock_gf_support_votes facts S rho (s + 1) source hsrcMem
      hproposal input hinput,
      facts.dt.with_proposal_input_id_gf_support_votes _ _ _ _ _ input hinput psv
        (by rw [facts.sto.toHealing_s]; exact hpsv)]
  have hbridge : Restated.Vocabulary.Protocol.CandidateScorePreservingViewExtension M
      source.st.core.T target.st.core.T P.gf_votes.toFinset
      P.gf_support_votes.toFinset vv vsv C := by
    refine
      { raw_subset := hrawSubset
        raw_extra_equiv := ?_
        forward := ?_
        backward := ?_ }
    · intro u hu hnot
      simpa only [Proofs.NamedWire.erase_goldfish_votes] using
        hrawExtra u hu (by simpa only [Proofs.NamedWire.erase_goldfish_votes] using hnot)
    · intro u hu b hb htargets
      obtain ⟨H, hfindSource, hCH⟩ := (facts.fc.targets_under_iff b hb).mp htargets
      have hHsource : H ∈ source.st.core.T :=
        Proofs.HealingLemmas.find?_mem hfindSource
      have hHpre : H ∈ (W Np (S.E.proposer (s + 1))).st.core.T := by
        rw [← hsourceT]
        exact hHsource
      obtain ⟨HN, hHNbody, hHNerase⟩ :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
          Np (S.E.proposer (s + 1)) (W Np) (hW Np).1 hHpre
      have hFC : Block.Preceq target.st.core.F C := by
        have hCfiltered : C ∈ M.get_filtered_block_tree (M.toHealing target.st.core).toFG :=
          facts.fc.voter_filtered_block_tree_subset_filtered S.E target.st.core VT hVT
            (Finset.mem_of_mem_erase hCtarget)
        have hFC :=
          facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hCfiltered
        rw [facts.sto.ModelProperties_toHealing_F] at hFC
        exact hFC
      have hFH : Block.Preceq target.st.core.F H :=
        preceq_trans_Preceq hFC (preceq_eq_true_iff_Preceq.mp hCH.2)
      have hdeadline : max (M.proposal_time S.E (s + 1)) lo +
          S.E.Δ ≤ M.vote_time S.E (s + 1) := by
        rw [max_eq_left hlo_ptsucc]
        exact hptsucc_delta
      have hrelay := Restated.healthy_head_body_at_read_after_gst_admitOn facts
        S rho Hs Xb hf hHs hHsXb (S.E.proposer (s + 1))
        v HN (M.proposal_time S.E (s + 1))
        (M.vote_time S.E (s + 1))
        (M.vote_time S.E (s + 1)) hproposerAtProposal hv hHNbody hdeadline le_rfl
        hvoteHor (by
          rw [hHNerase, ← htargetF]
          exact hFH)
      have hfindTarget : Block.find? target.st.core.T u.head = some H := by
        have hfind := hrelay.2.2
        rw [hHNerase] at hfind
        have hroot : H.root = u.head := Proofs.HealingLemmas.find?_root hfindSource
        rw [htargetT, ← hroot]
        exact hfind
      obtain ⟨bT, hbT⟩ := facts.sto.resolved_nonempty target.st.core.T u
      have hbTtrue : bT = true :=
        (facts.sto.resolved_eq_true_iff _ _ bT hbT).mpr ⟨H, hfindTarget, hCH.1⟩
      subst hbTtrue
      have huList : u ∈ P.gf_support_votes := List.mem_toFinset.mp hu
      have huslot : u.slot + 1 = P.erase.slot := by
        rw [Proofs.NamedWire.erase_slot]
        apply hslots u
        obtain ⟨bS, hbS⟩ := facts.sto.resolved_nonempty
          (M.toHealing source.st.core).toFG.toSG.toGoldfishStore.T u
        have h : u ∈ psv := by
          rw [← List.mem_toFinset, hsupp]
          exact hu
        have h' := (facts.fc.mem_proposer_support_view_iff _ _ u psv hpsv bS hbS).mp h
        rw [← List.mem_toFinset, ← hraw, List.mem_toFinset, facts.fc.proposer_view_eq]
        exact h'.1
      have huTarget : u ∈ vsv := by
        exact Restated.Vocabulary.Protocol.mem_voter_support_view_of_carried facts S.E
          (M.toHealing target.st.core).toFG.toSG.toGoldfishStore
          (by rw [facts.sto.toHealing_gs_T]; exact hPtargetT)
          (by rw [Proofs.NamedWire.erase_slot, hPslotEq, htargetSlot])
          (by simpa only [Proofs.NamedWire.erase_goldfish_support] using huList)
          (by rw [facts.sto.toHealing_gs_T]; exact hbT) huslot vsv hvsv
      exact Or.inl ⟨huTarget, fun b' hb' =>
        (facts.fc.targets_under_iff b' hb').mpr ⟨H, hfindTarget, hCH.1, hCH.2⟩⟩
    · intro u hu b hb htargets
      have huRaw : u ∈ vv := by
        apply (facts.fc.voter_support_view_subset S.E
          (M.toHealing target.st.core).toFG.toSG.toGoldfishStore target.st.core.s
          (by
            intro D hD x hx
            have hDprefix : D ∈ (W Nv v).st.core.T := by
              rw [facts.sto.toHealing_gs_T, htargetT] at hD
              exact hD
            exact Restated.carried_support_subset_of_mem_TOn facts S Hs Xb hf v Nv hDprefix x hx)
          vsv hvsv vv hvv) hu
      obtain ⟨bR, hbR⟩ := facts.sto.resolved_nonempty
        (M.toHealing target.st.core).toFG.toSG.toGoldfishStore.T u
      rcases facts.fc.voter_support_view_cases S.E _ _ vsv hvsv hu bR hbR with
        ⟨-, X, hX, -, τ, σ, -, hσ, -, hσlt⟩ | ⟨D, hD, hDslot, huD, -, -⟩
      · by_cases huSource : u ∈ P.gf_votes.toFinset
        · obtain ⟨K, hfindTarget, hCK⟩ :=
            (facts.fc.targets_under_iff b hb).mp htargets
          have hKtarget : K ∈ target.st.core.T :=
            Proofs.HealingLemmas.find?_mem hfindTarget
          have hKpre : K ∈ (W Nv v).st.core.T := by
            rw [← htargetT]
            exact hKtarget
          obtain ⟨KN, hKNbody, hKNerase⟩ :=
            Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
              Nv v (W Nv) (hW Nv).1 hKpre
          have hstamp : stampedBefore (W Nv v).st.core.timestamp_block
              (M.view_freeze S.E s) KN.erase = true := by
            rw [facts.sto.toHealing_gs_T, hfindTarget] at hX
            obtain rfl : K = X := Option.some.inj hX
            rw [facts.sto.toHealing_gs_timestamp_block, htargetTs] at hσ
            rw [htargetSlot, Nat.add_sub_cancel] at hσlt
            rw [hKNerase]
            exact stampedBefore_of_lt hσ hσlt
          have hKNfreeze := Restated.pinScoreEq_body_held_at_public_cutOn facts
            S Hs Xb hf (Restated.Vocabulary.Protocol.publicTime_view_freeze facts S s) hvFreeze
            hloFreeze hKNbody hstamp
          have hFC : Block.Preceq source.st.core.F C := by
            have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree
              (st := (M.toHealing source.st.core).toFG) hCsource
            rw [facts.sto.ModelProperties_toHealing_F] at h
            exact h
          have hFK : Block.Preceq source.st.core.F K :=
            preceq_trans_Preceq hFC (preceq_eq_true_iff_Preceq.mp hCK.2)
          have hdeadline : max (M.view_freeze S.E s) lo +
              S.E.Δ ≤ M.proposal_time S.E (s + 1) := by
            rw [max_eq_left hlo_freeze]
            exact hfreeze_delta
          have hrelay := Restated.healthy_head_body_at_read_after_gst_admitOn facts
            S rho Hs Xb hf hHs hHsXb v (S.E.proposer (s + 1))
            KN (M.view_freeze S.E s)
            (M.proposal_time S.E (s + 1))
            (M.proposal_time S.E (s + 1)) hvFreezeMax hproposerAtProposal'
            hKNfreeze hdeadline le_rfl
            hproposalHor (by
              rw [hKNerase, ← hsourceF]
              exact hFK)
          have hfindSource : Block.find? source.st.core.T u.head = some K := by
            have hfind := hrelay.2.2
            rw [hKNerase] at hfind
            have hroot : K.root = u.head := Proofs.HealingLemmas.find?_root hfindTarget
            rw [hsourceT, ← hroot]
            exact hfind
          have huList : u ∈ P.gf_votes := List.mem_toFinset.mp huSource
          have huSupport : u ∈ P.gf_support_votes.toFinset := by
            rw [← hsupp, List.mem_toFinset]
            obtain ⟨bS, hbS⟩ := facts.sto.resolved_nonempty
              (M.toHealing source.st.core).toFG.toSG.toGoldfishStore.T u
            refine (facts.fc.mem_proposer_support_view_iff _ _ u psv hpsv bS hbS).mpr ⟨?_, ?_⟩
            · have h := huSource
              rw [← hraw, List.mem_toFinset, facts.fc.proposer_view_eq] at h
              exact h
            · exact (facts.sto.resolved_eq_true_iff _ _ bS hbS).mpr
                ⟨K, by rw [facts.sto.toHealing_gs_T]; exact hfindSource, hCK.1⟩
          exact Or.inl ⟨huSupport, fun b' hb' =>
            (facts.fc.targets_under_iff b' hb').mpr ⟨K, hfindSource, hCK.1, hCK.2⟩⟩
        · exact Or.inr (by
            simpa only [Proofs.NamedWire.erase_goldfish_votes] using
              hrawExtra u huRaw
                (by simpa only [Proofs.NamedWire.erase_goldfish_votes] using huSource))
      · have hDprefix : D ∈ (W Nv v).st.core.T := by
          rw [facts.sto.toHealing_gs_T, htargetT] at hD
          exact hD
        have hDeq : D = P.erase := Restated.unique_slot_block_in_store_beforeOn facts
          S Hs Xb hf hHs (Nat.succ_pos s) hproposerHonest hnconf hnconf
          hDprefix hPprefix (by rw [hDslot, htargetSlot])
          (by rw [Proofs.NamedWire.erase_slot, hPslotEq])
        subst D
        have huSource : u ∈ P.gf_support_votes.toFinset := by
          simpa only [Proofs.NamedWire.erase_goldfish_support, List.mem_toFinset] using huD
        obtain ⟨K, hfindTarget, hCK⟩ :=
          (facts.fc.targets_under_iff b hb).mp htargets
        obtain ⟨bS, hbS⟩ := facts.sto.resolved_nonempty
          (M.toHealing source.st.core).toFG.toSG.toGoldfishStore.T u
        have hbStrue : bS = true := by
          have h : u ∈ psv := by
            rw [← List.mem_toFinset, hsupp]
            exact huSource
          exact ((facts.fc.mem_proposer_support_view_iff _ _ u psv hpsv bS hbS).mp h).2
        obtain ⟨H, hfindSource, -⟩ := (facts.sto.resolved_eq_true_iff _ _ bS hbS).mp hbStrue
        rw [facts.sto.toHealing_gs_T] at hfindSource
        have hHK : H = K := Restated.pinScoreEq_resolved_blocks_eqOn facts
          S Hs Xb hf (hHsXb _ hproposerHonest) (hHsXb _ hv)
          (sourceTime := M.proposal_time S.E (s + 1))
          (readerTime := M.vote_time S.E (s + 1))
          (by have h := hfindSource; rw [hsourceT] at h; exact h)
          (by have h := hfindTarget; rw [htargetT] at h; exact h)
        have hHslot : H.slot ≤ u.slot := by
          simpa only [← hHK] using hCK.1
        have hHC : C.preceq H = true := by
          simpa only [← hHK] using hCK.2
        exact Or.inl ⟨huSource, fun b' hb' =>
          (facts.fc.targets_under_iff b' hb').mpr ⟨H, hfindSource, hHslot, hHC⟩⟩
  have hscore := candidateScore_eq₄₇ facts hbridge S.E (s + 1 - 1)
  rw [hraw, hsupp, hsourceSlot] at hy
  rw [htargetSlot] at hx
  exact (hscore y hy x hx).symm

end

end DecoupledConsensusModel.Sts.Restated
