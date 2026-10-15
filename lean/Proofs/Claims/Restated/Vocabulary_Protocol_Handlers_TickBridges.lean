import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# What a tick emits and reads

The outputs of a tick's confirmation, vote and proposal branches, the public tick times, the slots
of the stores the duties read, and the origin of an attestation in an SG pool, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- For every positive slot `s` at whose round `v`'s tick on `n` runs the confirmation and
    attestation duties, every outcome `w₁` of `v`'s tick at slot `s`'s support cutoff `t` from `n`,
    every outcome `c` of the phase tick at `t`, and every outcome `D` of the confirmation duty for
    slot `s - 1`, run with `c`'s grade contract on `n`'s store with its clock set to `t`, the
    `live_confirmed` of `w₁`'s store is that of `D`. -/
theorem Vocabulary.Proofs.Optimistic.on_tick_emit_confirmation (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N)
    (s : Slot) (hs : 0 < s)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v n (M.round_of S.hc s)) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.on_tick_emit M S v n (M.support_cutoff S.E s),
    ∀ c, M.onPhaseTick S.E S.hc n.st.core.toHealing (M.support_cutoff S.E s) n.cache ⇢ c →
    ∀ D, M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E n.st (M.support_cutoff S.E s)) (s - 1) ⇢ D →
    ∀ (hn : M.reachedNode n := by trivial),
    w₁.1.st.live_confirmed = D.live_confirmed :=
  fun w₁ hw₁ c hc D hD _hn => facts.nd.on_tick_emit_confirmation_of_outcomes S v n s hs w₁ hw₁ c hc D hD hrun

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- The vote time of slot `s` is a public tick time. -/
theorem Vocabulary.Proofs.Optimistic.publicTime_vote_time (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    PublicTime S (M.vote_time S.E s) :=
  (facts.sch.publicTime_iff S _).mpr ⟨s, Or.inr (Or.inl rfl)⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- The confirmation time of slot `s` is a public tick time. -/
theorem Vocabulary.Proofs.Optimistic.publicTime_confirmation_time (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    PublicTime S (M.confirmation_time S.E s) :=
  (facts.sch.publicTime_iff S _).mpr ⟨s + 1, Or.inr (Or.inr (Or.inl
    (facts.sch.confirmation_time_eq_support_cutoff_succ S.E s)))⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- The vote store of `st` at slot `s` has slot `s`. -/
theorem Vocabulary.Proofs.Optimistic.voteStore_slot (facts : Record.Facts M) (S : Setup V) (st : M.S) (s : Slot) :
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S st s).s = s := by
  simp only [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.sch.slotOf_vote_time]
  exact facts.sto.store_with_t_s_s st _ s

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- Every node state of `v`'s vote-duty read at slot `s` has a core store of slot `s`. -/
theorem Vocabulary.Proofs.Optimistic.voteDutyRead_slot (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (v : V) (s : Slot) : ∀ w₁ ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S ρ v s, 
    w₁.st.core.s = s := by
  intro w₁ hw₁
  obtain ⟨w, -, c, -, rfl⟩ := hw₁
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.ModelProperties_setClock_core_s]
  exact facts.sch.slotOf_vote_time S.E s

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- For every positive slot `s`, if `c` is an outcome of the phase tick at slot `s`'s vote time `t`
    and the Goldfish vote duty, run with `c`'s grade contract on `n`'s store with its clock set to
    `t`, can return the vote `u`, and `n` passes the grade-1 awake test of slot `s`'s round, then
    every outcome `w₁` of `v`'s tick at `t` from `n` sends `u`. -/
theorem Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (s : Slot)
    (hs : 0 < s) {u : GoldfishVote V}
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing (M.vote_time S.E s) n.cache ⇢ c)
    (D : M.NS × Option (GoldfishVote V))
    (hD : M.duties_goldfish_vote_with (M.gradeContract c) S.E S.hc (S.node v)
        (M.ns_setClock S.E n.st (M.vote_time S.E s)) ⇢ D)
    (hu : D.2 = some u) (hrun : M.awake_for_grade1 S v n (M.round_of S.hc s)) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.on_tick_emit M S v n (M.vote_time S.E s),
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    Object.gfVote u ∈ w₁.2 :=
  fun w₁ hw₁ _hn _hv => facts.nd.on_tick_emit_vote_mem_of_outcomes S v n s hs c hc D hD hu w₁ hw₁ hrun

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- If `m ≤ n` and none of the events `m` to `n - 1` of `ρ` is a tick of `v`, then for every world
    `w₁` before the `m`-th event of `ρ`, and every world `w₂` that the events `m` to `n - 1` of `ρ`
    can lead to from `w₁`, `v`'s `live_confirmed` is the same in `w₂` as in `w₁`. -/
theorem Vocabulary.Proofs.Optimistic.stateBefore_live_confirmed_of_no_tick (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (v : V)
    {m : Nat} :
    ∀ n : Nat, m ≤ n →
      (∀ (j : Nat) (e : Record.Event V), m ≤ j → j < n → ρ.events[j]? = some e →
        ∀ t' : Time, e ≠ Record.Event.tick v t') →
      ∀ w₁ ∈ Record.stateBeforeOf M S ρ m,
      ∀ w₂ ∈ ((ρ.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w₁,
      (w₂ v).st.live_confirmed = (w₁ v).st.live_confirmed := by
  intro n hmn hno w₁ _
  have hl : ∀ e ∈ (ρ.events.drop m).take (n - m), ∀ t' : Time, e ≠ Record.Event.tick v t' := by
    intro e he t'
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
    have hklt : k < n - m := by
      have h1 := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at h1
      omega
    rw [List.getElem?_take_of_lt hklt, List.getElem?_drop] at hk
    exact hno (m + k) e (by omega) (by omega) hk t'
  suffices h : ∀ (l : List (Record.Event V)) (w : V → M.N),
      (∀ e ∈ l, ∀ t' : Time, e ≠ Record.Event.tick v t') →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w,
        (w₂ v).st.live_confirmed = (w v).st.live_confirmed from h _ w₁ hl
  intro l
  induction l with
  | nil =>
      intro w _ w₂ hw₂
      rw [Set.mem_singleton_iff.mp hw₂]
  | cons e l ih =>
      intro w hle w₂ hw₂
      rw [List.foldlM_cons, Set.bind_def] at hw₂
      obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
      rw [ih w' (fun e' he' => hle e' (List.mem_cons_of_mem _ he')) w₂ hw₂']
      cases e with
      | wake u t' =>
          obtain rfl : w' = Function.update w u (M.wake (w u)) := hw'
          by_cases hu : u = v
          · subst hu
            rw [Function.update_self, (facts.nd.wake_st_record (w u)).1]
          · rw [Function.update_of_ne (Ne.symm hu)]
      | tick u t' =>
          have hu : u ≠ v := fun h => hle _ List.mem_cons_self t' (by rw [h])
          rcases hw' with ⟨out, -, rfl⟩ | ⟨-, rfl⟩
          · rw [Function.update_of_ne (Ne.symm hu)]
          · rfl
      | deliver u o t' =>
          by_cases hu : u = v
          · subst hu
            rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
            · rw [Function.update_self]
              exact facts.ndRun.process_live_confirmed S (w u) o n' hn'
            · rfl
          · rcases hw' with ⟨n', -, rfl⟩ | ⟨-, rfl⟩
            · rw [Function.update_of_ne (Ne.symm hu)]
            · rfl

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- The proposal time of slot `s` is a public tick time. -/
theorem Vocabulary.Proofs.Optimistic.publicTime_proposal_time (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    PublicTime S (M.proposal_time S.E s) :=
  (facts.sch.publicTime_iff S _).mpr ⟨s, Or.inl rfl⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- For every positive slot `s` whose proposer is `v`'s node, if `c` is an outcome of the phase tick
    at slot `s`'s proposal time `t` and the proposal duty, run with `c`'s grade contract on `n`'s
    store with its clock set to `t`, can return the block `B`, and `n` passes the grade-1 awake test
    of slot `s`'s round, then every outcome `w₁` of `v`'s tick at `t` from `n` sends `B`. -/
theorem Vocabulary.Proofs.Optimistic.on_tick_emit_proposal_mem (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (s : Slot)
    (hs : 0 < s) (hpr : S.E.proposer s = (S.node v).val_index) {B : NamedBlock V}
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing (M.proposal_time S.E s) n.cache ⇢ c)
    (D : M.NS × Option (NamedBlock V))
    (hD : M.duties_propose_block_with (M.gradeContract c) S.E S.hc S.cfg (S.node v)
        (M.ns_setClock S.E n.st (M.proposal_time S.E s)) ⇢ D)
    (hB : D.2 = some B) (hrun : M.awake_for_grade1 S v n (M.round_of S.hc s)) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.on_tick_emit M S v n (M.proposal_time S.E s),
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    Object.block B ∈ w₁.2 :=
  fun w₁ hw₁ _hn _hv => facts.nd.on_tick_emit_proposal_mem_of_outcomes S v n s hs hpr c hc D hD hB w₁ hw₁ hrun

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- For every proposal `p` that slot `s`'s proposer can compute at slot `s`'s proposal time in `ρ`,
    if `p` is the block `B`, then `B`'s slot is `s`. -/
theorem Vocabulary.Proofs.Optimistic.proposedBlockAt_slot (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S ρ s, p = some B →
      B.slot = s := by
  intro p hp hB
  obtain ⟨n, ⟨w, -, c, -, rfl⟩, hp⟩ := hp
  have hst : (M.mkNode (M.ns_setClock S.E (w (S.E.proposer s)).st (M.proposal_time S.E s))
      (w (S.E.proposer s)).record c).st.core.s = s := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.ModelProperties_setClock_core_s]
    exact facts.sch.slotOf_proposal_time S.E s
  exact (facts.dt.ModelProperties_proposal_with_slot _ _ _ _ _ _ B p hp hB).trans hst

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Execution

/-- For every path `W` of `ρ`, if the attestation `a` is in the attestation set of round `r` of
    `v`'s store in `W i`, then some event `j < i` of `ρ` is at a time at which `v` processes, along
    `W`, an object `o` that carries `a`. -/
theorem Vocabulary.Proofs.Optimistic.processes_attest_of_mem_sg_pool (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (v : V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W) :
    ∀ (i : Nat) (r : Round) (a : CombinedAttestation V),
      a ∈ (W i v).st.core.sg_pool r →
        ∃ (j : Nat) (e : Record.Event V) (o : Object V), j < i ∧ ρ.events[j]? = some e ∧
          Restated.Vocabulary.Execution.NamedRun.processes M S ρ W v o e.time ∧ CarriesRow o a := by
  have htick := facts.stoRun.tick_sg_pool_mem
  intro i
  induction i with
  | zero =>
    intro r a ha
    exfalso
    have h0 : W 0 = fun u => M.initial S u := (hW 0).1
    rw [h0] at ha
    change a ∈ (M.initial S v).st.core.sg_pool r at ha
    rw [facts.nd.initial_st] at ha
    exact facts.hd.initial_core_not_mem_sg_pool r a ha
  | succ n ih =>
    intro r a ha
    have lift : a ∈ (W n v).st.core.sg_pool r →
        ∃ (j : Nat) (e : Record.Event V) (o : Object V), j < n + 1 ∧ ρ.events[j]? = some e ∧
          Restated.Vocabulary.Execution.NamedRun.processes M S ρ W v o e.time ∧ CarriesRow o a := by
      intro h
      obtain ⟨j, e, o, hj, hje, hp, hc⟩ := ih r a h
      exact ⟨j, e, o, Nat.lt_succ_of_lt hj, hje, hp, hc⟩
    obtain ⟨hn, hstep⟩ := hW n
    cases hev : ρ.events[n]? with
    | none =>
      have hlen : ρ.events.length ≤ n := List.getElem?_eq_none_iff.mp hev
      rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
      have hsame : W (n + 1) = W n := hstep
      rw [hsame] at ha
      exact lift ha
    | some e =>
      by_cases hv : v = e.node
      · cases e with
        | wake u t' =>
          change v = u at hv
          subst hv
          have hl : (ρ.events.drop n).take (n + 1 - n) = [Record.Event.wake v t'] := by
            rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hev]
            rfl
          rw [hl, List.foldlM_cons, Set.bind_def] at hstep
          obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp hstep
          obtain rfl := Set.mem_singleton_iff.mp h2
          have hw : W (n + 1) = Function.update (W n) v (M.wake (W n v)) := hw'
          rw [hw, Function.update_self, (facts.nd.wake_st_record _).1] at ha
          exact lift ha
        | tick u t' =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S ρ hev (W n) hn
              (W (n + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
          · rw [hw] at ha
            rcases htick S v (W n v) t' r out hout ha with h | ⟨o, ho, hc⟩
            · exact lift h
            · exact ⟨n, .tick v t', o, Nat.lt_succ_self n, hev,
                Or.inl ⟨n, hev, out, hout, hw, ho⟩, hc⟩
          · rw [hw] at ha
            exact lift ha
        | deliver u o' t' =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S ρ hev (W n) hn
              (W (n + 1)) hstep with hproc | ⟨-, hw⟩
          · rcases facts.stoRun.process_sg_pool_mem S (W n v) o' r (W (n + 1) v) hproc ha with
              h | hc
            · exact lift h
            · exact ⟨n, .deliver v o' t', o', Nat.lt_succ_self n, hev, Or.inr ⟨n, hev⟩, hc⟩
          · rw [hw] at ha
            exact lift ha
      · have hw := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S ρ hev v hv (W n) hn
          (W (n + 1)) hstep
        rw [hw] at ha
        exact lift ha

end

end DecoupledConsensusModel.Sts.Restated
