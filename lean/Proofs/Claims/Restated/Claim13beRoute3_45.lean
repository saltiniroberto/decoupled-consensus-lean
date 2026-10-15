import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.Claim13beRoute3_29
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_FinalityCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_JustificationCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_NamedNjGap
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Views_VoteSetValidityCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryCapturedActionCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_CommitteePools
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_ReceiptCallsF1
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecoveryTimeout
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FinalityGadget_Crossing
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_FinalityPairCore
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_RecordFresh
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Certificates
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_45

/-!
# Run facts read along the path of the admissibility bundle

Facts about a run read along a path `W` of the run, most of them along the path the bundle
`AdmissibleFieldsOn` is read along: the event order and the worlds before an instant, run blocks and
root injectivity, finality and justification of stores, vote sets and the Goldfish cone, the round's
action read, relays of SG votes, and what a tick emits and writes. Stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel DecoupledConsensusModel.Execution

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₄₅ (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (Restated.strictEventIndex rho t) := by
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
    `strictEventIndex rho t` is a world strictly before the instant `t`. -/
private theorem mem_stateBeforeTime_along₄₅ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (Restated.strictEventIndex rho t) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₄₅ S rho hsorted]
  exact (hW _).1

/-- In a named store whose bodies contain genesis and the parent of each body, every named ancestor
    of a held body is held. -/
private theorem namedAncestor_mem₄₅ {st : M.NS}
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

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₄₅ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- Every outcome of the early confirmation votes of `st` at slot `s` is a subset of its late
    confirmation votes. -/
private theorem confEarly_subset_late₄₅ (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₄₅ _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- Every outcome of the counted confirmation votes of `st` at slot `s` is a subset of its late
    confirmation votes. -/
private theorem confVotes_subset_late₄₅ (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ cv, Restated.Vocabulary.Protocol.confVotes M E st s ⇢ cv →
      cv ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro cv hcv
  obtain ⟨e, he, rfl⟩ := returns_map_elim₄₅ _ _ _ hcv
  exact fun _ hu => confEarly_subset_late₄₅ facts E st s e he (Finset.mem_filter.mp hu).1

/-- For every outcome `cv` of the counted confirmation votes of `st` at slot `s`, no validator
    equivocates among the votes of `cv`. -/
private theorem confVotes_no_equivocation₄₅ (facts : Record.Facts M) (E : Env V) (st : M.S)
    (s : Slot) (cv : Finset (GoldfishVote V))
    (hcv : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ cv) (x : V) :
    M.equivocates cv x = false := by
  apply facts.sch.equivocates_eq_false_of_card_le_one
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  rw [facts.sch.mem_votes_by_iff] at ha hb
  obtain ⟨e, he, rfl⟩ := returns_map_elim₄₅ _ _ _ hcv
  have hb2 := (Finset.mem_filter.mp hb.1).2
  rcases (facts.fc.no_second_vote_in_eq_true_iff _ b).mp hb2 a
      (confVotes_subset_late₄₅ facts E st s _ hcv ha.1) with h | h
  · exact h
  · exact absurd (ha.2.trans hb.2.symm) h

/-- If `receiver` processes `o` at the `i`-th event of `rho` along the path `W`, and that event is
    `receiver`'s at time `t`, then `receiver` processes `o` at `t` along `W`. -/
private theorem direct_index_processes_at₄₅ (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    {i : Nat} {receiver : V} {o : NamedObject V} {t : Time}
    (hcall : Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W i receiver o)
    (htimed : ∃ e : Record.Event V, rho.events[i]? = some e ∧ e.node = receiver ∧ e.time = t) :
    Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver o t := by
  obtain ⟨e, he, _, ht⟩ := htimed
  rcases hcall with ⟨time, hi, hem⟩ | ⟨time, hi⟩
  · have heq : Record.Event.tick receiver time = e := Option.some.inj (hi.symm.trans he)
    have htime : time = t := by
      simpa only [Record.Event.time] using (congrArg Record.Event.time heq).trans ht
    subst time
    exact Or.inl ⟨i, hi, hem⟩
  · have heq : Record.Event.deliver receiver o time = e := Option.some.inj (hi.symm.trans he)
    have htime : time = t := by
      simpa only [Record.Event.time] using (congrArg Record.Event.time heq).trans ht
    subst time
    exact Or.inr ⟨i, hi⟩

/-- If the `i`-th event of `rho`, read along the path `W`, is a call of `receiver` on the block `B`,
    and that event is `receiver`'s at time `t`, then `receiver` processes `B` at `t` along `W`. -/
private theorem block_call_processes_at₄₅ (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    {i : Nat} {receiver : V} {B : NamedBlock V} {before : M.NS} {t : Time}
    (hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i receiver B before)
    (htimed : ∃ e : Record.Event V, rho.events[i]? = some e ∧ e.node = receiver ∧ e.time = t) :
    Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver (.block B) t := by
  apply direct_index_processes_at₄₅ S rho W ?_ htimed
  rcases hcall with ⟨time, hi, _⟩ | ⟨time, hi, hem, _⟩
  · exact Or.inr ⟨time, hi⟩
  · exact Or.inl ⟨time, hi, hem⟩

/-- Every node state the round-`r` action read computed from the node state `before` can yield holds
    the bodies `before` holds. -/
private theorem actionReadFrom_bodies₄₅ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- Every node state the round-`r` action read computed from the node state `before` can yield has
    the chain-state map of `before`'s store. -/
private theorem actionReadFrom_σ₄₅ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.core.σ = before.st.core.σ := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_σ _ _ _ _ _ X hX, facts.hd.ModelProperties_setClock_core_σ]

/-- For every node state `nr` that `v`'s round-`r` action read can yield, the live confirmation of
    `nr`'s store is in that store's filtered tree. -/
private theorem liveConfirmed_mem_filtered_of₄₅ (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
    nr.st.core.live_confirmed ∈ M.get_filtered_block_tree (M.toHealing nr.st.core).toFG := by
  rintro _ ⟨w, hw, c, -, st, hst, rfl⟩
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ X hX]
  have hroot : M.get_fg_root (M.toHealing (M.ns_setClock S.E (w v).st
        (Restated.Vocabulary.Execution.Setup.a M S r)).core).toFG ∈
      M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E (w v).st
        (Restated.Vocabulary.Execution.Setup.a M S r)).core).toFG := by
    rw [facts.hd.setClock_core_eq_store_with_t_s]
    have h1 := facts.fc.get_filtered_block_tree_toHealing_clock (w v).st.core
      (Restated.Vocabulary.Execution.Setup.a M S r)
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r))
    have h2 := facts.fc.get_fg_root_toHealing_clock (w v).st.core
      (Restated.Vocabulary.Execution.Setup.a M S r)
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r))
    simp only [Record.Model.S.toHealing] at h1 h2
    rw [h1, h2]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v w hw
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core)
    (M.round_of S.hc (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core.s)
  exact facts.dt.update_confirmation_with_live_confirmed_mem_filtered _ _ _ _ _ hroot R hR
    (facts.fc.get_sg_root_with_gradeContract_mem_filtered _ S.E S.hc _ _ hroot R hR) X hX

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₄₅ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_reach_le₄₅ {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {m n : Nat} (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₄₅ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
/-- When the event at index `i` of `rho` is `e`, the events from index `i` to index `i` of `rho` are
    the list `[e]`. -/
private theorem drop_take_succ₄₅ {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

/-- The worlds the one-event list `[e]` leads to from `w` are the worlds
    `Record.worldStepOf M S w e`. -/
private theorem mem_foldlM_singleton₄₅ (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, if the `i`-th event is `v`'s tick at `t`, the number of events with a
    time before `t` is at most `i`. -/
private theorem strict_le_tick₄₅ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (Record.Event.tick v t)) :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤ i := by
  by_contra hnot
  have hlt : i < (rho.events.filter (fun e => decide (e.time < t))).length := Nat.lt_of_not_ge hnot
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hmem : Record.Event.tick v t ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
  have hp := (List.mem_filter.mp hmem).2
  simp only [decide_eq_true_eq, Record.Event.time] at hp
  exact lt_irrefl _ hp

/-- When the `i`-th event of `rho` is a wake of `v`, `v`'s store in every world that event leads to
    from `w₁` is `v`'s store in `w₁`. -/
private theorem stateBefore_wake_st₄₅ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
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

/-- For every path `W` of `rho`, in every world `W i` the slot of `v`'s store is the slot of its
    clock. -/
private theorem slot_clock_along₄₅ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V) :
    ∀ i : Nat, (W i v).st.core.s = S.E.slotOf (W i v).st.core.t := by
  intro i
  induction i with
  | zero =>
    have h0 : W 0 = fun u => M.initial S u := (hW 0).1
    rw [h0]
    show (M.initial S v).st.core.s = S.E.slotOf (M.initial S v).st.core.t
    rw [facts.nd.initial_st, facts.hd.initial_core_s, facts.hd.initial_core_t,
      _root_.DecoupledConsensusModel.Proofs.ModelProperties.slotOf_zero]
  | succ n ih =>
    obtain ⟨hn, hstep⟩ := hW n
    cases hev : rho.events[n]? with
    | none =>
      have hlen : rho.events.length ≤ n := List.getElem?_eq_none_iff.mp hev
      rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
      have hsame : W (n + 1) = W n := hstep
      rw [hsame]
      exact ih
    | some e =>
      by_cases hv : v = e.node
      · cases e with
        | wake u t =>
          change v = u at hv
          subst hv
          rw [stateBefore_wake_st₄₅ facts S rho hev (W n) (W (n + 1)) hstep]
          exact ih
        | tick u t =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho hev (W n) hn
              (W (n + 1)) hstep with ⟨out, hout, hw⟩ | ⟨-, hw⟩
          · rw [hw, (facts.nd.tick_clock S v (W n v) t out hout).1,
              (facts.nd.tick_clock S v (W n v) t out hout).2]
          · rw [hw]
            exact ih
        | deliver u o t =>
          change v = u at hv
          subst hv
          rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hev (W n) hn
              (W (n + 1)) hstep with hproc | ⟨-, hw⟩
          · rw [(facts.nd.process_clock S (W n v) o (W (n + 1) v) hproc).1,
              (facts.nd.process_clock S (W n v) o (W (n + 1) v) hproc).2]
            exact ih
          · rw [hw]
            exact ih
      · rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho hev v hv (W n) hn
          (W (n + 1)) hstep]
        exact ih

/-- If the slot of `st` is the slot of its clock, and the clock is at or after the opening of round
    `q` and before the opening of round `r`, then the round of `st`'s slot is at least `q` and less
    than `r`. -/
private theorem round_bounds_of_clock₄₅ (facts : Record.Facts M) (S : Setup V) (q r : Round)
    (st : M.NS) (hclock : st.core.s = S.E.slotOf st.core.t)
    (hlo : M.opening S.E S.hc q ≤ st.core.t) (hhi : st.core.t < M.opening S.E S.hc r) :
    q ≤ M.round_of S.hc st.core.s ∧ M.round_of S.hc st.core.s < r := by
  rw [facts.gr.opening_eq_proposal_time] at hlo hhi
  have hslot : M.opening_slot S.hc q ≤ st.core.s := by
    rw [hclock]
    exact facts.sch.slot_le_slotOf_of_proposal_time_le S.E hlo
  refine ⟨?_, ?_⟩
  · have h := facts.gr.le_round_of_sub_two S.hc (Nat.add_le_add_right hslot 2)
    rwa [Nat.add_sub_cancel] at h
  · by_contra hn
    have hr : r ≤ M.round_of S.hc st.core.s := Nat.le_of_not_gt hn
    have hro : M.opening_slot S.hc r ≤ st.core.s := facts.gr.opening_slot_le_of_le_round_of S.hc hr
    have ht0 : 0 ≤ st.core.t := (facts.sch.Sts_proposal_time_nonneg S _).trans hlo
    have hTslot : M.proposal_time S.E st.core.s ≤ st.core.t := by
      rw [hclock]
      exact facts.sch.proposal_time_slotOf_le S.E ht0
    exact (not_lt_of_ge ((facts.sch.proposal_time_mono S.E hro).trans hTslot)) hhi

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along: if every body a member of `X`
    holds in `W n` has the `nj` bit at height `blocked`, and `v ∈ X` holds in `W n` what it holds in
    `W (strictEventIndex rho (a r))`, then for every node state `nr` the round-`r` action read
    computed from that world can yield, an outcome `some Q` of `nr`'s selected source with `Q` at
    height `blocked` has the `nj` bit there. -/
theorem actionSource_nj_of_honestPrefixNJUniverseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {n : Nat} {blocked : Height}
    (huniverse : Restated.HonestPrefixNJUniverseOn M S rho W X n blocked)
    {v : V} (hv : v ∈ X) {r : Round}
    (hstate : W n v = W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v)
    (nr : M.N)
    (hnr : nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {Q : Block V}
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ some Q)
    (hheight : (nr.st.σ Q).h = blocked) :
    (nr.st.σ Q).nj = true := by
  have hW := _hf.onePath
  have hwk : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S r) := by
    rw [stateBeforeTime_eq_strict₄₅ S rho _hf.sorted]
    exact (hW _).1
  have hmem : nr ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨_, hwk, hnr⟩
  obtain ⟨C, hC, hErase, hderive, -⟩ :=
    Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho v r nr hmem Q hsource
  have hCprefix : C ∈ (W n v).st.bodies := by
    rw [hstate, ← actionReadFrom_bodies₄₅ facts S _ r nr hnr]
    exact hC
  have hheight' : (M.derive_named S.E S.cfg C).h = blocked := by
    rw [← hderive]
    exact hheight
  have hnj := (huniverse v hv C hCprefix).1 hheight'
  show (nr.st.core.σ Q).nj = true
  rw [hderive]
  exact hnj

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, under the same `nj` universe of
    `X` and prefix equation as `actionSource_nj_of_honestPrefixNJUniverseOn`: for every node state
    `nr` the round-`r` action read computed from `v`'s node state in
    `W (strictEventIndex rho (a r))` can yield and every outcome `H` of `nr`'s action head, `H` has
    justified height other than `blocked` in `nr`'s store. -/
theorem actionHead_h_j_ne_of_honestPrefixNJUniverseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {n : Nat} {blocked : Height}
    (huniverse : Restated.HonestPrefixNJUniverseOn M S rho W X n blocked)
    {v : V} (hv : v ∈ X) {r : Round}
    (hstate : W n v = W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ H, Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract nr.cache)
        S.E S.hc (M.toHealing nr.st.core) ⇢ H →
      (nr.st.core.σ H).h_j ≠ blocked := by
  intro nr hnr H hH
  have hW := _hf.onePath
  have hwk : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S r) := by
    rw [stateBeforeTime_eq_strict₄₅ S rho _hf.sorted]
    exact (hW _).1
  have hhead := Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith_mem_storeBeforeTime facts
    (rho := rho) S v r _ hwk nr hnr H hH
  obtain ⟨D, hDtime, hErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v _ hwk hhead
  have hDprefix : D ∈ (W n v).st.bodies := by
    rw [hstate]
    exact hDtime
  have hderivedNe := (huniverse v hv D hDprefix).2
  have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v _ hwk D hDtime
  have hσ : nr.st.core.σ =
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.σ :=
    actionReadFrom_σ₄₅ facts S _ r nr hnr
  rw [hσ, ← hErase, hview]
  exact hderivedNe

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, under the `nj` universe of `X`
    and the prefix equation: for every node state `nr` the round-`r` action read can yield, if
    `some Q` is an outcome of `nr`'s selected source, `Q` is at height `blocked` in `nr`'s store and
    `nr`'s record is fresh at `blocked`, then for every outcome `D` of the action duty computed from
    `nr`, the attestation of `D` carries the vote at `blocked` for `Q`'s target root with the
    timeout bit. -/
theorem actionAttestationAt_height_pair_timeout_of_honestPrefixNJUniverseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {n : Nat} {blocked : Height}
    (huniverse : Restated.HonestPrefixNJUniverseOn M S rho W X n blocked)
    {v : V} (hv : v ∈ X) {r : Round}
    (hstate : W n v = W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v)
    (nr : M.N)
    (hnr : nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {Q : Block V}
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ some Q)
    (hheight : (nr.st.σ Q).h = blocked)
    (hfresh : Restated.Vocabulary.Proofs.HealingSurface.RecordFreshAt M nr.record.legacy blocked) :
    ∀ D, M.duties_attest_with (M.gradeContract nr.cache) S.E S.hc (S.node v) nr.st nr.record ⇢ D →
      D.2.2.height_pair = NamedHeightPair.vote blocked (nr.st.σ Q).T_h.root true := by
  intro D hD
  have hnj := Restated.actionSource_nj_of_honestPrefixNJUniverseOn facts
    S Hs Xb X hf huniverse hv hstate nr hnr hsource hheight
  have hheadj := Restated.actionHead_h_j_ne_of_honestPrefixNJUniverseOn facts
    S Hs Xb X hf huniverse hv hstate nr hnr
  let gc := M.gradeContract nr.cache
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty gc S.E S.hc (S.node v)
    (M.toHealing nr.st.core) nr.record
  have hres : ∀ u, ∃ b, M.resolved (M.toHealing nr.st.core).T u ⇢ b :=
    fun u => facts.sto.resolved_nonempty _ u
  choose res hres using hres
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_with_nonempty gc S.E S.hc (M.toHealing nr.st.core)
    ((M.toHealing nr.st.core).toFG.toSG.toGoldfishStore.pool (M.toHealing nr.st.core).s)
    (((M.toHealing nr.st.core).toFG.toSG.toGoldfishStore.pool (M.toHealing nr.st.core).s).filter
      (fun u => res u = true))
    (M.toHealing nr.st.core).s
  have hHd' : Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M gc S.E S.hc
      (M.toHealing nr.st.core) ⇢ Hd := ⟨res, hres, hHd⟩
  rw [facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA]
  have hσ : (M.toHealing nr.st.core).σ = nr.st.core.σ := facts.sto.ModelProperties_toHealing_σ _
  have h := Restated.Vocabulary.Proofs.HealingSurface.round_action_height_pair_timeout_of_fresh_source
    facts gc S.E S.hc (S.node v) (M.toHealing nr.st.core) nr.record A hA hsource
    (by rw [hσ]; exact hheight) (by rw [hσ]; exact hnj) hfresh hHd'
    (by rw [hσ]; exact hheadj Hd hHd')
  rw [hσ] at h
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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Along any path `W` of the run: if every member of slot `s`'s committee in the set for the vote
    instant voted for `B`, a run block read through `Xb` that the cone `tgt` admits, then the cone
    holds at `s`. -/
theorem honestVotesCone_of_nameOn (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (s : Slot) {B : NamedBlock V}
    {tgt : Block V → Prop} (htgt : tgt B.erase) (hB : Restated.RunBlockOn M S ρ W Xb B)
    (h : Restated.NamedHonestVotesNameOn M S ρ W Hs s B.erase) :
    Restated.NamedHonestVotesConeOn M S ρ W Hs Xb s tgt :=
  fun x hx hxc => ⟨B, htgt, hB, h x hx hxc⟩

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

/-- Along any path `W` of the run: if every member of slot `s`'s committee in the set for the vote
    instant voted for the run block `B`, the cone of the descendants of `B` holds at `s`. -/
theorem honestVotesCone_preceqOn (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (s : Slot) {B : NamedBlock V}
    (hB : Restated.RunBlockOn M S ρ W Xb B) (h : Restated.NamedHonestVotesNameOn M S ρ W Hs s B.erase) :
    Restated.NamedHonestVotesConeOn M S ρ W Hs Xb s (fun X => Block.Preceq B.erase X) :=
  Restated.honestVotesCone_of_nameOn facts S ρ W Hs Xb s
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self B.erase)) hB h

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

/-- For every path `W`, if every head picked along `W` from slot `s`'s committee in the set for its
    confirmation instant is in `T`, `T` is root-injective, and every such head is stamped before the
    support cutoff, then the heads resolve in `T`. -/
theorem headsResolveIn_ofOn (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V)
    (s : Slot)
    {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    (hmem : ∀ X : Block V, Restated.HonestHeadOn M S ρ W Hs Xb s X → X ∈ T)
    (hinj : ∀ X Y : Block V, X ∈ T → Y ∈ T → X.root = Y.root → X = Y)
    (harr : ∀ X : Block V, Restated.HonestHeadOn M S ρ W Hs Xb s X →
      stampedBefore tb (M.support_cutoff S.E s) X = true) :
    Restated.HeadsResolveInOn M S ρ W Hs Xb s T tb :=
  fun X hX =>
    ⟨find?_eq_some_of_unique (hmem X hX)
      (fun Y hY hroot => hinj Y X hY (hmem X hX) hroot), harr X hX⟩

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

/-- For every path `W`, every store `st` that `v`'s confirmation read at slot `s` can yield and
    every outcome `cv` of `st`'s counted votes at `s`: if more than half of each committee is in the
    set for its confirmation instant, the family shrinks as time grows, the cone holds at `s` along
    `W`, every vote of a member of the set for `s`'s confirmation instant emitted along `W` whose
    head arrived in `st` before the support cutoff is in `cv`, and the heads picked along `W`
    resolve in `st`, then `cv` gives cone support at `s` over the set for `s`'s confirmation
    instant. -/
theorem coneSupport_confVotesOn (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot}
    {tgt : Block V → Prop} (hnames : Restated.NamedHonestVotesConeOn M S ρ W Hs Xb s tgt)
    (v : V) :
    ∀ st ∈ Restated.Vocabulary.Proofs.Optimistic.confStore M S ρ v s,
    ∀ cv, Restated.Vocabulary.Protocol.confVotes M S.E st s ⇢ cv →
    (∀ u : GoldfishVote V, u.slot = s →
      u.val_index ∈ Hs (M.confirmation_time S.E s) →
      (Restated.Vocabulary.Execution.Run.emits M S ρ W u.val_index (Object.gfVote u) (M.vote_time S.E s)) →
      HeadArrivesBefore st.T st.timestamp_block (M.support_cutoff S.E s) u →
      u ∈ cv) →
    Restated.HeadsResolveInOn M S ρ W Hs Xb s st.T st.timestamp_block →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T cv cv
      (Restated.Vocabulary.Protocol.confLate M S.E st s) s (Hs (M.confirmation_time S.E s)) tgt := by
  intro st _ cv hcv hcount hres
  refine Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts (hcom s)
    (confVotes_subset_late₄₅ facts S.E st s cv hcv) (subset_refl _)
    (fun y _ _ => confVotes_no_equivocation₄₅ facts S.E st s cv hcv y) ?_
  intro y hy hyH
  have hyV : y ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hyH
  obtain ⟨X, htgt, hrun, hemit⟩ := hnames y hyV hy
  obtain ⟨hfind, hstamp⟩ := hres X.erase ⟨y, hyH, hy, ⟨X, rfl, hrun⟩, hemit⟩
  let u : GoldfishVote V := ⟨y, s, X.erase.root⟩
  have hu : u ∈ cv := hcount u rfl hyH hemit ⟨X.erase, hfind, hstamp⟩
  obtain ⟨e, he, hce⟩ := returns_map_elim₄₅ _ _ _ hcv
  obtain ⟨τ, hτ, hτe⟩ := returns_map_elim₄₅ _ _ _ he
  have huEarly : u ∈ beforeCutoff τ (M.support_cutoff S.E s) (st.pool s) := by
    rw [hτe]
    rw [← hce, Finset.mem_filter] at hu
    exact hu.1
  rw [mem_beforeCutoff_iff] at huEarly
  have hXslot : X.erase.slot ≤ u.slot :=
    facts.sto.head_slot_le_of_tau _ hfind τ hτ huEarly.2
  exact ⟨X.erase, htgt, hXslot, hu, hfind⟩

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

/-- With `st` the store `w` holds in `W (strictEventIndex rho read)`, `W` the path the bundle
    `AdmissibleFieldsOn` is read along: if `st` holds `D`, `D`'s derived height is at least `H`, `D`
    is a descendant of `st`'s finality-gadget root and `D` is not in `st`'s filtered tree, then
    `st`'s `h_max` is at least `H + 2`. -/
theorem filteredOut_hMax_of_root_preceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {read : Time} (_hw : w ∈ Hs read) {H : Height} {D : NamedBlock V} :
    D ∈ (W (strictEventIndex rho read) w).st.bodies →
    H ≤ (M.derive_named S.E S.cfg D).h →
    Block.Preceq (M.get_fg_root (W (strictEventIndex rho read) w).st.toHealing.toFG) D.erase →
    D.erase ∉ M.get_filtered_block_tree (W (strictEventIndex rho read) w).st.toHealing.toFG →
    H + 2 ≤ (W (strictEventIndex rho read) w).st.h_max := by
  have hw₁ := mem_stateBeforeTime_along₄₅ _hf.sorted _hf.onePath read
  generalize W (strictEventIndex rho read) = w₁ at hw₁ ⊢
  intro hDmem' hheight hrootP' hnotFiltered'
  set st : M.NS := (w₁ w).st with hst
  by_contra hnotProgress
  have hlt : st.h_max < H + 2 := Nat.lt_of_not_ge hnotProgress
  have hcap : st.h_max ≤ H + 1 :=
    Nat.lt_succ_iff.mp (by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hlt)
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho read w w₁ hw₁).1.1.1
  have hPmem' : D.erase ∈ st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hDmem'
  have hlocalHeight : H ≤ (st.core.σ D.erase).h := by
    rw [show st.core.σ D.erase = M.derive_named S.E S.cfg D from
      Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho read w w₁ hw₁
        D hDmem']
    exact hheight
  have hFJ : Block.Preceq st.core.F st.core.J :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts S rho
      read w w₁ hw₁
  have hFroot : Block.Preceq st.core.F (M.get_fg_root (M.toHealing st.core).toFG) := by
    rcases facts.fc.get_fg_root_eq_J_or_F st.core with h | h
    · rw [h]
      exact hFJ
    · rw [h]
      exact Proofs.ModelProperties.Preceq_self _
  have hFP : Block.Preceq st.core.F D.erase := preceq_trans_Preceq hFroot hrootP'
  have hbound : st.h_max ≤ (st.core.σ D.erase).h + 1 :=
    hcap.trans (Nat.add_le_add_right hlocalHeight 1)
  have hfrontier : st.h_max - 1 ≤ (st.core.σ D.erase).h :=
    Nat.sub_le_iff_le_add.mpr hbound
  have hfiltered :
      D.erase ∈ M.get_filtered_block_tree st.toHealing.toFG := by
    refine facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing st.core) (W := D.erase) ?_ ?_ ?_
      (Proofs.ModelProperties.Preceq_self _) ?_ hrootP'
    · rw [facts.sto.toHealing_T]
      exact hPmem'
    · rw [facts.sto.ModelProperties_toHealing_F]
      exact hFP
    · rw [facts.sto.toHealing_T]
      exact hPmem'
    · rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
      exact hfrontier
  exact hnotFiltered' hfiltered

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

/-- With `st` the store `w` holds in `W (strictEventIndex rho read)`, `W` the path the bundle
    `AdmissibleFieldsOn` is read along: if `st` holds `D` of derived height at least `H` and the
    height filter interferes with `D` in `st`, then `st`'s `h_max` is at least `H + 2`. -/
theorem heightFilterInterference_hMaxOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {read : Time} (_hw : w ∈ Hs read) {H : Height} {D : NamedBlock V} :
    D ∈ (W (strictEventIndex rho read) w).st.bodies →
    H ≤ (M.derive_named S.E S.cfg D).h →
    Restated.Vocabulary.Proofs.HealingSurface.HeightFilterInterferenceAt M
      (W (strictEventIndex rho read) w).st D.erase →
    H + 2 ≤ (W (strictEventIndex rho read) w).st.h_max := by
  intro hDmem hheight hint
  exact Restated.filteredOut_hMax_of_root_preceqOn facts S Hs Xb hf _hw hDmem hheight
    (prec_iff_ne_Preceq.mp hint.1).2 hint.2

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

/-- For every node state `nr` that the round-`r` action read computed from `v`'s node state in
    `W (strictEventIndex rho (a r))` can yield, `W` the path the bundle `AdmissibleFieldsOn` is read
    along, the live confirmation of `nr`'s store is in that store's filtered tree. -/
theorem liveConfirmed_mem_filtered_actionStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    nr.st.core.live_confirmed ∈ M.get_filtered_block_tree (M.toHealing nr.st.core).toFG :=
  fun nr hnr => liveConfirmed_mem_filtered_of₄₅ facts S rho v r nr
    ⟨_, mem_stateBeforeTime_along₄₅ _hf.sorted _hf.onePath _, hnr⟩

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

/-- For every path `W` and every outcome `cv` of `st`'s counted votes at `s`: if more than half of
    each committee is in the set for its confirmation instant, the family shrinks as time grows,
    every member of slot `s`'s committee in the set for the vote instant voted along `W` for `B`,
    `B` is found by its root in `st`, and every such vote of a member of the set for the
    confirmation instant emitted along `W` is in `cv`, then `cv` gives honest support for `B` at `s`
    in `st`'s tree over the set for `s`'s confirmation instant. -/
theorem honestSupport_of_namesOn (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (s : Slot)
    (B : Block V)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hvt : Restated.NamedHonestVotesNameOn M S ρ W Hs s B)
    {st : M.S} (hfind : Block.find? st.T B.root = some B)
    (cv : Finset (GoldfishVote V)) (hcv : Restated.Vocabulary.Protocol.confVotes M S.E st s ⇢ cv)
    (hcount : ∀ u : GoldfishVote V, u.slot = s →
      u.val_index ∈ Hs (M.confirmation_time S.E s) →
      u.val_index ∈ S.E.committee s →
      (Restated.Vocabulary.Execution.Run.emits M S ρ W u.val_index (Object.gfVote u) (M.vote_time S.E s)) →
      u ∈ cv) :
    HonestSupport S.E st.T cv s (Hs (M.confirmation_time S.E s)) B where
  majority := hcom s
  vote := by
    intro x hx hxH
    let u : GoldfishVote V := ⟨x, s, B.root⟩
    have hxV : x ∈ Hs (M.vote_time S.E s) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hxH
    have hu : u ∈ cv := hcount u rfl hxH hx (hvt x hxV hx)
    obtain ⟨e, he, hce⟩ := returns_map_elim₄₅ _ _ _ hcv
    obtain ⟨τ, hτ, hτe⟩ := returns_map_elim₄₅ _ _ _ he
    have huEarly : u ∈ beforeCutoff τ (M.support_cutoff S.E s) (st.pool s) := by
      rw [hτe]
      rw [← hce, Finset.mem_filter] at hu
      exact hu.1
    rw [mem_beforeCutoff_iff] at huEarly
    have hBslot : B.slot ≤ u.slot :=
      facts.sto.head_slot_le_of_tau _ hfind τ hτ huEarly.2
    exact ⟨u, hu, rfl, rfl, hfind, hBslot⟩

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

/-- For every path `W` and every world `wd`: if every member of slot `s`'s committee in the set for
    the vote instant has, at every vote read staged from its node state in `wd`, a vote store
    extending to `B`, and emits along `W` the vote the duty computes, then every such member voted
    along `W` for `B`. -/
theorem honestVotesName_of_extendsOn (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V)
    (s : Slot) (B : NamedBlock V) {wd : V → M.N}
    (hvt : Restated.VoteTickExtendsOn M S ρ W Hs s wd B) :
    Restated.NamedHonestVotesNameOn M S ρ W Hs s B.erase := by
  intro v hv hcom
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (wd v).st.core.toHealing
    (M.vote_time S.E s) (wd v).cache
  set n := M.mkNode (M.ns_setClock S.E (wd v).st (M.vote_time S.E s)) (wd v).record c with hn
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) n.st
  obtain ⟨tree₀, H, u, hslot, hal, hduty, hemit⟩ := hvt v hv hcom c hc D hD
  have hnode : (S.node v).val_index = v := S.node_val_index v
  have hcomx : (S.node v).val_index ∈ S.E.committee n.st.core.s := by
    rw [hnode, hslot]; exact hcom
  have hue : D.2 = some ⟨(S.node v).val_index, n.st.core.s, B.erase.root⟩ := by
    obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
    obtain ⟨Wv, hWv⟩ := facts.fc.voter_view_nonempty S.E
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
    obtain ⟨U, hU⟩ := facts.fc.voter_support_view_nonempty S.E
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
    obtain ⟨X, hX⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
      S.hc (M.toHealing n.st.core) T Wv U (n.st.core.s - 1)
    rw [facts.fc.goldfish_vote_with_snd_of_mem_committee _ _ _ _ _ hcomx D hD T hT Wv hWv U hU X hX,
      hal.head T hT Wv hWv U hU X hX]
  rw [hduty, Option.some.injEq] at hue
  rw [hue, hnode, hslot] at hemit
  exact hemit

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

/-- With `w₁ = W (strictEventIndex rho read)`, `W` the path the bundle `AdmissibleFieldsOn` is read
    along: if `P ⪯ B` and the finality filter leaves `B` in place in `w`'s store in `w₁`, it leaves
    `P` in place there too. -/
theorem ancestorOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {read : Time} {P B : Block V}
    (hPB : Block.Preceq P B)
    (hBquiet : Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w read
      (W (strictEventIndex rho read)) B) :
    Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w read
      (W (strictEventIndex rho read)) P := by
  have hw₁ := mem_stateBeforeTime_along₄₅ _hf.sorted _hf.onePath read
  generalize W (strictEventIndex rho read) = w₁ at hw₁ hBquiet ⊢
  set st : M.NS := (w₁ w).st with hst
  rcases hBquiet with hBroot | hBfiltered
  · exact Or.inl (preceq_trans_Preceq hPB hBroot)
  · have hrootB : Block.Preceq
        (M.get_fg_root (M.toHealing st.core).toFG) B := by
      exact preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hBfiltered)
    rcases preceq_linear_Preceq hrootB hPB with hrootP | hProot
    · right
      have hpc : Restated.Vocabulary.Internal.ParentClosed M st.core :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho read w w₁ hw₁
      have hBT : B ∈ st.core.T := by
        have h := facts.fc.get_filtered_block_tree_subset (M.toHealing st.core).toFG hBfiltered
        rw [facts.sto.toHealing_gs_T] at h
        exact h
      have hpc' : ∀ X ∈ st.core.T, X.parent? = none ∨ X.parent ∈ st.core.T := by
        unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
        have h := hpc.2
        rw [facts.sto.toHealing_gs_T] at h
        exact h
      have hPT : P ∈ st.core.T :=
        Proofs.Records.mem_of_preceq hpc' P B hBT (preceq_eq_true_iff_Preceq.mpr hPB)
      have hFJ : Block.Preceq st.core.F st.core.J :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts S rho
          read w w₁ hw₁
      exact facts.fc.mem_filtered_of_preceq
          (st := (M.toHealing st.core).toFG)
          (by rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]; exact preceq_eq_true_iff_Preceq.mpr hFJ)
          hBfiltered (by rw [facts.sto.toHealing_gs_T]; exact hPT)
          (preceq_eq_true_iff_Preceq.mpr hPB)
          (preceq_eq_true_iff_Preceq.mpr hrootP)
    · exact Or.inl hProot

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

/-- Along any path `W` of the run: if no two run blocks read through `Xb` have distinct blocks with
    one root on their chains, then for two such run blocks `A` and `B`, two erased ancestors of `A`
    or `B` with one root are equal. -/
theorem rootInjectiveOnAncestors_of_collisionFreeOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V)
    (hroot : Restated.RootCollisionFreeOn M S rho W Xb)
    (A B : NamedBlock V) (hA : Restated.blockInRunOn M S rho W Xb A)
    (hB : Restated.blockInRunOn M S rho W Xb B) :
    Execution.RootInjectiveOnAncestors A.erase B.erase := by
  refine rootInjectiveOnAncestors_intro ?_
  intro X Y Z W hZmem hXZ hWmem hYW hroots
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZmem hWmem
  rcases hZmem with hZmem | hZmem <;> subst hZmem <;>
      rcases hWmem with hWmem | hWmem <;> subst hWmem
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inl hX'anc) (Or.inl hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inl hX'anc) (Or.inr hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inr hX'anc) (Or.inl hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inr hX'anc) (Or.inr hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]

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

/-- For every path `W`, if `v ∈ Xb` holds `C` in `W i`, then `C` is a run block read through `Xb`
    along `W`. -/
theorem runBlock_of_stateBefore_memOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (W : Nat → V → M.N) (Xb : Finset V) {v : V}
    (hv : v ∈ Xb) {i : Nat} {C : NamedBlock V}
    (hC : C ∈ (W i v).st.bodies) : Restated.RunBlockOn M S ρ W Xb C :=
  ⟨C, Or.inr ⟨v, hv, i, hC⟩, Proofs.NamedAncestry.named_self C⟩

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

/-- Along a path `W` of the run: if no two run blocks read through `Xb` collide on a root and every
    member of `T` is such a run block, the erasure of `T` is root-injective on ancestors. -/
theorem rootInjectiveBelow_of_runBlocksOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (W : Nat → V → M.N) (Xb : Finset V)
    (hcf : Restated.RootCollisionFreeOn M S ρ W Xb) {T : Finset (NamedBlock V)}
    (hRun : ∀ C ∈ T, Restated.RunBlockOn M S ρ W Xb C) :
    RootInjectiveBelow (T.image NamedBlock.erase) := by
  refine rootInjectiveBelow_intro ?_
  intro A C B D hBT hAB hDT hCD hr
  obtain ⟨B', hB'T, rfl⟩ := Finset.mem_image.mp hBT
  obtain ⟨D', hD'T, rfl⟩ := Finset.mem_image.mp hDT
  obtain ⟨A', hA'B, rfl⟩ := Proofs.NamedAncestry.erased_ancestor_lift B' hAB
  obtain ⟨C', hC'D, rfl⟩ := Proofs.NamedAncestry.erased_ancestor_lift D' hCD
  have hroots : A'.root = C'.root := by
    rwa [Proofs.NamedWire.erase_root, Proofs.NamedWire.erase_root] at hr
  rw [hcf.root_injective B' D' (hRun B' hB'T) (hRun D' hD'T) A' C'
    (Or.inl hA'B) (Or.inr hC'D) hroots]

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

/-- For every path `W`, if no two run blocks read through `Xb` along `W` collide on a root, the
    erasure of the union of the bodies `u ∈ Xb` holds in `W i` and `v ∈ Xb` holds in `W j` is
    root-injective on ancestors. -/
theorem rootInjectiveBelow_stateBefore_unionOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (W : Nat → V → M.N) (Xb : Finset V)
    (hcf : Restated.RootCollisionFreeOn M S ρ W Xb) {u v : V}
    (hu : u ∈ Xb) (hv : v ∈ Xb) (i j : Nat) :
    RootInjectiveBelow (((W i u).st.bodies ∪ (W j v).st.bodies).image NamedBlock.erase) :=
  Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hcf (by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Restated.runBlock_of_stateBefore_memOn facts S W Xb hu hC
    · exact Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hC)

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the clock of `v`'s store in
    `W n` is at most the instant of the event at index `n`. -/
theorem store_time_le_event_timeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {n : Nat} {e : Record.Event V} (he : ρ.events[n]? = some e) (v : V) :
    (W n v).st.t ≤ e.time :=
  Restated.Vocabulary.Protocol.store_time_le_event_time_of_fields facts S hf.sorted hf.in_horizon he v
    (W n) (hf.onePath n).1

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along and every `n`, `v`'s store in
    `W n` carries the pool-stamp bundle. -/
theorem poolStamps_stateBeforeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (v : V) : ∀ n : Nat,
      Restated.Vocabulary.Protocol.PoolStamps M (W n v).st.core := fun n =>
  Restated.Vocabulary.Protocol.poolStamps_stateBefore_of_fields facts S hf.sorted hf.in_horizon v n
    (W n) (hf.onePath n).1

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along and `m ≤ n`, a vote in `v`'s pool
    in `W m` is in `v`'s pool in `W n`, with the stamp it was first given. -/
theorem pool_carryOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo) (v : V)
    {m : Nat} : ∀ n : Nat, m ≤ n →
      Restated.Vocabulary.Protocol.PoolCarry M (W m v).st.core (W n v).st.core := fun n hmn =>
  Restated.Vocabulary.Protocol.pool_carry_of_fields facts S hf.sorted hf.in_horizon v
    (W m) (hf.onePath m).1 n hmn (W n) (onePath_reach_le₄₅ hf.onePath hmn)

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along and `t ≤ u`, `v`'s `h_max` in
    `W (inclusiveEventIndex rho t)` is at most its `h_max` in `W (inclusiveEventIndex rho u)`. -/
theorem stateAt_h_max_monoOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V)
    {t u : Time} (htu : t ≤ u) :
    (W (inclusiveEventIndex rho t) v).st.h_max ≤ (W (inclusiveEventIndex rho u) v).st.h_max :=
  Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v
    (inclusiveEventIndex_mono rho htu) _ (hf.onePath _).1 _
    (onePath_reach_le₄₅ hf.onePath (inclusiveEventIndex_mono rho htu))

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

/-- For every path `W`, if every object, every Goldfish vote included in a block and every
    attestation included in a block processed along `W` at `t` and authored by a member of `Hs t`
    was emitted along `W` by that member by `t`, then an actual handle along `W` at `t` of an object
    authored by `author ∈ Hs t` was emitted along `W` by `author` by `t`. -/
theorem authentic_actual_handles_of_clausesOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V)
    (hDirect : ∀ receiver o t, Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver o t →
      ∀ author ∈ Hs t, o.author = some author →
        ∃ sent, sent ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W author o sent)
    (hCarriedGF : ∀ receiver B t, Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver (.block B) t →
      ∀ u ∈ B.gf_votes, u.val_index ∈ Hs t →
        ∃ sent, sent ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (.gfVote u) sent)
    (hCarriedRow : ∀ receiver B t, Restated.Vocabulary.Execution.NamedRun.processes M S rho W receiver (.block B) t →
      ∀ a ∈ B.attestations, a.val_index ∈ Hs t →
        ∃ sent, sent ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a) sent)
    {i : Nat} {receiver author : V} {o : NamedObject V} {t : Time}
    (h : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i receiver o t)
    (hHon : author ∈ Hs t) (hAuthor : o.author = some author) :
    ∃ sent, sent ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W author o sent := by
  obtain ⟨hcall, htimed⟩ := h
  cases o with
  | block B =>
    exact hDirect receiver (.block B) t
      (direct_index_processes_at₄₅ S rho W hcall htimed) author hHon hAuthor
  | gfVote u =>
    rcases hcall with hdirect | ⟨B, j, before, hcarrier, _, _, hindex⟩
    · exact hDirect receiver (.gfVote u) t
        (direct_index_processes_at₄₅ S rho W hdirect htimed) author hHon hAuthor
    · have hval : u.val_index = author := Option.some.inj ((author_gfVote u).symm.trans hAuthor)
      have hbody := block_call_processes_at₄₅ S rho W hcarrier htimed
      have hmember : u ∈ B.gf_votes := List.mem_of_getElem? hindex
      have hsigner : u.val_index ∈ Hs t := hval.symm ▸ hHon
      simpa only [hval] using hCarriedGF receiver B t hbody u hmember hsigner
  | attest a =>
    rcases hcall with hdirect | ⟨B, j, before, hcarrier, _, _, hindex⟩
    · exact hDirect receiver (.attest a) t
        (direct_index_processes_at₄₅ S rho W hdirect htimed) author hHon hAuthor
    · have hval : a.val_index = author := Option.some.inj ((author_attest a).symm.trans hAuthor)
      have hbody := block_call_processes_at₄₅ S rho W hcarrier htimed
      have hmember : a ∈ B.attestations := List.mem_of_getElem? hindex
      have hsigner : a.val_index ∈ Hs t := hval.symm ▸ hHon
      simpa only [hval] using hCarriedRow receiver B t hbody a hmember hsigner

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, an actual handle along `W` at
    `t` of an object authored by `author ∈ Hs t` was emitted along `W` by `author` by `t`. -/
theorem actual_handles_authenticatedOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {receiver author : V} {o : NamedObject V} {t : Time}
    (h : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i receiver o t)
    (hHon : author ∈ Hs t) (hAuthor : o.author = some author) :
    ∃ sent, sent ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W author o sent :=
  Restated.authentic_actual_handles_of_clausesOn facts S rho W Hs hf.unforgeable
    hf.carried_gf hf.carried_attest h hHon hAuthor

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

/-- Along a path `W` of the run: if `lo ≤ hi`, the cone of the descendants of `B` holds at `lo`, and
    from each `k` in `[lo, hi)` the cone at `k` gives the cone at `k + 1` or `Exit`, then the cone
    holds at `hi` or `Exit` holds. -/
theorem honestVotesCone_or_exit_of_bounded_foldOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V) (Xb : Finset V) {lo hi : Nat}
    {B : Block V}
    {Exit : Prop}
    (hlohi : lo ≤ hi)
    (hbase : Restated.NamedHonestVotesConeOn M S rho W Hs Xb lo
      (fun X => Block.Preceq B X))
    (hstep : ∀ k, lo ≤ k → k < hi →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb k
        (fun X => Block.Preceq B X) →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (k + 1)
        (fun X => Block.Preceq B X) ∨ Exit) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb hi
        (fun X => Block.Preceq B X) ∨ Exit := by
  revert lo
  induction hi with
  | zero =>
      intro lo hlohi hbase hstep
      have hlo : lo = 0 := Nat.le_zero.mp hlohi
      subst lo
      exact Or.inl hbase
  | succ hi ih =>
      intro lo hlohi hbase hstep
      by_cases htop : lo = hi + 1
      · subst lo
        exact Or.inl hbase
      · have hmid : lo ≤ hi := by omega
        have hfold :
            Restated.NamedHonestVotesConeOn M S rho W Hs Xb hi
                (fun X => Block.Preceq B X) ∨ Exit :=
          ih hmid hbase (fun k hk hkh hcone =>
            hstep k hk (by omega) hcone)
        rcases hfold with hcone | hexit
        · rcases hstep hi hmid (Nat.lt_succ_self hi) hcone with hnext | hexit
          · exact Or.inl hnext
          · exact Or.inr hexit
        · exact Or.inr hexit

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

/-- On every path `W` of the run, `v` is a round-`k` voter of the family along `W` exactly when `v`
    is in the set for round `k`'s action instant and emitted there, along `W`, a round-`k`
    attestation it signs. -/
theorem honestRoundVoters_iffOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (Hs : Int → Finset V) (v : V)
    (k : Round) :
    v ∈ Restated.honestRoundVotersOn M S rho W Hs k ↔ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)) ∧
      ∃ a : NamedAttestation V, a.val_index = v ∧ a.round = k ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) ((Restated.Vocabulary.Execution.Setup.a M S k)) := by
  simp only [Restated.honestRoundVotersOn, Finset.mem_filter,
    Restated.Vocabulary.Proofs.NamedOutageInputs.emittedInRound_iff facts S rho W hW]

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

/-- Along any path `W` of the run: if `r − η_SG ≤ k`, `k + 1 < r` and `u` is a round-`k` voter of
    the family, then `u` is a historical voter of `r`. -/
theorem historical_of_voteOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V)
    {u : V} {k r : Round} (hlo : r - S.hc.η_SG ≤ k) (hbefore : k + 1 < r)
    (hvote : u ∈ Restated.honestRoundVotersOn M S rho W Hs k) :
    u ∈ Restated.historicalHonestVotersOn M S rho W Hs r := by
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hlo, hbefore⟩, hvote⟩
  exact Nat.lt_trans (Nat.lt_succ_self k) hbefore

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

/-- Along any path `W` of the run: if `k` is in the latest window of `r`, `u` is a round-`k` voter
    of the family and not a round-`(r − 1)` voter, then `u` is a stale historical voter of `r`. -/
theorem stale_of_eligible_voteOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V)
    {u : V} {k r : Round} (hwindow : k ∈ M.latest_window S.hc.η_SG r)
    (hvote : u ∈ Restated.honestRoundVotersOn M S rho W Hs k)
    (hnot : u ∉ Restated.honestRoundVotersOn M S rho W Hs (r - 1)) :
    u ∈ Restated.staleHistoricalVotersOn M S rho W Hs r := by
  have hlo := facts.fc.mem_latest_window_ge hwindow
  have hlt := facts.fc.mem_latest_window_lt hwindow
  have hne : k ≠ r - 1 := by intro heq; exact hnot (heq ▸ hvote)
  have before : ∀ k r : Nat, k < r → k ≠ r - 1 → k + 1 < r := by
    intro k r h1 h2
    omega
  have hbefore := before k r hlt hne
  exact Finset.mem_sdiff.mpr ⟨Restated.historical_of_voteOn facts S rho W Hs hlo hbefore hvote, hnot⟩

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

/-- Along any path `W` of the run, a block delivered at event index `i` is a direct run block read
    through `Xb`. -/
theorem directBlock_of_deliveryOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Xb : Finset V)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v (.block B) t)) :
    Restated.directBlockInRunOn M S rho W Xb B := Or.inl (Restated.objects_of_delivery rho hi)

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

/-- For every path `W`, a body a member of `Xb` holds in `W i` is a direct run block read through
    `Xb` along `W`. -/
theorem directBlock_of_prefixOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Xb : Finset V) {v : V}
    (hv : v ∈ Xb) (i : Nat) {B : NamedBlock V}
    (hB : B ∈ (W i v).st.bodies) :
    Restated.directBlockInRunOn M S rho W Xb B := Or.inr ⟨v, hv, i, hB⟩

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

/-- Along any path `W` of the run, a direct run block read through `Xb` is a run block read through
    `Xb`. -/
theorem blockInRun_of_directOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Xb : Finset V)
    {B : NamedBlock V}
    (h : Restated.directBlockInRunOn M S rho W Xb B) : Restated.blockInRunOn M S rho W Xb B :=
  ⟨B, h, Proofs.NamedAncestry.named_self B⟩

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

/-- Along any path `W` of the run, if `B` is a run block read through `Xb` and `A ⪯ B`, then `A` is
    a run block read through `Xb`. -/
theorem blockInRun_of_ancestorOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Xb : Finset V)
    {A B : NamedBlock V}
    (hB : Restated.blockInRunOn M S rho W Xb B) (hAB : NamedBlock.Preceq A B) :
    Restated.blockInRunOn M S rho W Xb A := by
  obtain ⟨C, hC, hBC⟩ := hB
  exact ⟨C, hC, (priv% Proofs.Vocabulary.Execution.Runtime
    DecoupledConsensusModel.Proofs.NamedRuntime.named_preceq_trans) hAB hBC⟩

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, `v`'s store in
    `W (strictEventIndex rho t)` holds a body `B` whose derived finalized root is that store's
    finalized root. -/
theorem exists_carrier_of_FOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (t : Time) (_hv : v ∈ Hs t) :
    ∃ B ∈ (W (strictEventIndex rho t) v).st.bodies,
      (M.derive_named S.E S.cfg B).F = (W (strictEventIndex rho t) v).st.core.F := by
  obtain ⟨B, hB, hF, -⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime facts S rho t v _
      (mem_stateBeforeTime_along₄₅ _hf.sorted _hf.onePath t)
  exact ⟨B, hB, hF⟩

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

/-- For the path `W` the bundle is read along, if every body a member of `X` holds in `W n` has
    finalized height at most `hF0`, the same holds in `W m` for every `m ≤ n`. -/
theorem honestPrefixFinalityCap_of_leOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {m n : Nat} (hmn : m ≤ n) {hF0 : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X n hF0) :
    Restated.HonestPrefixFinalityCapOn M S rho W X m hF0 := by
  intro v hv B hB
  exact hcap v hv B
    (Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hmn (W m)
      (_hf.onePath m).1 (W n) (onePath_reach_le₄₅ _hf.onePath hmn) hB)

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

/-- For every world `w` after the first `n` events, every body a member of `X` holds in `w` has
    finalized height at most the largest finalized height of any body a member of `X` holds in `w`. -/
theorem honestPrefixFinalityCap_recoveryPrefixFinalityHeightOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (X : Finset V) (n : Nat) :
    ∀ w ∈ Record.stateBeforeOf M S rho n, ∀ v ∈ X, ∀ B ∈ (w v).st.bodies,
      (M.derive_named S.E S.cfg B).h_F ≤
        X.sup fun u => (w u).st.bodies.sup fun C => (M.derive_named S.E S.cfg C).h_F := by
  intro w hw v hv B hB
  exact (Finset.le_sup
    (f := fun C : NamedBlock V => (M.derive_named S.E S.cfg C).h_F)
    hB).trans (Finset.le_sup
      (f := fun u : V =>
        (w u).st.bodies.sup
          (fun C => (M.derive_named S.E S.cfg C).h_F))
      hv)

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

/-- For the path `W` the bundle is read along, if every body a member of `X` holds in `W n` has
    finalized height at most `hF0`, and `blocked` is a recovery height for `hF0`, then every such
    body has the `nj` bit at height `blocked` and no justification at `blocked`. -/
theorem honestPrefixNJUniverse_of_finalityCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {n : Nat} {hF0 blocked : Height}
    (hcap : Restated.HonestPrefixFinalityCapOn M S rho W X n hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked) :
    Restated.HonestPrefixNJUniverseOn M S rho W X n blocked := by
  intro v hv B hB
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (W n v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n v (W n)
      (_hf.onePath n).1).1.1.1.2.2.1
  have hchainCap :
      ∀ C : NamedBlock V, NamedBlock.Preceq C B →
        (M.derive_named S.E S.cfg C).h_F ≤ hF0 := by
    intro C hCB
    exact hcap v hv C (namedAncestor_mem₄₅ hpc hB hCB)
  constructor
  · intro hheight
    exact Restated.Vocabulary.Proofs.NjGap.nj_of_cap_named facts (E := S.E) (cfg := S.cfg) hrec
      (hchainCap B (Proofs.NamedAncestry.named_self B)) hheight
  · exact facts.csAdded.h_j_ne_recovery_height_named (E := S.E) (cfg := S.cfg)
      hrec B hchainCap

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

/-- Along a path `W` of the run, under the slashable bound and collision freedom through `Xb`, for
    run blocks `C` and `D` read through `Xb`, if `D`'s finalized height is less than `C`'s height
    then `D`'s finalized block is an ancestor of `C`. -/
theorem finalized_preceq_of_height_ltOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) (C D : NamedBlock V)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    (hroot : Restated.RootCollisionFreeOn M S rho W Xb)
    (hC : Restated.blockInRunOn M S rho W Xb C) (hD : Restated.blockInRunOn M S rho W Xb D)
    (hlt : (M.derive_named S.E S.cfg D).h_F < (M.derive_named S.E S.cfg C).h) :
    Block.Preceq (M.derive_named S.E S.cfg D).F C.erase := by
  by_cases hz : (M.derive_named S.E S.cfg D).h_F = 0
  · rw [facts.cs.finalized_zero_is_genesis S.E S.cfg D hz]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis C.erase))
  · obtain ⟨F, hFD, hFE, Qf, hQf, hwf⟩ :=
      Restated.Vocabulary.Proofs.NamedFinalityCertificates.finality_certificate facts S.E S.cfg D hz
    obtain ⟨X, hXC, _hXheight, Qc, hQc, hwc⟩ :=
      facts.cs.height_crossing S.E S.cfg C
        (M.derive_named S.E S.cfg D).h_F (Nat.one_le_iff_ne_zero.mpr hz) hlt
    by_cases hroots : X.root = F.root
    · have hXF : X = F :=
        hroot.root_injective C D hC hD X F (Or.inl hXC) (Or.inr hFD) hroots
      rw [← hFE, ← hXF]
      exact Proofs.NamedWire.erase_preceq hXC
    · exfalso
      apply hsb C D hC hD
      refine facts.ev.Sts_hasSlashableWeightBetween_intro (Qc ∩ Qf) (facts.ev.quorum_intersection S.E hQc hQf) ?_
      intro signer hsigner
      obtain ⟨hc, hf⟩ := Finset.mem_inter.mp hsigner
      obtain ⟨carrierA, a, hcarrierA, ha, hav, hamatch⟩ := hwc signer hc
      obtain ⟨carrierB, b, hcarrierB, hb, hbv, hbfinal⟩ := hwf signer hf
      refine facts.ev.Sts_slashableBetween_intro a.erase
        (facts.ev.named_row_erase_mem hcarrierA ha)
        b.erase (facts.ev.named_row_erase_mem hcarrierB hb) ?_ ?_ ?_
      · rw [namedAttestation_erase_val_index]; exact hav
      · rw [namedAttestation_erase_val_index]; exact hbv
      · exact facts.csAdded.matching_finality_e1 a b
          (M.derive_named S.E S.cfg D).h_F X.root F.root
          (hav.trans hbv.symm) hamatch hbfinal hroots

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

/-- Along a path `W` of the run, under the slashable bound and collision freedom through `Xb`: if
    `BF` and every body of `st` are run blocks read through `Xb`, `st` has provenance, and `BF`
    finalized `F` at a height `h_f` at most `st`'s justified height, then `F` is an ancestor of
    `st`'s justified block. -/
theorem upgrade_of_height_leOn (facts : Record.Facts M) {S : Setup V} {ρ : Record.Run V}
    {W : Nat → V → M.N} {Xb : Finset V}
    {st : M.NS} {BF : NamedBlock V} {F : Block V} {h_f : Height}
    (hsb : Restated.SlashableBoundOn M S ρ W Xb)
    (hcf : Restated.RootCollisionFreeOn M S ρ W Xb)
    (hBF : Restated.RunBlockOn M S ρ W Xb BF)
    (hRun : ∀ D ∈ st.bodies, Restated.RunBlockOn M S ρ W Xb D)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hfin : Restated.Vocabulary.Statements.Instantiation.NamedFinalizedAt M S.E S.cfg BF F h_f)
    (hle : h_f ≤ st.core.h_j) :
    Block.preceq F st.core.J = true := by
  obtain ⟨C, hC, hCJ, hCh⟩ := hprov.2
  have hCrun : Restated.RunBlockOn M S ρ W Xb C := hRun C hC
  by_cases hz : h_f = 0
  · have hFg : F = Block.genesis := by
      rw [← hfin.1]
      exact facts.cs.finalized_zero_is_genesis S.E S.cfg BF
        (by rw [hfin.2]; exact hz)
    rw [hFg]
    exact Protocol.preceq_genesis st.core.J
  have hFnz : (M.derive_named S.E S.cfg BF).h_F ≠ 0 := by
    rw [hfin.2]
    exact hz
  have hjnz : (M.derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hCh]
    intro h0
    rw [h0] at hle
    exact hz (Nat.le_zero.mp hle)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hCbelow : h_f < (M.derive_named S.E S.cfg C).h := by
      have hjh :=
        (facts.cs.chainOrder_derive_named S.E S.cfg C).justified_below_height
      rw [hCh] at hjh
      exact lt_trans hlt hjh
    have hFC : Block.Preceq F C.erase := by
      have h := Restated.finalized_preceq_of_height_ltOn facts S ρ W Xb C BF hsb hcf
        hCrun hBF (by rw [hfin.2]; exact hCbelow)
      rwa [hfin.1] at h
    have hJC : Block.Preceq st.core.J C.erase := by
      rw [← hCJ]
      exact ((facts.cs.derive_named_anchors_preceq S.E S.cfg C)).2
    rcases preceq_linear_Preceq hFC hJC with hFJ | hJF
    · exact preceq_eq_true_iff_Preceq.mpr hFJ
    · exfalso
      obtain ⟨Jn, hJnC, hJnE, hJnh⟩ :=
        (facts.cs.justified_ancestor_height S.E S.cfg C).resolve_left hjnz
      obtain ⟨Fn, hFnBF, hFnE, hFnh⟩ :=
        (facts.csAdded.finalized_ancestor_height S.E S.cfg BF).resolve_left hFnz
      have hlift : Block.Preceq Jn.erase Fn.erase := by
        rw [hJnE, hCJ, hFnE, hfin.1]
        exact hJF
      obtain ⟨J', hJ'Fn, hJ'E⟩ := Proofs.NamedAncestry.erased_ancestor_lift Fn hlift
      have hroots : Jn.root = J'.root := by
        rw [← Proofs.NamedWire.erase_root Jn, ← Proofs.NamedWire.erase_root J', hJ'E]
      have hEq : Jn = J' :=
        hcf.root_injective C BF hCrun hBF Jn J' (Or.inl hJnC)
          (Or.inr ((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.StoreFinalityUpgrade
            DecoupledConsensusModel.Proofs.StoreFinality.named_trans) hJ'Fn hFnBF)) hroots
      have hmono : (M.derive_named S.E S.cfg Jn).h ≤ (M.derive_named S.E S.cfg Fn).h := by
        rw [hEq]
        exact facts.cs.derive_height_mono S.E S.cfg hJ'Fn
      rw [hJnh, hCh, hFnh, hfin.2] at hmono
      exact absurd hmono (Nat.not_le_of_gt hlt)
  · obtain ⟨Jn, hJnC, hJnE, Qj, hQj, hwj⟩ :=
      Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg C hjnz
    obtain ⟨Fn, hFnBF, hFnE, Qf, hQf, hwf⟩ :=
      Restated.Vocabulary.Proofs.NamedFinalityCertificates.finality_certificate facts S.E S.cfg BF hFnz
    have hJnroot : Jn.root = st.core.J.root := by
      rw [← Proofs.NamedWire.erase_root Jn, hJnE, hCJ]
    have hFnroot : Fn.root = F.root := by
      rw [← Proofs.NamedWire.erase_root Fn, hFnE, hfin.1]
    by_cases hr : st.core.J.root = F.root
    · have hinj : Execution.RootInjectiveOnAncestors C.erase BF.erase :=
        Restated.rootInjectiveOnAncestors_of_collisionFreeOn facts S ρ W Xb hcf C BF
          hCrun hBF
      have hJF : st.core.J = F :=
        RootInjectiveOnAncestors.eq_of_root_eq hinj
          (by
            rw [← hCJ]
            exact ((facts.cs.derive_named_anchors_preceq S.E S.cfg C)).2)
          (by
            rw [← hfin.1]
            exact ((facts.cs.derive_named_anchors_preceq S.E S.cfg BF)).1)
          hr
      rw [hJF]
      exact Block.preceq_self _
    · exfalso
      apply hsb C BF hCrun hBF
      refine facts.ev.Sts_hasSlashableWeightBetween_intro (Qj ∩ Qf) (facts.ev.quorum_intersection S.E hQj hQf)
        (fun i hi => ?_)
      obtain ⟨hij, hif⟩ := Finset.mem_inter.mp hi
      obtain ⟨ca, a, hca, ha, hav, hap⟩ := hwj i hij
      obtain ⟨cb, b, hcb, hb, hbv, hbp⟩ := hwf i hif
      refine facts.ev.Sts_slashableBetween_intro a.erase (facts.ev.erase_mem_chain_attestations C ca hca a ha)
        b.erase (facts.ev.erase_mem_chain_attestations BF cb hcb b hb)
        (by rw [namedAttestation_erase_val_index]; exact hav)
        (by rw [namedAttestation_erase_val_index]; exact hbv) ?_
      refine facts.csAdded.matching_finality_e1 a b h_f Jn.root Fn.root (hav.trans hbv.symm) ?_ ?_ ?_
      · rw [hap, matchesEntry_vote_iff]
        refine ⟨?_, rfl⟩
        rw [hCh, ← heq]
      · rw [hbp, hfin.2]
      · rw [hJnroot, hFnroot]
        exact hr

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

/-- Along a path `W` of the run, under the slashable bound and collision freedom through `Xb`, with
    `st` free of high justifications and with provenance: if `st` holds `B` justifying `F` at `h_f`,
    `BF` and every body of `st` are run blocks read through `Xb`, and `BF` finalized `F` at `h_f`,
    then `F` is an ancestor of `st`'s justified block. -/
theorem upgradeOn (facts : Record.Facts M) {S : Setup V} {ρ : Record.Run V} {W : Nat → V → M.N}
    {Xb : Finset V} {st : M.NS}
    {BF B : NamedBlock V} {F : Block V} {h_f : Height}
    (hnhj : Restated.Vocabulary.Internal.NamedNoHighJustifications M S.E S.cfg st)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hB : B ∈ st.bodies)
    (hjust : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg B F h_f)
    (hsb : Restated.SlashableBoundOn M S ρ W Xb)
    (hcf : Restated.RootCollisionFreeOn M S ρ W Xb)
    (hBF : Restated.RunBlockOn M S ρ W Xb BF)
    (hRun : ∀ D ∈ st.bodies, Restated.RunBlockOn M S ρ W Xb D)
    (hfin : Restated.Vocabulary.Statements.Instantiation.NamedFinalizedAt M S.E S.cfg BF F h_f) :
    Block.preceq F st.core.J = true := by
  have hfloor : h_f ≤ st.core.h_j := by
    rw [← hjust.2]
    exact hnhj B hB
  exact Restated.upgrade_of_height_leOn facts hsb hcf hBF hRun hprov hfin hfloor

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, `v`'s slot-`k` pool in `W n` is
    a valid vote set for `k`. -/
theorem voteSetValid_pool_stateBeforeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (n : Nat) (k : Slot) :
    Protocol.VoteSetValid S.E k ((W n v).st.pool k) := by
  intro u hu
  have hslots := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf v n
  have hcom := Restated.Vocabulary.Protocol.CommitteePools.stateBefore facts S rho v n (W n)
    (hf.onePath n).1
  have hu' := (facts.sto.mem_store_pool_iff (W n v).st.core k u).mp hu
  exact ⟨hslots.slot k u hu', hcom k u hu'⟩

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the proposer view of `v`'s store
    in `W n` at `s` is a valid vote set for `s − 1`. -/
theorem voteSetValid_proposer_view_stateBeforeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (n : Nat) (s : Slot) :
    Protocol.VoteSetValid S.E (s - 1)
      (M.proposer_view
        (W n v).st.toHealing.toFG.toSG.toGoldfishStore s).toFinset :=
  Restated.Vocabulary.Protocol.voteSetValid_proposer_view facts
    (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf v n)
    (Restated.Vocabulary.Protocol.CommitteePools.stateBefore facts S rho v n (W n) (hf.onePath n).1) s

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the late confirmation votes of
    `v`'s store in `W n` at `s` are a valid vote set for `s`. -/
theorem voteSetValid_confLate_stateBeforeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (n : Nat) (s : Slot) :
    Protocol.VoteSetValid S.E s (Restated.Vocabulary.Protocol.confLate M S.E (W n v).st.core s) :=
  Restated.Vocabulary.Protocol.voteSetValid_confLate facts
    (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf v n)
    (Restated.Vocabulary.Protocol.CommitteePools.stateBefore facts S rho v n (W n) (hf.onePath n).1) s

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the proposer view of `v`'s store
    in `W (strictEventIndex rho t)` at `s` is a valid vote set for `s − 1`. -/
theorem voteSetValid_proposer_view_stateBeforeTimeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (t : Time) (s : Slot) :
    Protocol.VoteSetValid S.E (s - 1)
      (M.proposer_view
        (W (strictEventIndex rho t) v).st.toHealing.toFG.toSG.toGoldfishStore s).toFinset :=
  Restated.voteSetValid_proposer_view_stateBeforeOn facts S Hs Xb hf v _ s

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the late confirmation votes of
    `v`'s store in `W (strictEventIndex rho t)` at `s` are a valid vote set for `s`. -/
theorem voteSetValid_confLate_stateBeforeTimeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (t : Time) (s : Slot) :
    Protocol.VoteSetValid S.E s
      (Restated.Vocabulary.Protocol.confLate M S.E (W (strictEventIndex rho t) v).st.core s) :=
  Restated.voteSetValid_confLate_stateBeforeOn facts S Hs Xb hf v _ s

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

/-- Along any path `W` of the run: if the validators outside `X` weigh less than a third and no
    member of `X` emits two targets at one height, at most one target per height is completable from
    `X`. -/
theorem perHeightCompletability_ofOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (W : Nat → V → M.N) (X : Finset V)
    (hfb : Execution.BelowOneThird S X)
    (hcore : Restated.HonestNoDoubleTargetOn M S ρ W X) :
    Restated.PerHeightCompletabilityOn M S ρ W X := by
  rintro h T T' ⟨Q, hQhon, hQw, hQem⟩ ⟨Q', hQ'hon, hQ'w, hQ'em⟩
  by_contra hne
  have hsub : Q ∩ Q' ⊆ (∅ : Finset V) := by
    intro v hv
    obtain ⟨hvQ, hvQ'⟩ := Finset.mem_inter.mp hv
    obtain ⟨a, t, hemit, hmem⟩ := hQem v hvQ
    obtain ⟨a', t', hemit', hmem'⟩ := hQ'em v hvQ'
    exact absurd (hcore v (hQhon hvQ) a a' t t' hemit hemit' h T T' hmem hmem') hne
  have hinter : S.E.electorate.weightOf (Q ∩ Q') ≤ 0 :=
    le_trans (S.E.electorate.weightOf_mono hsub) (le_of_eq (weightOf_empty S.E.electorate))
  have hie := S.E.electorate.weight_inter_add_weight_union Q Q'
  have hunion : S.E.electorate.weightOf (Q ∪ Q') ≤
      S.E.electorate.weightOf X :=
    S.E.electorate.weightOf_mono (Finset.union_subset hQhon hQ'hon)
  have hcompl := weightOf_add_weightOf_sdiff_eq_W S.E X
  have hq := Proofs.HealingSurface.two_mul_W_le_three_mul_q S.E
  unfold Execution.BelowOneThird at hfb
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
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the finalized block of `w`'s
    store in `W (strictEventIndex rho t)` is an ancestor of that store's finality-gadget root. -/
theorem finalizedRoot_preceq_fgRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) {w : V} {t : Time} :
    Block.Preceq (W (strictEventIndex rho t) w).st.core.F
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho t) w).st.core).toFG) := by
  have hw₁ := mem_stateBeforeTime_along₄₅ _hf.sorted _hf.onePath t
  generalize W (strictEventIndex rho t) = w₁ at hw₁ ⊢
  have hFJ : Block.Preceq (w₁ w).st.core.F (w₁ w).st.core.J :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts S rho t w
      w₁ hw₁
  rcases facts.fc.get_fg_root_eq_J_or_F (w₁ w).st.core with h | h
  · rw [h]
    exact hFJ
  · rw [h]
    exact Proofs.ModelProperties.Preceq_self _

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

/-- On every path `W` of the run, for any set `X`, no member of `X` emits along `W` two attestations
    with different targets at one height. -/
theorem honestNoDoubleTargetOn (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W) (X : Finset V) :
    Restated.HonestNoDoubleTargetOn M S ρ W X := by
  intro v hv a a' t t' he he' h T T' hT hT'
  exact Restated.Vocabulary.Proofs.HealingSurface.honestNoDoubleTarget facts S { ρ with honest := X } W hW
    v hv a a' t t' he he' h T T' hT hT'

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

/-- On every path `W` of the run, if the validators outside `X` weigh less than a third, at most one
    target per height is completable from `X` along `W`. -/
theorem perHeightCompletabilityOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W) (X : Finset V)
    (hfb : Execution.BelowOneThird S X) :
    Restated.PerHeightCompletabilityOn M S ρ W X :=
  Restated.perHeightCompletability_ofOn facts S W X hfb (Restated.honestNoDoubleTargetOn facts S ρ W hW X)

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

/-- Every event of a run satisfying the bundle `AdmissibleFieldsOn` is at an instant in
    `[0, rho.horizon]`. -/
theorem in_horizonOn (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V}
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) :
    ∀ e ∈ rho.events, 0 ≤ Record.Event.time e ∧ Record.Event.time e ≤ rho.horizon :=
  hf.in_horizon

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
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedRawRelay
local macro "rr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.RawRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawRelay ++ n.getId)))

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the reader's stores in `W i` and
    in `W (i + 1)` have their clock and every held row's stamp at or before the instant of event
    `i`. -/
theorem data_at_eventOn_RawRelay (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {e : Record.Event V}
    (he : rho.events[i]? = some e) (reader : V) :
    Restated.Vocabulary.Proofs.NamedRawRelay.Data M e.time (W i reader).st ∧
      Restated.Vocabulary.Proofs.NamedRawRelay.Data M e.time (W (i + 1) reader).st :=
  Restated.Vocabulary.Proofs.NamedRawRelay.data_at_event_of_fields facts S rho hf.sorted hf.in_horizon he reader
    (W i) (hf.onePath i).1 (W (i + 1)) (hf.onePath (i + 1)).1

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
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedRawRelay

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, a tick of the reader at `p`
    before a delivery to it at `td ≥ p`, the `i`-th event, is at most the clock of the reader's
    store in `W i`. -/
theorem tick_le_clock_before_deliveryOn_RawRelay (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {reader : V} {o : NamedObject V} {td p : Time}
    (he : rho.events[i]? = some (.deliver reader o td))
    (hp : Record.Event.tick reader p ∈ rho.events) (hpt : p ≤ td) :
    p ≤ (W i reader).st.core.t := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
  have hji : j < i := by
    by_contra hn
    have hij : i ≤ j := Nat.le_of_not_gt hn
    have hne : i ≠ j := by
      intro h
      subst j
      rw [he] at hj
      cases hj
    obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
    have hkey := (List.pairwise_iff_getElem.mp hf.sorted) i j hiLen hjLen (lt_of_le_of_ne hij hne)
    rw [hiGet, hjGet] at hkey
    have hbad : ¬ Record.Event.key (Record.Event.deliver reader o td) ≤
        Record.Event.key (Record.Event.tick reader p) := by
      simp only [Record.Event.key, Record.Event.time, Record.Event.phase, Prod.Lex.le_iff]
      rintro (hlt | ⟨_, hphase⟩)
      · exact (not_lt_of_ge hpt) hlt
      · norm_num at hphase
    exact hbad hkey
  have hstep := (hf.onePath j).2
  rw [drop_take_succ₄₅ hj, mem_foldlM_singleton₄₅] at hstep
  have ht : (W (j + 1) reader).st.core.t = p := by
    rcases Restated.Vocabulary.Proofs.NamedRuntime.step_tick facts S (W j) reader p (W (j + 1)) hstep with
      ⟨out, hout, h⟩ | ⟨hno, -⟩
    · rw [h]
      exact (facts.nd.tick_clock S reader (W j reader) p out hout).1
    · obtain ⟨out, hout⟩ := hf.tick_outcome j reader p hj
      exact absurd hout (hno out)
  rw [← ht]
  exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_mono facts S rho hf.sorted
    (fun e he' => (hf.in_horizon e he').1) reader (by omega : j + 1 ≤ i) (W (j + 1))
    (hf.onePath (j + 1)).1 (W i) (onePath_reach_le₄₅ hf.onePath (by omega : j + 1 ≤ i))

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along: if the reader is in the set for
    `opening q` and `lo ≤ opening q`, a delivery to it at `td` in `[opening q, opening r)`, the
    `i`-th event, finds its store in `W i` in a round `≥ q` and `< r`. -/
theorem delivery_round_boundsOn_RawRelay (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {reader : V} {o : NamedObject V} {td : Time}
    (q r : Round) (he : rho.events[i]? = some (.deliver reader o td))
    (hlo : M.opening S.E S.hc q ≤ td) (hhi : td < M.opening S.E S.hc r)
    (hr : reader ∈ Hs (M.opening S.E S.hc q)) (hgat : lo ≤ M.opening S.E S.hc q) :
    q ≤ M.round_of S.hc (W i reader).st.core.s ∧
      M.round_of S.hc (W i reader).st.core.s < r := by
  have hW := hf.onePath
  have hmem := List.mem_of_getElem? he
  have htk := hf.tick_total (M.opening S.E S.hc q) hgat reader hr
    (by
      rw [facts.gr.opening_eq_proposal_time]
      exact Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S
        (M.opening_slot S.hc q))
    (hlo.trans (hf.in_horizon _ hmem).2)
  have hclock := tick_le_clock_before_deliveryOn_RawRelay facts S rho Hs Xb hf he htk hlo
  have hup := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S rho
    hf.sorted he (hf.in_horizon _ hmem).1 reader (W i) (hW i).1
  exact round_bounds_of_clock₄₅ facts S q r _ (slot_clock_along₄₅ facts S rho W hW reader i)
    hclock (hup.trans_lt hhi)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- `st` holds, in the rows of its own round, a named attestation of `a`'s round and `a`'s signer
    confirming `a`'s confirmed block, or two such named attestations confirming different blocks. -/
def Vocabulary.Proofs.NamedRawRelay.Outcome (M : Record.Model V) (st : M.NS) (a : NamedAttestation V) :
    Prop :=
  (∃ vote : NamedAttestation V, vote ∈ st.sg_rows vote.round ∧ vote.round = a.round ∧
    vote.val_index = a.val_index ∧ vote.confirmed = a.confirmed) ∨
  ∃ left right : NamedAttestation V,
    left ∈ st.sg_rows left.round ∧ right ∈ st.sg_rows right.round ∧
    left.round = a.round ∧ right.round = a.round ∧
    left.val_index = a.val_index ∧ right.val_index = a.val_index ∧
    left.confirmed ≠ right.confirmed

/-- The SG vote stamps of `st` with its clock set to `t` are the SG vote stamps of `st`. -/
private theorem setClock_timestamp_sg_vote₄₅ (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (t : Time) :
    (M.ns_setClock E st t).core.timestamp_sg_vote = st.core.timestamp_sg_vote := by
  rw [← facts.gr.gradeView_timestamp_sg_vote (M.ns_setClock E st t).core,
    facts.hd.setClock_gradeView, facts.gr.gradeView_timestamp_sg_vote]

/-- The SG vote stamps of every store `D` the named confirmation duty can return on `st` are the SG
    vote stamps of `st`. -/
private theorem confirmation_timestamp_sg_vote₄₅ (facts : Record.Facts M) (gc : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot) (D : M.NS)
    (hD : M.duties_update_confirmation_with gc E hc st s ⇢ D)
    (hn : M.reachedCore st.core := by trivial) :
    D.core.timestamp_sg_vote = st.core.timestamp_sg_vote := by
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty gc E hc st.core s
  rw [facts.dt.named_update_confirmation_with_core gc E hc st s D hD X hX,
    ← facts.gr.gradeView_timestamp_sg_vote X,
    facts.dt.update_confirmation_with_toHealing_gradeView gc E hc st.core s X hX hn,
    facts.gr.gradeView_timestamp_sg_vote]

/-- A store with the rows, the SG vote stamps and the clock of a store satisfying `Data` at `bound`
    satisfies `Data` at `bound`. -/
private theorem data_fields₄₅ {bound : Time} {st out : M.NS}
    (h : Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound st) (hr : out.sg_rows = st.sg_rows)
    (hs : out.core.timestamp_sg_vote = st.core.timestamp_sg_vote)
    (ht : out.core.t = st.core.t) : Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound out :=
  ⟨by rw [ht]; exact h.1, by rw [hr, hs]; exact h.2⟩

/-- If `st` satisfies `Data` at `bound` and `t ≤ bound`, so does `st` with its clock set to `t`. -/
private theorem clock_data₄₅ (facts : Record.Facts M) (S : Setup V) (bound : Time) (st : M.NS)
    (t : Time) (ht : t ≤ bound) (hd : Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound st) :
    Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound (M.ns_setClock S.E st t) :=
  ⟨by rw [facts.hd.ModelProperties_setClock_core_t]; exact ht,
    by rw [facts.hd.setClock_sg_rows, setClock_timestamp_sg_vote₄₅ facts]; exact hd.2⟩

/-- If `st` is coherent and satisfies `Data` at `bound`, so does the store the admission of the rows
    `rows` returns on `st`. -/
private theorem rows_data₄₅ (facts : Record.Facts M) (S : Setup V) (bound : Time) (st : M.NS)
    (rows : List (NamedAttestation V))
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st)
    (hd : Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound st) :
    Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound (M.admit_rows S.hc st rows) :=
  facts.hd.sgArrival_rows_data S bound st rows hcoh hd

/-- The admission of a list of rows keeps a store coherent. -/
private theorem coherent_admit_rows₄₅ (facts : Record.Facts M) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS)
    (rows : List (NamedAttestation V))
    (h : Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg st) :
    Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg (M.admit_rows hc st rows) :=
  facts.hd.NamedAdmission_coherent_admit_rows E hc cfg st rows h

/-- On every path `W` of `rho`, if the `i`-th event delivers `o` to `v` and the receipt has an
    outcome, `v`'s store in `W (i + 1)` is `M.make_grades_compatible_with_finalized` of the store
    the receipt of `o` returns on `v`'s store in `W i`. -/
private theorem deliver_post₄₅ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {i : Nat} {v : V} {o : NamedObject V} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    -- `v`'s receipt of `o` from its node state in `W i` has an outcome
    (hout : ∃ n' : M.N, M.process S (W i v) o ⇢ n') :
    (W (i + 1) v).st =
      M.make_grades_compatible_with_finalized (M.receipt_process S (W i v).st o) := by
  obtain ⟨hWi, hstep⟩ := hW i
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) hWi
      (W (i + 1)) hstep with hproc | ⟨hno, -⟩
  · exact facts.nd.process_st S (W i v) o (W (i + 1) v) hproc
  · obtain ⟨n', hn'⟩ := hout
    exact absurd hn' (hno n')

/-- On every path `W` of `rho`, if a block call of `B` at `reader` at the `i`-th event has input
    `before`, every row the block handler holds in its own round's rows on `before` is held by
    `reader`'s store in `W (i + 1)`. -/
private theorem block_call_rows_after_event₄₅ (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    -- every delivery event has an outcome from the node state `W` holds before it
    (hreceipt : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Int),
      rho.events[i]? = some (Record.Event.deliver v o t) →
      ∃ n' : M.N, M.process S (W i v) o ⇢ n')
    {i : Nat} {reader : V} {B : NamedBlock V} {before : M.NS}
    (hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i reader B before)
    (a : NamedAttestation V)
    (ha : a ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg before B).sg_rows a.round) :
    a ∈ (W (i + 1) reader).st.sg_rows a.round := by
  have _hr_0 : M.reachedNode (W i reader) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 reader
  have _hv_0 : M.runs_as (W i reader) reader := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 reader
  obtain ⟨hWi, -⟩ := hW i
  rcases hcall with ⟨t, he, rfl⟩ | ⟨t, he, ⟨out, hout, hw, hem⟩, rfl⟩
  · rw [deliver_post₄₅ facts S rho W hW he (hreceipt _ _ _ _ he),
      facts.nd.make_grades_compatible_with_finalized_sg_rows, facts.nd.process_block]
    exact ha
  · obtain ⟨hpos, hprop, hproposer⟩ :=
      (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1
    have hdue : 0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node reader).val_index ∧
        M.awake_for_grade1 S reader (W i reader) (M.round_of S.hc (S.E.slotOf t)) :=
      ⟨hpos, hprop, hproposer.trans (S.node_val_index reader).symm,
        facts.nd.block_mem_on_tick_emit_awake S reader (W i reader) t out hout hem⟩
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i reader).st.core.toHealing t
      (W i reader).cache
    obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S reader (W i reader) t out hout
      (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1.1 (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1.2.1
      (facts.nd.block_mem_on_tick_emit S reader (W i reader) t out hout hem).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S reader (W i reader) t out hout hem) c hc
    have hcallEq := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho
      he (W i) hWi out hout hem c hc D hD
    rw [hw]
    apply (facts.nd.tick_rows_after_proposal_of_outcomes S reader (W i reader) t out hout).1 hdue
      c hc D hD a
    rw [hcallEq]
    simp only [facts.nd.store_with_cache_sg_rows]
    exact ha

/-- If `input` is coherent and satisfies `Data` at `bound`, every key `input` holds for `a`'s signer
    and round is the confirmed block of a named attestation of `a`'s round and signer held in the
    rows of its own round. -/
private theorem key_representative₄₅ (facts : Record.Facts M) (S : Setup V) (input : M.NS)
    (bound : Time) (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg input)
    (hd : Restated.Vocabulary.Proofs.NamedRawRelay.Data M bound input)
    (a : NamedAttestation V) (key : Option BlockId)
    (hk : key ∈ M.round_votes input.core a.erase) :
    ∃ b : NamedAttestation V, b ∈ input.sg_rows b.round ∧ b.round = a.round ∧
      b.val_index = a.val_index ∧ b.confirmed = key := by
  obtain ⟨erased, herased, hval, hkey⟩ := (facts.hd.mem_round_votes_iff _ _ _).mp hk
  rw [_root_.DecoupledConsensusModel.Sts.namedAttestation_erase_round] at herased
  rw [_root_.DecoupledConsensusModel.Sts.namedAttestation_erase_val_index] at hval
  have hpool : erased ∈ input.core.sg_votes a.round :=
    (facts.sto.ModelProperties_mem_sg_pool_iff _ _ _).mp herased
  rw [hcoh.2.2.2.1 a.round] at hpool
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hpool
  have hr : b.round = a.round := (hd.2 a.round b hb).1
  refine ⟨b, by rw [hr]; exact hb, hr, ?_, ?_⟩
  · rw [← _root_.DecoupledConsensusModel.Sts.namedAttestation_erase_val_index b]
    exact (congrArg CombinedAttestation.val_index he).trans hval
  · rw [← _root_.DecoupledConsensusModel.Sts.namedAttestation_erase_confirmed b]
    exact (congrArg CombinedAttestation.confirmed he).trans hkey

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along: if the reader is in the set for
    `opening a.round` and `lo ≤ opening a.round`, a handle of `a` by it at `td` in
    `[opening a.round, opening r)`, at the `i`-th event read along `W`, has an input store that is
    coherent, has its clock and stamps bounded by `td`, is in a round from `a.round` to before `r`,
    and whose admission of `a` is kept in the reader's store in `W (i + 1)`. -/
theorem relay_call_inputOn_RawRelay (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (r : Round) {i : Nat} {reader : V} {a : NamedAttestation V} {td : Time}
    (hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i reader (.attest a) td)
    (hlo : M.opening S.E S.hc a.round ≤ td) (hhi : td < M.opening S.E S.hc r)
    (hr : reader ∈ Hs (M.opening S.E S.hc a.round)) (hgat : lo ≤ M.opening S.E S.hc a.round) :
    ∃ input : M.NS, Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg input ∧
      Restated.Vocabulary.Proofs.NamedRawRelay.Data M td input ∧
      (a.round ≤ M.round_of S.hc input.core.s ∧ M.round_of S.hc input.core.s < r) ∧
      ∀ b : NamedAttestation V,
        b ∈ (M.admit_row S.hc input a).sg_rows b.round →
        b ∈ (W (i + 1) reader).st.sg_rows b.round := by
  have _hr_0 : M.reachedNode (W i reader) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 reader
  have _hv_0 : M.runs_as (W i reader) reader := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 reader
  have hW := hf.onePath
  obtain ⟨hWi, -⟩ := hW i
  have hWi1 := (hW (i + 1)).1
  have htime_of : ∀ {e : Record.Event V}, rho.events[i]? = some e → e.time = td := by
    intro e he
    obtain ⟨f, hf', _, ht⟩ := hcall.2
    have hef : e = f := Option.some.inj (he.symm.trans hf')
    rw [hef]
    exact ht
  have hdeliv : ∀ {o : NamedObject V}, rho.events[i]? = some (.deliver reader o td) →
      Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W i reader).st ∧
      Restated.Vocabulary.Proofs.NamedRawRelay.Data M td (W i reader).st ∧
      (a.round ≤ M.round_of S.hc (W i reader).st.core.s ∧
        M.round_of S.hc (W i reader).st.core.s < r) := by
    intro o he
    exact ⟨(Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i reader
        (W i) hWi).1.1.1,
      (data_at_eventOn_RawRelay facts S rho Hs Xb hf he reader).1,
      delivery_round_boundsOn_RawRelay facts S rho Hs Xb hf a.round r he hlo hhi hr hgat⟩
  rcases hcall.1 with hdirect | ⟨B, k, before, hF1⟩
  · rcases hdirect with ⟨t, he, out, hout, hw, hem⟩ | ⟨t, he⟩
    · have ht : t = td := htime_of he
      subst ht
      have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W reader (.attest a) t :=
        ⟨i, he, out, hout, hw, hem⟩
      obtain ⟨j, hj, out', hout', hw', hmem', hstages, hval, htime, hawake⟩ :=
        Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hW hemit
      have hij : j = i := Restated.tick_index_eq_of_unique
        hf.tickIndexUnique hj he
      subst hij
      subst htime
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W j reader).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S a.round) (W j reader).cache
      obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c)
        S.E S.hc (M.ns_setClock S.E (W j reader).st (Restated.Vocabulary.Execution.Setup.a M S a.round))
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S a.round) - 1)
      have hn : M.mkNode st (W j reader).record c ∈
          Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom M S (W j reader) a.round :=
        ⟨c, hc, st, hst, rfl⟩
      obtain ⟨hrowall, -⟩ := hstages _ hn
      obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract c) S.E S.hc (S.node reader)
        st (W j reader).record
      have hrow : D.2.2 = a := hrowall D (by
        rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.duties_attest_with_store_with_cache,
          facts.nd.mkNode_record]
        exact hD)
      have hpre := (data_at_eventOn_RawRelay facts S rho Hs Xb hf he reader).1
      have hd : Restated.Vocabulary.Proofs.NamedRawRelay.Data M
          (Restated.Vocabulary.Execution.Setup.a M S a.round) st :=
        data_fields₄₅ (clock_data₄₅ facts S _ _ _ le_rfl hpre)
          (facts.dt.confirmation_metadata _ _ _ _ _ st hst).2
          (confirmation_timestamp_sg_vote₄₅ facts _ _ _ _ _ st hst
            (facts.nd.reachedCore_of_store _ (facts.sto.reachedStore_setClock S.E _ _
              (facts.nd.reachedStore_of_node _ _hr_0))))
          (facts.dt.named_confirmation_clock _ _ _ _ _ st hst).1
      have hnt : st.core.t = Restated.Vocabulary.Execution.Setup.a M S a.round := by
        rw [(facts.dt.named_confirmation_clock _ _ _ _ _ st hst).1,
          facts.hd.ModelProperties_setClock_core_t]
      have hns : st.core.s = S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
        rw [(facts.dt.named_confirmation_clock _ _ _ _ _ st hst).2,
          facts.hd.ModelProperties_setClock_core_s]
      have hinv := Restated.Vocabulary.Proofs.NamedOutageInputs.action_read_invariant facts S rho j
        reader a.round (W j) hWi _ hn
      rewrite [facts.nd.mkNode_st] at hinv
      have _hrs : M.reachedStore (M.store_with_cache st c) := by
        have h := facts.nd.reachedStore_of_node _ (facts.nd.reachedNode_confirmationDuty S.E S.hc
          (W j reader) _ c st hc hst _hr_0)
        rwa [facts.nd.mkNode_st] at h
      have hD' : M.duties_attest_with (M.gradeContract c) S.E S.hc (S.node reader)
          (M.store_with_cache st c) (W j reader).record ⇢ D := by
        rw [facts.dt.duties_attest_with_store_with_cache]; exact hD
      refine ⟨M.store_with_cache st c, hinv.1.1,
        data_fields₄₅ hd (funext (facts.nd.store_with_cache_sg_rows st c))
          (facts.nd.store_with_cache_core_timestamp_sg_vote st c)
          (facts.nd.store_with_cache_core_t st c),
        round_bounds_of_clock₄₅ facts S a.round r _
          (by rw [facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, hns, hnt])
          (by rw [facts.nd.store_with_cache_core_t, hnt]; exact hlo)
          (by rw [facts.nd.store_with_cache_core_t, hnt]; exact hhi), ?_⟩
      intro b hb
      rw [hw, facts.nd.action_tick_store_of_outcomes S reader (W j reader) a.round hawake out hout
          c hc st hst D hD,
        facts.dt.namedDuties_attest_with_fst _ _ _ _ _ _ D hD' _hrs, hrow,
        facts.nd.store_with_cache_sg_rows]
      exact hb
    · have ht : t = td := htime_of he
      subst ht
      obtain ⟨hcoh, hd, hbounds⟩ := hdeliv he
      refine ⟨(W i reader).st, hcoh, hd, hbounds, ?_⟩
      intro b hb
      rw [deliver_post₄₅ facts S rho W hW he (hf.receipt_outcome _ _ _ _ he),
        facts.nd.make_grades_compatible_with_finalized_sg_rows, facts.nd.process_attest]
      exact hb
  · have hbefore : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg before ∧
        Restated.Vocabulary.Proofs.NamedRawRelay.Data M td before ∧
        (a.round ≤ M.round_of S.hc before.core.s ∧ M.round_of S.hc before.core.s < r) := by
      rcases hF1.1 with ⟨t, he, hbef⟩ | ⟨t, he, -, hbef⟩
      · have ht : t = td := htime_of he
        subst ht
        rw [hbef]
        exact hdeliv he
      · have ht : t = td := htime_of he
        subst ht
        rw [hbef]
        refine ⟨(facts.hd.invariant_clock S.E S.cfg _ t
            (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i reader
              (W i) hWi).1).1.1,
          clock_data₄₅ facts S t _ t le_rfl
            (data_at_eventOn_RawRelay facts S rho Hs Xb hf he reader).1, ?_⟩
        exact round_bounds_of_clock₄₅ facts S a.round r _
          (by rw [facts.hd.ModelProperties_setClock_core_s,
            facts.hd.ModelProperties_setClock_core_t])
          (by rw [facts.hd.ModelProperties_setClock_core_t]; exact hlo)
          (by rw [facts.hd.ModelProperties_setClock_core_t]; exact hhi)
    let input := Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input M S before B k
    have hcore := facts.nd.coherent_postCore S before B hbefore.1
    have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg input :=
      coherent_admit_rows₄₅ facts S.E S.hc S.cfg _ (B.attestations.take k) hcore
    have hd : Restated.Vocabulary.Proofs.NamedRawRelay.Data M td input :=
      rows_data₄₅ facts S td _ (B.attestations.take k) hcore
        (data_fields₄₅ hbefore.2.1 (facts.nd.postCore_sg_rows S before B)
          (facts.nd.postCore_timestamp_sg_vote S before B) (facts.nd.postCore_clock S before B).1)
    have hround : a.round ≤ M.round_of S.hc input.core.s ∧ M.round_of S.hc input.core.s < r := by
      rw [(Restated.Vocabulary.Proofs.NamedReceiptCallsF1.actual_f1_clock facts S rho i reader B k a
        before W hW hF1).2]
      exact hbefore.2.2
    refine ⟨input, hcoh, hd, hround, ?_⟩
    intro b hb
    apply block_call_rows_after_event₄₅ facts S rho W hW hf.receipt_outcome hF1.1 b
    rw [(Restated.Vocabulary.Proofs.NamedReceiptCallsF1.actual_carried_call facts S rho i reader B k a
      before W hW hF1).2.2.2.2]
    exact facts.hd.admit_rows_mem_mono S.hc _ (B.attestations.drop (k + 1)) b hb

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along: if the reader is in the set for
    `opening a.round` and `lo ≤ opening a.round`, after its handle of `a` in
    `[opening a.round, opening r)` at the `j`-th event read along `W`, with `a` of `r`'s window, the
    reader's store in `W (j + 1)` holds `a`'s key or an equivocation pair of `a`'s signer and round. -/
theorem call_vote_or_equivOn_RawRelay (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (r : Round) {j : Nat} {reader : V} {a : NamedAttestation V} {td : Time}
    (hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j reader (.attest a) td)
    (hlo : M.opening S.E S.hc a.round ≤ td) (hhi : td < M.opening S.E S.hc r)
    (hwindow : a.round ∈ M.latest_window S.hc.η_SG r)
    (hr : reader ∈ Hs (M.opening S.E S.hc a.round)) (hgat : lo ≤ M.opening S.E S.hc a.round) :
    Restated.Vocabulary.Proofs.NamedRawRelay.Outcome M (W (j + 1) reader).st a := by
  obtain ⟨input, hcoh, hd, hbounds, hpost⟩ :=
    relay_call_inputOn_RawRelay facts S rho Hs Xb hf r hcall hlo hhi hr hgat
  have hw := facts.fc.window_bounds hwindow
  have hexp : ¬ a.round < M.round_of S.hc input.core.s - S.hc.η_SG := by
    apply Nat.not_lt.mpr
    exact (Nat.sub_le_sub_right hbounds.2.le S.hc.η_SG).trans hw.1
  have hfuture : ¬ M.round_of S.hc input.core.s < a.round := Nat.not_lt.mpr hbounds.1
  have held_to_post (b : NamedAttestation V) (hb : b ∈ input.sg_rows b.round) :
      b ∈ (W (j + 1) reader).st.sg_rows b.round :=
    hpost b (facts.hd.admit_row_mem_mono S.hc input a b hb)
  by_cases hdup : a.confirmed ∈ M.round_votes input.core a.erase
  · obtain ⟨vote, hvote, hr', hv, hk⟩ :=
      key_representative₄₅ facts S input td hcoh hd a a.confirmed hdup
    exact Or.inl ⟨vote, held_to_post vote hvote, hr', hv, hk⟩
  · by_cases hcap : (M.round_votes input.core a.erase).card = 2
    · have htwo : 1 < (M.round_votes input.core a.erase).card := by omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
      obtain ⟨left, hl, hrl, hvl, hkl⟩ := key_representative₄₅ facts S input td hcoh hd a x hx
      obtain ⟨right, hr'', hrr, hvr, hkr⟩ := key_representative₄₅ facts S input td hcoh hd a y hy
      refine Or.inr ⟨left, right, held_to_post left hl, held_to_post right hr'',
        hrl, hrr, hvl, hvr, ?_⟩
      intro heq
      exact hxy (hkl.symm.trans (heq.trans hkr))
    · have hguard : ¬ (a.erase.round < M.round_of S.hc input.core.s - S.hc.η_SG ∨
          M.round_of S.hc input.core.s < a.erase.round ∨
          a.erase.confirmed ∈ M.round_votes input.core a.erase ∨
          (M.round_votes input.core a.erase).card = 2) := by
        rw [_root_.DecoupledConsensusModel.Sts.namedAttestation_erase_round,
          _root_.DecoupledConsensusModel.Sts.namedAttestation_erase_confirmed]
        simp only [not_or]
        exact ⟨hexp, hfuture, hdup, hcap⟩
      have hpre : a.erase ∉ M.store_sg_pool input.core a.round := by
        intro ha
        rw [← _root_.DecoupledConsensusModel.Sts.namedAttestation_erase_round] at ha
        exact hdup ((facts.hd.mem_round_votes_iff _ _ _).mpr ⟨a.erase, ha, rfl,
          _root_.DecoupledConsensusModel.Sts.namedAttestation_erase_confirmed a⟩)
      have hnew : a.erase ∈ M.store_sg_pool (M.on_sg_vote S.hc input.core a.erase) a.round := by
        have h := facts.hd.mem_on_sg_vote_sg_pool_of_not S.hc input.core a.erase hguard
        rwa [_root_.DecoupledConsensusModel.Sts.namedAttestation_erase_round] at h
      have ha := hpost a (facts.hd.NamedAdmission_admitted_original_row S.hc input a hpre hnew)
      exact Or.inl ⟨a, ha, rfl, rfl, rfl⟩

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

/-- In a run satisfying the bundle `AdmissibleFieldsOn`, the events satisfying a filter closed
    downward along the key order are exactly a prefix of the run. -/
theorem filter_eq_takeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (p : Record.Event V → Bool)
    (hdc : ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f → p f = true → p e = true) :
    ρ.events.filter p = ρ.events.take (ρ.events.filter p).length :=
  filter_eq_take_of_sorted hf.sorted p hdc

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

/-- In a run satisfying the bundle `AdmissibleFieldsOn`, an event at an index at or past the number
    of events satisfying a filter closed downward along the key order does not satisfy it. -/
theorem filter_false_of_index_geOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (p : Record.Event V → Bool)
    (hdc : ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f → p f = true → p e = true)
    {j : Nat} {e : Record.Event V} (hj : (ρ.events.filter p).length ≤ j)
    (hget : ρ.events[j]? = some e) : p e = false :=
  filter_false_of_index_ge_of_sorted hf.sorted p hdc hj hget

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

/-- In a run satisfying the bundle `AdmissibleFieldsOn`, the worlds strictly before `t` are the
    worlds after the events before `t`. -/
theorem stateBeforeTime_eq_takeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo) (t : Time) :
    Restated.Vocabulary.Execution.Run.stateBeforeTime M S ρ t =
      (Record.stateBeforeOf M S ρ (ρ.events.filter (fun e => decide (e.time < t))).length) :=
  Restated.Vocabulary.Proofs.Optimistic.stateBeforeTime_eq_take_of_sorted facts S hf.sorted t

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

/-- In a run satisfying the bundle `AdmissibleFieldsOn`, an event at an index at or past the number
    of events before `t` is at or after `t`. -/
theorem le_time_of_index_geOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {t : Time} {j : Nat} {e : Record.Event V}
    (hj : (ρ.events.filter (fun e => decide (e.time < t))).length ≤ j)
    (hget : ρ.events[j]? = some e) : t ≤ e.time :=
  Restated.le_time_of_index_ge_of_sorted hf.sorted hj hget

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

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, if the `i`-th event is `v`'s
    tick at `t`, `v`'s node state in `W i` is its node state in `W (strictEventIndex ρ t)`, or the
    wake of that node state. -/
theorem stateBefore_tick_eq_stateBeforeTimeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {i : Nat} {v : V} {t : Time}
    (hi : ρ.events[i]? = some (Record.Event.tick v t)) :
    W i v = W (strictEventIndex ρ t) v ∨ W i v = M.wake (W (strictEventIndex ρ t) v) := by
  have hle : strictEventIndex ρ t ≤ i := strict_le_tick₄₅ hf.sorted hi
  have hreach := onePath_reach₄₅ W hf.onePath (strictEventIndex ρ t) (i - strictEventIndex ρ t)
  rw [Nat.add_sub_of_le hle] at hreach
  exact Restated.Vocabulary.Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields facts S ρ hf.sorted
    hf.tickIndexUnique hi _ (mem_stateBeforeTime_along₄₅ hf.sorted hf.onePath t) (W i) hreach

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

/-- In a run satisfying the bundle `AdmissibleFieldsOn`, the event at index `j` has key at most the
    key of the event at a later index `i`. -/
theorem key_le_of_index_ltOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {j i : Nat} {e f : Record.Event V} (hji : j < i)
    (hj : ρ.events[j]? = some e) (hi : ρ.events[i]? = some f) :
    Record.Event.key e ≤ Record.Event.key f :=
  key_le_of_index_lt_of_sorted hf.sorted hji hj hi

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

/-- In a run satisfying the bundle `AdmissibleFieldsOn`, an event at an index less than the number
    of events satisfying a filter closed downward along the key order satisfies it. -/
theorem filter_true_of_index_ltOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (p : Record.Event V → Bool)
    (hdc : ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f → p f = true → p e = true)
    {j : Nat} {e : Record.Event V} (hj : j < (ρ.events.filter p).length)
    (hget : ρ.events[j]? = some e) : p e = true :=
  filter_true_of_index_lt_of_sorted hf.sorted p hdc hj hget

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

/-- On a path `W` of a run satisfying the bundle, if the `i`-th event is `v`'s tick at `t`, `v`'s
    node state in `W i` is its node state in `W (strictEventIndex ρ t)` or the wake of that node
    state. -/
private theorem tick_world_eq_strict₄₅ (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {i : Nat} {v : V} {t : Time} (hi : ρ.events[i]? = some (Record.Event.tick v t)) :
    W i v = W (strictEventIndex ρ t) v ∨ W i v = M.wake (W (strictEventIndex ρ t) v) :=
  Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hi

/-- A node state that is `m` or the wake of `m` has the store and the grade cache of `m`. -/
private theorem st_cache_of_eq_or_wake₄₅ (facts : Record.Facts M) {n m : M.N}
    (hn : n = m ∨ n = M.wake m) : n.st = m.st ∧ n.cache = m.cache := by
  rcases hn with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨(facts.nd.wake_st_record _).1, facts.nd.wake_cache _⟩

/-- Along the path `W` the bundle `AdmissibleFieldsOn` is read along: if `v` is in the set for the
    public instant `t`, `lo ≤ t ≤ horizon`, and, at every event `j` of the run that is `v`'s tick at
    `t`, `v`'s tick from its node state in `W j` has an outcome and every outcome of it sends `o`,
    then `v` emits `o` at `t` along `W`. -/
theorem emits_of_on_tick_emitOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {v : V} {t : Time} (hv : v ∈ Hs t) (hpub : PublicTime S t) (hgat : lo ≤ t)
    (hthor : t ≤ ρ.horizon)
    (hneTick : ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick v t) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) t ⇢ out)
    {o : Object V}
    (ho : ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick v t) →
      ∀ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v (W j v) t, o ∈ out.2) :
    Restated.Vocabulary.Execution.Run.emits M S ρ W v o t := by
  have hW := hf.onePath
  have hmem : Record.Event.tick v t ∈ ρ.events := hf.tick_total t hgat v hv hpub hthor
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S ρ hi (W i) (hW i).1
      (W (i + 1)) (hW i).2 with ⟨out, hout, hw⟩ | ⟨hno, -⟩
  · exact ⟨i, hi, out, hout, hw, ho i hi out hout⟩
  · obtain ⟨out, hout⟩ := hneTick i hi
    exact absurd hout (hno out)

/-- Along the path `W` the bundle `AdmissibleFieldsOn` is read along, with
    `wd = W (strictEventIndex ρ (vote_time s))`: if `0 < s`, `lo ≤ vote_time s ≤ horizon`, every
    member `v` of slot `s`'s committee in the set for the vote instant has, for every outcome `c` of
    the cache update at the vote instant on `v`'s node state in `wd`, a vote store at `s` extending
    to `B` at the node state staged from `wd v` with the cache `c`, and, at every event `j` that is
    its tick at the vote instant, its tick from its node state in `W j` has an outcome and that node
    state passes the grade-1 awake test of `s`'s round, then `VoteTickExtendsOn` holds along `W` at
    the world `wd`. -/
theorem voteTickExtends_of_extendsOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo) {s : Slot} (hs : 0 < s)
    (hhor : M.vote_time S.E s ≤ ρ.horizon) (hgat : lo ≤ M.vote_time S.E s)
    {B : NamedBlock V}
    (hal : ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s →
      ∀ c : M.Cache,
        M.onPhaseTick S.E S.hc (W (strictEventIndex ρ (M.vote_time S.E s)) v).st.core.toHealing
          (M.vote_time S.E s) (W (strictEventIndex ρ (M.vote_time S.E s)) v).cache ⇢ c →
      ∃ (tree₀ : Finset (Block V)) (H : Block V),
        Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S ρ v s
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex ρ (M.vote_time S.E s)) v).st
            (M.vote_time S.E s)) (W (strictEventIndex ρ (M.vote_time S.E s)) v).record c)
          tree₀ H B)
    (hneTick : ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s → ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick v (M.vote_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (M.vote_time S.E s) ⇢ out)
    (hrun : ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s → ∀ j : Nat,
      ρ.events[j]? = some (Record.Event.tick v (M.vote_time S.E s)) →
      M.awake_for_grade1 S v (W j v) (M.round_of S.hc s)) :
    Restated.VoteTickExtendsOn M S ρ W Hs s (W (strictEventIndex ρ (M.vote_time S.E s))) B := by
  intro v hv hcom c hc D hD
  have _hr_0 : M.reachedNode (W (strictEventIndex ρ (M.vote_time S.E s)) v) := facts.ndRun.stateBeforeOf_reachedNode S ρ (strictEventIndex ρ (M.vote_time S.E s)) (W (strictEventIndex ρ (M.vote_time S.E s))) (hf.onePath (strictEventIndex ρ (M.vote_time S.E s))).1 v
  obtain ⟨tree₀, H, halv⟩ := hal v hv hcom c hc
  have hwk : W (strictEventIndex ρ (M.vote_time S.E s)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S ρ (M.vote_time S.E s) :=
    mem_stateBeforeTime_along₄₅ hf.sorted hf.onePath _
  have hn : M.mkNode (M.ns_setClock S.E (W (strictEventIndex ρ (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex ρ (M.vote_time S.E s)) v).record c ∈
      Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S ρ v s :=
    ⟨_, hwk, c, hc, rfl⟩
  have hslot := Restated.Vocabulary.Proofs.Optimistic.voteDutyRead_slot facts S ρ v s _ hn
  have hcomv : (S.node v).val_index ∈ S.E.committee
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex ρ (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex ρ (M.vote_time S.E s)) v).record
        c).st.core.s := by
    rw [S.node_val_index, hslot]; exact hcom
  have hu := Restated.Vocabulary.Proofs.Optimistic.goldfish_vote_eq_extends_with facts S ρ v s
    _ hn halv hcomv D hD
  refine ⟨tree₀, H, _, hslot, halv, hu, ?_⟩
  have hDk := hD
  rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.duties_goldfish_vote_with_store_with_cache]
    at hDk
  have huk := hu
  rw [hslot] at huk
  rw [hslot]
  exact emits_of_on_tick_emitOn facts S Hs Xb hf hv
    (Restated.Vocabulary.Proofs.Optimistic.publicTime_vote_time facts S s) hgat hhor
    (hneTick v hv hcom)
    (fun j hj => by
      have _hr_j : M.reachedNode (W j v) := facts.ndRun.stateBeforeOf_reachedNode S ρ j (W j) (hf.onePath j).1 v
      have _hv_j : M.runs_as (W j v) v := facts.ndRun.stateBeforeOf_runs_as S ρ j (W j) (hf.onePath j).1 v
      obtain ⟨hst, hca⟩ := st_cache_of_eq_or_wake₄₅ facts (tick_world_eq_strict₄₅ facts S Hs Xb hf hj)
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem facts S v (W j v) s hs c
        (by rw [hst, hca]; exact hc) D (by rw [hst]; exact hDk) huk (hrun v hv hcom j hj))

/-- Along the path `W` the bundle `AdmissibleFieldsOn` is read along: if `v` is in the set for the
    public instant `t`, `lo ≤ t ≤ horizon`, and, at every event `j` that is `v`'s tick at `t`, `v`'s
    tick from its node state in `W j` has an outcome, then some event `j` of the run is `v`'s tick
    at `t`, and some outcome of that tick has the field `live_confirmed` of `v`'s store in
    `W (inclusiveEventIndex ρ t)`. -/
theorem live_confirmed_stateAtOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {v : V} {t : Time} (hv : v ∈ Hs t) (hpub : PublicTime S t) (hgat : lo ≤ t)
    (hthor : t ≤ ρ.horizon)
    (hneTick : ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick v t) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) t ⇢ out) :
    ∃ j : Nat, ρ.events[j]? = some (Record.Event.tick v t) ∧
      ∃ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v (W j v) t,
        (W (inclusiveEventIndex ρ t) v).st.live_confirmed = out.1.st.live_confirmed := by
  have hW := hf.onePath
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hf.tick_total t hgat v hv hpub hthor)
  have hiN : i < inclusiveEventIndex ρ t := by
    by_contra hcon
    have hp := Restated.filter_false_of_index_geOn facts S Hs Xb hf _ (downward_le t)
      (Nat.le_of_not_lt hcon) hi
    simp only [Record.Event.time, decide_eq_false_iff_not, not_le] at hp
    exact lt_irrefl _ hp
  have hno : ∀ (j : Nat) (e : Record.Event V), i + 1 ≤ j → j < inclusiveEventIndex ρ t →
      ρ.events[j]? = some e → ∀ t' : Time, e ≠ Record.Event.tick v t' := by
    intro j e hij hjN hget t' hcon
    subst hcon
    have hle : t' ≤ t := by
      have hp := Restated.filter_true_of_index_ltOn facts S Hs Xb hf _ (downward_le t) hjN hget
      simpa [Record.Event.time] using hp
    have hge : t ≤ t' := by
      have hk := Restated.key_le_of_index_ltOn facts S Hs Xb hf (Nat.lt_of_succ_le hij) hi hget
      exact Restated.time_le_of_key_le hk
    have hteq : t' = t := le_antisymm hle hge
    subst hteq
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hev : ρ.events[j] = ρ.events[i] := by rw [hje, hie]
    have := hf.tickIndexUnique hje hev
    omega
  have hreach := onePath_reach₄₅ W hW (i + 1) (inclusiveEventIndex ρ t - (i + 1))
  rw [Nat.add_sub_of_le hiN] at hreach
  have hlc := Restated.Vocabulary.Proofs.Optimistic.stateBefore_live_confirmed_of_no_tick facts S ρ v
    (inclusiveEventIndex ρ t) hiN hno (W (i + 1)) (hW (i + 1)).1 _ hreach
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S ρ hi (W i) (hW i).1
      (W (i + 1)) (hW i).2 with ⟨out, hout, hw⟩ | ⟨hno', -⟩
  · refine ⟨i, hi, out, hout, ?_⟩
    rw [hlc, hw]
  · obtain ⟨out, hout⟩ := hneTick i hi
    exact absurd hout (hno' out)

/-- Along the path `W` the bundle `AdmissibleFieldsOn` is read along: if `v` is in the set for slot
    `s`'s confirmation instant `c`, `lo ≤ c ≤ horizon`, and, at every event `j` that is `v`'s tick
    at `c`, that tick from `v`'s node state in `W j` has an outcome and that node state passes the
    grade-2 awake test under `Setup.alwaysAwake S` of slot `s + 1`'s round, then for every outcome
    `cc` of the cache update at `c` on that node state and every outcome `D` of the confirmation
    duty for slot `s`, run with `cc`'s grade contract on that node state's store with its clock set
    to `c`, the field `live_confirmed` of `v`'s store in `W (inclusiveEventIndex ρ c)` is `D`'s. -/
theorem live_confirmed_eq_updateOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {v : V} (s : Slot) (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hthor : M.confirmation_time S.E s ≤ ρ.horizon)
    (hgat : lo ≤ M.confirmation_time S.E s)
    (hneTick : ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (M.confirmation_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E s)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) v (W j v) (M.round_of S.hc (s + 1))) :
    ∀ cc : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex ρ (M.confirmation_time S.E s)) v).st.core.toHealing
        (M.confirmation_time S.E s) (W (strictEventIndex ρ (M.confirmation_time S.E s)) v).cache ⇢
        cc →
    ∀ D : M.NS, M.duties_update_confirmation_with (M.gradeContract cc) S.E S.hc
        (M.ns_setClock S.E (W (strictEventIndex ρ (M.confirmation_time S.E s)) v).st
          (M.confirmation_time S.E s)) s ⇢ D →
    (W (inclusiveEventIndex ρ (M.confirmation_time S.E s)) v).st.live_confirmed =
      D.live_confirmed := by
  intro cc hcc D hD
  obtain ⟨j, hj, out, hout, heq⟩ := live_confirmed_stateAtOn facts S Hs Xb hf hv
    (Restated.Vocabulary.Proofs.Optimistic.publicTime_confirmation_time facts S s) hgat hthor
    hneTick
  have _hr_j : M.reachedNode (W j v) := facts.ndRun.stateBeforeOf_reachedNode S ρ j (W j) (hf.onePath j).1 v
  have _hv_j : M.runs_as (W j v) v := facts.ndRun.stateBeforeOf_runs_as S ρ j (W j) (hf.onePath j).1 v
  obtain ⟨hst, hca⟩ := st_cache_of_eq_or_wake₄₅ facts (tick_world_eq_strict₄₅ facts S Hs Xb hf hj)
  rw [heq]
  have hsucc : M.confirmation_time S.E s = M.support_cutoff S.E (s + 1) :=
    facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_confirmation facts S v
    (W j v) (s + 1) (Nat.succ_pos s) (hrun j hj) out
    (by rw [← hsucc]; exact hout) cc (by rw [← hsucc, hst, hca]; exact hcc) D
    (by rw [← hsucc, Nat.add_sub_cancel, hst]; exact hD)

/-- Along the path `W` the bundle `AdmissibleFieldsOn` is read along: if the family shrinks as time
    grows, `0 < s`, slot `s`'s proposer is in the set for `s`'s confirmation instant,
    `lo ≤ p ≤ horizon` with `p` the proposal instant, at every event `j` that is the proposer's tick
    at `p` its tick from its node state in `W j` has an outcome and that node state passes the
    grade-1 awake test of `s`'s round, `c` is an outcome of the cache update at `p` on that node
    state, and `some B` is an outcome of the proposal computed with `c`'s grade contract on that
    node state's store with its clock set to `p`, then `B` has slot `s` and the proposer emits it at
    `p` along `W`. -/
theorem proposalTickOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (s : Slot) (hs : 0 < s) (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ ρ.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, ρ.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex ρ (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex ρ (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex ρ (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    B.slot = s ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S ρ W (S.E.proposer s) (.block B)
        (M.proposal_time S.E s) := by
  have _hr_0 : M.reachedNode (W (strictEventIndex ρ (M.proposal_time S.E s)) (S.E.proposer s)) := facts.ndRun.stateBeforeOf_reachedNode S ρ (strictEventIndex ρ (M.proposal_time S.E s)) (W (strictEventIndex ρ (M.proposal_time S.E s))) (hf.onePath (strictEventIndex ρ (M.proposal_time S.E s))).1 (S.E.proposer s)
  have hwk : W (strictEventIndex ρ (M.proposal_time S.E s)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S ρ (M.proposal_time S.E s) :=
    mem_stateBeforeTime_along₄₅ hf.sorted hf.onePath _
  refine ⟨Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts S ρ s (some B)
    ⟨_, ⟨_, hwk, c, hc, rfl⟩, by
      rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
      exact hB⟩ rfl, ?_⟩
  exact emits_of_on_tick_emitOn facts S Hs Xb hf
    (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E s) hprop)
    (Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S s) hgat hhor hneTick
    (fun j hj => by
      have _hr_j : M.reachedNode (W j (S.E.proposer s)) :=
        facts.ndRun.stateBeforeOf_reachedNode S ρ j (W j) (hf.onePath j).1 (S.E.proposer s)
      have _hv_j : M.runs_as (W j (S.E.proposer s)) (S.E.proposer s) :=
        facts.ndRun.stateBeforeOf_runs_as S ρ j (W j) (hf.onePath j).1 (S.E.proposer s)
      obtain ⟨hst, hca⟩ := st_cache_of_eq_or_wake₄₅ facts (tick_world_eq_strict₄₅ facts S Hs Xb hf hj)
      have hc' : M.onPhaseTick S.E S.hc (W j (S.E.proposer s)).st.core.toHealing
          (M.proposal_time S.E s) (W j (S.E.proposer s)).cache ⇢ c := by
        rw [hst, hca]; exact hc
      have hslot : S.E.slotOf (M.proposal_time S.E s) = s := facts.sch.slotOf_proposal_time S.E s
      obtain ⟨out, hout⟩ := hneTick j hj
      obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S (S.E.proposer s)
        (W j (S.E.proposer s)) (M.proposal_time S.E s) out hout (by rw [hslot]; exact hs)
        (by rw [hslot]) (by rw [hslot]) (by rw [hslot]; exact hrun j hj) c hc'
      rw [← facts.nd.gradeContract_eq_frameContract] at hD
      have hD' : M.duties_propose_block_with (M.gradeContract c) S.E S.hc S.cfg
          (S.node (S.E.proposer s))
          (M.ns_setClock S.E (W (strictEventIndex ρ (M.proposal_time S.E s)) (S.E.proposer s)).st
            (M.proposal_time S.E s)) ⇢ D := by
        rw [← hst]; exact hD
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_proposal_mem facts S (S.E.proposer s)
        (W j (S.E.proposer s)) s hs (S.node_val_index (S.E.proposer s)).symm c hc' D hD
        (facts.dt.propose_block_with_snd_of_some _ _ _ _ _ _ (some B) hB rfl D hD') (hrun j hj))

end

end DecoupledConsensusModel.Sts.Restated
