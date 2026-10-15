import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_49b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGRepresentation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGTargetCanonicality
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Head_PreparedProposalReadBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Staleness
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Internal_StoreFinality
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_56

/-!
# Fixed-root opening proposals and height progress along one path

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`, read along the path
`W` of the bundle `AdmissibleFieldsOn`: the prepared frame, anchor, cone support and parent of an
opening proposal under a fixed-height justification root, the case where the largest `h_max` is `1`,
and the pointwise and eventual height progress under the seed contract `HeightProgressSeedFromOn`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₆ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₅₆ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₆ S rho hsorted]
  exact (hW _).1

/-- For a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of `rho`
    lead to from `W m`. -/
private theorem onePath_reach₅₆ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₅₆ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₆ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W` of a run, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an
    ancestor of the one in `W n`. -/
private theorem F_mono_along₅₆ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₅₆ W hW hjn)

omit [DecidableEq V] [Fintype V] in
/-- For `t ≤ t'`, `strictEventIndex rho t ≤ strictEventIndex rho t'`. -/
private theorem strict_mono₅₆ (rho : Record.Run V) {t t' : Time} (h : t ≤ t') :
    strictEventIndex rho t ≤ strictEventIndex rho t' :=
  Restated.strict_lengths_mono rho h

/-- A block of the filtered block tree of a store is a descendant of the store's finalized block. -/
private theorem F_preceq_of_mem_filtered₅₆ (facts : Record.Facts M) (st : M.S) {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG) : Block.Preceq st.F C := by
  have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hC
  rwa [facts.sto.Sts_toHealing_F] at h

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read can
    return some `g` and the SG vote selector on `g` some block. -/
private theorem exists_actionSG₅₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, ?_⟩
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s) g
  exact ⟨g, hg, B, hB⟩

/-- In a run sorted by key, every event before index `strictEventIndex rho t` has a time before `t`. -/
private theorem time_lt_of_lt_strict₅₆ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho t → rho.events[j]? = some e →
      e.time < t := by
  intro j e hj he
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun e => decide (e.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  have hp := (List.mem_filter.mp hmem).2
  simpa only [decide_eq_true_eq] using hp

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₅₆ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- Every node state of the round-`r` action read from `before` holds the bodies `before` holds. -/
private theorem actionReadFrom_bodies₅₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `0 < r`, `t` is round `r`'s grade-1 domain time inside the
    horizon, and `c` is an outcome of `w`'s cache update at `t`, then for every outcome `fr` of the
    grade-1 store root of `w`'s store before that time, the grade-1 frame of `w`'s node state staged
    at `t` with `c` is `fr` clipped to that node state's finalized block. -/
theorem fixedRoot_preparedFrame_g1_eq_storeRoot_at_openingOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (r : Round) (hr : 0 < r) (t : Time) (_hw : w ∈ Hs t)
    (hround : (M.round_of S.hc (S.E.slotOf t)) = r)
    (hopen : M.domain S.E S.hc r .g1 = t)
    (_hhor : M.domain S.E S.hc r .g1 ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) w).st.core.toHealing t
      (W (strictEventIndex rho t) w).cache ⇢ c) :
    ∀ fr, Restated.Vocabulary.Internal.PhaseGrades.storeRoot M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 ⇢ fr →
    (M.readFrame
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).cache
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).st.core) r).g1 =
      some (fr.map
        (fun X => M.clipGrade X
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
            (W (strictEventIndex rho t) w).record c).st.core.F)) := by
  intro fr hfr
  have hwmem := mem_stateBeforeTime_along₅₆ hf.sorted hf.onePath t
  have hrawNone :
      M.phaseResult (M.cacheAtRound (W (strictEventIndex rho t) w).cache r) .g1 = none := by
    by_contra hnone
    obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hnone
    rcases Restated.Vocabulary.Proofs.NamedCacheProvenance.completed_phase_before_read_of_fields
      facts S rho hf.sorted hf.tickIndexUnique t w r .g1 root _ hwmem hroot with hzero | hdone
    · exact (Nat.ne_of_gt hr) hzero.1
    · obtain ⟨j, u, hj, hu, hdom, -⟩ := hdone
      have hlt : t < t := by
        calc
          t = M.domain S.E S.hc r .g1 := hopen.symm
          _ = u := hdom.symm
          _ < t := hu
      exact (lt_irrefl t) hlt
  have hfr' : M.freezeRoot S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (M.toHealing (W (strictEventIndex rho t) w).st.core).toFG.F
      S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) ⇢ fr := by
    rw [facts.sto.Sts_toHealing_F, ← hopen]
    exact hfr
  have hphase := facts.gr.phaseResult_onPhaseTick_domain_current S.E S.hc
    (M.toHealing (W (strictEventIndex rho t) w).st.core) t
    (by rw [← hopen, facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]; exact facts.sch.Optimistic_proposal_time_nonneg S.E _)
    (W (strictEventIndex rho t) w).cache hround hopen.symm hrawNone c hc fr hfr'
  rewrite [← facts.gr.phaseResult_g1, facts.gr.readFrame_phase, facts.nd.mkNode_cache, hphase,
    facts.nd.mkNode_st]
  simp only [facts.sto.Sts_toHealing_F, facts.nd.store_with_cache_core_F, facts.hd.setClock_core_F]
  rw [facts.gr.clipResult_some_map_clipGrade]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `0 < q`, the proposer `p` of round `q`'s opening slot is in
    `Hs tp` for that slot's proposal time `tp` inside the horizon, and the grade-1 frame of `p`'s
    node state staged at `tp` with the cache outcome `c` is `A`, then every outcome of the grade-1
    store grade of round `q` for `A` at `p`'s store before round `q`'s grade-1 domain time is
    `true`. -/
theorem namedG1At_of_preparedOpeningFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (M.opening_slot S.hc q) ∈
      Hs (M.proposal_time S.E (M.opening_slot S.hc q)))
    (hhor : M.proposal_time S.E
      (M.opening_slot S.hc q) ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    {A : Block V}
    (hframe :
      (M.readFrame
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).cache
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) q).g1 =
        some (some A)) :
    ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
        (S.E.proposer (M.opening_slot S.hc q))).st q .g1 A ⇢ b → b = true := by
  have hopen : M.domain S.E S.hc q .g1 =
      M.proposal_time S.E (M.opening_slot S.hc q) := by
    rw [facts.gr.Sts_domain_g1_eq_opening]
    exact facts.gr.opening_eq_proposal_time S.E S.hc q
  have hround : (M.round_of S.hc) (S.E.slotOf
      (M.proposal_time S.E (M.opening_slot S.hc q))) = q := by
    simpa only [facts.sch.slotOf_proposal_time] using
      (facts.gr.round_of_opening_slot_eq S.hc q)
  have hdomainHor : M.domain S.E S.hc q .g1 ≤ rho.horizon := by
    rw [hopen]
    exact hhor
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
      (S.E.proposer (M.opening_slot S.hc q))).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
      (S.E.proposer (M.opening_slot S.hc q))).st.core.F
    S.hc.η_SG q (M.early S.E S.hc q .g1) (M.late S.E S.hc q .g1)
  have hframeStore := Restated.fixedRoot_preparedFrame_g1_eq_storeRoot_at_openingOn facts
    S rho Hs Xb hf (S.E.proposer (M.opening_slot S.hc q)) q hq
    (M.proposal_time S.E (M.opening_slot S.hc q)) hprop hround hopen hdomainHor c hc fr hfr
  rw [hframe] at hframeStore
  cases fr with
  | none => cases hframeStore
  | some raw =>
      have hA := Option.some.inj (Option.some.inj hframeStore)
      intro b hb
      obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
          (S.E.proposer (M.opening_slot S.hc q))).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.F
        S.hc.η_SG q (M.early S.E S.hc q .g1) (M.late S.E S.hc q .g1) raw
      have hrawTrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl braw hbraw
      rw [hA] at hb
      exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ q .g1
        (facts.gr.q10_clip_preceq raw _) braw hbraw hrawTrue b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the committee majority, if the opening cone root lock of height
    `H`, round `q − 1` and slot `opening_slot q − 1` holds, then some member `v0` of
    `Hs (S.a (q − 1))` has a round-`(q − 1)` action block `C` that every round-`(q − 1)` action
    block of every member of that set is an ancestor of, and slot `opening_slot q − 1`'s committee
    votes into the descendants of `C`. -/
theorem fixedRoot_commonActionCeiling_of_lockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hcom : Restated.HonestCommitteesOn M S Hs) {H : Height} {q : Round} {wd : V → M.N}
    (hlock : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
      ((M.opening_slot S.hc q) - 1) wd
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))))) :
    ∃ C : Block V,
      (∃ v0 ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
        ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v0) (q - 1),
        ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
          M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ C) ∧
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
        ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
        ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
          Block.Preceq B C) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1)
        (fun X => Block.Preceq C X) := by
  classical
  have hnonempty : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)))).Nonempty :=
    Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _
  set i := strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) with hi
  let Act : V → Block V → Prop := fun v B =>
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i v) (q - 1),
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B
  have hActT : ∀ v B, Act v B → B ∈ (W i v).st.core.T := by
    rintro v B ⟨n, hn, g, hg, hB⟩
    exact Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v
      (q - 1) _ (mem_stateBeforeTime_along₅₆ hf.sorted hf.onePath _) n hn g hg B hB
  have hconeOf : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))), ∀ B, Act v B →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1)
        (fun X => Block.Preceq B X) := by
    rintro v hv B ⟨n, hn, g, hg, hB⟩
    exact hlock.canonical v hv n hn g hg B hB
  let Fin : Finset (Block V) := (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)))).biUnion
    (fun v => (W i v).st.core.T.filter (fun B => Act v B))
  have hmemFin : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))), ∀ B, Act v B →
      B ∈ Fin := fun v hv B hB =>
    Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨hActT v B hB, hB⟩⟩
  have hne : Fin.Nonempty := by
    obtain ⟨v0, hv0⟩ := hnonempty
    obtain ⟨n, hn, g, hg, B, hB⟩ := exists_actionSG₅₆ facts S (W i v0) (q - 1)
    exact ⟨B, hmemFin v0 hv0 B ⟨n, hn, g, hg, hB⟩⟩
  obtain ⟨C, hCFin, hCmax⟩ := Finset.exists_max_image Fin (fun B => B.depth) hne
  obtain ⟨v0, hv0, hCv0⟩ := Finset.mem_biUnion.mp hCFin
  have hCact : Act v0 C := (Finset.mem_filter.mp hCv0).2
  refine ⟨C, ⟨v0, hv0, hCact⟩, ?_, hconeOf v0 hv0 C hCact⟩
  intro v hv n hn g hg B hB
  have hBact : Act v B := ⟨n, hn, g, hg, hB⟩
  have hcompat := Restated.sgTargetCompatible_of_honestVotesConeOn facts S Hs Xb hf hHs hcom
    (hconeOf v hv B hBact) (hconeOf v0 hv0 C hCact)
  exact AlignedRoundLemmas.preceq_of_compatible_of_depth_le hcompat (hCmax B (hmemFin v hv B hBact))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the weight bound, if `lo ≤ S.a q`, round `q + 1`'s earliest grade
    cutoff and the next opening's proposal time are inside the horizon, every round-`q` action block
    of every member of `Hs (S.a q)` is an ancestor of `C`, the next opening proposer is in `Hs` of
    its proposal time and the finality root of its node state staged with the cache outcome `c` is
    an ancestor of `C`, and the members of `Hs (S.a q + Δ)` are awake at `q`, then every anchor that
    node state can read at round `q + 1` is an ancestor of `C`. -/
theorem fixedRoot_preparedProposalAnchor_preceq_of_previousCarriersOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc (q + 1))) ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    (hprop : S.E.proposer ((M.opening_slot S.hc (q + 1))) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (S.E.proposer (M.opening_slot S.hc (q + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (S.E.proposer (M.opening_slot S.hc (q + 1)))).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).record c).st.core).toFG) C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).record c) (q + 1) ⇢ A →
      Block.Preceq A C := by
  intro A0 hA0
  have hW := hf.onePath
  have hround : M.round_of S.hc (M.opening_slot S.hc (q + 1)) = q + 1 :=
    facts.gr.round_of_opening_slot_eq_schedule S.hc (q + 1)
  have hopen : M.domain S.E S.hc (q + 1) .g1 =
      M.proposal_time S.E (M.opening_slot S.hc (q + 1)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hroundTime : M.round_of S.hc (S.E.slotOf
      (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))) = q + 1 := by
    rw [facts.sch.slotOf_proposal_time]
    exact hround
  have hdomainHor : M.domain S.E S.hc (q + 1) .g1 ≤ rho.horizon := by
    rw [hopen]
    exact hproposalHor
  set tp := M.proposal_time S.E (M.opening_slot S.hc (q + 1)) with htp
  set p := S.E.proposer (M.opening_slot S.hc (q + 1)) with hp
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
    (W (strictEventIndex rho tp) p).record c with hn
  have hcore : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp) c := by
    rw [hn, facts.nd.mkNode_st]
  have hroundSt : M.round_of S.hc n.st.core.s = q + 1 := by
    rw [hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, htp, facts.sch.slotOf_proposal_time]
    exact hround
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho
      (M.opening_slot S.hc (q + 1)) :=
    ⟨W (strictEventIndex rho tp), mem_stateBeforeTime_along₅₆ hf.sorted hW tp, c, hc, rfl⟩
  have hA0' : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ A0 := by
    rw [hroundSt]
    exact hA0
  rcases Restated.Vocabulary.Proofs.HealingSurface.proposalAnchor_cases facts S rho
      (M.opening_slot S.hc (q + 1)) n hnmem A0 hA0' with hfg | ⟨root, A, hframe, hactive, hAA0⟩
  · rw [hfg]
    exact hroot
  rw [hAA0]
  rw [hroundSt] at hframe
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1)
  have hframeStore := Restated.fixedRoot_preparedFrame_g1_eq_storeRoot_at_openingOn facts S rho Hs Xb
    hf p (q + 1) (Nat.succ_pos q) tp hprop hroundTime hopen hdomainHor c hc fr hfr
  have hfs := hframe.symm.trans hframeStore
  rcases fr with _ | raw
  · cases hfs
  have hrootEq : root = M.clipGrade raw n.st.core.F := Option.some.inj (Option.some.inj hfs)
  have hLraw : Block.Preceq A raw := by
    have hLroot := facts.gr.preceq_of_activePrefix_eq_some hactive
    rw [hrootEq] at hLroot
    exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw _)
  have hrdmem := mem_stateBeforeTime_along₅₆ hf.sorted hW (M.domain S.E S.hc (q + 1) .g1)
  have hrawTree : raw ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.T := by
    have h := facts.gr.mem_T_of_freezeRoot_eq_some (some raw) hfr rfl
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  have hAtree : A ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.T := by
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.domain S.E S.hc (q + 1) .g1) p _ hrdmem
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    rw [facts.sto.toHealing_T] at hpc
    exact Proofs.Records.mem_of_preceq hpc.2 A raw hrawTree (preceq_eq_true_iff_Preceq.mpr hLraw)
  obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1) raw
  have hrawTrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl braw hbraw
  obtain ⟨gA, hgA⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1) A
  have hgAtrue : gA = true :=
    facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ (q + 1) .g1 hLraw braw hbraw hrawTrue gA hgA
  have hFroot : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
      (M.get_fg_root (M.toHealing n.st.core).toFG) := by
    have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      facts S rho tp p _ (mem_stateBeforeTime_along₅₆ hf.sorted hW tp)
    have h := facts.fc.preceq_get_fg_root_of_F (st := (M.toHealing n.st.core).toFG)
      (by
        rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J, hcore]
        try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
        rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
        exact preceq_eq_true_iff_Preceq.mpr hFJ)
    have hFn : n.st.core.F = (W (strictEventIndex rho tp) p).st.core.F := by
      rw [hcore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.setClock_core_F]
    rw [facts.sto.Sts_toHealing_F, hFn] at h
    rw [hopen]
    exact preceq_eq_true_iff_Preceq.mp h
  have hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F C :=
    preceq_trans_Preceq hFroot hroot
  have hlatest : q ∈ M.latest_window S.hc.η_SG (q + 1) := by
    simpa only [Nat.add_sub_cancel] using
      facts.fc.pred_mem_latest_window S.hc.η_SG (q + 1) S.hc.η_SG_ge_one (Nat.succ_pos q)
  have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
      M.early S.E S.hc (q + 1) .g1 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
      (facts.gr.q10_early_g2_le_early_g1 S (q + 1))
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((facts.gr.action_add_delta_le_next_Γ_neg1 S q).trans hcut)
  have hearlyHor : M.early S.E S.hc (q + 1) .g1 ≤ rho.horizon :=
    (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
      (by rw [← facts.gr.gammaNeg1_eq_domain_g2_succ S q]; exact hcut)
  have hearlyDomain : M.early S.E S.hc (q + 1) .g1 ≤ M.domain S.E S.hc (q + 1) .g1 :=
    (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
      (facts.gr.q10_domain_g2_lt_domain_g1 S (q + 1)).le
  have hw : p ∈ Hs (M.domain S.E S.hc (q + 1) .g1) := by
    rw [hopen]
    exact hprop
  have hwE : p ∈ Hs (M.early S.E S.hc (q + 1) .g1) := hHs _ _ hearlyDomain hw
  have hmemE : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1), v ∈ Hs (M.early S.E S.hc (q + 1) .g1) :=
    fun v hv => hHs _ _ hearlyDomain hv
  have hmemAD : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ) :=
    fun v hv => hHs _ _ (hactionDeadline.trans hearlyDomain) hv
  have hmemA : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q) :=
    fun v hv => hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) (hmemAD v hv)
  -- Every member of `Hs` at the domain time emitted a round-`q` action vote whose head is an
  -- ancestor of `C`, and that vote is an interpreted input of `p`'s grade read.
  have hvoteIn : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      ∃ (a : NamedAttestation V) (B : Block V) (Bn : NamedBlock V),
        a.val_index = v ∧ a.round = q ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a)
          (Restated.Vocabulary.Execution.Setup.a M S q) ∧
        a.confirmed = some B.root ∧ Bn.erase = B ∧ Restated.RunBlockOn M S rho W Xb Bn ∧
        Block.Preceq B C ∧
        ∀ Y, M.interpretedInputs
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
          S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v ⇢ Y → M.sgVote a.erase ∈ Y := by
    intro v hv
    have hvA := hmemA v hv
    obtain ⟨nv, hnv, g, hg, B, hB⟩ := exists_actionSG₅₆ facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc (S.node v)
      nv.st nv.record
    have hem := Restated.honest_emits_actionAttestationAtOn facts S Hs Xb hf q hvA hactionHor hpost
      (hA v (hmemAD v hv)) (fun j hj => hf.tick_outcome j _ _ hj) nv hnv D hD
    have hsg := hem.2 g hg B hB
    have haval : D.2.2.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hsg
      rw [facts.sto.sgVote_val_index_eq_val_index, namedAttestation_erase_val_index] at h
      exact h
    have haround : D.2.2.round = q := by
      have h := congrArg Protocol.SGVote.round hsg
      rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round] at h
      exact h
    have haconf : D.2.2.confirmed = some B.root := by
      have h := congrArg Protocol.SGVote.confirmed hsg
      rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed] at h
      exact h
    obtain ⟨i, hi, -, -, -, -, hall⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hW hem.1
    obtain ⟨ni, hni, -⟩ := exists_actionSG₅₆ facts S (W i v) D.2.2.round
    obtain ⟨H, hH, hHconf⟩ := hall ni hni
    have hHbody : H ∈ (W i v).st.bodies := by
      rw [← actionReadFrom_bodies₅₆ facts S _ _ ni hni]
      exact hH
    have hHrun : Restated.RunBlockOn M S rho W Xb H :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hHbody
    have hBmem : B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T :=
      Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v q _
        (mem_stateBeforeTime_along₅₆ hf.sorted hW _) nv hnv g hg B hB
    obtain ⟨Bn, hBnerase, hBnrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb
      hf (hHsXb _ hv) (Restated.Vocabulary.Execution.Setup.a M S q) hBmem
    have hrootEq : H.erase.root = Bn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hBnerase]
      exact Option.some.inj (hHconf.symm.trans haconf)
    have hHB : H.erase = Bn.erase :=
      Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHrun hBnrun hrootEq
    have hBC : Block.Preceq B C := hupper v hvA nv hnv g hg B hB
    have hHC : Block.Preceq H.erase C := by
      rw [hHB, hBnerase]
      exact hBC
    have hmem := Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb .g1 hlatest (hmemE v hv) hwE
      ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩ hHC hFC
      (by rw [haround]; exact hpost)
      (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
      hearlyDomain hearlyHor
    exact ⟨D.2.2, B, Bn, haval, haround, hem.1, haconf, hBnerase, hBnrun, hBC, hmem⟩
  have hwin : ∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
        S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v ⇢ ins v) →
      S.E.electorate.weightOf (Finset.univ \ Hs (M.domain S.E S.hc (q + 1) .g1)) <
        S.E.electorate.weightOf ((Hs (M.domain S.E S.hc (q + 1) .g1)).filter
          fun v => (ins v).Nonempty) := by
    intro ins hins
    have hsubset : Hs (M.domain S.E S.hc (q + 1) .g1) ⊆
        (Hs (M.domain S.E S.hc (q + 1) .g1)).filter fun v => (ins v).Nonempty := by
      intro v hv
      obtain ⟨a, -, -, -, -, -, -, -, -, -, hmem⟩ := hvoteIn v hv
      exact Finset.mem_filter.2 ⟨hv, ⟨_, hmem _ (hins v)⟩⟩
    exact lt_of_lt_of_le
      (by simpa only [HonestWeightMajority] using
        honestWeightMajorityOn_of_belowOneThirdOn hfb _ hdomainHor)
      (S.E.electorate.weightOf_mono hsubset)
  obtain ⟨v, hv, I, hI, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
    facts.gr.exists_honest_max_positive_supporter_of_relativeGrade S.E S.hc hwin gA hgA hgAtrue
  obtain ⟨a, B, Bn, haval, haround, hemit, haconf, hBnerase, hBnrun, hBC, hmem⟩ := hvoteIn v hv
  have hqle : q ≤ u.round := by
    have h := hmax (M.sgVote a.erase) (hmem I hI)
    rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round, haround] at h
    exact h
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v
  obtain ⟨bu, hbu⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    (M.early S.E S.hc (q + 1) .g1) u
  have huraw := ((facts.gr.mem_interpretedInputs_iff I hI R hR bu hbu).mp hu).1
  obtain ⟨b, -, hbround, hbproj, huwindow, -, hbemit⟩ :=
    Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (M.domain S.E S.hc (q + 1) .g1)
      (M.early S.E S.hc (q + 1) .g1) p S.hc.η_SG (q + 1) v hv R hR huraw
  have hule : u.round ≤ q := Nat.le_of_lt_succ (facts.fc.window_bounds huwindow).2
  have huroundEq : u.round = q := Nat.le_antisymm hule hqle
  have hba : b = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hbemit hemit
    ((hbround.trans huroundEq).trans haround.symm)
  have huEq : u = M.sgVote a.erase := by
    rw [← hbproj, hba]
  have hheadRoot : head.root = B.root := by
    have huconf := congrArg Protocol.SGVote.confirmed huEq
    rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed, hconf, haconf] at huconf
    exact Option.some.inj huconf
  have hheadMem : head ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  obtain ⟨Headn, hHeaderase, hHeadrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts
    S Hs Xb hf (hHsXb _ hw) (M.domain S.E S.hc (q + 1) .g1) hheadMem
  have hheadBnRoot : Headn.erase.root = Bn.erase.root := by
    rw [hHeaderase, hBnerase]
    exact hheadRoot
  have hheadB : head = B := by
    rw [← hHeaderase, ← hBnerase]
    exact Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHeadrun hBnrun hheadBnRoot
  rw [hheadB] at hAhead
  exact preceq_trans_Preceq hAhead hBC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `J` is a run block with `J.erase` an ancestor of `C`,
    `v ∈ Hs (S.a r)` holds `C` before `S.a r`, the proposer of slot `s` is in `Hs` of that slot's
    proposal time inside the horizon, `lo ≤ S.a r`, `S.a r + Δ ≤ proposal_time s`, and the
    proposer's store before its proposal time has finality root `J.erase` and `h_max` at most `J`'s
    height plus one, then that store holds `C` and `J`. -/
theorem fixedRoot_actionCarrier_mem_proposerReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {J : NamedBlock V} {C : Block V} {v : V}
    (hJrun : Restated.RunBlockOn M S rho W Xb J) (hJC : Block.Preceq J.erase C)
    {r : Round} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hCsource : C ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T)
    {s : Slot} (hprop : S.E.proposer s ∈ Hs (M.proposal_time S.E s))
    (hproposalHor : M.proposal_time S.E s ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E s)
    (hroot : M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E s))
          (S.E.proposer s)).st.core).toFG = J.erase)
    (hcap : (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.h_max ≤
      (M.derive_named S.E S.cfg J).h + 1) :
    C ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T ∧
      J ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.bodies := by
  have hwp := mem_stateBeforeTime_along₅₆ hf.sorted hf.onePath (M.proposal_time S.E s)
  have hrootMem : M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E s))
      (S.E.proposer s)).st.core).toFG ∈
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
    have hroots :=
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        (M.proposal_time S.E s) (S.E.proposer s) _ hwp).1.1.2
    exact Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts _ hroots
  obtain ⟨K, hKbody, hKerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.proposal_time S.E s) (S.E.proposer s) _ hwp hrootMem
  have hKrun : Restated.RunBlockOn M S rho W Xb K :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hprop) hKbody
  have hKroot : K.root = J.root := by
    calc
      K.root = K.erase.root := (Proofs.NamedWire.erase_root K).symm
      _ = (M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E s))
          (S.E.proposer s)).st.core).toFG).root :=
        congrArg Block.root hKerase
      _ = J.erase.root := congrArg Block.root hroot
      _ = J.root := Proofs.NamedWire.erase_root J
  have hKJ : K = J := by
    apply hf.rootCollisionFree.root_injective
      K J hKrun hJrun K J (Or.inl (Proofs.NamedAncestry.named_self K))
      (Or.inr (Proofs.NamedAncestry.named_self J)) hKroot
  have hJbody : J ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.bodies := by
    rw [← hKJ]
    exact hKbody
  have hJactive : J.erase ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E s))
        (S.E.proposer s)).st.core).toFG :=
    Restated.Vocabulary.Proofs.HealingSurface.mem_filtered_of_mem_tree_of_exactFGRoot_heightCap facts
      S rho (S.E.proposer s) (M.proposal_time S.E s) _ hwp hJbody rfl hroot
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self J.erase)) hcap
  rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts
      S Hs Xb hf v ((Restated.Vocabulary.Execution.Setup.a M S r)) hCsource with
    hgen | ⟨Cn, i, t, hCnerase, hacc, ht⟩
  · rw [hgen]
    exact ⟨(Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf (S.E.proposer s)
      (M.proposal_time S.E s) (M.proposal_time S.E s)).1, hJbody⟩
  · have hCpos : 0 < Cn.slot := by
      rw [← Proofs.NamedWire.erase_slot Cn]
      exact Nat.zero_lt_of_lt
        (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
    have hFp : Block.Preceq
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.F Cn.erase := by
      rw [hCnerase]
      exact preceq_trans_Preceq (F_preceq_of_mem_filtered₅₆ facts _ hJactive) hJC
    have hFhist : ∀ j : Nat,
        j ≤ (rho.events.filter (fun e =>
          decide (e.time < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))).length →
        Block.Preceq (W j (S.E.proposer s)).st.core.F Cn.erase := by
      intro j hj
      have hjp : j ≤ strictEventIndex rho (M.proposal_time S.E s) :=
        hj.trans (strict_mono₅₆ rho hdelay)
      exact preceq_trans_Preceq (F_mono_along₅₆ facts S hf.onePath (S.E.proposer s) hjp) hFp
    have hvMax : v ∈ Hs (max t lo) := hHs _ _ (max_le ht.le hpost) hv
    have hpOut : S.E.proposer s ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) :=
      hHs _ _ hdelay hprop
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W (S.E.proposer s) C
        ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := by
      have hadm' := Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hvMax hpOut hCpos hacc ht hpost rfl
          (le_trans hdelay hproposalHor) hFhist
      rw [hCnerase] at hadm'
      exact hadm'
    have hCmem := (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hdelay).1
    exact ⟨hCmem, hJbody⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `support_cutoff s` is inside the horizon, the proposer of slot `s + 1` is in
    `Hs (support_cutoff s)`, the finality root of its node state staged at its proposal time with
    the cache outcome `c` is an ancestor of `T`, and slot `s`'s committee votes into the descendants
    of `T`, then for every support view of that node state its views give cone support for the
    descendants of `T` over `Hs (confirmation_time s)`. -/
theorem fixedRoot_preparedProposalConeSupport_of_namedConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs) {s : Slot}
    (hs : 0 < s) (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.support_cutoff S.E s)) {T : Block V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
      (M.proposal_time S.E (s + 1))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
        c).st.core).toFG) T)
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq T X)) :
    ∀ L : List (GoldfishVote V),
      M.proposer_support_view
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
          (M.proposal_time S.E (s + 1)))
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
          c).st.core).toFG.toSG.toGoldfishStore
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
          (M.proposal_time S.E (s + 1)))
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
          c).st.core.s ⇢ L →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
        c).st.core.T
      (M.proposer_view
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
          (M.proposal_time S.E (s + 1)))
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
          c).st.core).toFG.toSG.toGoldfishStore
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
          (M.proposal_time S.E (s + 1)))
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
          c).st.core.s).toFinset
      L.toFinset
      (M.proposer_view
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
          (M.proposal_time S.E (s + 1)))
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
          c).st.core).toFG.toSG.toGoldfishStore
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
          (M.proposal_time S.E (s + 1)))
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
          c).st.core.s).toFinset
      ((M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
        c).st.core.s - 1)
      (Hs (M.confirmation_time S.E s))
      (fun X => Block.Preceq T X) := by
  intro L hL
  set tp := M.proposal_time S.E (s + 1) with htp
  set p := S.E.proposer (s + 1) with hp
  set wp := W (strictEventIndex rho tp) p with hwp
  set n := M.mkNode (M.ns_setClock S.E wp.st tp) wp.record c with hn
  have hvoteConf : M.vote_time S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E s
  have hsuppConf : M.support_cutoff S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s
  have hpropConf : tp ≤ M.confirmation_time S.E s :=
    (facts.sch.proposal_time_succ_lt_confirmation_time S.E s).le
  have hcore : n.st = M.store_with_cache (M.ns_setClock S.E wp.st tp) c := by
    rw [hn, facts.nd.mkNode_st]
  have htickStore : (M.ns_setClock S.E wp.st tp).core =
      Restated.Vocabulary.Proofs.Optimistic.tickStore M S wp.st.core tp :=
    setClock_core_tickStore₅₆ facts S wp tp
  have hslot : n.st.core.s = s + 1 := by
    rw [hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, htp, facts.sch.slotOf_proposal_time]
  have hprev : n.st.core.s - 1 = s := by
    rw [hslot]
    exact Nat.add_sub_cancel s 1
  have hT : n.st.core.T = wp.st.core.T := by
    rw [hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hrootTick : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        wp.st.core tp)).toFG) T := by
    rw [← htickStore]
    have h := hroot
    rw [hcore, facts.nd.store_with_cache_get_fg_root] at h
    exact h
  have hresolve := Restated.headsResolveIn_proposerDutyStore_of_postHealingConeOn facts
    S Hs Xb hf hHs hHsXb hpost hhor hprop hrootTick hnames
  have hss : L.toFinset ⊆ (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      n.st.core.s).toFinset := by
    intro u hu
    obtain ⟨b, hb⟩ := facts.sto.resolved_nonempty
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T u
    have hmem := (facts.fc.mem_proposer_support_view_iff _ _ u L hL b hb).mp
      (List.mem_toFinset.mp hu)
    rw [List.mem_toFinset, facts.fc.proposer_view_eq]
    exact hmem.1
  have hne : ∀ x ∈ S.E.committee s, x ∈ Hs (M.confirmation_time S.E s) →
      M.equivocates (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        n.st.core.s).toFinset x = false := by
    intro x _ hx
    have hno := Restated.pool_no_honest_equivocationOn facts S Hs Xb hf hHs
      p (strictEventIndex rho tp) (T := tp)
      (fun j e hj he => (time_lt_of_lt_strict₅₆ hf.sorted tp j e hj he).le) s (hHs _ _ hpropConf hx)
    rw [facts.fc.proposer_view_toFinset, facts.sto.toHealing_gs_pool, hprev, hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_pool]
    exact hno
  have hvote : ∀ x ∈ S.E.committee s, x ∈ Hs (M.confirmation_time S.E s) →
      ∃ X : Block V, Block.Preceq T X ∧
        X.slot ≤ s ∧
        (⟨x, s, X.root⟩ : GoldfishVote V) ∈ L.toFinset ∧
        Block.find? n.st.core.T X.root = some X := by
    intro x hxCommittee hxHonest
    obtain ⟨X, hX, hXrun, hXemit⟩ := hnames x (hHs _ _ hvoteConf hxHonest) hxCommittee
    have hhead : Restated.HonestHeadOn M S rho W Hs Xb s X.erase :=
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    obtain ⟨hfind, -⟩ := hresolve X.erase hhead
    have hfindn : Block.find? n.st.core.T X.erase.root = some X.erase := by
      rw [hcore, facts.nd.store_with_cache_core_T, htickStore]
      exact hfind
    have hcut := Restated.gfVote_in_cutoff_view_after_gstOn facts
      S Hs Xb hf hHs (hHs _ _ hsuppConf hxHonest) hs hpost hXemit rfl hprop tp tp
      (facts.sch.support_cutoff_le_proposal_time_succ S.E s)
      (facts.sch.support_cutoff_le_proposal_time_succ S.E s) hhor
    rw [mem_beforeCutoff_iff] at hcut
    have hpool' : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ wp.st.core.gf_votes s :=
      (facts.sto.mem_store_pool_iff _ _ _).mp hcut.1
    have hXmem : X.erase ∈ wp.st.core.T := by
      rw [← hT]
      exact Proofs.HealingLemmas.find?_mem hfindn
    have hXslot : X.erase.slot ≤ s :=
      Restated.emitted_vote_head_slot_le_of_store_memOn facts S Hs Xb hf
        (hHsXb _ hxHonest) (hHsXb _ hprop) hXemit rfl hXmem rfl
    have hraw : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.gf_votes
          ((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s - 1) := by
      rw [facts.sto.toHealing_gs_gf_votes, facts.sto.toHealing_s, hprev, hcore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.setClock_core_gf_votes]
      exact hpool'
    obtain ⟨b, hb⟩ := facts.sto.resolved_nonempty
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T (⟨x, s, X.erase.root⟩ : GoldfishVote V)
    have hbt : b = true := (facts.sto.resolved_eq_true_iff _ _ b hb).mpr
      ⟨X.erase, by rw [facts.sto.toHealing_gs_T]; exact hfindn, hXslot⟩
    have hL' : M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s ⇢ L := by
      rw [facts.sto.toHealing_s]
      exact hL
    have hsupport : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ L.toFinset :=
      List.mem_toFinset.mpr
        ((facts.fc.mem_proposer_support_view_iff _ _ _ L hL' b hb).mpr ⟨hraw, hbt⟩)
    exact ⟨X.erase, hX, hXslot, hsupport, hfindn⟩
  have hcone := Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts (E := S.E)
    (T := n.st.core.T)
    (votes := (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      n.st.core.s).toFinset) (support := L.toFinset)
    (late := (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      n.st.core.s).toFinset) (s := s)
    (Hon := Hs (M.confirmation_time S.E s)) (tgt := fun X => Block.Preceq T X)
    (hcom s) (subset_refl _) hss hne hvote
  rw [hprev]
  exact hcone

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if the finality root of the proposer's node state `n` staged at slot
    `s`'s proposal time with the cache outcome `c` is compatible with `P`, `n`'s store has a
    canonical-cone witness for `P`, every SG root `n` can read is an ancestor of `P`, `n`'s views
    give cone support for the descendants of `P` over `X`, and `n`'s proposer view is a valid vote
    set, then `P` is an ancestor of the parent of every proposal input `n` can compute. -/
theorem fixedRoot_preparedProposalHead_preceq_of_coneOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) (X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {P : Block V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    (hcompat : Block.compatible
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core).toFG)
      P = true)
    (hwitness : Restated.Vocabulary.Proofs.HealingSurface.CanonicalConeWitness M
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core P)
    (hanchor : ∀ R : Block V, M.get_sg_root_with (M.gradeContract c) S.E S.hc
      (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.s) ⇢ R →
      Block.Preceq R P)
    (hsupport : ∀ L : List (GoldfishVote V),
      M.proposer_support_view
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core).toFG.toSG.toGoldfishStore
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.s ⇢ L →
      Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.T
        (M.proposer_view
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core).toFG.toSG.toGoldfishStore
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.s).toFinset
        L.toFinset
        (M.proposer_view
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core).toFG.toSG.toGoldfishStore
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.s).toFinset
        ((M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.s - 1) X
        (fun X => Block.Preceq P X))
    (hvalid : Protocol.VoteSetValid S.E
      ((M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.s - 1)
      (M.proposer_view
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core).toFG.toSG.toGoldfishStore
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core.s).toFinset) :
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer s))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core) ⇢ I →
      Block.Preceq P I.parent := by
  intro I hI
  have hwp := mem_stateBeforeTime_along₅₆ hf.sorted hf.onePath (M.proposal_time S.E s)
  set wp := W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s) with hwp_def
  set n := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) wp.record c with hn_def
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) c := by
    rw [hn_def, facts.nd.mkNode_st]
  have hpc : Restated.Vocabulary.Internal.ParentClosed M n.st.core := by
    have h := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.proposal_time S.E s) (S.E.proposer s) _ hwp
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at h ⊢
    rw [facts.sto.toHealing_T] at h ⊢
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
    exact h
  have hFJ : Block.Preceq n.st.core.F n.st.core.J := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.proposal_time S.E s) (S.E.proposer s) _ hwp
  obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing n.st.core)
    (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s).toFinset
    L.toFinset ((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s - 1)
  have hparent : I.parent = H :=
    facts.dt.with_proposal_input_id_parent (M.gradeContract c) S.E S.hc
      (S.node (S.E.proposer s)) (M.toHealing n.st.core) I hI L hL H hH
  rw [hparent]
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  have hR' : M.get_sg_root_with (M.gradeContract c) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s) ⇢ R := by
    rw [facts.sto.toHealing_s]
    exact hR
  have hfgsg : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) R :=
    facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract c S.E S.hc
      (M.toHealing n.st.core) _ R hR
  rcases Restated.Vocabulary.Proofs.HealingSurface.canonicalFloor_preceq_root_or_mem_filtered facts
      hpc hFJ hcompat hwitness with hProot | hPfiltered
  · have hsghead := Restated.Vocabulary.Proofs.HealingSurface.get_sg_root_with_preceq_get_head_with
      facts (M.gradeContract c) S.E S.hc (M.toHealing n.st.core) _ _ _ R hR' H hH
    exact preceq_trans_Preceq hProot (preceq_trans_Preceq hfgsg hsghead)
  · have hPT : P ∈ n.st.core.T := by
      have h := facts.fc.get_filtered_block_tree_subset _ hPfiltered
      rw [facts.sto.toHealing_T] at h
      exact h
    have hpc' := hpc
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc'
    rw [facts.sto.toHealing_T] at hpc'
    have hpath : ∀ C : Block V, Block.Preceq R C → C ≠ R → Block.Preceq C P →
        C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
      intro C hAC _ hCP
      have hCT : C ∈ n.st.core.T :=
        Proofs.Records.mem_of_preceq hpc'.2 C P hPT (preceq_eq_true_iff_Preceq.mpr hCP)
      exact facts.fc.mem_filtered_of_preceq
        (by
          rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J]
          exact preceq_eq_true_iff_Preceq.mpr hFJ)
        hPfiltered (by rw [facts.sto.toHealing_T]; exact hCT)
        (preceq_eq_true_iff_Preceq.mpr hCP)
        (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hfgsg hAC))
    have hsup := hsupport L (by rw [← facts.sto.toHealing_s]; exact hL)
    have hfc := (facts.gr.get_head_with_eq_fork_choice (M.gradeContract c) S.E S.hc
      (M.toHealing n.st.core) _ _ _ R hR' H).mp hH
    rw [facts.sto.toHealing_s] at hfc
    refine facts.fc.goldfish_passes_cone S.E _ _ _ _ _ _ _ _ X hsup.majority ?_ ?_ ?_ ?_ ?_
      (hanchor R hR) hpath H hfc
    · exact subset_refl _
    · simpa only [facts.sto.toHealing_s] using hsup.sub
    · simpa only [facts.sto.toHealing_s] using hsup.no_equiv
    · simpa only [facts.sto.toHealing_T] using hsup.vote
    · simpa only [facts.sto.toHealing_s] using hvalid

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- If `FixedHeightJustificationRootAtReadOn` holds for `w` at `H` in the world `wd`, some run block
    `J` read through `Xb` along `W` erases to the justified block of `w`'s store in `wd` and has
    height `H − 1`. -/
theorem fixedRoot_namedTarget_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {W : Nat → V → M.N}
    {H : Height} {w : V} {read : Time} {wd : V → M.N}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read wd) :
    ∃ J : NamedBlock V,
      J.erase = (wd w).st.J ∧
        Restated.RunBlockOn M S rho W Xb J ∧
          (M.derive_named S.E S.cfg J).h = H - 1 := by
  obtain ⟨D, _hDbody, hDrun, hjust⟩ := h.carrierExists
  have hhj : (M.derive_named S.E S.cfg D).h_j = H - 1 := by
    exact hjust.2.trans h.fixedTarget.justificationHeight
  have hhjNe : (M.derive_named S.E S.cfg D).h_j ≠ 0 := by
    rw [hhj]
    exact Nat.ne_of_gt h.targetHeightPositive
  obtain ⟨J, hJD, hJerase, hJheight⟩ :=
    (facts.cs.justified_ancestor_height S.E S.cfg D).resolve_left hhjNe
  refine ⟨J, hJerase.trans hjust.1, ?_, ?_⟩
  · exact Restated.blockInRun_of_ancestorOn facts S rho W Xb hDrun hJD
  · rw [hJheight, hhj]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `w ∈ Xb` and `B` is a named body of `w`'s store before `read`,
    then `B` is a run block read through `Xb` along `W`. -/
theorem fixedRoot_runBlock_of_body_at_readOn_FixedHeightRootOpeningParent (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) {read : Time} {B : NamedBlock V}
    (hB : B ∈ (W (strictEventIndex rho read) w).st.bodies) :
    Restated.RunBlockOn M S rho W Xb B :=
  Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open scoped DC

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₆s (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₅₆s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₆s S rho hsorted]
  exact (hW _).1

/-- One delay after round `r`'s phase-`p` domain time is strictly before `S.a r`. -/
private theorem domain_add_delta_lt_action₅₆s (facts : Record.Facts M) (S : Setup V) (r : Round)
    (p : Protocol.Phase) :
    M.domain S.E S.hc r p + S.E.Δ < Restated.Vocabulary.Execution.Setup.a M S r := by
  have h := facts.gr.domain_add_five_delta_le_action S r p
  have hΔ := S.E.Δ_pos
  show _ < M.a S.hc S.E.Δ r
  linarith

/-- A named block whose chain state is at height `1` has genesis as its height entry block. -/
private theorem derivedTarget_eq_genesis_of_height_one₅₆s (facts : Record.Facts M)
    (E : Env V) (cfg : Protocol.HeightConfig) : ∀ B : NamedBlock V,
    (M.derive_named E cfg B).h = 1 → (M.derive_named E cfg B).T_h = Block.genesis := by
  intro B
  induction B with
  | genesis =>
    intro _
    have h := facts.csAdded.derive_named_T_h_preceq E cfg NamedBlock.genesis
    rw [erase_named_genesis] at h
    simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using h
  | node p s root votes support rows proposer ih =>
    intro hheight
    rw [facts.csAdded.derive_named_node] at hheight ⊢
    rcases facts.csAdded.transition_height_entry_cases E cfg (M.derive_named E cfg p)
        (.node p s root votes support rows proposer) with hstay | hstep
    · rw [hstay.2]
      exact ih (hstay.1.symm.trans hheight)
    · exfalso
      have hp : 1 ≤ (M.derive_named E cfg p).h := facts.cs.one_le_derive_named_h E cfg p
      have heq : (M.derive_named E cfg p).h + 1 = 1 := hstep.1.symm.trans hheight
      have hz : (M.derive_named E cfg p).h = 0 := by
        simpa only [Nat.add_eq_one_iff, Nat.one_ne_zero, and_false, or_false, and_true] using heq
      rw [hz] at hp
      exact Nat.not_succ_le_zero 0 hp

/-- Under the bundle along `W`, if the largest `h_max` over `Hs (S.a start)` at `S.a start` is `Mh`,
    `lo ≤ S.a start`, `S.a start + 1 + Δ ≤ read`, the largest `h_max` over `Hs read` at `read` is at
    most `Mh`, `read` is inside the horizon and `2 ≤ Mh`, then either some member of `Hs read` has a
    fixed-height justification root at `Mh` before `read`, or every member of `Hs read` has, before
    `read`, `h_j + 2 ≤ Mh` and `h_max = Mh`. -/
theorem frontierRegime_at_read_l56 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon)) (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {start : Round} {Mh : Height} {read : Time}
    (hM : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) u).st.core.h_max) = Mh)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S start))
    (hrelayStep : (Restated.Vocabulary.Execution.Setup.a M S start) + 1 + S.E.Δ ≤ read)
    (hcap : ((Hs read).sup fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) ≤ Mh)
    (hhor : read ≤ rho.horizon) (h2 : 2 ≤ Mh) :
    (∃ u ∈ Hs read,
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read))) ∨
    (∀ w ∈ Hs read,
      (W (strictEventIndex rho read) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho read) w).st.core.h_max = Mh) := by
  set n := inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start) with hn
  have hpred : Mh - 1 + 1 = Mh :=
    Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans h2)
  have hprefixSucc : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
      (W n u).st.core.h_max) = Mh - 1 + 1 := by
    rw [hpred]; exact hM
  obtain ⟨holder, hholder, carrier, hcarrierMem, hcarrierRun, hcarrierHeight⟩ :=
    Restated.exists_honest_exactHMaxCarrierAtPrefixOn facts S Hs Xb
      (Hs (Restated.Vocabulary.Execution.Setup.a M S start)) hf (hHsXb _) n (Mh - 1) hprefixSucc
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n holder
    (W n) (hf.onePath n).1).1.1.1
  have hcarrierT : carrier.erase ∈ (W n holder).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hcarrierMem
  have hcarrier : Restated.HonestHMaxCarrierAtOn M S rho W Hs Xb
      (Restated.Vocabulary.Execution.Setup.a M S start) (W n) Mh holder carrier.erase :=
    { holderHonest := hholder
      processed := hcarrierT
      namedWitness := ⟨carrier, rfl, hcarrierRun, by rw [hcarrierHeight, hpred]⟩ }
  have hexact : ∀ w ∈ Hs read, (W (strictEventIndex rho read) w).st.core.h_max = Mh := by
    intro w hw
    exact (hcarrier.visibleWithExactFrontier_after_oneDelay_of_noRise
      facts S Hs Xb hf hHs hHsXb hsb hpost hrelayStep hhor hcap w hw).2
  by_cases hgate : ∃ u ∈ Hs read, (W (strictEventIndex rho read) u).st.core.h_j = Mh - 1
  · rcases hgate with ⟨u, hu, hju⟩
    left
    refine ⟨u, hu, ?_⟩
    obtain ⟨C, hC, hCrun, hjust⟩ :=
      Restated.justificationCarrierAtStrictRead_l1On facts S Hs Xb hf (hHsXb _ hu) read
    have hjust' : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg C
        (W (strictEventIndex rho read) u).st.J (Mh - 1) := by
      rw [← hju]; exact hjust
    have hMsubPos : 0 < Mh - 1 :=
      Nat.sub_pos_iff_lt.mpr ((by decide : 1 < 2).trans_le h2)
    have hcert : Restated.CertificateOn M S rho W Xb (Mh - 1)
        (W (strictEventIndex rho read) u).st.J.root :=
      Restated.certificate_of_justifiedRunBlock_l1On facts S Xb hCrun hjust'
        (Nat.ne_of_gt hMsubPos)
    refine
      { readerHonest := hu
        readInHorizon := hhor
        carrierExists := ⟨C, hC, hCrun, hjust⟩
        targetHeightPositive := hMsubPos
        fixedTarget :=
          { frontier := hexact u hu
            justificationHeight := hju
            gate := by rw [hexact u hu, hju, hpred]
            certificate := hcert
            uniqueAtHeight := ?_
            targetBlock := Restated.runBlockOf_justified_atStrictRead_l1On facts S Hs Xb hf
              (hHsXb _ hu) read } }
    intro T hT
    exact Restated.certificateTarget_uniqueOn facts S Hs Xb hf hHs hfb (Mh - 1) T
      (W (strictEventIndex rho read) u).st.J.root hT hcert
  · right
    intro w hw
    have hbelow : (W (strictEventIndex rho read) w).st.core.h_j < Mh := by
      have hbelow' := Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime
        facts S rho read w _ (mem_stateBeforeTime_along₅₆s hf.sorted hf.onePath read)
      have hbelow'' : (W (strictEventIndex rho read) w).st.core.h_j <
          (W (strictEventIndex rho read) w).st.core.h_max := by
        simpa only [Restated.Vocabulary.Internal.JustificationBelowMax] using hbelow'
      rw [← hexact w hw]; exact hbelow''
    have hne : (W (strictEventIndex rho read) w).st.core.h_j ≠ Mh - 1 := by
      intro heq
      exact hgate ⟨w, hw, heq⟩
    refine ⟨?_, hexact w hw⟩
    have hlt : (W (strictEventIndex rho read) w).st.core.h_j < Mh - 1 :=
      lt_of_le_of_ne (Nat.le_pred_of_lt hbelow) hne
    have hstep := Nat.add_le_add_right (Nat.succ_le_of_lt hlt) 1
    rw [hpred] at hstep
    exact hstep

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `w ∈ Hs read` and the largest `h_max` over `Hs read` at `read` is
    at most `1`, then `w`'s store before `read` has finality root genesis and `h_max = 1`. -/
theorem honestStrictRead_root_eq_genesis_and_hMax_eq_oneOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {read : Time} (hw : w ∈ Hs read)
    (hcap : ((Hs read).sup fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) ≤ 1) :
    M.get_fg_root (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG = Block.genesis ∧
      (W (strictEventIndex rho read) w).st.core.h_max = 1 := by
  have hmem := mem_stateBeforeTime_along₅₆s hf.sorted hf.onePath read
  have hlocalUpper : (W (strictEventIndex rho read) w).st.core.h_max ≤ 1 :=
    ((Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf w read).trans
      (Finset.le_sup (f := fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) hw)).trans
      hcap
  obtain ⟨D, _hDbody, hDheight⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime facts S rho read w _ hmem
  have hlocalLower : 1 ≤ (W (strictEventIndex rho read) w).st.core.h_max := by
    rw [← hDheight]
    exact facts.cs.one_le_derive_named_h S.E S.cfg D
  have hlocal : (W (strictEventIndex rho read) w).st.core.h_max = 1 :=
    Nat.le_antisymm hlocalUpper hlocalLower
  have hbelow : (W (strictEventIndex rho read) w).st.core.h_j <
      (W (strictEventIndex rho read) w).st.core.h_max :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime facts S rho
      read w _ hmem
  have hhj : (W (strictEventIndex rho read) w).st.core.h_j = 0 := by
    rw [hlocal] at hbelow
    exact Nat.lt_one_iff.mp hbelow
  obtain ⟨Jc, _hJbody, hJ, hJh⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w _ hmem
  have hJgen : (W (strictEventIndex rho read) w).st.core.J = Block.genesis := by
    rw [← hJ]
    exact facts.cs.justified_zero_is_genesis S.E S.cfg Jc (hJh.trans hhj)
  have hgate : (W (strictEventIndex rho read) w).st.core.h_max =
      (W (strictEventIndex rho read) w).st.core.h_j + 1 := by
    rw [hlocal, hhj]
  exact ⟨(facts.fc.get_fg_root_toHealing_of_eq _ hgate).trans hJgen, hlocal⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the committee majority, if `2 + delayExtra ≤ q`, round `q` is a
    carrier round, `p + Δ < endpoint` for the proposal time `p` of `q`'s opening slot `s`,
    `endpoint` is inside the horizon, the largest `h_max` over `Hs endpoint` is at most `1`,
    `lo ≤ p`, and the proposer passes the grade-1 awake test at `p`, then every parent of every
    block the proposer can propose at `p` has its target slot plus the timeout delay at most `s`. -/
theorem heightOne_opening_timeoutMatureOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {delayExtra : Nat}
    (hdelay : TimeoutDelayBound S delayExtra) {q : Round}
    (hqWait : 2 + delayExtra ≤ q) (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    {endpoint : Time}
    (hproposalEnd :
      M.proposal_time S.E ((M.opening_slot S.hc q)) + S.E.Δ < endpoint)
    (hendHor : endpoint ≤ rho.horizon)
    (hcapEnd : ((Hs endpoint).sup fun u => (W (inclusiveEventIndex rho endpoint) u).st.core.h_max) ≤ 1)
    (hlo : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c →
      ∀ B : NamedBlock V, M.proposal_with (M.gradeContract c)
          Protocol.ProposalRowSource.poolAndCarried S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q)))
          (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
              (S.E.proposer (M.opening_slot S.hc q))).st
            (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some B →
        ∀ P : NamedBlock V, NamedBlock.parent? B = some P →
          (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q := by
  intro c hc Q hQ P hP
  have hqpos : 0 < q :=
    (by decide : 0 < 2).trans_le
      ((Nat.le_add_right 2 delayExtra).trans hqWait)
  have hspos : 0 < (M.opening_slot S.hc q) := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hqpos
  have hΔ := S.E.Δ_pos
  have hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon := by linarith
  have hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  have hQheight : (M.derive_named S.E S.cfg Q).h ≤ 1 :=
    (Restated.honestProposedBlock_height_le_honestHMaxAtOn facts S Hs Xb hf hHs hspos hprop hproposalHor
      c hc hQ hlo (fun j hj => hf.tick_outcome j _ _ hj) hrun).trans
        ((Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hlo hproposalEnd hendHor
          (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs endpoint)).trans hcapEnd)
  have hPQ : NamedBlock.Preceq P Q :=
    (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressCompose
      DecoupledConsensusModel.Proofs.HealingSurface.compose_namedParent_preceq_of_parent?) hP
  have hPupper : (M.derive_named S.E S.cfg P).h ≤ 1 :=
    (facts.cs.derive_height_mono S.E S.cfg hPQ).trans hQheight
  have hPheight : (M.derive_named S.E S.cfg P).h = 1 :=
    Nat.le_antisymm hPupper
      (facts.cs.one_le_derive_named_h S.E S.cfg P)
  rw [derivedTarget_eq_genesis_of_height_one₅₆s facts S.E S.cfg P hPheight]
  have hopen : M.opening_slot S.hc q = q * S.hc.R := by
    have h := facts.gr.opening_slot_add_mk S.hc 0 q
    rw [Nat.zero_add, facts.gr.opening_slot_zero_mk, Nat.zero_add] at h
    exact h
  rw [genesis_slot_inclG2, Nat.zero_add, hopen]
  exact (timeoutDelay_le_roundBound S hdelay).trans
    (Nat.mul_le_mul_right S.hc.R hqWait)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `w ∈ Hs read` and the largest `h_max` over `Hs read` at `read` is
    at most `1`, then genesis is in the filtered tree of `w`'s store before `read`. -/
theorem genesis_filtered_of_heightOneCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {read : Time} (hw : w ∈ Hs read)
    (hcap : ((Hs read).sup fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) ≤ 1) :
    (Block.genesis : Block V) ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG := by
  have hroot :=
    (Restated.honestStrictRead_root_eq_genesis_and_hMax_eq_oneOn facts S Hs Xb hf hw hcap).1
  have hmem := Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime
    facts S rho read w _ (mem_stateBeforeTime_along₅₆s hf.sorted hf.onePath read)
  rw [hroot] at hmem
  exact hmem

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, the committee majority and the weight bound, if genesis has the
    named grade of round `base` in the world of `W`, `S.E.t_GST ≤ S.a base`, `base ≤ q'`, `S.a q'`
    is inside the horizon, the largest `h_max` over `Hs (S.a q')` is at most `1`, `lo ≤ S.a base`,
    and the members of `Hs (S.a k + Δ)` pass the grade-2 awake test at round `base` and at every
    round `k` whose grade-2 window starts at or after `lo`, then genesis has the named grade of
    every round from `base` to `q'` and is in the filtered tree of every member of `Hs (S.a q')`
    before `S.a q'`. -/
theorem genesisGradeFormsAt_persist_of_heightOneCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {base q' : Round}
    (hseed : ∀ v ∈ Hs (M.domain S.E S.hc base .g2),
      (Block.genesis : Block V) ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc base .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc base .g2)) v).st base .g2
          (Block.genesis : Block V) ⇢ b → b = true)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hwindow : base ≤ q')
    (hendpoint : (Restated.Vocabulary.Execution.Setup.a M S q') ≤ rho.horizon)
    (hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S q')).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q')) u).st.core.h_max) ≤ 1)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAbase : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S base) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S base)) → M.awake_for_grade2 S u (W j u) base) :
    (∀ r', base ≤ r' → r' ≤ q' →
      ∀ v ∈ Hs (M.domain S.E S.hc r' .g2),
        (Block.genesis : Block V) ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (W (strictEventIndex rho (M.domain S.E S.hc r' .g2)) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc r' .g2)) v).st r' .g2
            (Block.genesis : Block V) ⇢ b → b = true) ∧
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q')),
      (Block.genesis : Block V) ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q')) v).st.core).toFG := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  refine ⟨?_, fun v hv => Restated.genesis_filtered_of_heightOneCapOn facts S Hs Xb hf hv hcapEnd⟩
  intro r' hbase hr'end
  rcases eq_or_lt_of_le hbase with hEq | hlt
  · subst r'
    exact hseed
  · cases r' with
    | zero => exact (Nat.not_lt_zero _ hlt).elim
    | succ r =>
        have hbasePrev : base ≤ r := Nat.le_of_lt_succ hlt
        have hactionNext : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q') :=
          (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hr'end
        have hloR : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePrev)
        have hloNext : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
          hloR.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ r))
        have hdomainGe : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
            M.domain S.E S.hc (r + 1) .g2 :=
          Restated.action_add_delta_le_domain_g2_succ_l54 facts S r
        have hloDom : lo ≤ M.domain S.E S.hc (r + 1) .g2 :=
          hloR.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans hdomainGe)
        have hdomainLt := domain_add_delta_lt_action₅₆s facts S (r + 1) .g2
        have hcapNext : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 1))).sup fun u =>
            (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) u).st.core.h_max) ≤ 1 :=
          (Restated.honestHMaxAtOn_action_mono_l56 facts S Hs Xb hf hHs hHsXb hcom hr'end hloNext
            hendpoint).trans hcapEnd
        have hcapDom : ((Hs (M.domain S.E S.hc (r + 1) .g2)).sup fun u =>
            (W (inclusiveEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) u).st.core.h_max) ≤ 1 :=
          (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloDom
            (lt_of_lt_of_le hdomainLt hactionNext) hendpoint
            (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)).trans hcapEnd
        have hactive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
            (Block.genesis : Block V) ∈ M.get_filtered_block_tree
              (M.toHealing (W (strictEventIndex rho
                (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG :=
          fun w hw => Restated.genesis_filtered_of_heightOneCapOn facts S Hs Xb hf hw hcapNext
        have hactiveDomain : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
            (Block.genesis : Block V) ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
              (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w) :=
          fun w hw => Restated.genesis_filtered_of_heightOneCapOn facts S Hs Xb hf hw hcapDom
        have hAr : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat,
            rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) →
            M.awake_for_grade2 S u (W j u) r := by
          rcases eq_or_lt_of_le hbasePrev with hb | hb
          · subst hb
            exact hAbase
          · exact hA r (le_sub_iff_add_le.mpr ((Int.add_le_add_right hlo S.E.Δ).trans
              (facts.gr.action_delta_le_early S S.hc.R_ge_three hb)))
        have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon :=
          (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r)).trans
            (hactionNext.trans hendpoint)
        exact Restated.namedGradeFormsAt_succ_of_fgRootFloorOn facts
          S Hs Xb hf hHs hHsXb hmajority (r := r) (P := (Block.genesis : Block V))
            (F := (Block.genesis : Block V))
            (fun _ _ _ _ => (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)))
            (hpost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hbasePrev))
            hcut hactive hactiveDomain hAr hloR
            (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, the committee majority and the weight bound, with carrier rounds
    recurring within `gap` rounds from `t₀ ≤ S.a start`, the timeout delay bound,
    `S.E.t_GST ≤ S.a start`, `start + 3 + delayExtra + gap ≤ endpointRound` with `S.a endpointRound`
    inside the horizon, `lo ≤ S.a start`, `lo ≤ opening (start − η_SG)`, and the grade-2 awake test
    at every round whose grade-2 window starts at or after `lo`: if the largest `h_max` over
    `Hs (S.a endpointRound)` is at most `1`, it is greater than `1`. -/
theorem heightOneFrontier_riseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {delayExtra : Nat}
    {start endpointRound gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S start))
    (hbound : start + 3 + delayExtra + gap ≤ endpointRound)
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon)
    (hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) u).st.core.h_max) ≤ 1)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S start))
    (hloOpen : lo ≤ M.opening S.E S.hc (start - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S start))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    1 < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) u).st.core.h_max) := by
  have hΔ := S.E.Δ_pos
  have hloAt : ∀ {k : Round}, start ≤ k → lo ≤ (Restated.Vocabulary.Execution.Setup.a M S k) :=
    fun hk => hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk)
  have hloEarlyAt : ∀ {k : Round}, start < k → lo ≤ M.early S.E S.hc k .g2 - S.E.Δ :=
    fun hk => le_sub_iff_add_le.mpr ((Int.add_le_add_right hlo S.E.Δ).trans
      (facts.gr.action_delta_le_early S S.hc.R_ge_three hk))
  have hcapAt : ∀ {k : Round}, start ≤ k → k ≤ endpointRound →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun u =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) u).st.core.h_max) ≤ 1 := by
    intro k hk hkEnd
    exact (Restated.honestHMaxAtOn_action_mono_l56 facts S Hs Xb hf hHs hHsXb hcom hkEnd (hloAt hk)
      hendHor).trans hcapEnd
  have hcapDom : ∀ {k : Round}, start < k → k ≤ endpointRound →
      ((Hs (M.domain S.E S.hc k .g2)).sup fun u =>
        (W (inclusiveEventIndex rho (M.domain S.E S.hc k .g2)) u).st.core.h_max) ≤ 1 := by
    intro k hk hkEnd
    have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_of_lt hk)
    have hge : (Restated.Vocabulary.Execution.Setup.a M S (k - 1)) + S.E.Δ ≤ M.domain S.E S.hc k .g2 := by
      simpa only [hkpred] using Restated.action_add_delta_le_domain_g2_succ_l54 facts S (k - 1)
    have hloDom : lo ≤ M.domain S.E S.hc k .g2 :=
      (hloAt (Nat.le_sub_one_of_lt hk)).trans ((le_add_of_nonneg_right hΔ.le).trans hge)
    have hlt := domain_add_delta_lt_action₅₆s facts S k .g2
    exact (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloDom
      (lt_of_lt_of_le hlt (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hkEnd)) hendHor
      (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)).trans hcapEnd
  have hhorAt : ∀ {k : Round}, k ≤ endpointRound →
      (Restated.Vocabulary.Execution.Setup.a M S k) ≤ rho.horizon := by
    intro k hk
    exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk).trans hendHor
  have hpostAt : ∀ {k : Round}, start ≤ k → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S k) := by
    intro k hk
    exact hpost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk)
  have hactiveGenesis : ∀ {k : Round}, start ≤ k → k ≤ endpointRound →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        (Block.genesis : Block V) ∈ M.get_filtered_block_tree (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.core).toFG := by
    intro k hk hkEnd w hw
    exact Restated.genesis_filtered_of_heightOneCapOn facts S Hs Xb hf hw (hcapAt hk hkEnd)
  have hactiveGenesisDomain : ∀ {k : Round}, start < k → k ≤ endpointRound →
      ∀ w ∈ Hs (M.domain S.E S.hc k .g2),
        (Block.genesis : Block V) ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) w) := by
    intro k hk hkEnd w hw
    exact Restated.genesis_filtered_of_heightOneCapOn facts S Hs Xb hf hw (hcapDom hk hkEnd)
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  obtain ⟨hseedRoundEnd, hstartTwo, hstartOne, htrigger⟩ := lowPrelude_nat_l56 hbound
  have hseedHor : (Restated.Vocabulary.Execution.Setup.a M S (start + 2)) ≤ rho.horizon :=
    hhorAt (k := start + 2) hseedRoundEnd
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (start + 1 + 1) ≤ rho.horizon :=
    (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S (start + 1))).trans
      hseedHor
  have hseed : ∀ v ∈ Hs (M.domain S.E S.hc (start + 2) .g2),
      (Block.genesis : Block V) ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (start + 2) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (start + 2) .g2)) v).st (start + 2) .g2
          (Block.genesis : Block V) ⇢ b → b = true :=
    Restated.namedGradeFormsAt_succ_of_fgRootFloorOn facts
      S Hs Xb hf hHs hHsXb hmajority (r := start + 1) (P := (Block.genesis : Block V))
        (F := (Block.genesis : Block V))
        (fun _ _ _ _ => (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)))
        (hpostAt (k := start + 1) (Nat.le_succ start)) hcut
        (hactiveGenesis (k := start + 2) hstartTwo hseedRoundEnd)
        (hactiveGenesisDomain (k := start + 2) hstartOne hseedRoundEnd)
        (hA (start + 1) (hloEarlyAt (Nat.lt_succ_self start))) (hloAt (Nat.le_succ start))
        (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)
  obtain ⟨q, hqlo, hqhi, hcarrier⟩ := hrec (start + 3 + delayExtra)
    (ht₀.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S htrigger)))
    ((Restated.Vocabulary.Proofs.HealingLemmas.openingProposal_window_le_action facts S (start + 3 + delayExtra) gap).trans
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbound).trans hendHor))
  obtain ⟨hqEnd, hqpos, hseedQPred, hstartQPred, hprevEnd, hqWait, hstartQ, hstartTwoQ⟩ :=
    lowSelected_nat_l56 hbound hqlo hqhi
  have hqPred : q - 1 < q := Nat.sub_lt hqpos (by decide)
  obtain ⟨hforms, hwindowPrev⟩ :=
    Restated.genesisGradeFormsAt_persist_of_heightOneCapOn facts
      S Hs Xb hf hHs hHsXb hcom hfb hseed (hpostAt (k := start + 2) hstartTwo)
        hseedQPred (hhorAt hprevEnd) (hcapAt hstartQPred hprevEnd)
        (hloAt hstartTwo) hA (hA (start + 2) (hloEarlyAt (by omega)))
  have hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hpostAt (k := q - 1) hstartQPred
  have hdomainWindow : ∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      (Block.genesis : Block V) ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.core).toFG :=
    fun w hw => Restated.genesis_filtered_of_heightOneCapOn facts S Hs Xb hf hw (hcapDom hstartQ hqEnd)
  have hGRun : Restated.RunBlockOn M S rho W Xb (NamedBlock.genesis : NamedBlock V) :=
    Restated.namedGenesis_runBlockOn facts S Xb (Hs rho.horizon) (hHsXb _) (hfb _ le_rfl) W hf.onePath
  have hproposalLt := Restated.openingProposal_add_delta_lt_action_l56 facts S q
  have hloProposal : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    (hloAt hstartQPred).trans ((Int.le_add_of_nonneg_right hΔ.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hqPred))
  have hmature := Restated.heightOne_opening_timeoutMatureOn facts S Hs Xb hf hHs hHsXb hcom
    hdelay hqWait hcarrier
    (lt_of_lt_of_le hproposalLt (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqEnd)) hendHor hcapEnd
    hloProposal
    -- The proposer of `q`'s opening slot passes the grade-1 awake test at its proposal time.
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) (hcarrier 0 (by decide)))
      (by
        rw [facts.gr.round_of_opening_slot_eq S.hc q]
        have h1 := facts.gr.lo_le_early_g2_of_window_start S hqpos (hloOpen.trans
          (facts.gr.NamedOutageClosure_opening_mono S
            (Nat.sub_le_sub_right (hstartQPred.trans (Nat.sub_le q 1)) _)))
        have h2 := facts.gr.early_g2_add_delta_le_early_g1 S q
        linarith))
  have hloOpenQ : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hstartQPred _))
  obtain ⟨cq, hcq⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc q))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))).cache
  obtain ⟨oq, hoq⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cq)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
  obtain ⟨Bq, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts S rho
    (M.opening_slot S.hc q) oq
    ⟨M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).record cq,
      ⟨W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))),
        mem_stateBeforeTime_along₅₆ hf.sorted hf.onePath _, cq, hcq, rfl⟩,
      by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
         exact hoq⟩
  rcases Restated.activeExactHeightOpening_fixedInterference_or_hMaxRiseOn facts
      S Hs Xb hf hHs hHsXb hfb (H := 1) (source := (NamedBlock.genesis : NamedBlock V))
        hqpos hcarrier
        (by rw [erase_named_genesis]; exact hforms (q - 1) hseedQPred (Nat.le_refl _))
        (by rw [erase_named_genesis]; exact hwindowPrev)
        (by rw [erase_named_genesis]; exact hdomainWindow) hGRun
        (facts.cs.derive_named_genesis_h S.E S.cfg)
        hpostPrev (hmature cq hcq Bq hoq)
        (by rw [erase_named_genesis]; exact hactiveGenesis hstartQ.le hqEnd)
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqEnd)
        hendHor (hloAt hstartQPred) hloOpenQ
          (hA (q - 1) (hloEarlyAt (Nat.lt_of_lt_of_le (by omega : start < start + 2) hseedQPred)))
          cq hcq hoq with
    hrise | hfixed
  · exact hrise
  · have himpossible : 0 < 0 := by
      simpa only using hfixed.1.targetHeightPositive
    exact False.elim ((Nat.lt_irrefl 0) himpossible)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- If every member of `Hs` at round `q`'s grade-2 domain time has `P` active in the world of `W`
    before that time, then `P` is in that member's store in the world of `W` before every read at or
    after `S.a q`. -/
private theorem formsW_processedAtRead₅₆ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {q : Round} {P : Block V}
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st q .g2 P ⇢ b → b = true)
    {reader : V}
    (hreader : reader ∈ Hs (M.domain S.E S.hc q .g2))
    {read : Time} (hle : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ read) :
    P ∈ (W (strictEventIndex rho read) reader).st.T := by
  have hdle : M.domain S.E S.hc q .g2 ≤ read := (facts.gr.domain_le_a S q .g2).trans hle
  have hsource : P ∈
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) reader).st.core.T := by
    have hfiltered := (hforms reader hreader).1
    have htree := facts.fc.get_filtered_block_tree_subset _ hfiltered
    rw [facts.sto.toHealing_gs_T] at htree
    exact htree
  have hmn : strictEventIndex rho (M.domain S.E S.hc q .g2) ≤ strictEventIndex rho read :=
    strict_mono₅₆ rho hdle
  exact Restated.Vocabulary.Proofs.stateBefore_T_subset facts S rho reader
    _ (hf.onePath _).1 _ hmn _ (onePath_slice₅₆ W hf.onePath hmn) hsource

/-- Under the bundle along `W`, if `0 < q`, `Q` has the named grade of round `q − 1` in the world of
    `W`, `Q` is a run block of height `Mh ≥ 1`, every member of `Hs (S.a (q − 1))` and of
    `Hs (domain q .g2)` has `h_j + 2 ≤ Mh` and `h_max = Mh` before that time, and `S.a q` is inside
    the horizon, then `Q` is in the filtered tree of each such member's store before that time. -/
theorem gradeWindows_of_gateOff_at_nextActionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {Q : NamedBlock V}
    (hq : 0 < q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2 Q.erase ⇢ b →
            b = true)
    (hQrun : Restated.RunBlockOn M S rho W Xb Q)
    (hQheight : (M.derive_named S.E S.cfg Q).h = Mh)
    (hM : 1 ≤ Mh)
    (hgatePrev : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core.h_max = Mh)
    (hgateDomain : ∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.core.h_max = Mh)
    (hhorQ : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon) :
    (∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      Q.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core).toFG) ∧
    (∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      Q.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.core).toFG) := by
  have hretain : ∀ {target : Time}, (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ target →
      target ≤ rho.horizon →
      (∀ w ∈ Hs target, (W (strictEventIndex rho target) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho target) w).st.core.h_max = Mh) →
      ∀ w ∈ Hs target,
        Q.erase ∈ M.get_filtered_block_tree (M.toHealing
          (W (strictEventIndex rho target) w).st.core).toFG := by
    intro target hafter htargetHor hgate w hw
    have hdomPrev : M.domain S.E S.hc (q - 1) .g2 ≤ target :=
      (facts.gr.domain_le_a S (q - 1) .g2).trans hafter
    have hprocessed : Q.erase ∈ (W (strictEventIndex rho target) w).st.T :=
      formsW_processedAtRead₅₆ facts S hf hforms (hHs _ _ hdomPrev hw) hafter
    exact Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hf.slashableBound (hHsXb _ hw)
      htargetHor hprocessed rfl hQrun (by rw [hQheight]; exact Nat.sub_le Mh 1)
        hM (hgate w hw).2 (hgate w hw).1
  have hpredAction : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le q 1)
  have hdomainAction :
      M.domain S.E S.hc q .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    facts.gr.domain_le_a S q .g2
  have hpredDomain : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      M.domain S.E S.hc q .g2 := by
    have hstep := Restated.Vocabulary.Proofs.NamedOutageClosure.action_le_domain facts
      S S.hc.R_ge_three (Nat.sub_lt hq (by decide : 0 < 1))
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hq))] using hstep
  refine ⟨?_, ?_⟩
  · exact hretain (le_refl _) (hpredAction.trans hhorQ) hgatePrev
  · exact hretain hpredDomain (hdomainAction.trans hhorQ) hgateDomain

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds after the events at or before `t` are the worlds before the
    event at index `inclusiveEventIndex rho t`. -/
private theorem readAt_eq_inclusive₅₆h (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.readAt M S rho t =
      Record.stateBeforeOf M S rho (inclusiveEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact le_trans (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time ≤ t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time ≤ t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, the world of a path `W` before the event at index
    `inclusiveEventIndex rho t` is a world after the events at or before `t`. -/
private theorem mem_readAt_along₅₆h {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (inclusiveEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.readAt M S rho t := by
  rw [readAt_eq_inclusive₅₆h S rho hsorted]
  exact (hW _).1

open scoped DC in
/-- Along the bundle's path `W`, every outcome of the proposal duty of slot `s`'s proposer at its
    proposal time, with the cache outcome `c`, is one of the values `proposedBlockAt M S rho s`. -/
private theorem proposedBlockAt_mem₅₆h (facts : Record.Facts M) (S : Setup V)
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
  ⟨M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c,
    ⟨W (strictEventIndex rho (M.proposal_time S.E s)),
      mem_stateBeforeTime_along₅₆ hf.sorted hf.onePath _, c, hc, rfl⟩,
    by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
       exact ho⟩

/-- A fixed-height root interference at a read gives the fixed-height justification root at that
    read, in the same world. -/
private theorem justificationRoot_of_interference₅₆h {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} {Hs : Int → Finset V} {Xb : Finset V} {H : Height} {w : V}
    {read : Time} {wd : V → M.N} {P : Block V}
    (h : Restated.FixedHeightRootInterferenceAtReadOn M S rho W Hs Xb H w read wd P) :
    Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read wd :=
  ⟨h.readerHonest, h.readInHorizon, h.carrierExists, h.targetHeightPositive,
    ⟨h.fixedTarget.frontier, h.fixedTarget.justificationHeight, h.fixedTarget.gate,
      h.fixedTarget.certificate, h.fixedTarget.uniqueAtHeight, h.fixedTarget.targetBlock⟩⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, the committee majority and the weight bound, with carrier rounds
    recurring within `gap` rounds from `t₀ ≤ S.a r0`, the seed contract `HeightProgressSeedFromOn`
    from `r0`, the timeout delay bound, `S.E.t_GST ≤ S.a r0`, a callback turning every fixed-height
    justification root into a rise of the largest `h_max`, `r0 ≤ start`, the endpoint
    `start + progressLag' gap delayExtra` inside the horizon, `lo ≤ S.a r0`,
    `lo ≤ opening (r0 − η_SG)` and the grade-2 awake test, the largest `h_max` over `Hs (S.a start)`
    is less than the largest `h_max` over `Hs` at the endpoint's action time. -/
theorem heightProgress_pointwiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {delayExtra : Nat}
    {r0 gap start : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hseed : Restated.HeightProgressSeedFromOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb r0 gap delayExtra)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (_of_fixedRootProgress : ∀ {Mh : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read)) →
      S.E.t_GST ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) v).st.core.h_max) ≤
          Mh →
      lo ≤ read → t₀ ≤ read →
      lo ≤ M.opening S.E S.hc (r + 2 - S.hc.η_SG) →
      Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) v).st.core.h_max))
    (hr0 : r0 ≤ start)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (start + progressLag' gap delayExtra)) ≤ rho.horizon)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) <
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S (start + progressLag' gap delayExtra))).sup fun v =>
        (W (inclusiveEventIndex rho
          (Restated.Vocabulary.Execution.Setup.a M S (start + progressLag' gap delayExtra))) v).st.core.h_max) := by
  have hΔ := S.E.Δ_pos
  obtain ⟨_hstartEnd, hrelayEnd, hfixedBound, hseedEnd, hseedFixedBound, hbound⟩ :=
    composeStaticBounds_nat_l56 start gap delayExtra
  have hloStart : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S start) :=
    hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)
  have hloAt : ∀ {k : Round}, start ≤ k → lo ≤ (Restated.Vocabulary.Execution.Setup.a M S k) :=
    fun hk => hloStart.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk)
  have ht₀At : ∀ {k : Round}, start ≤ k → t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S k) :=
    fun hk => (ht₀.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)).trans
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk)
  have hloOpenAt : ∀ {k : Round}, start ≤ k →
      lo ≤ M.opening S.E S.hc (k + 2 - S.hc.η_SG) :=
    fun hk => hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right (hr0.trans (hk.trans (Nat.le_add_right _ 2))) _))
  have hhorAt : ∀ {k : Round}, k ≤ start + progressLag' gap delayExtra →
      (Restated.Vocabulary.Execution.Setup.a M S k) ≤ rho.horizon := by
    intro k hk
    exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk).trans hhor
  have hmonoA : ∀ {k k' : Round}, start ≤ k → k ≤ k' →
      k' ≤ start + progressLag' gap delayExtra →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun v =>
          (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core.h_max) ≤
        ((Hs (Restated.Vocabulary.Execution.Setup.a M S k')).sup fun v =>
          (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k')) v).st.core.h_max) := by
    intro k k' hk hkk hk'
    exact Restated.honestHMaxAtOn_action_mono_l56 facts S Hs Xb hf hHs hHsXb hcom hkk (hloAt hk)
      (hhorAt hk')
  by_cases hrise : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) <
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S (start + progressLag' gap delayExtra))).sup fun v =>
        (W (inclusiveEventIndex rho
          (Restated.Vocabulary.Execution.Setup.a M S (start + progressLag' gap delayExtra))) v).st.core.h_max)
  · exact hrise
  · have hcapEnd := Nat.le_of_not_gt hrise
    have hMone : 1 ≤ ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) :=
      Restated.one_le_honestHMaxAtOn facts S Hs Xb hf hcom hHs
        (Restated.Vocabulary.Execution.Setup.a M S start) _
        ⟨_, mem_readAt_along₅₆h hf.sorted hf.onePath (Restated.Vocabulary.Execution.Setup.a M S start), rfl⟩
    have hpostStart : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S start) :=
      hpost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)
    have hpostAt : ∀ {k : Round}, start ≤ k → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S k) :=
      fun hk => hpostStart.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk)
    have hcapAt : ∀ {k : Round}, start ≤ k → k ≤ start + progressLag' gap delayExtra →
        ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun v =>
            (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core.h_max) ≤
          ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
            (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) :=
      fun hk hkEnd => (hmonoA hk hkEnd le_rfl).trans hcapEnd
    have hfrontierAt : ∀ {k : Round}, start ≤ k → k ≤ start + progressLag' gap delayExtra →
        ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun v =>
            (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core.h_max) =
          ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
            (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) :=
      fun hk hkEnd => Nat.le_antisymm (hcapAt hk hkEnd) (hmonoA le_rfl hk hkEnd)
    by_cases hMtwo : 2 ≤ ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max)
    · have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
      have hfbHor : Execution.BelowOneThird S (Hs rho.horizon) := hfb _ le_rfl
      rcases Restated.frontierRegime_after_oneDelayOn facts
          S Hs Xb hf hHs hHsXb hfbHor hsb (start := start) rfl hloStart
            (hcapAt (Nat.le_succ start) hrelayEnd)
            (hhorAt hrelayEnd) hMtwo with
        ⟨u, hu, hfix⟩ | hgateOff
      · exact _of_fixedRootProgress hfix
          (hpostAt (Nat.le_succ start)) (le_refl _) hfixedBound hhor hcapEnd
          (hloAt (Nat.le_succ start)) (ht₀At (Nat.le_succ start))
          (hloOpenAt (Nat.le_succ start))
      · have hstartBase : start ≤ start + 1 := Nat.le_succ start
        have hbaseFrontier := hfrontierAt hstartBase hrelayEnd
        have hseedOutcome := hseed (start + 1)
          (hr0.trans hstartBase)
          (hpostAt hstartBase) _ hbaseFrontier
          (fun w hw => (hgateOff w hw).2) (fun w hw => (hgateOff w hw).1)
          (hhorAt hseedEnd)
        unfold Restated.HeightProgressSeedOutcomeOn at hseedOutcome
        rcases hseedOutcome with
          hseedRise | hseedFix | hseedGrade
        · exact hseedRise.trans_le
            (hmonoA ((Nat.le_succ start).trans (Nat.le_add_right _ _)) hseedEnd le_rfl)
        · rcases hseedFix with ⟨u, read, hu, hpostRead, hread, hbaseRead, hfix⟩
          -- The read is at or after `S.a (start + 1)`.
          have hreadLower : (Restated.Vocabulary.Execution.Setup.a M S (start + 1)) ≤ read := by
            rcases hbaseRead with hge | huBase
            · exact hge
            · by_contra hlt
              have hlt' : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (start + 1)) :=
                le_of_lt (lt_of_not_ge hlt)
              have hidx := strict_mono₅₆ rho hlt'
              have hmono : (W (strictEventIndex rho read) u).st.core.h_j ≤
                  (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (start + 1))) u).st.core.h_j :=
                Restated.Vocabulary.Proofs.HealingSurface.stateBefore_h_j_mono facts S rho u hidx
                  _ (hf.onePath _).1 _ (onePath_slice₅₆ W hf.onePath hidx)
              have hgate := (hgateOff u huBase).1
              have hJ : (W (strictEventIndex rho read) u).st.core.h_j =
                  ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
                    (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) - 1 :=
                hfix.fixedTarget.justificationHeight
              have hkey := Nat.le_trans (Nat.add_le_add_right hmono 2) hgate
              rw [hJ] at hkey
              have hone : 1 ≤ ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
                  (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) :=
                Nat.le_trans (by decide) hMtwo
              rw [show ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
                    (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) -
                    1 + 2 =
                  ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
                    (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) -
                    1 + 1 + 1 from rfl, Nat.sub_add_cancel hone] at hkey
              exact absurd hkey (Nat.not_succ_le_self _)
          exact _of_fixedRootProgress hfix hpostRead hread hseedFixedBound hhor hcapEnd
            ((hloAt (Nat.le_succ start)).trans hreadLower)
            ((ht₀At (Nat.le_succ start)).trans hreadLower)
            (hloOpenAt ((Nat.le_succ start).trans (Nat.le_add_right _ _)))
        · rcases hseedGrade with
            ⟨entry0, q0, Q, Next, Parent, hentry0lo, hentry0space, hq0hi,
              hcarrier0, hQentry, hforms0, hQrun, hQheight,
              hNext, hParent, hQpreceq, hQsameHeight⟩
          obtain ⟨hentry0pos, hq0pos, hstartQ0PP, hstartQ0Pred, hq0PP, hq0PredAdd, hq0End,
              hq0PredEnd, hq0PPEnd, hq0PredFixedBound, hq0FixedBound⟩ :=
            seedGradeBounds_nat_l56 hentry0lo hentry0space hq0hi hseedFixedBound
          have hq0Pred : q0 - 1 < q0 := Nat.sub_lt hq0pos (by decide)
          have hq0PredLe : q0 - 1 ≤ q0 := Nat.sub_le q0 1
          have hhorQ0 : (Restated.Vocabulary.Execution.Setup.a M S q0) ≤ rho.horizon := hhorAt hq0End
          have hfrontierQ0Pred := hfrontierAt hstartQ0Pred hq0PredEnd
          have hfrontierQ0PP := hfrontierAt hstartQ0PP hq0PPEnd
          have hpostQ0Pred : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q0 - 1)) :=
            hpostAt hstartQ0Pred
          have hcapQ0 := hcapAt (hstartQ0Pred.trans hq0PredLe) hq0End
          obtain ⟨cE, hcE, hQE⟩ := hQentry
          obtain ⟨cN, hcN, hNextP⟩ := hNext
          have hmatureQ0 : ∀ P' : NamedBlock V, NamedBlock.parent? Next = some P' →
              (M.derive_named S.E S.cfg P').T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q0 :=
            Restated.laterOpening_timeoutMature_of_sameHeightOn facts
              S Hs Xb hf hdelay hentry0pos hentry0space
                (proposedBlockAt_mem₅₆h facts S hf _ cE hcE hQE)
                (mem_stateBeforeTime_along₅₆ hf.sorted hf.onePath _) cN hcN hNextP hParent
                hQpreceq hQsameHeight
          have hregimeQ0Raw := Restated.frontierRegime_after_oneDelayOn facts
            S Hs Xb hf hHs hHsXb hfbHor hsb (start := q0 - 1)
              hfrontierQ0Pred (hloAt hstartQ0Pred)
                (by simpa only [hq0PredAdd] using hcapQ0)
                (by simpa only [hq0PredAdd] using hhorQ0) hMtwo
          rw [hq0PredAdd] at hregimeQ0Raw
          rcases hregimeQ0Raw with ⟨u, hu, hfix⟩ | hgateQ0
          · exact _of_fixedRootProgress hfix (hpostAt (hstartQ0Pred.trans hq0PredLe))
              (le_refl _) hq0FixedBound hhor hcapEnd
              (hloAt (hstartQ0Pred.trans hq0PredLe)) (ht₀At (hstartQ0Pred.trans hq0PredLe))
              (hloOpenAt (hstartQ0Pred.trans hq0PredLe))
          ·
            have hstepPrev : (Restated.Vocabulary.Execution.Setup.a M S (q0 - 2)) + 1 + S.E.Δ ≤
                (Restated.Vocabulary.Execution.Setup.a M S (q0 - 1)) := by
              simpa only [hq0PP] using Restated.action_add_one_add_delta_le_next_action_l52 facts S (q0 - 2)
            have hdomGe : (Restated.Vocabulary.Execution.Setup.a M S (q0 - 1)) + S.E.Δ ≤
                M.domain S.E S.hc q0 .g2 := by
              simpa only [hq0PredAdd] using Restated.action_add_delta_le_domain_g2_succ_l54 facts S (q0 - 1)
            have hdomLt := domain_add_delta_lt_action₅₆s facts S q0 .g2
            have hdomHor : M.domain S.E S.hc q0 .g2 ≤ rho.horizon := by linarith
            have hloDom : lo ≤ M.domain S.E S.hc q0 .g2 := by
              have := hloAt hstartQ0Pred
              linarith
            have hcapDom : ((Hs (M.domain S.E S.hc q0 .g2)).sup fun v =>
                  (W (inclusiveEventIndex rho (M.domain S.E S.hc q0 .g2)) v).st.core.h_max) ≤
                ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
                  (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) :=
              (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloDom hdomLt hhorQ0
                (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)).trans hcapQ0
            rcases Restated.frontierRegime_at_read_l56 facts S Hs Xb hf hHs hHsXb hfbHor hsb
                (start := q0 - 2) hfrontierQ0PP (hloAt hstartQ0PP) hstepPrev
                (by rw [hfrontierQ0Pred]) (hhorAt hq0PredEnd) hMtwo with
              ⟨u, hu, hfix⟩ | hgatePrev
            · exact _of_fixedRootProgress hfix hpostQ0Pred (le_refl _)
                hq0PredFixedBound hhor hcapEnd
                (hloAt hstartQ0Pred) (ht₀At hstartQ0Pred) (hloOpenAt hstartQ0Pred)
            · rcases Restated.frontierRegime_at_read_l56 facts S Hs Xb hf hHs hHsXb hfbHor hsb
                  (start := q0 - 2) hfrontierQ0PP (hloAt hstartQ0PP)
                  (by linarith) hcapDom hdomHor hMtwo with
                ⟨u, hu, hfix⟩ | hgateDomain
              · exact _of_fixedRootProgress hfix (by linarith)
                  (facts.gr.domain_le_a S q0 .g2) hq0FixedBound hhor hcapEnd
                  hloDom (by have := ht₀At hstartQ0Pred; linarith)
                  (hloOpenAt (hstartQ0Pred.trans hq0PredLe))
              · have hdomPrev : M.domain S.E S.hc (q0 - 1) .g2 ≤
                    (Restated.Vocabulary.Execution.Setup.a M S q0) :=
                  (facts.gr.domain_le_a S (q0 - 1) .g2).trans
                    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq0PredLe)
                have hactiveQ0 : ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q0),
                    Q.erase ∈ M.get_filtered_block_tree (M.toHealing
                      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q0)) w).st.core).toFG := by
                  intro w hw
                  exact Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw)
                    hhorQ0
                    (formsW_processedAtRead₅₆ facts S hf hforms0
                      (hHs _ _ hdomPrev hw) (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq0PredLe))
                    rfl hQrun (by rw [hQheight]; exact Nat.sub_le _ 1) hMone
                    (hgateQ0 w hw).2 (hgateQ0 w hw).1
                obtain ⟨hwindowPrev, hdomainWindow⟩ :=
                  Restated.gradeWindows_of_gateOff_at_nextActionOn facts
                    S Hs Xb hf hHs hHsXb hq0pos hforms0 hQrun hQheight hMone
                      hgatePrev hgateDomain hhorQ0
                have hloOpenQ0 : lo ≤ M.opening S.E S.hc (q0 - 1 - S.hc.η_SG) :=
                  hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
                    (Nat.sub_le_sub_right (hr0.trans hstartQ0Pred) _))
                rcases Restated.activeExactHeightOpening_fixedInterference_or_hMaxRiseOn facts
                    S Hs Xb hf hHs hHsXb hfb hq0pos hcarrier0
                      hforms0 hwindowPrev
                      hdomainWindow hQrun hQheight hpostQ0Pred
                      hmatureQ0 hactiveQ0
                      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hq0End) hhor
                      (hloAt hstartQ0Pred) hloOpenQ0
                      (hA (q0 - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloStart
                        (lt_of_le_of_lt hstartQ0PP (by rw [← hq0PP]; exact Nat.lt_succ_self _))))
                      cN hcN hNextP with
                  hrise0 | hfixed0
                · exact hrise0
                · have hpropAfter := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
                    facts S hq0Pred
                  have hpostProposal : S.E.t_GST ≤
                      M.proposal_time S.E (M.opening_slot S.hc q0) := by
                    linarith
                  exact _of_fixedRootProgress
                    (justificationRoot_of_interference₅₆h hfixed0.1) hpostProposal
                      hfixed0.2.1 hq0FixedBound hhor hcapEnd
                      (by have h1 := hloAt hstartQ0Pred; linarith)
                      (by have h1 := ht₀At hstartQ0Pred; linarith)
                      (hloOpenAt (hstartQ0Pred.trans hq0PredLe))
    · have hMeq : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun v =>
          (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) v).st.core.h_max) = 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hMtwo)) hMone
      have hr := Restated.heightOneFrontier_riseOn facts S Hs Xb hf hHs hHsXb hcom hfb hrec
        hdelay hpostStart hbound hhor (by rw [← hMeq]; exact hcapEnd) hloStart
        (hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hr0 _)))
        (ht₀.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)) hA
      rw [hMeq]
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

/-- Under the hypotheses of `heightProgress_pointwiseOn`, `progressLag' gap delayExtra` is positive
    and, for every `r ≥ r0` whose lag ends inside the horizon, the largest `h_max` over `Hs (S.a r)`
    is less than the largest `h_max` over `Hs (S.a (r + progressLag' gap delayExtra))`. -/
theorem eventualHeightProgressFrom_of_seedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {delayExtra : Nat}
    {r0 gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hseed : Restated.HeightProgressSeedFromOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb r0 gap delayExtra)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (_of_fixedRootProgress : ∀ {Mh : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read)) →
      S.E.t_GST ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) v).st.core.h_max) ≤
          Mh →
      lo ≤ read → t₀ ≤ read →
      lo ≤ M.opening S.E S.hc (r + 2 - S.hc.η_SG) →
      Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) v).st.core.h_max))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    0 < progressLag' gap delayExtra ∧ ∀ r : Round, r0 ≤ r →
      (Restated.Vocabulary.Execution.Setup.a M S (r + progressLag' gap delayExtra)) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S r)).sup fun u =>
          (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u).st.core.h_max) <
        (Hs (Restated.Vocabulary.Execution.Setup.a M S (r + progressLag' gap delayExtra))).sup fun u =>
          (W (inclusiveEventIndex rho
            (Restated.Vocabulary.Execution.Setup.a M S (r + progressLag' gap delayExtra))) u).st.core.h_max := by
  refine ⟨progressLag'_pos (delayExtra := delayExtra) gap, ?_⟩
  intro r hr0 hhor
  exact heightProgress_pointwiseOn facts S Hs Xb hf hHs hHsXb hcom hfb hrec hseed hdelay hpost
    _of_fixedRootProgress hr0 hhor hlo hloOpen ht₀ hA

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

end

end DecoupledConsensusModel.Sts.Restated
