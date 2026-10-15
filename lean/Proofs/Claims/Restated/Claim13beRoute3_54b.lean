import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Head_PreparedProposalReadBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FrameFloorBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_ProposalCanonicality
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_54b
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Opening proposals, freeze roots and confirmation cones along one path

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`, read along the path
`W` of the bundle `AdmissibleFieldsOn`: the grade-1 freeze root from the grade-2 one, the parent of
the next opening proposal, the height of a proposed block, the case analysis at an active
exact-height opening, and the confirmation of a Goldfish vote cone.
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

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₄b (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₅₄b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₄b S rho hsorted]
  exact (hW _).1

/-- For a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of `rho`
    lead to from `W m`. -/
private theorem onePath_reach₅₄b {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₅₄b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₄b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₅₄b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The SG root read under any grade contract from a store with a cache written in is the one read
    from the store itself. -/
private theorem sgRoot_store_with_cache₅₄b (facts : Record.Facts M) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.NS) (c c' : M.Cache) (r : Round) (x : Block V) :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

/-- Every node state `n` of the round-`r` action read from `before` has as store
    `M.store_with_cache st n.cache`, where `st.core` is an outcome of the confirmation update of
    `before`'s store staged at `S.a r`. -/
private theorem actionReadFrom_core₅₄b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state of the round-`r` action read from `before` has the `h_max` of `before`'s core
    store. -/
private theorem actionReadFrom_h_max₅₄b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₄b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _ hX₀,
    facts.hd.setClock_toHealing_h_max]

/-- The late vote set of the store `tickStore` stages from `st` at `t` is the late vote set of `st`. -/
private theorem confLate_tickStore₅₄b (facts : Record.Facts M) (S : Setup V) (st : M.S) (t : Time)
    (s : Slot) :
    Restated.Vocabulary.Protocol.confLate M S.E (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t) s =
      Restated.Vocabulary.Protocol.confLate M S.E st s := by
  rw [Restated.Vocabulary.Protocol.confLate, Restated.Vocabulary.Protocol.confLate,
    Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.pool_set_clock_slot,
    facts.sto.store_with_t_s_timestamp_vote]

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₄b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

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
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `v` is in `Hs` of round `r`'s late grade-1 time, `0 < r`, the
    grade-2 freeze root of `r` of `v`'s store before the grade-2 domain time can return `some g2`,
    the finalized block of `v`'s store before the grade-1 domain time is an ancestor of `g2`, and
    `lo ≤ opening (r − η_SG)`, then every outcome of the grade-1 freeze root of `r` of that store is
    `some g1` for a descendant `g1` of `g2`. -/
theorem q10_g1_of_g2_freeze_localOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (v : V) (r : Round) (hv : v ∈ Hs (M.late S.E S.hc r .g1)) (hr : 0 < r) {g2 : Block V}
    (hg2raw : M.freezeRoot S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ some g2)
    (hFB : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F g2)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) ⇢ fr →
      ∃ g1 : Block V, fr = some g1 ∧ Block.Preceq g2 g1 := by
  intro fr hfr
  have hmem2 := facts.gr.mem_T_of_freezeRoot_eq_some _ hg2raw rfl
  obtain ⟨b2, hb2⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) g2
  have hb2t : b2 = true := facts.gr.gradeBool_of_freezeRoot_eq_some _ hg2raw rfl b2 hb2
  subst hb2t
  have hgrade1 := Restated.q10_grade_crossOn facts S rho Hs Xb hf hHs hHsXb v r hv hr hlo
    g2 hFB hb2
  have hmem1 := Restated.q10_tree_fwdOn facts S rho Hs Xb hf v
    (facts.gr.q10_domain_g2_lt_domain_g1 S r).le hmem2
  obtain ⟨b1, hb1⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) g2
  exact facts.gr.q10_freeze_of_graded S.E _ _ S.hc.η_SG r (facts.gr.q10_early_le_late S r .g1)
    hmem1 b1 hb1 (hgrade1 b1 hb1) fr hfr

/-- Under the bundle along `W`, if `w` is in `Hs` of round `r`'s late grade-1 time, `0 < r`, `t` is
    round `r`'s grade-1 domain time, `P` is active at `w`'s node state staged at `t` with the cache
    outcome `c`, the grade-2 freeze root of `r` can return a descendant of `P`, and
    `lo ≤ opening (r − η_SG)`, then the grade-1 frame of that node state has a root descending from
    `P`. -/
theorem frameG1_preceq_of_freezeRoot_prepared_openingOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (w : V) (r : Round) (hw : w ∈ Hs (M.late S.E S.hc r .g1)) (hr : 0 < r) (t : Time)
    (hround : (M.round_of S.hc (S.E.slotOf t)) = r)
    (hopen : M.domain S.E S.hc r .g1 = t)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) w).st.core.toHealing t
      (W (strictEventIndex rho t) w).cache ⇢ c)
    {P raw : Block V}
    (hPtree : P ∈ M.get_filtered_block_tree
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).st.core).toFG)
    (hfreeze : M.freezeRoot S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) w).st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ some raw)
    (hPraw : Block.Preceq P raw)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∃ root, (M.readFrame
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).cache
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).st.core) r).g1 =
        some (some root) ∧ Block.Preceq P root := by
  have hwmem := mem_stateBeforeTime_along₅₄b hf.sorted hf.onePath t
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
  have hF1 : (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
      (W (strictEventIndex rho t) w).record c).st.core).toFG.F =
      (W (strictEventIndex rho t) w).st.core.F := by
    rw [facts.nd.mkNode_st, facts.sto.Sts_toHealing_F, facts.nd.store_with_cache_core_F, facts.hd.setClock_core_F]
  have hFP : Block.Preceq (W (strictEventIndex rho t) w).st.core.F P := by
    have h := facts.fc.q10_filtered_F hPtree
    rwa [hF1] at h
  have hFB : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F raw := by
    rw [hopen]
    exact preceq_trans_Preceq hFP hPraw
  have hq10 := Restated.q10_g1_of_g2_freeze_localOn facts S rho Hs Xb hf hHs hHsXb w r hw hr
    hfreeze hFB hlo
  rw [hopen] at hq10
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
    (M.toHealing (W (strictEventIndex rho t) w).st.core).toFG.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hfr' := hfr
  rw [facts.sto.Sts_toHealing_F] at hfr'
  obtain ⟨raw1, rfl, hPraw1⟩ := hq10 _ hfr'
  have hphase := facts.gr.phaseResult_onPhaseTick_domain_current S.E S.hc
    (M.toHealing (W (strictEventIndex rho t) w).st.core) t
    (by rw [← hopen, facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]; exact facts.sch.Optimistic_proposal_time_nonneg S.E _)
    (W (strictEventIndex rho t) w).cache hround hopen.symm hrawNone c hc _ hfr
  rw [Option.map_some] at hphase
  have hcomp : Block.compatible P (W (strictEventIndex rho t) w).st.core.F = true :=
    Proofs.ModelProperties.compatible_eq_true_of_Preceq_symm hFP
  rw [facts.nd.mkNode_cache]
  refine ⟨_, facts.gr.readFrame_g1_of_cache hphase, ?_⟩
  rw [hF1, facts.sto.Sts_toHealing_F]
  exact (facts.gr.q10_retained_prefix _ _ P hcomp).mpr
    ((facts.gr.q10_retained_prefix raw1 _ P hcomp).mpr (preceq_trans_Preceq hPraw hPraw1))

/-- Under the bundle along `W` with the weight majority `HonestWeightMajorityOn`, if `P` is cleanly
    read at round `r`, the proposer of round `r + 1`'s opening slot is in `Hs (S.a (r + 1))` and has
    `P` active in its duty store, `B` is a block it can propose with the cache outcome `c`,
    `lo ≤ S.a r`, the members of `Hs (S.a r + Δ)` are awake at `r`, and
    `lo ≤ opening (r + 1 − η_SG)`, then `P` is an ancestor of `B`'s parent. -/
theorem protected_preceq_nextOpeningProposedParent_of_cleanActionReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    (hprop : S.E.proposer (M.opening_slot S.hc (r + 1)) ∈
      Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hactive : P ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))).toFG)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))) ⇢ some B)
    (hlo : lo ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hA : ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r)
    (hloOpen : lo ≤ M.opening S.E S.hc (r + 1 - S.hc.η_SG)) :
    Block.Preceq P B.erase.parent := by
  have hwdom : S.E.proposer (M.opening_slot S.hc (r + 1)) ∈ Hs (M.domain S.E S.hc (r + 1) .g2) :=
    hHs _ _ (facts.gr.domain_le_a S (r + 1) .g2) hprop
  have hwlate : S.E.proposer (M.opening_slot S.hc (r + 1)) ∈ Hs (M.late S.E S.hc (r + 1) .g1) :=
    hHs _ _ (facts.gr.q10_late_g1_le_domain_g2 S (r + 1)) hwdom
  have hforms := Restated.namedGradeFormsAt_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb
    hmajority hclean ⟨_, hprop⟩ hlo hA
  obtain ⟨hPf, hPg⟩ := hforms _ hwdom
  have hPmem : P ∈ (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core)).T := by
    rw [facts.gr.Sts_gradeView_T]
    exact Restated.Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree facts hPf
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2))
      (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.F
    S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) P
  have hbt : b = true := hPg b hb
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2))
      (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.F
    S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2)
  obtain ⟨raw, rfl, hPraw⟩ := facts.gr.q10_freeze_of_graded S.E _ _ S.hc.η_SG (r + 1)
    (facts.gr.q10_early_le_late S (r + 1) .g2) hPmem b hb hbt fr hfr
  have hround : M.round_of S.hc (S.E.slotOf (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))) =
      r + 1 := by
    rw [facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_opening_slot_eq S.hc (r + 1)
  have hopen : M.domain S.E S.hc (r + 1) .g1 = M.proposal_time S.E (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hncore := setClock_core_tickStore₅₄b facts S
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (S.E.proposer (M.opening_slot S.hc (r + 1))))
    (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
  have hPtree : P ∈ M.get_filtered_block_tree (M.toHealing (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).st.core).toFG := by
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_filtered_block_tree, hncore]
    exact hactive
  obtain ⟨root, hroot, hProot⟩ := Restated.frameG1_preceq_of_freezeRoot_prepared_openingOn facts
    S rho Hs Xb hf hHs hHsXb _ (r + 1) hwlate (Nat.succ_pos r) _ hround hopen c hc hPtree
    hfr hPraw hloOpen
  have hanchor := Restated.Vocabulary.Proofs.HealingSurface.anchor_preceq_of_frame_floor facts S _
    (r + 1) P hPtree (Or.inl ⟨root, hroot, hProot⟩)
  have hnmem : M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (M.opening_slot S.hc (r + 1)) :=
    ⟨_, mem_stateBeforeTime_along₅₄b hf.sorted hf.onePath _, c, hc, rfl⟩
  have hnround : M.round_of S.hc (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).st.core.s = r + 1 := by
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_core_s, hncore,
      Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.store_with_t_s_s]
    exact hround
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).st.core) (r + 1)
  have hA0 : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c) (r + 1) ⇢ G.anchor := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    rw [facts.nd.mkNode_cache]
    exact returns_map_intro₅₄b _ _ _ hG
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty
    (M.gradeContract (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).cache)
    S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
    (M.toHealing (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).st.core)
  have hparent := Restated.Vocabulary.Proofs.HealingSurface.proposalAnchor_preceq_proposedParent facts
    S rho (M.opening_slot S.hc (r + 1)) _ hnmem G.anchor (by rw [hnround]; exact hA0) input hinput
  have hBn : M.proposal_with (M.gradeContract (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
      (M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
            (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
          (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).st ⇢ some B := by
    rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
    exact hB
  rw [Restated.Vocabulary.Proofs.HealingSurface.proposedBlockErased_parent facts S rho _ _ hnmem hBn
    input hinput]
  exact preceq_trans_Preceq (hanchor _ hA0) hparent

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
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `w ∈ Xb` has the named body `D` in its store before `t`, then `D`
    is a run block read through `Xb` along `W`. -/
theorem lifecycle_runBlock_of_mem_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (W (strictEventIndex rho t) w).st.bodies) : Restated.RunBlockOn M S rho W Xb D :=
  Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hD

/-- Under the bundle along `W`, two run blocks read through `Xb` with the same erasure are equal. -/
theorem lifecycle_runBlock_unique_of_erase_eqOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A D : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hD : Restated.RunBlockOn M S rho W Xb D)
    (herase : A.erase = D.erase) : A = D :=
  hf.rootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A))
    (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- Under the bundle along `W`, if `v ∈ Hs endpoint` and `S.a r ≤ endpoint`, every node state of
    `v`'s round-`r` action read has `h_max` at most the largest `h_max` over `Hs endpoint` in the
    world of `W` at `endpoint`. -/
theorem actionStore_hMax_le_honestHMaxAt_lifecycleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {v : V} {endpoint : Time} (hv : v ∈ Hs endpoint)
    (hle : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ endpoint) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    n.st.core.h_max ≤
      (Hs endpoint).sup fun u => (W (inclusiveEventIndex rho endpoint) u).st.core.h_max := by
  intro n hn
  rw [actionReadFrom_h_max₅₄b facts S _ r n hn]
  exact (Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf v
      (Restated.Vocabulary.Execution.Setup.a M S r)).trans
    ((Restated.stateAt_h_max_monoOn facts S Hs Xb hf v hle).trans
      (Finset.le_sup (f := fun u => (W (inclusiveEventIndex rho endpoint) u).st.core.h_max) hv))

/-- Under the bundle along `W`, if `0 < s`, the proposer of `s` is in `Hs` of `s`'s confirmation
    time, `lo ≤ proposal_time s` and the proposal time is inside the horizon, then a block `B` the
    proposer can propose with the cache outcome `c` has height at most the `h_max` of the proposer's
    store in the world of `W` at `proposal_time s`. -/
theorem proposedBlock_height_le_proposer_hMax_l54 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    (M.derive_named S.E S.cfg B).h ≤
      (W (inclusiveEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.h_max := by
  obtain ⟨i, hacc⟩ :=
    Restated.acceptsAt_proposedBlockOn facts S Hs Xb hf hHs hs hprop hhor hgat hneTick hrun c hc hB
  have hBmem : B ∈ (W (i + 1) (S.E.proposer s)).st.bodies :=
    of_decide_eq_true hacc.2.2
  have hheightLe :
      (M.derive_named S.E S.cfg B).h ≤ (W (i + 1) (S.E.proposer s)).st.core.h_max :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho (i + 1)
      (S.E.proposer s) _ (hf.onePath (i + 1)).1 B hBmem
  obtain ⟨_, e, hie, _, hetime⟩ := hacc.1
  have hi : i < inclusiveEventIndex rho (M.proposal_time S.E s) := by
    unfold inclusiveEventIndex
    exact Restated.index_lt_stateAt_lengthOn facts S Hs Xb hf hie (le_of_eq hetime)
  exact hheightLe.trans
    (Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho (S.E.proposer s)
      (Nat.succ_le_iff.mpr hi) _ (hf.onePath (i + 1)).1 _
      (onePath_slice₅₄b W hf.onePath (Nat.succ_le_iff.mpr hi)))

/-- The round-`r` action read from any node state has some node state. -/
private theorem actionReadFrom_nonempty₅₄b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- If the validators outside `X` weigh less than a third, `B` is a proposed block of slot `s` whose
    parent has a mature timeout at `s` and is at height `H` with target root `T`, and every member
    of `X` attests, at every round-`r` action read from its node state in the world `wa` before
    `S.a r`, a block covered by `B`'s parent chain or included in `B` with the height pair `(H, T)`,
    then `B` is at height `H + 1`. -/
private theorem named_proposedBlock_height_eq_succ_along₅₄b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (X : Finset V) {r : Round}
    (hfb : Execution.BelowOneThird S X)
    {s : Slot} {H : Height} {T : BlockId}
    {B : NamedBlock V} (hB : some B ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s)
    (hmatureB : ∀ P : NamedBlock V, NamedBlock.parent? B = some P →
      (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ s)
    (wa : V → M.N)
    (hwa : wa ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcoverage : ∀ v ∈ X,
      ∀ nA ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wa v) r,
      ∀ D, M.duties_attest_with (M.gradeContract nA.cache) S.E S.hc (S.node v) nA.st nA.record ⇢ D →
        ((D.2.2 ∈ named_chain_attestations B.parent ∧
            v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
            (D.2.2.height_pair = NamedHeightPair.vote H T false →
              v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
          D.2.2 ∈ B.attestations) ∧
        (D.2.2.height_pair = NamedHeightPair.vote H T false ∨
          D.2.2.height_pair = NamedHeightPair.vote H T true))
    (hPheight : (M.derive_named S.E S.cfg B.parent).h = H)
    (hPtarget :
      (M.derive_named S.E S.cfg B.parent).T_h.root = T) :
    (M.derive_named S.E S.cfg B).h = H + 1 := by
  obtain ⟨nP, hnP, hnPB⟩ := id hB
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract nP.cache) S.E
    S.hc (S.node (S.E.proposer s)) (M.toHealing nP.st.core)
  obtain ⟨parent, hparent, -⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho s nP hnP hnPB
      input hinput
  have hslotB : B.slot = s :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s (some B) hB rfl
  cases B with
  | genesis => cases hparent
  | node parent' slot root votes support rows proposer =>
      have hparentEq : parent' = parent := Option.some.inj hparent
      subst parent
      rw [Proofs.ModelProperties.named_parent_node] at hPheight hPtarget hcoverage
      let sigma := M.derive_named S.E S.cfg parent'
      let block : NamedBlock V :=
        .node parent' slot root votes support rows proposer
      have hslot : slot = s := by
        exact (named_node_slot parent' slot root votes support rows proposer).symm.trans hslotB
      have hm := hmatureB parent' rfl
      change sigma.T_h.slot + S.cfg.timeoutDelay ≤ s at hm
      rw [facts.cs.derive_named_node_h_eq_succ_of_progressQuorum S.E S.cfg parent' slot root votes support
        rows proposer X ((isQuorum_iff_q_le S.E X).mpr
          (AlignedRoundLemmas.honestQuorum_of_belowOneThird hfb)) (hslot ▸ hm)]
      · exact congrArg (· + 1) hPheight
      · intro v hv
        obtain ⟨nA, hnA'⟩ := actionReadFrom_nonempty₅₄b facts S (wa v) r
        have hnA : nA ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r :=
          ⟨wa, hwa, hnA'⟩
        obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nA.cache) S.E S.hc
          (S.node v) nA.st nA.record
        obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nA.cache) S.E S.hc
          (M.toHealing nA.st.core) (M.round_of S.hc (M.toHealing nA.st.core).s)
        obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract nA.cache) S.E S.hc
          (M.toHealing nA.st.core) (M.round_of S.hc (M.toHealing nA.st.core).s) g2
        obtain ⟨hcovered, hpair⟩ := hcoverage v hv nA hnA' D hD
        rw [named_node_attestations] at hcovered
        rcases hcovered with hparentCovered | hchild
        · exact Or.inl hparentCovered.2.1
        · refine Or.inr ⟨_, hchild,
            (Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho v r nA hnA
              D hD g2 hg2 G hG).1, ?_⟩
          rcases hpair with htarget | htimeout
          · rw [htarget, matchesEntry_vote_iff]
            exact And.intro hPheight.symm hPtarget.symm
          · rw [htimeout, matchesEntry_vote_iff]
            exact And.intro hPheight.symm hPtarget.symm

end

/-! ## The named grade, the retention and the timeout maturity in the world of `W` -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-- Under the bundle along `W`, if every member of `Hs (domain q .g2)` has `source.erase` active
    with grade `true` in the world of `W` before that time, `source` is a run block read through
    `Xb`, the reader is in that set and `S.a q ≤ read`, then `source` is a body of the reader's
    store before `read`. -/
private theorem formsW_namedGradeSource_mem₅₄b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} {source : NamedBlock V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      source.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st q .g2 source.erase ⇢ b →
            b = true)
    (hsourceRun : Restated.RunBlockOn M S rho W Xb source)
    {reader : V}
    (hreader : reader ∈ Hs (M.domain S.E S.hc q .g2))
    {read : Time} (hle : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ read) :
    source ∈ (W (strictEventIndex rho read) reader).st.bodies := by
  have hsourceMem : source.erase ∈ (W (strictEventIndex rho read) reader).st.T :=
    (priv% Proofs.Claims.Restated.Claim13beRoute3_54
      DecoupledConsensusModel.Sts.Restated.formsW_processedAtRead₅₄s) facts
      S Hs Xb hf hformsW hreader hle
  obtain ⟨D, hDbody, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts
      S rho read reader _ (mem_stateBeforeTime_along₅₄b hf.sorted hf.onePath read) hsourceMem
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hreader) hDbody
  have hDsource : D = source :=
    Restated.lifecycle_runBlock_unique_of_erase_eqOn facts hf hDrun hsourceRun hDerase
  rw [← hDsource]
  exact hDbody

/-- If every member of `Hs` at round `r`'s grade-2 domain time has `C` active with grade `true` in
    `W`, `v ∈ Hs (domain r .g0)`, and `C` is active at a node state `n` of `v`'s round-`r` action
    read, then every outcome of `n`'s Q2 read is `some Q` with `C` an ancestor of `Q`. -/
private theorem formsW_preceq_actionQ2₅₄b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) {r : Round} (hr : 0 < r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) {C : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 C ⇢ b → b = true)
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
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
  have hbtrue : b = true := (hformsW v hvG2).2 b hb
  subst hbtrue
  exact Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
    (hformsW v hvG2).1 hb n hn hactive

/-- Under the bundle along `W`, with the named grade of `C` read in the world of `W` before round
    `r`'s grade-2 domain time and `C.erase` in the filtered tree of `v`'s store before `S.a r`,
    every attestation of `v`'s round-`r` action read votes `(H, T)`, or `H` is less than that node
    state's `h_max`. -/
private theorem formsW_actionAttestationAt_pair_or_hMaxRise₅₄b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {C : NamedBlock V} {H : Height} {T : BlockId}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      C.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 C.erase ⇢ b → b = true)
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : (M.derive_named S.E S.cfg C).h = H)
    (hCtarget : (M.derive_named S.E S.cfg C).T_h.root = T)
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (hwindowW : C.erase ∈ M.get_filtered_block_tree (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    (D.2.2.height_pair = .vote H T false ∨ D.2.2.height_pair = .vote H T true) ∨
      H < n.st.core.h_max := by
  intro ast hast D hD
  have hW := hf.onePath
  have hwmem := mem_stateBeforeTime_along₅₄b hf.sorted hW (Restated.Vocabulary.Execution.Setup.a M S r)
  have hmem : ast ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)), hwmem, hast⟩
  have hactive : C.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M ast :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v)
      _ hwmem hwindowW ast hast
  have hround : (M.round_of S.hc (M.toHealing ast.st.core).toFG.toSG.toGoldfishStore.s) = r := by
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r ast hmem
  have hround' : M.round_of S.hc (M.toHealing ast.st.core).s = r := hround
  have hsrcEq : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S ast =
      Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S ast r := by
    simp only [Restated.Vocabulary.Proofs.HealingSurface.actionFGSource,
      Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource]
    rw [hround']
    rfl
  obtain ⟨o, ho⟩ := (priv% Proofs.Claims.Restated.Claim13beRoute3_51
    DecoupledConsensusModel.Sts.Restated.actionFGSource_nonempty₅₁) facts S ast
  rw [hsrcEq] at ho
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract ast.cache) S.E S.hc
    (M.toHealing ast.st.core) r
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S ast r ⇢ G.Q2 := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₅₄b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG
  obtain ⟨Q2, hQ2, hCQ2⟩ := formsW_preceq_actionQ2₅₄b facts S Hs Xb hf hHs hr hhor hformsW hv
    ast hast hactive hlo _ hGq
  rw [hQ2] at hGq
  obtain ⟨Q, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.exists_actionFGSource_of_actionQ2 facts
    S rho v r _ hwmem ast hast hGq o ho
  have hsource := ho
  have hsource' : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S ast ⇢ some Q := by
    rw [hsrcEq]
    exact hsource
  obtain ⟨DQ, hDQ, hDQerase, hDQderive, -⟩ :=
    Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho v r ast hmem Q hsource'
  have hDQrun : Restated.RunBlockOn M S rho W Xb DQ :=
    Restated.actionBody_runBlock_coverageOn facts S Hs Xb hf (hHsXb _ hv) hast hDQ
  have hCQerase : Block.Preceq C.erase DQ.erase := by
    rw [hDQerase]
    exact Restated.Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 facts S rho v r _
      hwmem ast hast hGq hCQ2 hsource
  obtain ⟨A, hADQ, hAerasure⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift DQ hCQerase
  have hArun : Restated.RunBlockOn M S rho W Xb A :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hDQrun hADQ
  have hAC : A = C :=
    hf.rootCollisionFree.root_injective
      A C hArun hCrun A C (Or.inl (Proofs.NamedAncestry.named_self A))
        (Or.inr (Proofs.NamedAncestry.named_self C)) (by
          rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root C,
            hAerasure])
  have hCQ : NamedBlock.Preceq C DQ := by
    rw [← hAC]
    exact hADQ
  have hfloor : H ≤ (ast.st.core.σ Q).h := by
    rw [hDQderive, ← hCheight]
    exact facts.cs.derive_height_mono S.E S.cfg hCQ
  have hcap : (ast.st.core.σ Q).h ≤ ast.st.core.h_max := by
    apply Restated.treeHeightsLeHMax_actionStoreOn facts S Hs Xb hf v r ast hast Q
    have hinv := (priv% Proofs.Claims.Restated.Claim13beRoute3_51
      DecoupledConsensusModel.Sts.Restated.actionReadFrom_invariant₅₁) facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho _ v _ hwmem).1
      ast hast
    rw [hinv.1.1.1, ← hDQerase]
    exact Finset.mem_image_of_mem NamedBlock.erase hDQ
  have hsourceCases :
      ((ast.st.core.σ Q).h = H ∧
        (ast.st.core.σ Q).T_h.root = T) ∨
        H < ast.st.core.h_max := by
    rcases eq_or_lt_of_le hfloor with heq | hlt
    · left
      have hsame : (M.derive_named S.E S.cfg DQ).h =
          (M.derive_named S.E S.cfg C).h := by
        calc
          _ = (ast.st.core.σ Q).h :=
            congrArg (fun X => X.h) hDQderive.symm
          _ = H := heq.symm
          _ = _ := hCheight.symm
      have htargetEq := facts.cs.entry_eq_on_plateau
        S.E S.cfg hCQ hsame.symm
      refine ⟨heq.symm, ?_⟩
      calc
        (ast.st.core.σ Q).T_h.root =
            (M.derive_named S.E S.cfg DQ).T_h.root :=
          congrArg (fun X => X.T_h.root) hDQderive
        _ = (M.derive_named S.E S.cfg C).T_h.root :=
          congrArg (fun X => X.root) htargetEq.symm
        _ = T := hCtarget
    · exact Or.inr (hlt.trans_le hcap)
  rcases hsourceCases with ⟨hQheight, hQtarget⟩ | hrise
  · have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionSource M (M.gradeContract ast.cache)
        S.E S.hc (M.toHealing ast.st.core) ⇢ some Q := hsource'
    obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract ast.cache) S.E S.hc
      (S.node v) (M.toHealing ast.st.core) ast.record
    have hDA : D.2.2 = A.2 := facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA
    have hcases := Restated.Vocabulary.Proofs.HealingSurface.round_action_height_pair_cases facts
      (M.gradeContract ast.cache) S.E S.hc (S.node v)
      (M.toHealing ast.st.core) ast.record (some Q) hsrc A hA
    have hσ : (M.toHealing ast.st.core).σ = ast.st.core.σ :=
      facts.sto.ModelProperties_toHealing_σ _
    rcases hcases with hnone | ⟨Q', hQ', hresult⟩
    · exact absurd hnone.1 (by simp)
    · have hQeq : Q' = Q := Option.some.inj hQ'.symm
      subst Q'
      rcases hresult with hoff | htarget | htimeout
      · right
        obtain ⟨locked, -, hown, -, -⟩ := hoff
        apply Restated.ownLockHeight_lt_actionHMax_namedOn facts S Hs Xb hf v r (locked := locked)
          ast hast D hD
        rw [hDA, ← (priv% Proofs.Claims.Restated.Claim13beRoute3_51
          DecoupledConsensusModel.Sts.Restated.actionReadFrom_record₅₁) facts S _ r ast hast,
          ← hQheight, ← hσ]
        exact hown
      · left; left
        rw [hσ, hQheight, hQtarget] at htarget
        rw [hDA]
        exact htarget
      · left; right
        rw [hσ, hQheight, hQtarget] at htimeout
        rw [hDA]
        exact htimeout
  · exact Or.inr hrise

/-- Under the bundle along `W`, with `C.erase` in the filtered tree of `v`'s store before `S.a r`,
    every round-`r` attestation of `v` carrying `(H, T)` is on the named chain of `B`'s parent with
    `v` in its progress set, or is among `B`'s attestations. -/
private theorem windowW_actionAttestationAt_coveredAtProposal₅₄b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {C : NamedBlock V} {H : Height} {T : BlockId}
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : (M.derive_named S.E S.cfg C).h = H)
    (hCtarget : (M.derive_named S.E S.cfg C).T_h.root = T)
    {s : Slot} {B : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c) .poolAndCarried
      S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B)
    (hCP : NamedBlock.Preceq C B.parent)
    (hPheight :
      (M.derive_named S.E S.cfg B.parent).h = H)
    (hprop : S.E.proposer s ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E s)
    {v : V} (hv : v ∈ Hs (M.proposal_time S.E s))
    (hwindowW : C.erase ∈ M.get_filtered_block_tree (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG)
    (hinWindow : M.inWindow S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)).core r = true)
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ ast ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract ast.cache) S.E S.hc (S.node v) ast.st ast.record ⇢ D →
    (D.2.2.height_pair = .vote H T false ∨ D.2.2.height_pair = .vote H T true) →
    ((D.2.2 ∈ Protocol.named_chain_attestations B.parent ∧
        v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
        (D.2.2.height_pair = .vote H T false →
          v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
      D.2.2 ∈ B.attestations) := by
  intro ast hast D hD hpair
  have hFchain := facts.dt.chainRows_iff_named_chain
  have hFprog := facts.csAdded.namedPair_mem_progress_of_suffix_same_height
  have hFtarget := facts.csAdded.namedTarget_mem_of_suffix_same_height
  have hW := hf.onePath
  have hwmem := mem_stateBeforeTime_along₅₄b hf.sorted hW (Restated.Vocabulary.Execution.Setup.a M S r)
  set a := D.2.2 with ha
  set pr := M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
    (M.proposal_time S.E s) with hpr
  have hmem : ast ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)), hwmem, hast⟩
  have hdelayLe : (Restated.Vocabulary.Execution.Setup.a M S r) ≤
      (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ :=
    le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hvDelta : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ hdelay hv
  have hvA : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) := hHs _ _ hdelayLe hvDelta
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    hdelayLe.trans (hdelay.trans hhor)
  have hemitV : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a)
      (Restated.Vocabulary.Execution.Setup.a M S r) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf r hvA hactionHor hpost hA
      (fun j hj => hf.tick_outcome j _ _ hj) ast hast D hD
  have haVal : a.val_index = v :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemitV).1
  have haRound : a.round = r := by
    obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract ast.cache) S.E S.hc
      (M.toHealing ast.st.core) (M.round_of S.hc (M.toHealing ast.st.core).s)
    obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract ast.cache) S.E S.hc
      (M.toHealing ast.st.core) (M.round_of S.hc (M.toHealing ast.st.core).s) g2
    exact (Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho v r ast hmem
      D hD g2 hg2 G hG).2.1
  have hemit : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index
      (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [haVal, haRound]
    exact hemitV
  have hemitAtR : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index
      (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
    rw [haVal]
    exact hemitV
  have hactive : C.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M ast :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v)
      _ hwmem hwindowW ast hast
  have hCcore : C.erase ∈ ast.st.core.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hactive
    rw [facts.sto.toHealing_T] at h
    exact h
  have hinv := (priv% Proofs.Claims.Restated.Claim13beRoute3_51
    DecoupledConsensusModel.Sts.Restated.actionReadFrom_invariant₅₁) facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho _ v _ hwmem).1
    ast hast
  have hcoh := hinv.1.1
  have hCimage := hCcore
  rw [hcoh.1] at hCimage
  obtain ⟨C', hC', hCerase⟩ := Finset.mem_image.mp hCimage
  have hC'run : Restated.RunBlockOn M S rho W Xb C' :=
    Restated.actionBody_runBlock_coverageOn facts S Hs Xb hf (hHsXb _ hvA) hast hC'
  have hC'eq : C' = C :=
    hf.rootCollisionFree.root_injective
      C' C hC'run hCrun C' C
        (Or.inl (Proofs.NamedAncestry.named_self C'))
        (Or.inr (Proofs.NamedAncestry.named_self C)) (by
          rw [← Proofs.NamedWire.erase_root C', ← Proofs.NamedWire.erase_root C,
            hCerase])
  have hCpre : C ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.bodies := by
    rw [← hC'eq, ← (priv% Proofs.Claims.Restated.Claim13beRoute3_51
      DecoupledConsensusModel.Sts.Restated.actionReadFrom_bodies₅₁) facts S _ r ast hast]
    exact hC'
  have hnotC := Restated.emittedAttestation_not_mem_named_chain_beforeOn facts
    S Hs Xb hf hHs hvA hemitV hCpre
  have hprocessed := Restated.honestAttestation_mem_processedAtProposal_after_gstOn facts
    S Hs Xb hf hHs hhor (by rw [haVal]; exact hvDelta) hprop hemitAtR hpost hdelay
  have haProcessed := Restated.exactRow_mem_namedProcessedOn facts
    S Hs Xb hf hHs (by rw [haVal]; exact hv) hemit hprocessed
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc pr
  have haSelected : a ∈ L :=
    facts.dt.mem_select_of_processed_inWindow .poolAndCarried S.hc _ haProcessed
      (by rw [haRound]; exact hinWindow) L hL
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing pr.core)
  have _hrs_pr : M.reachedStore pr := facts.sto.reachedStore_setClock S.E _ _
    (facts.nd.reachedStore_of_node _ (facts.ndRun.stateBeforeOf_reachedNode S rho _ (W _)
      (hf.onePath _).1 (S.E.proposer s)))
  have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts
    (M.gradeContract c) .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) pr B hB input hinput L hL
  by_cases hchain : a ∈ M.chainRows B.parent
  · left
    have hchain' := (hFchain B.parent a).mp hchain
    refine ⟨hchain', ?_, ?_⟩
    · rw [← haVal]
      apply hFprog S.E S.cfg hCP hchain' hnotC
      · rw [hPheight, hCheight]
      · rw [hCheight, hCtarget]
        exact hpair
    · intro htarget
      rw [← haVal]
      apply hFtarget S.E S.cfg hCP hchain' hnotC
      · rw [hPheight, hCheight]
      · rw [hCheight, hCtarget]
        exact htarget
  · right
    rw [hpay.2.2.2.2.2.2.1]
    apply facts.dt.mem_proposalRows_of_unique B.parent _ a haSelected hchain
    intro b hb hval hround
    exact Restated.honest_selected_row_uniqueOn facts S Hs Xb hf hHs s L hL haSelected hb
      (by rw [haVal]; exact hv) hval hround

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
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if the validators outside `Hs` weigh less than a third, round
    `q > 0` is a carrier round, `source` is a run block of height `H` with the named grade of round
    `q − 1` and is in the filtered trees of the members of `Hs` at the reads of rounds `q − 1` and
    `q`, and `B` is the block the proposer of `q`'s opening slot can propose with the cache outcome
    `c`, then either the largest `h_max` over `Hs endpoint` exceeds `H`, or the proposer's store
    before its proposal time shows fixed-height root interference, or
    `ActiveExactHeightProposalRootCarrierAtOn` holds at `endpoint` for some root. -/
theorem activeExactHeightOpeningLifecycle_or_hMaxRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {q : Round} {source : NamedBlock V} {endpoint : Time} {B : NamedBlock V}
    (hq : 0 < q)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hformsPrev : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      source.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2 source.erase ⇢ b →
            b = true)
    (hwindowPrev : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      source.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core).toFG)
    (hdomainWindow : ∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      source.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.core).toFG)
    (hsourceRun : Restated.RunBlockOn M S rho W Xb source)
    (hsourceHeight :
      (M.derive_named S.E S.cfg source).h = H)
    (hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hmature : ∀ P : NamedBlock V, NamedBlock.parent? B = some P →
      (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q)
    (hactiveAtAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      source.erase ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.core).toFG)
    (hactionEnd : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1))
    (hpropFrontier : Restated.ProposerProposalStoreBelowFrontierOn M S rho Hs q endpoint
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))))
      (W (inclusiveEventIndex rho endpoint)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some B) :
    H < ((Hs endpoint).sup fun v => (W (inclusiveEventIndex rho endpoint) v).st.core.h_max) ∨
      (Restated.FixedHeightRootInterferenceAtReadOn M S rho W Hs Xb H
          (S.E.proposer (M.opening_slot S.hc q))
          (M.proposal_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))))
          source.erase ∧
        M.proposal_time S.E (M.opening_slot S.hc q) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) ∧
        (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint ∧ endpoint ≤ rho.horizon) ∨
      ∃ root : NamedBlock V,
        Restated.ActiveExactHeightProposalRootCarrierAtOn M
          S rho W (fun t => W (strictEventIndex rho t)) (W (inclusiveEventIndex rho endpoint))
          Hs Xb H q endpoint source root c := by
  -- The proposer of `q`'s opening slot passes the grade-1 awake test at its proposal time.
  have hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q)) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc q]
      have h1 := facts.gr.lo_le_early_g2_of_window_start S hq (hloOpen.trans
        (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right (Nat.sub_le q 1) _)))
      have h2 := facts.gr.early_g2_add_delta_le_early_g1 S q
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) (hcarrier 0 (by decide))) hwin
  set s := M.opening_slot S.hc q with hs_def
  set p := S.E.proposer s with hp_def
  set read := M.proposal_time S.E s with hread_def
  set wr := W (strictEventIndex rho read) with hwr_def
  have hwr : wr ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read :=
    mem_stateBeforeTime_along₅₄b hf.sorted hf.onePath read
  have hconfA : M.confirmation_time S.E s = (Restated.Vocabulary.Execution.Setup.a M S q) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E q).symm
  have hpropConf : p ∈ Hs (M.confirmation_time S.E s) := by
    simpa only [s, add_zero] using hcarrier 0 (by decide)
  have hprop : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)) := by
    simpa only [hconfA] using hpropConf
  have hproposalAction : read ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    rw [hread_def, ← hconfA]
    exact facts.sch.proposal_time_le_confirmation_time S.E _
  have hreadEnd : read ≤ endpoint := hproposalAction.trans hactionEnd
  have hreadHor : read ≤ rho.horizon := hreadEnd.trans hendHor
  have hround : (M.round_of S.hc s) = q := by
    simpa only [s] using facts.gr.round_of_opening_slot_eq S.hc q
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤ read := by
    simpa only [read, hround] using
      (Restated.Vocabulary.Protocol.previous_action_add_delta_le_proposal facts S
        (s := s) (by simpa only [hround] using hq))
  have hprevActionRead : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ read :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay
  have hgatRead : lo ≤ read := hlo.trans hprevActionRead
  have hpropRead : p ∈ Hs read := hHs _ _ hproposalAction hprop
  have hpropDomPrev : p ∈ Hs (M.domain S.E S.hc (q - 1) .g2) :=
    hHs _ _ ((facts.gr.domain_le_a S (q - 1) .g2).trans
      (hprevActionRead.trans hproposalAction)) hprop
  have hsourceMem : source ∈ (wr p).st.bodies :=
    formsW_namedGradeSource_mem₅₄b facts
      S Hs Xb hf hHsXb hformsPrev hsourceRun hpropDomPrev hprevActionRead
  by_cases hriseEnd : H < ((Hs endpoint).sup fun v => (W (inclusiveEventIndex rho endpoint) v).st.core.h_max)
  · exact Or.inl hriseEnd
  have hcapEnd : ((Hs endpoint).sup fun v => (W (inclusiveEventIndex rho endpoint) v).st.core.h_max) ≤ H :=
    Nat.le_of_not_gt hriseEnd
  have hpropCap : (W (inclusiveEventIndex rho read) p).st.core.h_max ≤ H :=
    hpropFrontier.trans hcapEnd
  have hfrontier : (wr p).st.core.h_max = H := by
    apply Nat.le_antisymm
    · exact (Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf p read).trans hpropCap
    · rw [← hsourceHeight]
      exact Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts
        S rho read p wr hwr source hsourceMem
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hFT : M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (wr p).st.core read)).toFG =
        M.get_filtered_block_tree (M.toHealing (wr p).st.core).toFG :=
    facts.fc.get_filtered_block_tree_set_clock_slot _ _ _
  have hFR : M.get_fg_root
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (wr p).st.core read)).toFG =
        M.get_fg_root (M.toHealing (wr p).st.core).toFG :=
    facts.fc.get_fg_root_set_clock_slot _ _ _
  by_cases hactive : source.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (wr p).st.core read)).toFG
  · have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq
    have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q - 1 + 1) ≤ rho.horizon :=
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S (q - 1))).trans
        (by rw [hpred]; exact hactionEnd.trans hendHor)
    have ho : M.proposal_with (M.gradeContract c) .poolAndCarried S.E S.hc
        (S.node p) (M.ns_setClock S.E (wr p).st read) ⇢ some B := hB
    have hoMem : some B ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s :=
      ⟨M.mkNode (M.ns_setClock S.E (wr p).st read) (wr p).record c, ⟨wr, hwr, c, hc, rfl⟩,
        by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
           exact ho⟩
    have hspos : 0 < s := facts.gr.opening_slot_pos_of_round_pos S.hc hq
    have hBRun : Restated.RunBlockOn M S rho W Xb B :=
      Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb s hspos hpropConf
        hreadHor hgatRead (fun j hj => hf.tick_outcome j _ _ hj) hrun c hc ho
    have hparentRun : Restated.RunBlockOn M S rho W Xb B.parent :=
      Restated.blockInRun_of_ancestorOn facts S rho W Xb hBRun
        ((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RawHeightActiveLifecycle
          DecoupledConsensusModel.Proofs.HealingSurface.lifecycle_parent_preceq) B)
    have hparentMem : B.parent ∈ (wr p).st.bodies := by
      obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc (S.node p)
        (M.toHealing (M.ns_setClock S.E (wr p).st read).core)
      obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc (M.ns_setClock S.E (wr p).st read)
      have _hrs_w : M.reachedStore (M.ns_setClock S.E (wr p).st read) :=
        facts.sto.reachedStore_setClock S.E _ read
          (facts.nd.reachedStore_of_node _ (Record.reachedNode_stateBeforeTime facts S rho read wr hwr p))
      have h := (facts.dt.proposal_payload (M.gradeContract c) .poolAndCarried S.E S.hc (S.node p)
        (M.ns_setClock S.E (wr p).st read) B (some B) ho rfl I hI L hL).1
      rwa [facts.hd.Sts_setClock_bodies] at h
    have hprevActionHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
      hprevActionRead.trans hreadHor
    have hprevPositive : 0 < q - 1 := by
      by_contra hnonpos
      have hzero : q - 1 = 0 := Nat.eq_zero_of_not_pos hnonpos
      have hdomHor : M.domain S.E S.hc (q - 1) .g2 ≤ rho.horizon :=
        (facts.gr.domain_le_a S (q - 1) .g2).trans hprevActionHor
      obtain ⟨w, hw⟩ := nonempty_of_honestWeightMajority_l54 (hmajority _ hdomHor)
      have hgrade := (hformsPrev w hw).2
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
        (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) w).st.core).gradeView
        (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) w).st.core.F S.hc.η_SG (q - 1)
        (M.early S.E S.hc (q - 1) .g2) (M.late S.E S.hc (q - 1) .g2) source.erase
      have htrue := hgrade b hb
      rw [hzero] at hb
      have hfalse := facts.gr.gradeBool_round_zero _ _ _ _ _ _ _ _ hb
      rw [htrue] at hfalse
      exact Bool.noConfusion hfalse
    have hloOpen' : lo ≤ M.opening S.E S.hc (q - 1 + 1 - S.hc.η_SG) :=
      hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
        (Nat.sub_le_sub_right (Nat.le_succ (q - 1)) _))
    have hclean : Restated.CleanActionReadForOn M S rho Hs (q - 1)
        (fun t => W (strictEventIndex rho t)) source.erase := by
      apply (priv% Proofs.Claims.Restated.Claim13beRoute3_54
        DecoupledConsensusModel.Sts.Restated.formsW_cleanActionReadFor₅₄s) facts
        S Hs Xb hf hHs hHsXb hprevPositive hformsPrev hpostPrev hcut
      · intro v hv
        exact Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v)
          _ (mem_stateBeforeTime_along₅₄b hf.sorted hf.onePath _) (hwindowPrev v hv)
      · intro w hw
        rw [hpred] at hw ⊢
        exact hactiveAtAction w hw
      · intro w hw
        rw [hpred] at hw ⊢
        exact hdomainWindow w hw
      · exact hA
      · exact hlo
      · exact hloOpen
    have hsourceParent : Block.Preceq source.erase B.parent.erase := by
      have hfloor :=
        Restated.protected_preceq_nextOpeningProposedParent_of_cleanActionReadOn facts
          S Hs Xb hf hHs hHsXb hmajority hclean
            (by rw [hpred]; exact hprop)
            (by rw [hpred]; exact hactive)
            c (by rw [hpred]; exact hc)
            (by rw [hpred]; exact ho)
            hlo hA hloOpen'
      simpa only [Proofs.NamedWire.erase_parent] using hfloor
    have hsourceParentNamed : NamedBlock.Preceq source B.parent :=
      Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hsourceRun hparentRun hsourceParent
    have hparentHeight :
        (M.derive_named S.E S.cfg B.parent).h = H := by
      apply Nat.le_antisymm
      · exact (Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts
          S rho read p wr hwr B.parent hparentMem).trans_eq hfrontier
      · rw [← hsourceHeight]
        exact facts.cs.derive_height_mono S.E S.cfg hsourceParentNamed
    have hinWindow : M.inWindow S.hc (M.ns_setClock S.E (wr p).st read).core (q - 1) = true := by
      rw [facts.dt.inWindow_iff, facts.hd.Sts_setClock_core_s, hread_def, facts.sch.slotOf_proposal_time,
        hround]
      have heta := S.hc.η_SG_ge_one
      exact ⟨Nat.sub_le_sub_left heta q, Nat.sub_le q 1⟩
    have hsourceTarget :
        (M.derive_named S.E S.cfg source).T_h.root = (M.derive_named S.E S.cfg source).T_h.root :=
      rfl
    have hpropDelta : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ) :=
      hHs _ _ (hdelay.trans hproposalAction) hprop
    have hwa := mem_stateBeforeTime_along₅₄b hf.sorted hf.onePath
      (Restated.Vocabulary.Execution.Setup.a M S (q - 1))
    have hparentTarget :
        (M.derive_named S.E S.cfg B.parent).T_h.root =
          (M.derive_named S.E S.cfg source).T_h.root :=
      congrArg (fun X => X.root)
        (facts.cs.entry_eq_on_plateau S.E S.cfg
          hsourceParentNamed
          (by rw [hsourceHeight, hparentHeight])) |>.symm
    have hproposalHeight : (M.derive_named S.E S.cfg B).h = H + 1 := by
      refine named_proposedBlock_height_eq_succ_along₅₄b facts S (Hs endpoint) (hfb endpoint hendHor)
        hoMem hmature _ hwa ?_ hparentHeight hparentTarget
      intro v hv nA hnA D hD
      have hvPrev : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
        hHs _ _ (hprevActionRead.trans hreadEnd) hv
      have hvG0 : v ∈ Hs (M.domain S.E S.hc (q - 1) .g0) :=
        hHs _ _ (facts.gr.domain_le_a S (q - 1) .g0) hvPrev
      have hvRead : v ∈ Hs read := hHs _ _ hreadEnd hv
      have hvDelta : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ) :=
        hHs _ _ hdelay hvRead
      rcases formsW_actionAttestationAt_pair_or_hMaxRise₅₄b facts
          S Hs Xb hf hHs hHsXb hprevPositive hprevActionHor hformsPrev hsourceRun
            hsourceHeight hsourceTarget hvG0 (hwindowPrev v hvPrev) hloOpen nA hnA D hD with
        hpair | hlocal
      · refine ⟨?_, hpair⟩
        exact windowW_actionAttestationAt_coveredAtProposal₅₄b facts
          S Hs Xb hf hHs hHsXb hsourceRun hsourceHeight hsourceTarget c hc ho
            hsourceParentNamed hparentHeight hpropDelta hreadHor hlo
            hdelay hvRead (hwindowPrev v hvPrev) hinWindow (hA v hvDelta) nA hnA D hD hpair
      · have hpublic := hlocal.trans_le
          (Restated.actionStore_hMax_le_honestHMaxAt_lifecycleOn facts
            S Hs Xb hf hv (hprevActionRead.trans hreadEnd) nA hnA)
        exact False.elim (hriseEnd hpublic)
    have hproposalLocal := Restated.proposedBlock_height_le_proposer_hMax_l54 facts
      S Hs Xb hf hHs hspos hpropConf hreadHor hgatRead (fun j hj => hf.tick_outcome j _ _ hj) hrun c hc ho
    have hsuccLe : H + 1 ≤ H := by
      rw [← hproposalHeight]
      exact hproposalLocal.trans hpropCap
    exact False.elim (Nat.not_succ_le_self H hsuccLe)
  · set nr := M.mkNode (M.ns_setClock S.E (wr p).st read) (wr p).record c with hnr_def
    have hnFT : Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nr =
        M.get_filtered_block_tree (M.toHealing (wr p).st.core).toFG := by
      show M.get_filtered_block_tree (M.toHealing nr.st.core).toFG = _
      rw [hnr_def, facts.nd.mkNode_st, facts.nd.store_with_cache_get_filtered_block_tree,
        setClock_core_tickStore₅₄b facts S, hFT]
    have hnFR : M.get_fg_root (M.toHealing nr.st.core).toFG =
        M.get_fg_root (M.toHealing (wr p).st.core).toFG := by
      rw [hnr_def, facts.nd.mkNode_st, facts.nd.store_with_cache_get_fg_root,
        setClock_core_tickStore₅₄b facts S, hFR]
    have hrootActive : M.get_fg_root (M.toHealing (wr p).st.core).toFG ∈
        M.get_filtered_block_tree (M.toHealing (wr p).st.core).toFG :=
      Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts
        S rho read p wr hwr
    have hrootMem : M.get_fg_root (M.toHealing (wr p).st.core).toFG ∈ (wr p).st.core.T := by
      have h2 := facts.fc.get_filtered_block_tree_subset _ hrootActive
      rw [facts.sto.toHealing_gs_T] at h2
      exact h2
    obtain ⟨rootNamed, hrootBody, hrootErase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts
        S rho read p wr hwr hrootMem
    have hrootRun : Restated.RunBlockOn M S rho W Xb rootNamed :=
      Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hpropRead) hrootBody
    have hactive' : source.erase ∉ M.get_filtered_block_tree (M.toHealing (wr p).st.core).toFG := by
      rw [← hFT]; exact hactive
    by_cases hsourceRoot : Block.Preceq source.erase (M.get_fg_root (M.toHealing (wr p).st.core).toFG)
    · have hsourceRootErase : Block.Preceq source.erase rootNamed.erase := by
        rw [hrootErase]
        exact hsourceRoot
      have hsourceRootNamed : NamedBlock.Preceq source rootNamed :=
        Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hsourceRun hrootRun hsourceRootErase
      have hne : source.erase ≠ rootNamed.erase := by
        intro heq
        apply hactive'
        rw [heq, hrootErase]
        exact hrootActive
      have hsourceStrict : Block.Prec source.erase rootNamed.erase :=
        Proofs.ModelProperties.Prec_of_ne_of_Preceq hne hsourceRootErase
      have hrootHeight :
          (M.derive_named S.E S.cfg rootNamed).h = H := by
        apply Nat.le_antisymm
        · exact (Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts
            S rho read p wr hwr rootNamed hrootBody).trans_eq hfrontier
        · rw [← hsourceHeight]
          exact facts.cs.derive_height_mono S.E S.cfg hsourceRootNamed
      have hrootTarget :
          (M.derive_named S.E S.cfg rootNamed).T_h.root =
            (M.derive_named S.E S.cfg source).T_h.root :=
        congrArg (fun X => X.root)
          (facts.cs.entry_eq_on_plateau S.E S.cfg
            hsourceRootNamed (by rw [hsourceHeight, hrootHeight])) |>.symm
      have hrootParent : ∀ I : Protocol.ProposalInput V,
          Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract nr.cache) S.E S.hc
            (S.node p) (M.toHealing nr.st.core) ⇢ I →
          Block.Preceq rootNamed.erase I.parent := by
        intro I hI
        rw [hrootErase, ← hnFR]
        obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty
          (M.toHealing nr.st.core).toFG.toSG.toGoldfishStore
          (M.toHealing nr.st.core).toFG.toSG.toGoldfishStore.s
        obtain ⟨X, hX⟩ := facts.fc.get_head_with_nonempty (M.gradeContract nr.cache) S.E S.hc
          (M.toHealing nr.st.core)
          (M.proposer_view (M.toHealing nr.st.core).toFG.toSG.toGoldfishStore
            (M.toHealing nr.st.core).toFG.toSG.toGoldfishStore.s).toFinset L.toFinset
          ((M.toHealing nr.st.core).toFG.toSG.toGoldfishStore.s - 1)
        obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract nr.cache) S.E S.hc
          (M.toHealing nr.st.core) (M.round_of S.hc (M.toHealing nr.st.core).s)
        rw [facts.dt.with_proposal_input_id_parent _ _ _ _ _ I hI L hL X hX]
        exact preceq_trans_Preceq
          (facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract nr.cache S.E S.hc _ _ R hR)
          (Restated.Vocabulary.Proofs.HealingSurface.get_sg_root_with_preceq_get_head_with facts _
            S.E S.hc _ _ _ _ R hR X hX)
      exact Or.inr (Or.inr ⟨rootNamed,
        { proposerCarrier := hcarrier
          proposerHonest := hpropConf
          proposalRead_le_action := hproposalAction
          action_le_endpoint := hactionEnd
          endpointInHorizon := hendHor
          endpointCap := hcapEnd
          gradeFormsPrev := hformsPrev
          sourceActiveAtAction := hactiveAtAction
          sourceProcessed := hsourceMem
          sourceRunBlock := hsourceRun
          sourceExactHeight := hsourceHeight
          sourceNotActive := by rw [hnFT]; exact hactive'
          root_eq := by rw [hnFR]; exact hrootErase
          sourceStrictRoot := hsourceStrict
          rootActive := by rw [hnFT, hrootErase]; exact hrootActive
          rootProcessed := hrootBody
          rootRunBlock := hrootRun
          rootExactHeight := hrootHeight
          rootExactTarget := hrootTarget
          rootPreceqProposedParent := hrootParent }⟩)
    · have hnotQuiet : ¬ Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M
          S rho p read wr source.erase := by
        intro hquiet
        rcases hquiet with hroot | hfiltered
        · exact hsourceRoot hroot
        · exact hactive' hfiltered
      rcases (Restated.Vocabulary.Proofs.HealingSurface.not_finalityFilterNoninterferenceAtRead_iff facts
          S rho p read wr source.erase).mp hnotQuiet with
        hinterference | hheight
      · have hsourceCore : source.erase ∈ (wr p).st.T := by
          have htree :=
            (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho read p wr hwr).1.1.1.1
          show source.erase ∈ (wr p).st.core.T
          rw [htree]
          exact Finset.mem_image_of_mem NamedBlock.erase hsourceMem
        have hfixed := Restated.fixedHeightRootInterferenceAtRead_of_interferenceOn facts
          S Hs Xb hf hHs hHsXb (hfb _ le_rfl) hsb hpropRead hreadHor hsourceCore
            rfl hsourceRun (le_of_eq hsourceHeight.symm) hfrontier hinterference
        exact Or.inr (Or.inl ⟨hfixed, hproposalAction, hactionEnd, hendHor⟩)
      · have hstrict : H + 2 ≤ (wr p).st.h_max :=
          Restated.heightFilterInterference_hMaxOn facts (H := H)
            S Hs Xb hf hpropRead hsourceMem (le_of_eq hsourceHeight.symm) hheight
        have hbad : H + 2 ≤ H := hstrict.trans_eq hfrontier
        exact absurd (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) hbad)
          (Nat.lt_irrefl H)

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

/-- Under the bundle along `W`, if more than half of every slot's committee is in `Hs` of its
    confirmation time, `0 < s`, `lo ≤ vote_time s`, `s`'s confirmation time is inside the horizon,
    every honest committee vote of `s` is for a descendant of `C`, `w ∈ Hs (support_cutoff s)` has
    the cone's confirmation inputs at `C`, and `D` satisfies `GenuineConfirmationWith` for `w`'s
    store staged at `s`'s confirmation time under the cache outcome `c`, then `C` is an ancestor of
    `D`. -/
theorem goldfishCone_confirmationOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeConfirmationInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st
        (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).record c))
    {D : Block V}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
        (M.confirmation_time S.E s)) s D) :
    Block.Preceq C D := by
  have hcut : M.support_cutoff S.E s ≤ rho.horizon :=
    le_trans (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hhor
  set tc := M.confirmation_time S.E s with htc
  set ww := W (strictEventIndex rho tc) w with hww
  set st := Restated.Vocabulary.Proofs.Optimistic.tickStore M S ww.st.core tc with hst
  have hwmem := mem_stateBeforeTime_along₅₄b hf.sorted hf.onePath tc
  have hnmem : M.mkNode (M.ns_setClock S.E ww.st tc) ww.record c ∈
      Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead M S rho w s :=
    ⟨_, hwmem, c, hc, rfl⟩
  have hroot : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M st) C := by
    have h := hinputs.root
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_fg_root, setClock_core_tickStore₅₄b facts S] at h
    exact h
  have hresolve := Restated.headsResolveIn_confStore_of_postHealingConeOn facts
    S Hs Xb hf hHs hHsXb hw hpost hcut hroot hnames
  have hsupport := Restated.coneSupport_confVotes_after_gstOn facts
    S Hs Xb hf hHs hHsXb hcom hs hpost hhor hnames hw hresolve
  have hvalid : Protocol.VoteSetValid S.E s (Restated.Vocabulary.Protocol.confLate M S.E st s) := by
    rw [hst, confLate_tickStore₅₄b facts S]
    exact Restated.voteSetValid_confLate_stateBeforeTimeOn facts S Hs Xb hf w tc s
  have hAnamed : ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc st ⇢ A →
      Restated.Vocabulary.Internal.namedConfirmationAnchor M S
        (M.mkNode (M.ns_setClock S.E ww.st tc) ww.record c) ⇢ A := by
    intro A hA
    rw [Restated.Vocabulary.Internal.namedConfirmationAnchor, facts.nd.mkNode_cache, facts.nd.mkNode_st,
      sgRoot_store_with_cache₅₄b facts, facts.nd.store_with_cache_core_s,
      setClock_core_tickStore₅₄b facts S]
    exact hA
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨A, hA⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing st) (M.round_of S.hc st.s)
  have hu : Restated.Vocabulary.Protocol.confVotes M S.E st s ⇢
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true)) :=
    returns_map_intro₅₄b _ _ _ (returns_map_intro₅₄b _ _ _ htm)
  have hscore : ∀ B' : Block V, ∃ g, M.goldfish_score S.E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true))
      s B' ⇢ g :=
    fun B' => facts.fc.goldfish_score_nonempty _ _ _ _ _ _
  choose sc hsc using hscore
  obtain ⟨H, hH⟩ := facts.fc.ghost_nonempty A (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B' => decide (Restated.Vocabulary.Protocol.confCount M S.E st s < 2 * sc B'))
  have helig := hgenuine.genuine A hA _ hu sc hsc H hH
  have hlive := facts.hd.update_confirmation_with_live_confirmed_of_eligible (M.gradeContract c)
    S.E S.hc st s tm htm A hA sc hsc H hH helig
  obtain ⟨st', hst'⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc st s
  have hDH : D = H := by
    rw [← hgenuine.selected st' hst', hlive st' hst']
  rw [hDH]
  have hcompat : Block.compatible A C = true := by
    have h := hinputs.anchor A (hAnamed A hA)
    exact h
  rcases compatible_cases hcompat with hAC | hCA
  · have hpath : ∀ D' : Block V, Block.Preceq A D' → D' ≠ A → Block.Preceq D' C →
        D' ∈ Restated.Vocabulary.Protocol.confTree M st := by
      intro D' hAD hDne hD'C
      have hmem : D' ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (M.mkNode (M.ns_setClock S.E ww.st tc) ww.record c) := by
        by_cases hEq : D' = C
        · subst hEq
          exact hinputs.candidate
        · exact hinputs.path A (hAnamed A hA) D' hAD hDne hD'C hEq
      unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree at hmem
      rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_filtered_block_tree,
        setClock_core_tickStore₅₄b facts S] at hmem
      exact hmem
    have hcs := hsupport _ hu
    exact facts.fc.ghost_passes_cone S.E st.T (Restated.Vocabulary.Protocol.confTree M st) _ _
      (Restated.Vocabulary.Protocol.confLate M S.E st s) s (Hs tc)
      hcs.majority hcs.counted hcs.sub hcs.no_equiv hcs.vote hvalid hAC hpath sc hsc H hH
  · exact preceq_trans_Preceq hCA
      (facts.fc.ghost_preceq A (Restated.Vocabulary.Protocol.confTree M st) sc _ H hH)

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
open DecoupledConsensusModel.Statements.Instantiation

end

end DecoupledConsensusModel.Sts.Restated
