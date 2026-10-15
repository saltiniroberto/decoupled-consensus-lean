import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_56b
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeDelivery
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Q31_actionSGBlock_tiers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryCapturedNextActionExact
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeOneChain
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeSeedK3
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# The band cover, the opening at a round ceiling and frozen opening votes

Theorems over a model `M : Record.Model V` and its facts, read along a path `W` of a run with the
admissible fields `hf`. They carry a run block of height at least `Mh − 1` that is an ancestor of
every action carrier from round to round, derive the opening of a round at a round ceiling, give the
frozen opening votes from a fixed-height justification root, transport grades from one phase to the
earlier one, and make a member's prepared anchor compatible with the action carriers.
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
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before the time `t` are the worlds before the event
    of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₆ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₆ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₆ S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₆ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₆₆ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₆ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W`, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an ancestor
    of the one in `W n`. -/
private theorem F_mono_along₆₆ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₆₆ W hW hjn)

/-- On a path `W` of a run sorted by key, the finalized block of `v`'s core store in
    `W (strictEventIndex rho t)` is an ancestor of that store's FG root. -/
private theorem F_preceq_fgRoot_along₆₆ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
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
          S rho t v _ (mem_stateBeforeTime_along₆₆ hsorted hW t)))
  rw [facts.sto.Sts_toHealing_F] at hFroot
  exact preceq_eq_true_iff_Preceq.mp hFroot

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read and the
    SG vote selector each can return a value. -/
private theorem exists_actionSG₆₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state `n` of the round-`r` action read from `before` has a store `st` such that
    `n.st` is `st` with `n`'s cache written in, and `st`'s core store is an outcome of the
    confirmation update of `before`'s store staged at `S.a r`. -/
private theorem actionReadFrom_core₆₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state of the round-`r` action read from `before` has the filtered block tree of
    `before`'s core store. -/
private theorem actionReadFrom_filtered₆₆ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
        M.get_filtered_block_tree (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₆ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_filtered_block_tree,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₆ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If the contract's grade read at `n` can return `G`, `n`'s candidate read can return `G`'s
    candidate. -/
private theorem nodeQ2_of_read₆₆ (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₆ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

/-- If every outcome of a store grade is `true`, the store grade can return `true`. -/
private theorem storeGrade_true_of_all₆₆ (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) (B : Block V)
    (h : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ b → b = true) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ true := by
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty E (M.gradeView (M.toHealing st.core)) st.core.F
    hc.η_SG r (M.early E hc r p) (M.late E hc r p) B
  have hbt : b = true := h b hb
  subst hbt
  exact hb

/-- Along the path `W`, if `w ∈ Xb` holds the erasure of the run block `Qn` of height at least
    `Mh − 1` in its store in `W (strictEventIndex rho (S.a r))`, `S.a r` is in the horizon, and that
    store has `h_max = Mh` and `h_j + 2 ≤ Mh`, then `Qn`'s erasure is in the filtered tree of that
    store and of every node state of `w`'s round-`r` action read from that world. -/
private theorem seedBand_active_at_actionRead₆₆ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {Mh : Height} {r : Round} {Qn : NamedBlock V}
    (hQrun : Restated.RunBlockOn M S rho W Xb Qn)
    (hQband : Mh - 1 ≤ (M.derive_named S.E S.cfg Qn).h)
    {w : V} (hw : w ∈ Xb)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hmem : Qn.erase ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.T)
    (hfrontier : (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.core).toFG.h_max = Mh)
    (hgate : (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.core).toFG.h_j + 2 ≤ Mh) :
    Qn.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.core).toFG ∧
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
        Qn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
  rw [facts.sto.Sts_toHealing_h_max] at hfrontier
  rw [facts.sto.toHealing_h_j] at hgate
  have hM1 : 1 ≤ Mh :=
    (by decide : (1 : Nat) ≤ 2).trans ((Nat.le_add_left 2 _).trans hgate)
  have hbase := Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hf.slashableBound hw
    hhor hmem rfl hQrun hQband hM1 hfrontier hgate
  refine ⟨hbase, ?_⟩
  intro n hn
  show Qn.erase ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG
  rw [actionReadFrom_filtered₆₆ facts S _ r n hn]
  exact hbase

end

/-! ## Helpers on tick stores and the schedule -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The store a tick at `t` stages from `n`'s core store has the tree of `n`'s core store. -/
private theorem tickStore_T₆₆w (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store a tick at `t` stages from `n`'s core store has the `h_max` of `n`'s core store. -/
private theorem tickStore_h_max₆₆w (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- The store a tick at `t` stages from `n`'s core store has the `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₆₆w (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

/-- Round `q`'s action time is at most the vote time of round `q`'s last slot. -/
private theorem action_le_seedRoundLastSlotVote₆₆w (facts : Record.Facts M) (S : Setup V)
    (q : Round) :
    Restated.Vocabulary.Execution.Setup.a M S q ≤
      M.vote_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q) := by
  have hslot : M.opening_slot S.hc q + 1 + 1 ≤
      Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q := by
    unfold Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot
    rw [facts.gr.opening_slot_succ_eq S.hc q]
    have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
    exact Nat.le_sub_of_add_le (Nat.add_le_add_left hR (M.opening_slot S.hc q))
  have hsucc : Restated.Vocabulary.Execution.Setup.a M S q ≤
      M.vote_time S.E (M.opening_slot S.hc q + 1 + 1) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S q,
      facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_le_vote_time_succ S.E _
  exact hsucc.trans (facts.sch.vote_time_mono_slots S.E hslot)

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₆₆w (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The confirmation tree of the core store of a store with a cache written in is the store's own. -/
private theorem confTree_swc₆₆w (facts : Record.Facts M) (st : M.NS) (c : M.Cache) :
    Restated.Vocabulary.Protocol.confTree M (M.store_with_cache st c).core =
      Restated.Vocabulary.Protocol.confTree M st.core := by
  unfold Restated.Vocabulary.Protocol.confTree Record.Model.S.toHealing
  rw [facts.nd.store_with_cache_get_filtered_block_tree]

/-- If `P` is a proposal slot `s`'s proposer's duty can return on the store of `wp` staged to `t`
    under the grade contract of `c`, then some proposal input the proposal input routine can return
    at the node state staged from `wp` with `c` has its parent an ancestor of `P`'s block. -/
private theorem proposalInputParent₆₆w (facts : Record.Facts M) (S : Setup V) (wp : M.N)
    (s : Slot) (t : Time) (c : M.Cache) {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E wp.st t) ⇢ some P) :
    ∃ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer s))
        (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st t) wp.record c).st.core) ⇢ I ∧
      Block.Preceq I.parent P.erase := by
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node (S.E.proposer s))
    (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st t) wp.record c).st.core)
  have hI' : M.with_proposal_input (M.gradeContract c) S.E S.hc (S.node (S.E.proposer s))
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E wp.st t) c).core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  obtain ⟨par, hpar, hparE⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ P _
      (by rw [facts.dt.proposal_with_store_with_cache]; exact hP) rfl I hI'
  have hparentEq : P.erase.parent = I.parent := by
    rw [Proofs.NamedWire.erase_parent]
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hpar
    | node q' _ _ _ _ _ _ =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hpar
      subst hpar
      rw [Proofs.ModelProperties.named_parent_node]
      exact hparE
  refine ⟨I, hI, ?_⟩
  rw [← hparentEq]
  exact preceq_eq_true_iff_Preceq.1 (Proofs.preceq_parent P.erase)

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

/-- Along the path `W` with the admissible fields `hf`, two run blocks `A` and `D` read through `Xb`
    with `A.erase = D.erase` are equal. -/
theorem seedBandRunBlock_unique_of_erase_eqOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A D : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hD : Restated.RunBlockOn M S rho W Xb D)
    (herase : A.erase = D.erase) : A = D :=
  hf.rootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

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

/-- Along the path `W` with the admissible fields `hf`, if rounds `q − 1` and `q` have the band
    grade at `Mh` (`hbandPrev`, `hband`), then for every member of the set for `S.a (q − 1)` and
    every node state of its round-`(q − 1)` action read, every outcome of the grade-2 selection
    names a block, and likewise for every member of the set for `S.a q` at round `q`. -/
theorem seedRoundGraded_of_bandGradeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {Mh : Height} {q : Round}
    (hframePrev : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon ∧
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core).toFG.h_max
            = Mh ∧
          (M.toHealing
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core).toFG.h_j
            + 2 ≤ Mh)
    (hframe : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon ∧
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.core).toFG.h_max
            = Mh ∧
          (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.core).toFG.h_j
            + 2 ≤ Mh)
    (hbandPrev : Restated.SeedRoundBandGradeAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb Mh (q - 1))
    (hband : Restated.SeedRoundBandGradeAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb Mh q) :
    Restated.SeedRoundGradedAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs q :=
  ⟨hbandPrev.1, hband.1⟩

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

/-- Along the path `W` with the admissible fields `hf`: if `Qn` is a run block of height at least
    `Mh − 1` whose erasure is an ancestor of every round-`q` action carrier of every member of the
    set for `S.a q` (`hQcover`), `lo ≤ S.a q`, `S.a q + Δ` is in the horizon, and every member of
    the set for `S.a q + Δ` has `h_max = Mh` and `h_j + 2 ≤ Mh` in `W` before that time, then
    `Qn.erase` is in the tree of every such member's store in `W (strictEventIndex rho read)` for
    every `read` from `S.a q + Δ` on. -/
theorem seedBandCover_mem_atOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {Qn : NamedBlock V}
    (hQrun : Restated.RunBlockOn M S rho W Xb Qn)
    (hQband : Mh - 1 ≤ (M.derive_named S.E S.cfg Qn).h)
    (hQcover : Restated.ActionCarriersCoverOn M S rho Hs q Qn.erase
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hhorRelay : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ),
      (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_j + 2 ≤ Mh) :
    ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ read : Time,
      (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ read →
      Qn.erase ∈ (W (strictEventIndex rho read) w).st.T := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hΔ := S.E.Δ_pos
  intro w hw read hread
  have hp : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)) := hHs _ _ (by linarith) hw
  obtain ⟨n, hn, g, hg, B, hB⟩ := exists_actionSG₆₆ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w) q
  have hamem := mem_stateBeforeTime_along₆₆ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S q)
  have hBmem : B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho w q _
      hamem n hn g hg B hB
  have hQp : Qn.erase ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.T :=
    Restated.ancestor_mem_storeBeforeTimeOn facts S Hs Xb hf hBmem (hQcover w hp n hn g hg B hB)
  obtain ⟨D, hDbodies, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w _ (hf.onePath _).1 hQp
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hp) hDbodies
  have hDQ : D = Qn := Restated.seedBandRunBlock_unique_of_erase_eqOn facts hf hDrun hQrun hDerase
  have hsource : Qn ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.bodies := by
    rw [← hDQ]; exact hDbodies
  exact (Restated.thinBlock_visible_and_stamped_after_oneDelayOn facts S Hs Xb hf hHs hHsXb hsb hp hw hsource
    hQrun hQband hpost rfl hread hhorRelay (hframeRelay w hw).1 (hframeRelay w hw).2).1

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

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if `Qn` is a run
    block of height at least `Mh − 1` whose erasure is an ancestor of every round-`q` action carrier
    of the set for `S.a q`, the frames `hframeRelay`, `hframeAction` and `hframeDomain` hold at
    `Mh`, `S.a (q + 1)` is in the horizon, `t_GST ≤ S.a q`, `lo ≤ S.a q`, and every member of the
    set for `S.a q + Δ` is awake at `q`, then every member of the set for round `q + 1`'s grade-2
    domain time has `Qn.erase` in the filtered tree of its node state in `W` before that time, and
    every outcome of the grade-2 store grade of `Qn.erase` at round `q + 1` there is `true`. -/
theorem seedBandCover_namedGradeFormsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {Qn : NamedBlock V}
    (hQrun : Restated.RunBlockOn M S rho W Xb Qn)
    (hQband : Mh - 1 ≤ (M.derive_named S.E S.cfg Qn).h)
    (hQcover : Restated.ActionCarriersCoverOn M S rho Hs q Qn.erase
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))))
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hhorAction : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ),
      (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_j + 2 ≤ Mh)
    (hframeAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_max
          = Mh ∧
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_j
          + 2 ≤ Mh)
    (hframeDomain : ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_j + 2 ≤ Mh)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      Qn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) v).st (q + 1) .g2 Qn.erase ⇢ b →
          b = true := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hrelayAction : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S q)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q))
  have hhorRelay : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ rho.horizon := hrelayAction.trans hhorAction
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q)).trans hhorAction
  have hmemAt := Restated.seedBandCover_mem_atOn facts S Hs Xb hf hHs hHsXb hQrun hQband hQcover
    hlo hhorRelay hframeRelay
  have hactive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))), Qn.erase ∈
      M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG :=
    fun w hw => (seedBand_active_at_actionRead₆₆ facts S Hs Xb hf hQrun hQband (hHsXb _ hw) hhorAction
      (hmemAt w (hHs _ _ hrelayAction hw) _ hrelayAction)
      (hframeAction w hw).1 (hframeAction w hw).2).1
  have hdlo : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
      M.domain S.E S.hc (q + 1) .g2 :=
    (facts.gr.action_add_delta_le_next_Γ_neg1 S q).trans
      (le_of_eq (facts.gr.gammaNeg1_eq_domain_g2_succ S q))
  have hdhi : M.domain S.E S.hc (q + 1) .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    facts.gr.domain_le_a S (q + 1) .g2
  have hretained : ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      Qn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w) := by
    intro w hw
    have hM1 : 1 ≤ Mh :=
      (by decide : (1 : Nat) ≤ 2).trans ((Nat.le_add_left 2 _).trans (hframeDomain w hw).2)
    exact Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw)
      (hdhi.trans hhorAction) (hmemAt w (hHs _ _ hdlo hw) _ hdlo) rfl hQrun hQband
      hM1 (hframeDomain w hw).1 (hframeDomain w hw).2
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))).Nonempty :=
    nonempty_of_honestWeightMajority_l54 (hmajority _ hhorAction)
  exact Restated.namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn facts S Hs Xb hf hHs hHsXb
    hmajority hQcover hpost hcut hactive hretained hA hlo hne

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

/-- Under the hypotheses of `seedBandGrade_of_bandCarrierCoverOn`, for every member `v` of the set
    for `S.a (q + 1)` and every node state of `v`'s round-`(q + 1)` action read, every outcome of
    its grade-2 selection at round `q + 1` names a block. -/
theorem seedBandGrade_selected_of_bandCarrierCoverOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round}
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hhorAction : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ),
      (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_j + 2 ≤ Mh)
    (hframeAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_max
          = Mh ∧
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_j
          + 2 ≤ Mh)
    (hframeDomain : ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_j + 2 ≤ Mh)
    (hcover : Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh q
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hloOpen : lo ≤ M.opening S.E S.hc (q + 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) v) (q + 1),
        ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (q + 1) ⇢ o →
          ∃ Q : Block V, o = some Q := by
  obtain ⟨Qn, hQrun, hQband, hQcover⟩ := hcover
  have hrelayAction : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S q)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q))
  have hhorRelay : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ rho.horizon := hrelayAction.trans hhorAction
  have hmemAt := Restated.seedBandCover_mem_atOn facts S Hs Xb hf hHs hHsXb hQrun hQband hQcover
    hlo hhorRelay hframeRelay
  have hforms := Restated.seedBandCover_namedGradeFormsOn facts S Hs Xb hf hHs hHsXb hfb hQrun
    hQband hQcover hpost hhorAction hframeRelay hframeAction hframeDomain hlo hA
  intro v hv n hn o ho
  have hactiveRead : Qn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
    (seedBand_active_at_actionRead₆₆ facts S Hs Xb hf hQrun hQband (hHsXb _ hv) hhorAction
      (hmemAt v (hHs _ _ hrelayAction hv) _ hrelayAction)
      (hframeAction v hv).1 (hframeAction v hv).2).2 n hn
  have hvG0 : v ∈ Hs (M.domain S.E S.hc (q + 1) .g0) :=
    hHs _ _ (facts.gr.domain_le_a S (q + 1) .g0) hv
  have hvG2 : v ∈ Hs (M.domain S.E S.hc (q + 1) .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S (q + 1) .g2) hvG0
  obtain ⟨Q, hQ, -⟩ := Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs
    (Nat.succ_pos q) hhorAction hvG0 hloOpen (hforms v hvG2).1
    (storeGrade_true_of_all₆₆ facts S.E S.hc _ (q + 1) .g2 Qn.erase (hforms v hvG2).2)
    n hn hactiveRead o ho
  exact ⟨Q, hQ⟩

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

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if the band
    carrier cover `hcover` holds at round `q`, the frames `hframeRelay`, `hframeAction` and
    `hframeDomain` hold at `Mh`, `S.a (q + 1)` is in the horizon, and the bounds on `t_GST` and `lo`
    and the awake hypothesis `hA` hold, then round `q + 1` has the band grade at `Mh`: every grade-2
    selection of a round-`(q + 1)` action read of the set for `S.a (q + 1)` names a block, and every
    member of the set for the vote time of round `q + 1`'s last slot has a run block of height at
    least `Mh − 1` graded 2 in its store before `S.a (q + 1)` and present in its vote-duty store at
    every slot of round `q + 1`. -/
theorem seedBandGrade_of_bandCarrierCoverOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round}
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hhorAction : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ),
      (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_j + 2 ≤ Mh)
    (hframeAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_max
          = Mh ∧
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_j
          + 2 ≤ Mh)
    (hcover : Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh q
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))))
    (hframeDomain : ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_j + 2 ≤ Mh)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hloOpen : lo ≤ M.opening S.E S.hc (q + 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    Restated.SeedRoundBandGradeAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh
      (q + 1) := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hselected := Restated.seedBandGrade_selected_of_bandCarrierCoverOn facts S Hs Xb hf hHs
    hHsXb hfb hpost hhorAction hframeRelay hframeAction hframeDomain hcover hlo hloOpen hA
  obtain ⟨Qn, hQrun, hQband, hQcover⟩ := hcover
  have hrelayAction : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S q)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q))
  have hhorRelay : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ rho.horizon := hrelayAction.trans hhorAction
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q)).trans hhorAction
  have hmemAt := Restated.seedBandCover_mem_atOn facts S Hs Xb hf hHs hHsXb hQrun hQband hQcover
    hlo hhorRelay hframeRelay
  refine ⟨hselected, ?_⟩
  intro w hwLast
  have hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) :=
    hHs _ _ (action_le_seedRoundLastSlotVote₆₆w facts S (q + 1)) hwLast
  refine ⟨Qn, hQrun, hQband, ?_, ?_⟩
  · have hactiveW : Qn.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG :=
      (seedBand_active_at_actionRead₆₆ facts S Hs Xb hf hQrun hQband (hHsXb _ hw) hhorAction
        (hmemAt w (hHs _ _ hrelayAction hw) _ hrelayAction)
        (hframeAction w hw).1 (hframeAction w hw).2).1
    exact Restated.seedG2_of_actionCarriersCover_at_storeOn facts S Hs Xb hf hHs hHsXb
      (hmajority _ hhorAction) hw hQcover hlo hcut hactiveW
      (fun u hu => hA u (hHs _ _ hrelayAction hu))
  · intro d hlod hhid
    have hvote : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ M.vote_time S.E d :=
      ((Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        (Nat.lt_succ_self q)).trans (facts.sch.proposal_time_lt_vote_time S.E _).le).trans
        (facts.sch.vote_time_mono_slots S.E hlod)
    show Qn.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).T
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_T₆₆w facts]
    exact hmemAt w (hHs _ _ (hvote.trans (facts.sch.vote_time_mono_slots S.E hhid)) hwLast)
      (M.vote_time S.E d) hvote

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

/-- Under the hypotheses of `seedBandCover_namedGradeFormsOn` and `hloOpen`, if some run block of
    height at least `Mh − 1` is an ancestor of every round-`q` action carrier of the set for `S.a q`
    (`hcover`), the same run block is an ancestor of every round-`(q + 1)` action carrier of the set
    for `S.a (q + 1)`. -/
theorem seedBandCarrierCover_succOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round}
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hhorAction : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hframeRelay : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ),
      (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ)) w).st.h_j + 2 ≤ Mh)
    (hframeAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_max
          = Mh ∧
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w).st.core).toFG.h_j
          + 2 ≤ Mh)
    (hcover : Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh q
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))))
    (hframeDomain : ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w).st.h_j + 2 ≤ Mh)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hloOpen : lo ≤ M.opening S.E S.hc (q + 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh (q + 1)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1)))) := by
  unfold Restated.SeedBandCarrierCoverAtOn at hcover ⊢
  obtain ⟨Qn, hQrun, hQband, hQcover⟩ := hcover
  have hrelayAction : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S q)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q))
  have hmemAt := Restated.seedBandCover_mem_atOn facts S Hs Xb hf hHs hHsXb hQrun hQband hQcover
    hlo (hrelayAction.trans hhorAction) hframeRelay
  have hforms := Restated.seedBandCover_namedGradeFormsOn facts S Hs Xb hf hHs hHsXb hfb hQrun
    hQband hQcover hpost hhorAction hframeRelay hframeAction hframeDomain hlo hA
  refine ⟨Qn, hQrun, hQband, ?_⟩
  intro w hw n hn
  have hactiveRead : Qn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
    (seedBand_active_at_actionRead₆₆ facts S Hs Xb hf hQrun hQband (hHsXb _ hw) hhorAction
      (hmemAt w (hHs _ _ hrelayAction hw) _ hrelayAction)
      (hframeAction w hw).1 (hframeAction w hw).2).2 n hn
  have hwG0 : w ∈ Hs (M.domain S.E S.hc (q + 1) .g0) :=
    hHs _ _ (facts.gr.domain_le_a S (q + 1) .g0) hw
  have hwG2 : w ∈ Hs (M.domain S.E S.hc (q + 1) .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S (q + 1) .g2) hwG0
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (q + 1)
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (q + 1) ⇢ G.Q2 :=
    nodeQ2_of_read₆₆ S n (q + 1) G hG
  obtain ⟨Q, hQ, hCQ⟩ := Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs
    (Nat.succ_pos q) hhorAction hwG0 hloOpen (hforms w hwG2).1
    (storeGrade_true_of_all₆₆ facts S.E S.hc _ (q + 1) .g2 Qn.erase (hforms w hwG2).2)
    n hn hactiveRead _ hGq
  rw [hQ] at hGq
  exact Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb
    (Nat.succ_pos q) hhorAction (hHs _ _ (facts.gr.domain_le_domain_g0 S (q + 1) .g1) hwG0) hloOpen
    n hn hGq hCQ

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

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if every member
    of the set for each time from `S.a lo` to `S.a hi` has `h_j + 2 ≤ Mh` and `h_max = Mh` there
    (`hframe`), `S.a hi` is in the horizon, `t_GST ≤ S.a lo`, the bounds `hlo₀` and `hloOpen` and
    the awake hypotheses `hA` and `hAlo` hold, and some run block of height at least `Mh − 1` is an
    ancestor of every round-`lo` action carrier of the set for `S.a lo` (`hcover`), then for every
    round `k` from `lo` to `hi` some such run block is an ancestor of every round-`k` action carrier
    of the set for `S.a k`. -/
theorem seedBandCarrierCover_throughOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo₀ : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo₀)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {lo hi : Round}
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S lo))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S hi) ≤ rho.horizon)
    (hframe : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S lo) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S hi) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hcover : Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh lo
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S lo))))
    (hlo₀ : lo₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S lo))
    (hloOpen : lo₀ ≤ M.opening S.E S.hc (lo + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo₀ ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAlo : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S lo) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S lo)) → M.awake_for_grade2 S u (W j u) lo) :
    ∀ k : Round, lo ≤ k → k ≤ hi →
      Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh k
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k))) := by
  intro k hlo
  induction k, hlo using Nat.le_induction with
  | base => intro _; exact hcover
  | succ n hn ih =>
    intro hhi
    have hnhi : n ≤ hi := le_trans (Nat.le_succ n) hhi
    have hrelayAction : (Restated.Vocabulary.Execution.Setup.a M S n) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (n + 1)) :=
      le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S n)
        (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S n))
    have hdlo : (Restated.Vocabulary.Execution.Setup.a M S n) + S.E.Δ ≤
        M.domain S.E S.hc (n + 1) .g2 :=
      (facts.gr.action_add_delta_le_next_Γ_neg1 S n).trans
        (le_of_eq (facts.gr.gammaNeg1_eq_domain_g2_succ S n))
    have hdhi : M.domain S.E S.hc (n + 1) .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (n + 1)) :=
      facts.gr.domain_le_a S (n + 1) .g2
    have hloN : (Restated.Vocabulary.Execution.Setup.a M S lo) ≤ (Restated.Vocabulary.Execution.Setup.a M S n) + S.E.Δ :=
      le_trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hn) (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
    -- The grade-2 awake test at round `n`: `hAlo` when `n = lo`, otherwise `hA n`.
    have hAn : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S n) + S.E.Δ), ∀ j : Nat,
        rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S n)) →
        M.awake_for_grade2 S u (W j u) n := by
      rcases eq_or_lt_of_le hn with hb | hb
      · rw [← hb]
        exact hAlo
      · exact hA n (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hlo₀ hb)
    refine Restated.seedBandCarrierCover_succOn facts S Hs Xb hf hHs hHsXb hfb
      (hpost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hn))
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi).trans hhor) ?_ ?_ (ih hnhi) ?_
      (hlo₀.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hn))
      (hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
        (Nat.sub_le_sub_right (Nat.succ_le_succ hn) _)))
      hAn
    · intro w hw
      have h := hframe ((Restated.Vocabulary.Execution.Setup.a M S n) + S.E.Δ) hloN
        (hrelayAction.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi)) w hw
      exact ⟨h.2, h.1⟩
    · intro w hw
      have h := hframe ((Restated.Vocabulary.Execution.Setup.a M S (n + 1)))
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (hn.trans (Nat.le_succ n)))
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi) w hw
      exact ⟨by rw [facts.sto.Sts_toHealing_h_max]; exact h.2,
        by rw [facts.sto.toHealing_h_j]; exact h.1⟩
    · intro w hw
      have h := hframe _ (hloN.trans hdlo)
        (hdhi.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi)) w hw
      exact ⟨h.2, h.1⟩

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
open DecoupledConsensusModel.Internal.PhaseGrades
local macro "sad% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedAdoption)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- For every node state `n` of `v`'s round-`r` action read, if `n`'s `live_confirmed` is `D`, the
    grade view of `n` is batch-aligned to `Can` over `X` at `r`, `Can ⪯ D`, and for an outcome `G`
    of `n`'s grade read at `r` the anchor of `G` is `A`, `A ⪯ Can` and the clearance of `G` passes
    `D`, then every block the SG vote selector can return at `n`, with every outcome of the grade-2
    block read, is `D`. -/
theorem actionSGBlockAt_eq_liveConfirmed_of_batchAlignedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (X : Finset V) {v : V} {r : Round}
    {Can D A : Block V} :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
    n.st.core.live_confirmed = D →
    Restated.Vocabulary.Internal.PhaseGrades.BatchAlignedAt M S.hc (M.gradeView (M.toHealing n.st.core))
        n.st.core.F X r (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc r) Can →
    Block.Preceq Can D →
    ∀ G : Protocol.GradeRead V, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ G →
    G.anchor = A →
    Block.Preceq A Can →
    G.clear D = true →
    (let gc := M.gradeContract n.cache
     let st := M.toHealing n.st.core
     let k := M.round_of S.hc st.s
     ∀ g : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ g →
     ∀ Wb : Block V, M.get_sg_vote_with gc S.E S.hc st k g ⇢ Wb → Wb = D) :=
  fun n hn hconfirmed hbatch hCanD G hG hanchor hACan hclear =>
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_eq_liveConfirmed_of_batchAligned facts S
      (rho := { rho with honest := X }) n hn hconfirmed hbatch hCanD G hG hanchor hACan hclear

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
open DecoupledConsensusModel.Internal.PhaseGrades
local macro "sad% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedAdoption)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`: if round `q` is a carrier round (`hcarrier`), `C` is its round ceiling at `Mh`
    (`h`), the opening window `hwindow` holds for `P`, every member of the set for `S.a (q − 1)` has
    `h_max = Mh` there, every member of the set for round `q`'s grade-0 domain time has `h_max = Mh`
    and `h_j + 2 ≤ Mh` there, `P`'s block is active at round `q + 1`'s grade-2 domain read of every
    member of the set for that time, and the bounds `hloPrev` and `hloFrozen` and the awake
    hypotheses `hA` and `hAprev` hold, then `GateOffOpeningAdoptionOn` holds at round `q` for `P`. -/
theorem gateOff_openingLifecycle_of_roundCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hwindow : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q P)
    (hprevFrontier : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.h_max = Mh)
    (hnextActiveDomain : ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w))
    (hfrontierG0 : ∀ w ∈ Hs (M.domain S.E S.hc q .g0),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) w).st.h_max = Mh)
    (hgateOffG0 : ∀ w ∈ Hs (M.domain S.E S.hc q .g0),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) w).st.h_j + 2 ≤ Mh)
    (hloPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloFrozen : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    Restated.GateOffOpeningAdoptionOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb q P := by
  have hq : 0 < q := hwindow.roundPositive
  have hs : 0 < (M.opening_slot S.hc q) := facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hconfEq : (Restated.Vocabulary.Execution.Setup.a M S q) = M.confirmation_time S.E ((M.opening_slot S.hc q)) :=
    Restated.a_eq_confirmation_opening_l58 facts S q
  have hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  have hpropA : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)) := by
    rw [hconfEq]; exact hprop
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans hwindow.nextActionInHorizon
  have hconfHor :
      M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon := by
    rw [← hconfEq]; exact hactionHor
  have hvoteHor :
      M.vote_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hproposalHor :
      M.proposal_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E _).trans hconfHor
  have hfrozenLeProp : M.proposal_time S.E ((M.opening_slot S.hc q) - 1) ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    facts.sch.proposal_time_mono S.E (Nat.sub_le _ _)
  have hloProp : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    hloFrozen.trans hfrozenLeProp
  have hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q)) :=
    hloProp.trans (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hloVotePrev : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) :=
    hloFrozen.trans (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hloVote.trans ((facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans (le_of_eq hconfEq.symm))
  -- The awake tests of round `q`'s opening slot: grade 1 for the proposer and the committee, grade
  -- 2 for the confirmers.
  have hloEarlyG2 : lo ≤ M.early S.E S.hc q .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPrev (Nat.sub_lt hq Nat.one_pos)
  have hwinQ : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc q]
    have h2 := facts.gr.q10_early_g2_le_early_g1 S q
    linarith
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
      (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q)) :=
    fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop) hwinQ
  have hrunV : ∀ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)), v ∈ S.E.committee (M.opening_slot S.hc q) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S v (W j v) (M.round_of S.hc (M.opening_slot S.hc q)) :=
    fun _ hv _ j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hv hwinQ
  have hrunConf : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade2 (Setup.alwaysAwake S) v (W j v) (M.round_of S.hc (M.opening_slot S.hc q + 1)) := by
    intro v hv j hj
    have hround : M.round_of S.hc (M.opening_slot S.hc q + 1) = q := by
      have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
      apply facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      rw [facts.gr.opening_slot_succ_eq S.hc q]
      exact Nat.add_lt_add_left (by omega) _
    refine hf.awake_g2 _ _ j hj (by rw [← hconfEq]; exact hv) ?_
    rw [hround]
    exact hloEarlyG2
  have hM : 1 ≤ Mh :=
    (by decide : (1 : Nat) ≤ 2).trans ((Nat.le_add_left 2 _).trans hwindow.proposerGateOff)
  have hheight : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h :=
    hwindow.parentHeight.trans
      (facts.cs.derive_height_mono S.E S.cfg
        ((sad% seedAdoption_namedParent_preceq) P))
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  -- The opening proposal, read at the proposer's read on `W`.
  have hproposalP : ∃ cp : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ cp ∧
      M.proposal_with (M.gradeContract cp)
        Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
        ⇢ some P := hwindow.proposal
  obtain ⟨cp, hcp, ho⟩ := hproposalP
  have hP' : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record cp).st ⇢ some P := by
    rewrite [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact ho
  obtain ⟨I, hI, hIP⟩ := proposalInputParent₆₆w facts S
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q)))
    (M.opening_slot S.hc q) (M.proposal_time S.E (M.opening_slot S.hc q)) cp ho
  have hrun : Restated.blockInRunOn M S rho W Xb P :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      ((M.opening_slot S.hc q)) hs hprop hproposalHor hloProp (fun j hj => hf.tick_outcome j _ _ hj)
      hrunP cp hcp ho
  have haligned := Restated.openingAnchorsAligned_of_roundCeilingOn facts S Hs Xb hf hHs hHsXb
    hcom hcarrier h hloVotePrev
  have hstores := Restated.proposalWalkTransferred_of_roundCeilingOn facts S Hs Xb hf hHs hHsXb
    hcom hcarrier cp hcp hP' h haligned hwindow.nextActionInHorizon hheight hM
    hwindow.proposalAtVote hwindow.voteFrontier hwindow.voteGateOff
    hloFrozen hwindow.proposerFrontier hrunP
  obtain ⟨_hal1, _hal2, hal3, hal4, hal5⟩ := haligned
  have hCP : Block.Preceq C.erase P.erase := preceq_trans_Preceq (hal3 cp hcp I hI) hIP
  have hnames : Restated.NamedHonestVotesNameOn M S rho W Hs ((M.opening_slot S.hc q)) P.erase :=
    Restated.honestVotesName_of_voteStoresExtendOn facts S Hs Xb hf hs hvoteHor hloVote hstores
      (fun _ _ _ j hj => hf.tick_outcome j _ _ hj) hrunV
  have hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q))
      (fun X => Block.Preceq P.erase X) :=
    Restated.honestVotesCone_preceqOn facts S rho W Hs Xb ((M.opening_slot S.hc q)) hrun hnames
  -- The three local confirmation facts at every confirmer's read on `W`.
  have hreadBody : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
        (M.confirmation_time S.E (M.opening_slot S.hc q))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st
          (M.confirmation_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).record cc
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) P.erase ∧
        (∀ A, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          Block.Preceq A P.erase) ∧
        P.erase ∈ Restated.Vocabulary.Protocol.confTree M n.st.core := by
    intro v hv cc hcc n
    have hvc : v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
      rw [← hconfEq]; exact hv
    have hXconf : P.erase ∈
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.T := by
      have h1 := hwindow.proposalAtConfirmation v hvc
      rw [tickStore_T₆₆w facts] at h1
      exact h1
    have hfr : (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.h_max
        = Mh := by
      have h1 := hwindow.confirmationFrontier v hvc
      rw [tickStore_h_max₆₆w facts] at h1
      exact h1
    have hgt : (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.h_j
        + 2 ≤ Mh := by
      have h1 := hwindow.confirmationGateOff v hvc
      rw [tickStore_h_j₆₆w facts] at h1
      exact h1
    have hfiltered := Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hvc)
      hconfHor hXconf rfl hrun hheight hM hfr hgt
    have hcand : P.erase ∈ Restated.Vocabulary.Protocol.confTree M n.st.core := by
      show P.erase ∈ Restated.Vocabulary.Protocol.confTree M
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st
          (M.confirmation_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).record cc).st.core
      rw [facts.nd.mkNode_st, confTree_swc₆₆w facts, setClock_core_tickStore₆₆w facts S]
      unfold Restated.Vocabulary.Protocol.confTree Restated.Vocabulary.Proofs.Optimistic.tickStore
      rw [facts.fc.get_filtered_block_tree_set_clock_slot]
      exact hfiltered
    exact ⟨preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hcand),
      hal4 v hvc P cp hcp hP' cc hcc, hcand⟩
  have hlive := Restated.openingProposal_liveConfirmed_actionStore_after_gst_of_localReadsOn facts
    S Hs Xb hf hHs hHsXb hcom hq hloVote hactionHor hpropA cp hcp ho hstores hreadBody hloProp
    hrunV hrunP hrunConf
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S q)) - 1 = (M.opening_slot S.hc q) := by
    have hsc : (Restated.Vocabulary.Execution.Setup.a M S q) =
        M.support_cutoff S.E ((M.opening_slot S.hc q) + 1) :=
      Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts S.hc S.E q
    rw [hsc, facts.sch.slotOf_support_cutoff]
    exact Nat.add_sub_cancel ((M.opening_slot S.hc q)) 1
  have hgenuine : ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st.core.toHealing
          (M.confirmation_time S.E ((M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).cache ⇢ c →
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M
        (M.gradeContract
          (M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st
              (M.confirmation_time S.E ((M.opening_slot S.hc q))))
            (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).record c).cache)
        S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc q)))) ((M.opening_slot S.hc q)) P.erase := by
    intro v hv c hc
    have hvA : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)) := by rw [hconfEq]; exact hv
    obtain ⟨hroot, hanchor, hcand⟩ := hreadBody v hvA c hc
    obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st.core
        (M.confirmation_time S.E ((M.opening_slot S.hc q)))) (M.opening_slot S.hc q)
    have hall := Restated.genuineConfirmationAndPreceq_of_postHealingConeOn facts
      S Hs Xb hf hHs hHsXb hcom hs hloVote hconfHor
      (hHs _ _ (facts.sch.Sts_support_cutoff_le_confirmation_time S.E _) hv) hvotes
      c hc hroot hanchor hcand D hD
    -- `D` is the core store of a round-`q` action read of `v` on `W`, whose confirmation is `P`
    have hc' : M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S q)
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).cache ⇢ c := by
      rw [hconfEq]; exact hc
    obtain ⟨st', hst'⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
      S.hc (M.ns_setClock S.E (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st
        (Restated.Vocabulary.Execution.Setup.a M S q))
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S q) - 1)
    have hD' : M.update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st
          (Restated.Vocabulary.Execution.Setup.a M S q)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S q) - 1) ⇢ D := by
      rw [hslot, hconfEq, facts.hd.setClock_core_eq_store_with_t_s]
      exact hD
    have hcore : st'.core = D :=
      facts.dt.named_update_confirmation_with_core _ _ _ _ _ st' hst' D hD'
    have hliveD := hlive v hvA
      (M.mkNode st' (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).record c)
      ⟨c, hc', st', hst', rfl⟩
    rewrite [facts.nd.mkNode_st] at hliveD; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hliveD; rw [hcore] at hliveD
    rw [facts.nd.mkNode_cache, ← hliveD]
    exact hall.1
  have hdomainG0 : M.domain S.E S.hc q .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    facts.gr.domain_le_a S q .g0
  have hrelWindow := Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hq
    (p := .g0) hloPrev hprevFrontier hfrontierG0 hgateOffG0 (hdomainG0.trans hactionHor) hAprev
  have hfrontierA : ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.h_max = Mh := by
    intro x hx
    have h1 := hwindow.confirmationFrontier x (by rw [← hconfEq]; exact hx)
    rw [tickStore_h_max₆₆w facts, ← hconfEq] at h1
    exact h1
  have hgateA : ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) x).st.h_j + 2 ≤ Mh := by
    intro x hx
    have h1 := hwindow.confirmationGateOff x (by rw [← hconfEq]; exact hx)
    rw [tickStore_h_j₆₆w facts, ← hconfEq] at h1
    exact h1
  have hbatch := Restated.actionBatchAlignedAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hq
    hloPrev hactionHor hprevFrontier hfrontierA hgateA (Can := P.erase)
    (fun u hu n' hn' A2 hA2 G hG => preceq_trans_Preceq
      (hal5 u (hHs _ _ (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le q 1)) hu)
        n' hn' A2 hA2 G hG cp hcp I hI) hIP)
    hAprev
  have hclear := Restated.g0ClearAtAction_of_relativeCarrierWindowOn facts S Hs Xb hf hHs hfb hq
    hactionHor ((facts.gr.domain_le_a S q .g2).trans hactionHor)
    hloPrev hrelWindow cp hcp ho
    (fun u hu n' hn' A2 hA2 G hG I' hI' => hal5 u hu n' hn' A2 hA2 G hG cp hcp I' hI')
    hAprev
  have hcover : Restated.ActionCarriersCoverOn M S rho Hs q P.erase
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))) := by
    unfold Restated.ActionCarriersCoverOn
    intro v hv n hn g hg A hAsel
    obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) q
    have hGread : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n q ⇢ G := by
      unfold Restated.Vocabulary.Internal.PhaseGrades.nodeRead
      exact hG
    have hGanchor : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n q ⇢ G.anchor := by
      unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      exact returns_map_intro₆₆ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hGread
    have hGclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n q P.erase ⇢
        G.clear P.erase := by
      unfold Restated.Vocabulary.Internal.PhaseGrades.nodeClear
      exact returns_map_intro₆₆
        (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.clear P.erase) _ G hGread
    have hnmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v q :=
      ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)),
        mem_stateBeforeTime_along₆₆ hf.sorted hf.onePath _, hn⟩
    have hWb := Restated.actionSGBlockAt_eq_liveConfirmed_of_batchAlignedOn facts S
      (Hs ((Restated.Vocabulary.Execution.Setup.a M S q))) (Can := P.erase) (D := P.erase)
      (A := G.anchor) n hnmem (hlive v hv n hn) (hbatch v hv n hn)
      (Proofs.ModelProperties.Preceq_self _) G hGread rfl
      (preceq_trans_Preceq (h.actionAnchor v hv n hn _ hGanchor) hCP)
      (hclear v (hHs _ _ hdomainG0 hv) n hn _ hGclear) g hg A hAsel
    rw [hWb]
    exact Proofs.ModelProperties.Preceq_self _
  have hnextActive : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
      P.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) v).st.core).toFG := by
    intro v hv
    have hmem : P.erase ∈
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) v).st.T := by
      have h1 : P.erase ∈ (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) v).st.core
          ).toFG.toSG.toGoldfishStore.T := hwindow.proposalAtNext v hv
      rw [facts.sto.toHealing_T] at h1
      exact h1
    exact (seedBand_active_at_actionRead₆₆ facts S Hs Xb hf hrun hheight (hHsXb _ hv)
      hwindow.nextActionInHorizon hmem (hwindow.nextFrontier v hv) (hwindow.nextGateOff v hv)).1
  have hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hwindow.postOpeningVote.trans
      ((facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans (le_of_eq hconfEq.symm))
  have hnextCut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q)).trans
      hwindow.nextActionInHorizon
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))).Nonempty :=
    nonempty_of_honestWeightMajority_l54 (hmajority _ hwindow.nextActionInHorizon)
  have hgrade := Restated.namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn facts
    S Hs Xb hf hHs hHsXb hmajority hcover hpostAction hnextCut hnextActive hnextActiveDomain
    (hA q (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPrev (Nat.sub_lt hq Nat.one_pos)))
    hloAction hne
  have hlifecycle : Restated.NamedRawOpeningLifecycleAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb q P :=
    { roundPositive := hq
      proposal := hwindow.proposal
      proposerHonest := hprop
      proposalInHorizon := hproposalHor
      runBlock := hrun
      liveConfirmed := hlive
      actionCover := hcover
      gradeNext := hgrade }
  exact
    { proposal := hwindow.proposal
      votes := hvotes
      genuineConfirmation := hgenuine
      actionCover := hcover
      gradeNext := hgrade
      lifecycle := hlifecycle }

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-- Along the path `W` with the admissible fields `hf`, with `s` round `q`'s opening slot and `p`
    its proposer: if `w`'s store in `W (strictEventIndex rho read)` is a fixed-height justification
    root at `H` (`hfix`), `A` is a descendant of that store's justified block and an ancestor of the
    parent of every proposal input at `p`'s read with the cache `c`, `B` is a proposal `p`'s duty
    can return there, `0 < q`, `lo ≤ read`, `read + Δ` is at most `vote_time s`, which is in the
    horizon, no `h_max` over the set for `vote_time s` exceeds `H` (`hcap`), `lo ≤ proposal_time s`,
    `p` is in the set for `s`'s confirmation time, and `p` passes the grade-1 awake test at its
    proposal ticks (`hrun`), then every member of the set for `vote_time s` admits `B` along `W`
    before `vote_time s`. -/
theorem openingProposalAdmittedBeforeVote_atVote_l66 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} {A : Block V} {B : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some B)
    (hq : 0 < q)
    (hpostRead : lo ≤ read)
    (hdelay : read + S.E.Δ ≤ M.vote_time S.E ((M.opening_slot S.hc q)))
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hcap : ((Hs (M.vote_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H)
    (hpostProposal : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposer : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hJA : Block.Preceq (W (strictEventIndex rho read) w).st.J A)
    (hAparent : ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      Block.Preceq A I.parent)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v B.erase
        (M.vote_time S.E ((M.opening_slot S.hc q))) := by
  set s := M.opening_slot S.hc q with hs_def
  set p := S.E.proposer s with hp_def
  set tp := M.proposal_time S.E s with htp_def
  set J := (W (strictEventIndex rho read) w).st.J with hJ_def
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  -- the proposal's parent
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc (S.node p)
    (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
      (W (strictEventIndex rho tp) p).record c).st.core)
  have hAI : Block.Preceq A I.parent := hAparent I hI
  have hI' : M.with_proposal_input (M.gradeContract c) S.E S.hc (S.node p)
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp) c).core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  obtain ⟨par, hpar, hparE⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ B _
      (by rw [facts.dt.proposal_with_store_with_cache]; exact hB) rfl I hI'
  have hparentEq : B.erase.parent = I.parent := by
    rw [Proofs.NamedWire.erase_parent]
    cases B with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hpar
    | node q' _ _ _ _ _ _ =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hpar
      subst hpar
      rw [Proofs.ModelProperties.named_parent_node]
      exact hparE
  have hparentB : Block.Preceq I.parent B.erase := by
    rw [← hparentEq]
    exact preceq_eq_true_iff_Preceq.1 (Proofs.preceq_parent B.erase)
  have hJB : Block.Preceq J B.erase :=
    preceq_trans_Preceq hJA (preceq_trans_Preceq hAI hparentB)
  -- every receiver's finality root at the vote instant is `J`
  have hroot : ∀ v ∈ Hs (M.vote_time S.E s),
      M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core).toFG
        = J := by
    intro v hv
    exact (Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
      facts S Hs Xb hf hHs hHsXb hsb hfix hv hpostRead hdelay hvoteHor hcap).1
  have hFvote : ∀ v ∈ Hs (M.vote_time S.E s),
      Block.Preceq (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.F B.erase := by
    intro v hv
    have h := F_preceq_fgRoot_along₆₆ facts S hf.sorted hf.onePath v (M.vote_time S.E s)
    rw [hroot v hv] at h
    exact preceq_trans_Preceq h hJB
  have hs : 0 < s := facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hvoteConf : M.vote_time S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E s
  have hproposalVote : tp + S.E.Δ = M.vote_time S.E s :=
    (facts.sch.slot_instants_l55 S.E s).1.symm
  have hproposalLeVote : tp ≤ M.vote_time S.E s :=
    le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)
  have hproposalConf : tp ≤ M.confirmation_time S.E s := hproposalLeVote.trans hvoteConf
  have hproposalHor : tp ≤ rho.horizon := hproposalLeVote.trans hvoteHor
  have hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p tp) →
      ∃ out : M.N × List (NamedObject V), M.tick S p (W j p) tp ⇢ out :=
    fun j hj => hf.tick_outcome j _ _ hj
  obtain ⟨B0, hB0, hB0slot, hemit0⟩ :=
    Restated.proposedBlockAt_emits_of_honestOn facts S Hs Xb hf hHs s hs hproposer hproposalHor
      hpostProposal hneTick hrun c hc (some B) hB
  cases hB0
  have hBslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact hB0slot
  have hBpos : 0 < B.slot := by
    rw [hB0slot]
    exact hs
  obtain ⟨i0, hacc0⟩ := Restated.acceptsAt_proposedBlockOn facts S Hs Xb hf hHs hs hproposer
    hproposalHor hpostProposal hneTick hrun c hc hB
  intro v hv
  have hdeadline : tp + S.E.Δ ≤ rho.horizon := by
    rw [hproposalVote]
    exact hvoteHor
  have hguard : ∀ B' : NamedBlock V, Object.block B = .block B' →
      Block.compatible (W (strictEventIndex rho (tp + S.E.Δ)) v).st.core.F B'.erase = true := by
    intro B' hB'
    cases hB'
    rw [hproposalVote]
    exact compatible_of_cases (Or.inl (hFvote v hv))
  have hpropP : p ∈ Hs tp := hHs _ _ hproposalConf hproposer
  have hvRecv : v ∈ Hs (tp + S.E.Δ) := by
    rw [hproposalVote]
    exact hv
  obtain ⟨t, hlo, hhi, j, hcall⟩ :=
    hf.broadcast p _ _ hpropP hemit0 v hvRecv hpostProposal hdeadline hguard
  have hbeforeVote : t < M.vote_time S.E s := by
    rw [← hproposalVote]
    exact hhi
  obtain ⟨e, hej, -, heTime⟩ := hcall.2
  have hjBound : j + 1 ≤ strictEventIndex rho (M.vote_time S.E s) :=
    index_succ_le_strict_filter_length rho hf.sorted (M.vote_time S.E s) hej
      (by rw [heTime]; exact hbeforeVote)
  have hFj : Block.Preceq (W j v).st.core.F B.erase :=
    preceq_trans_Preceq
      (F_mono_along₆₆ facts S hf.onePath v ((Nat.le_succ j).trans hjBound))
      (hFvote v hv)
  have hvProp : v ∈ Hs (M.proposal_time S.E B.erase.slot) := by
    rw [hBslot]
    exact hHs _ _ hproposalLeVote hv
  have hheld := Restated.handled_block_held_of_finalized_prefixOn facts S rho Hs Xb hf hHsXb
    (hHsXb _ hpropP) hvProp (Or.inr (by rw [hBslot]; exact hpostProposal)) hacc0 hcall hlo hFj
  obtain ⟨j', t', hacc', ht'⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.acceptsAt_before_of_processed_after_event facts S rho
      hf.sorted (w := v) hBpos hej (by rw [heTime]; exact hbeforeVote) W hf.onePath
      (by simp only [Restated.Vocabulary.Execution.Object.processed]; exact decide_eq_true hheld)
  exact ⟨B, rfl, j', t', hacc', ht'⟩

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-! ## Frozen opening votes and the fixed-root anchors -/

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₆s {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- The node state staged from `b` with its clock set to `t` and the cache `c` has the filtered
    block tree of `b`'s core store. -/
private theorem stagedNode_filtered₆₆s (facts : Record.Facts M) (S : Setup V) (b : M.N) (t : Time)
    (c : M.Cache) :
    M.get_filtered_block_tree
        (M.toHealing (M.mkNode (M.ns_setClock S.E b.st t) b.record c).st.core).toFG =
      M.get_filtered_block_tree (M.toHealing b.st.core).toFG := by
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`, with `o` round
    `q`'s opening slot: if `w`'s store in `W (strictEventIndex rho read)` is a fixed-height
    justification root at `H` (`hfix`), `P` is a proposal of `o`'s proposer at its read with the
    cache `c`, `0 < q`, `read + Δ` is at most the proposal, vote and confirmation times of `o`, the
    confirmation time is in the horizon with no `h_max` over its set exceeding `H`, the bounds on
    `lo` hold, the proposer is in the set for its confirmation time, `A` is a descendant of the
    justified block and an ancestor of the parent of every proposal input at the proposer's read,
    the opening parent run `hparents` holds, every member of the set for the vote time has the pivot
    transfer and the frozen suffix at each of its vote-duty reads, and the awake hypothesis `hA`
    holds, then every committee member of `o` in the set for its vote time has, at each of its
    vote-duty reads, the frozen opening vote for `A` and `P`. -/
theorem openingFrozenVotes_of_fixedJustificationRootParentDataOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} {A : Block V} {P : NamedBlock V}
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
    (hq : 0 < q)
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hvoteDelay : read + S.E.Δ ≤
      M.vote_time S.E ((M.opening_slot S.hc q)))
    (_hconfirmationDelay : read + S.E.Δ ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)))
    (hconfirmationHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hconfirmationCap : ((Hs (M.confirmation_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H)
    (hpostSource : lo ≤ M.proposal_time S.E
      ((M.opening_slot S.hc q) - 1))
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hJA : Block.Preceq (W (strictEventIndex rho read) w).st.J A)
    (hAparent : ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      Block.Preceq A I.parent)
    (hparents : Restated.FixedHeightRootOpeningParentRunOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs q)
    (_of_pivotTransfer : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
      Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho
        ((M.opening_slot S.hc q)) A v P
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c)
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv))
    (_of_frozenSuffix : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
      ∀ vv : Finset (GoldfishVote V),
        M.voter_view S.E
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
            (M.vote_time S.E (M.opening_slot S.hc q)))
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record
              cv).st.core).toFG.toSG.toGoldfishStore
          ((M.opening_slot S.hc q)) ⇢ vv →
      ∀ u, u ∈ vv →
      u ∉ P.erase.gf_votes.toFinset →
      M.equivocates P.erase.gf_votes.toFinset u.val_index = true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      v ∈ S.E.committee ((M.opening_slot S.hc q)) →
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
      Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt M S rho
        ((M.opening_slot S.hc q) - 1) A v P
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c)
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv) := by
  set o := M.opening_slot S.hc q with ho_def
  set p := S.E.proposer o with hp_def
  have hΔ := S.E.Δ_pos
  have hqOne : 1 ≤ q := hq
  have hopenPos : 0 < o := facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hopen : o - 1 + 1 = o := Nat.sub_add_cancel hopenPos
  have hproposalHor : M.proposal_time S.E o ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E o).trans hconfirmationHor
  have hvoteHor : M.vote_time S.E o ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E o).trans hconfirmationHor
  have hpostProposal : lo ≤ M.proposal_time S.E o :=
    (hpostRead.trans (Int.le_add_of_nonneg_right hΔ.le)).trans hproposalDelay
  have hloVote : lo ≤ M.vote_time S.E o :=
    hpostProposal.trans (facts.sch.proposal_time_lt_vote_time S.E o).le
  have hvoteConf : M.vote_time S.E o + S.E.Δ < M.confirmation_time S.E o := by
    have h1 := facts.sch.slotStart_add_delta_eq_vote_time S.E o
    have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E o
    linarith
  have hvoteCap : ((Hs (M.vote_time S.E o)).sup fun u =>
      (W (inclusiveEventIndex rho (M.vote_time S.E o)) u).st.core.h_max) ≤ H :=
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloVote hvoteConf
      hconfirmationHor ⟨_, hprop⟩).trans hconfirmationCap
  -- The proposal's parent, read at the proposer's read on `W`.
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc (S.node p)
    (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E o)) p).st (M.proposal_time S.E o))
      (W (strictEventIndex rho (M.proposal_time S.E o)) p).record c).st.core)
  have hAI : Block.Preceq A I.parent := hAparent I hI
  have hI' : M.with_proposal_input (M.gradeContract c) S.E S.hc (S.node p)
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E o)) p).st
        (M.proposal_time S.E o)) c).core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  obtain ⟨par, hpar, hparE⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ P _
      (by rw [facts.dt.proposal_with_store_with_cache]; exact hP) rfl I hI'
  have hparentEq : P.erase.parent = I.parent := by
    rw [Proofs.NamedWire.erase_parent]
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hpar
    | node q' _ _ _ _ _ _ =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hpar
      subst hpar
      rw [Proofs.ModelProperties.named_parent_node]
      exact hparE
  have hparentP : Block.Preceq I.parent P.erase := by
    rw [← hparentEq]
    exact preceq_eq_true_iff_Preceq.1 (Proofs.preceq_parent P.erase)
  have hAP : Block.Preceq A P.erase := preceq_trans_Preceq hAI hparentP
  have hJP : Block.Preceq (W (strictEventIndex rho read) w).st.J P.erase :=
    preceq_trans_Preceq hJA hAP
  have hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p (M.proposal_time S.E o)) →
      ∃ out : M.N × List (NamedObject V), M.tick S p (W j p) (M.proposal_time S.E o) ⇢ out :=
    fun j hj => hf.tick_outcome j _ _ hj
  -- The opening proposer passes the grade-1 awake test at its proposal ticks.
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p (M.proposal_time S.E o)) →
      M.awake_for_grade1 S p (W j p) (M.round_of S.hc o) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc o) .g1 - S.E.Δ := by
      rw [ho_def, facts.gr.round_of_opening_slot_eq S.hc q]
      have h1 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hpostPreviousAction
        (Nat.sub_lt hq Nat.one_pos)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E o) hprop) hwin
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      o hopenPos hprop hproposalHor hpostProposal hneTick hrunP c hc hP
  obtain ⟨B0, hB0, hB0slot, -⟩ :=
    Restated.proposedBlockAt_emits_of_honestOn facts S Hs Xb hf hHs o hopenPos hprop hproposalHor
      hpostProposal hneTick hrunP c hc (some P) hP
  cases hB0
  have hPslot : P.erase.slot = o := by
    rw [Proofs.NamedWire.erase_slot]
    exact hB0slot
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.fixedRoot_namedTarget_of_fixedRootOn facts S Hs Xb hfix
  obtain ⟨Jp, hJpP, hJpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift P hJP
  have hJpRun : Restated.RunBlockOn M S rho W Xb Jp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hPrun hJpP
  have hrootEq : Jp.root = Jn.root := by
    rw [← Proofs.NamedWire.erase_root Jp, ← Proofs.NamedWire.erase_root Jn,
      hJpErase, hJnErase]
  have hJpEq : Jp = Jn :=
    hf.rootCollisionFree.root_injective
      Jp Jn hJpRun hJnRun Jp Jn
      (Or.inl (Proofs.NamedAncestry.named_self Jp))
      (Or.inr (Proofs.NamedAncestry.named_self Jn)) hrootEq
  have hPheight : H - 1 ≤ (M.derive_named S.E S.cfg P).h := by
    rw [← hJnHeight, ← hJpEq]
    exact facts.cs.derive_height_mono S.E S.cfg hJpP
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q - 1 + 1) ≤
      rho.horizon := by
    rw [Nat.sub_add_cancel hqOne]
    refine (le_of_lt (Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc
      S.E.Δ_pos q)).trans ?_
    rw [Restated.Vocabulary.Protocol.Γ_0_eq_proposal_time facts]
    exact hproposalHor
  have hadmit := openingProposalAdmittedBeforeVote_atVote_l66 facts
    S Hs Xb hf hHs hHsXb hfix c hc hP hq hpostRead hvoteDelay hvoteHor hvoteCap hpostProposal
    hprop hJA hAparent hrunP
  have hround : M.round_of S.hc (o - 1 + 1) = q - 1 + 1 := by
    rw [hopen, Nat.sub_add_cancel hqOne]
    exact facts.gr.round_of_opening_slot_eq_schedule S.hc q
  have hupperP : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B P.erase := by
    intro u hu n hn g hg B hB
    exact preceq_trans_Preceq (hparents.actionTargetParent u hu n hn g hg B hB c hc I hI) hparentP
  have hanchorGen := Restated.voterAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf
    hHs hHsXb hfb (q := q - 1) (s := o - 1) hround hpostPreviousAction hcut
  rw [hopen] at hanchorGen
  intro v hv _hcommittee cv hcv
  have hwv := mem_stateBeforeTime_along₆₆ hf.sorted hf.onePath (S := S) (M.vote_time S.E o)
  set wv := W (strictEventIndex rho (M.vote_time S.E o)) v with hwv_def
  set D := (M.ns_setClock S.E wv.st (M.vote_time S.E o)).core with hD_def
  set m := M.mkNode (M.ns_setClock S.E wv.st (M.vote_time S.E o)) wv.record cv with hm_def
  have hmcore : m.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  have hrootMax :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hv hpostRead hvoteDelay hvoteHor hvoteCap
  have hDT : D.T = wv.st.core.T := by
    rw [hD_def, facts.hd.Sts_setClock_core_T]
  have hDhmax : D.h_max = wv.st.core.h_max := by
    rw [hD_def, facts.hd.setClock_core_h_max]
  have hDs : D.s = o := by
    rw [hD_def, facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hDfiltered : M.get_filtered_block_tree (M.toHealing D).toFG =
      M.get_filtered_block_tree (M.toHealing wv.st.core).toFG := by
    rw [hD_def, facts.hd.setClock_core_eq_store_with_t_s]
    exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _
  have hDroot : M.get_fg_root (M.toHealing D).toFG =
      M.get_fg_root (M.toHealing wv.st.core).toFG := by
    rw [hD_def, facts.hd.setClock_core_eq_store_with_t_s]
    exact facts.fc.get_fg_root_set_clock_slot _ _ _
  have hrootD : M.get_fg_root (M.toHealing D).toFG = (W (strictEventIndex rho read) w).st.J :=
    hDroot.trans hrootMax.1
  have hmaxD : D.h_max = H := hDhmax.trans hrootMax.2
  have hPtreeW : P.erase ∈ wv.st.core.T :=
    (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf (hadmit v hv) (le_refl _)).1
  have hPT : P.erase ∈ D.T := by
    rw [hDT]
    exact hPtreeW
  have hPfiltered : P.erase ∈ M.get_filtered_block_tree (M.toHealing D).toFG := by
    rw [hDfiltered]
    exact Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts S Hs Xb hf (hHsXb _ hv) hPrun
      hPtreeW hJP hPheight hrootMax.1 hrootMax.2
  have hmaxP : D.h_max ≤ (M.derive_named S.E S.cfg P).h + 1 := by
    rw [hmaxD]
    have hHone : 1 ≤ H := Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hHone).symm
      _ ≤ (M.derive_named S.E S.cfg P).h + 1 := Nat.add_le_add_right hPheight 1
  have hFJ : Block.Preceq D.F D.J := by
    rw [hD_def, facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.vote_time S.E o) v _ hwv
  have hpc : Restated.Vocabulary.Internal.ParentClosed M D := by
    have h := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.vote_time S.E o) v _ hwv
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at h ⊢
    rw [facts.sto.toHealing_T] at h ⊢
    rw [hDT]
    exact h
  have hDs' : (M.toHealing D).s = o := (facts.sto.toHealing_gs_s D).trans hDs
  have hvFreeze : v ∈ Hs (M.view_freeze S.E (o - 1)) := by
    have h1 := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E (o - 1)
    have h2 := facts.sch.proposal_time_lt_vote_time S.E (o - 1 + 1)
    rw [hopen] at h1 h2
    exact hHs _ _ (by linarith) hv
  have hgatFreeze : lo ≤ M.view_freeze S.E (o - 1) :=
    hpostSource.trans ((facts.sch.proposal_time_lt_vote_time S.E (o - 1)).le.trans
      (facts.sch.vote_time_le_view_freeze S.E (o - 1)))
  -- every ancestor of the proposal that is a descendant of the finality root is a candidate
  have hcand : ∀ {C : Block V}, Block.Preceq C P.erase →
      Block.Preceq (M.get_fg_root (M.toHealing D).toFG) C →
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E D D.s ⇢ T → C ∈ T := by
    intro C hCP hrootC T hT
    obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
      (M.toHealing D).toFG.toSG.toGoldfishStore (M.toHealing D).s
    have hPQ : P.erase ∈ Q :=
      facts.fc.mem_voter_processed_block_tree_of_slot S.E _ _
        (by rw [facts.sto.toHealing_gs_T]; exact hPT)
        (by rw [hPslot]; exact hDs'.symm) Q hQ
    have hCT : C ∈ D.T := by
      have hpc' := hpc
      unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc'
      rw [facts.sto.toHealing_T] at hpc'
      exact Proofs.Records.mem_of_preceq hpc'.2 C P.erase hPT (preceq_eq_true_iff_Preceq.mpr hCP)
    have hCfiltered : C ∈ M.get_filtered_block_tree (M.toHealing D).toFG :=
      facts.fc.mem_filtered_of_preceq
        (by
          rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J]
          exact preceq_eq_true_iff_Preceq.mpr hFJ)
        hPfiltered (by rw [facts.sto.toHealing_T]; exact hCT) (preceq_eq_true_iff_Preceq.mpr hCP)
        (preceq_eq_true_iff_Preceq.mpr hrootC)
    have key := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts S Hs Xb hf
      hHsXb (s := o - 1) hvFreeze (C := C) (H := P)
    simp only [hopen] at key
    have hCfrom : C ∈ M.get_filtered_block_tree_from (M.toHealing D).toFG Q :=
      key Q hQ hPQ hPrun hCP hCfiltered hmaxP hgatFreeze
    have hTeq := facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E D Q hQ T hT
    rw [← hTeq]
    exact hCfrom
  have hTD : ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
      M.voter_filtered_block_tree S.E D D.s ⇢ T := by
    intro T hT
    rw [hmcore, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree] at hT
    exact hT
  have hAne : A ≠ P.erase := by
    intro heq
    have hPparent : Block.Preceq P.erase I.parent := by
      rw [← heq]
      exact hAI
    have heqParent : P.erase = I.parent :=
      Proofs.ModelProperties.Preceq_antisymm hPparent hparentP
    have hrawParent : P.erase.parent? = some par.erase := by
      simp only [Proofs.NamedWire.erase_parent_optional, hpar, Option.map_some]
    rw [hparE, ← heqParent] at hrawParent
    have hdepth := Protocol.depth_of_parent? hrawParent
    omega
  have hrootStore : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S wv.st.core o)).toFG)
      P.erase := by
    have hvs : Restated.Vocabulary.Proofs.Optimistic.voteStore M S wv.st.core o = D :=
      (facts.hd.setClock_core_eq_store_with_t_s S.E wv.st (M.vote_time S.E o)).symm
    rw [hvs, hrootD]
    exact hJP
  have hanchorP := hanchorGen hvoteHor hupperP hv hrootStore hA cv hcv
  have hrootAnchor : ∀ a : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ a →
      Block.Preceq (M.get_fg_root (M.toHealing D).toFG) a := by
    intro a ha
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead at ha
    obtain ⟨G, hG, hGa⟩ := returns_map_elim₆₆s _ _ _ ha
    obtain ⟨R, hR⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing m.st.core)
      (M.round_of S.hc m.st.core.s)
      (M.readFrame m.cache (M.toHealing m.st.core) (M.round_of S.hc m.st.core.s)).g1
    have hGR : G.anchor = R :=
      facts.nd.Sts_gradeContract_read_anchor m.cache S.E S.hc _ _ G hG R hR
    have h := Restated.Vocabulary.Proofs.NamedOutageClosure.fg_root_preceq_anchor facts S.E S.hc
      (M.toHealing m.st.core) _ _ R hR
    have hGa' : G.anchor = a := hGa
    rw [← hGa', hGR]
    rw [hmcore, facts.nd.store_with_cache_get_fg_root] at h
    exact h
  have hrootP : Block.Preceq (M.get_fg_root (M.toHealing D).toFG) P.erase := by
    rw [hrootD]
    exact hJP
  have hrootA : Block.Preceq (M.get_fg_root (M.toHealing D).toFG) A := by
    rw [hrootD]
    exact hJA
  refine
    { proposalCandidate := fun T hT =>
        hcand (Proofs.ModelProperties.Preceq_self P.erase) hrootP T (hTD T hT)
      pivotCandidate := fun T hT => Finset.mem_erase.mpr ⟨hAne, hcand hAP hrootA T (hTD T hT)⟩
      pivotAnchorCompatible := fun a ha =>
        compatible_of_preceq_common_Preceq (hanchorP a ha) hAP
      proposalAnchorCompatible := fun a ha =>
        compatible_of_preceq_common_Preceq (hanchorP a ha) (Proofs.ModelProperties.Preceq_self P.erase)
      pivotPath := fun a ha T hT _haA C haC _hCne hCA => ?_
      suffix := by rw [hopen]; exact _of_pivotTransfer v hv cv hcv
      rawExtra := by rw [hopen]; exact _of_frozenSuffix v hv cv hcv }
  refine Finset.mem_erase.mpr
    ⟨fun hCP => hAne (Proofs.ModelProperties.Preceq_antisymm hAP (by rw [← hCP]; exact hCA)), ?_⟩
  exact hcand (preceq_trans_Preceq hCA hAP)
    (preceq_trans_Preceq (hrootAnchor a ha) haC) T (hTD T hT)

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades

/-- Along the path `W` with the admissible fields `hf`: if `0 < r`, `t` is a time of round `r` equal
    to its grade-1 domain time and in the horizon, and `c` is an outcome of `w`'s cache update at
    `t` (`hc`), then for every outcome `fr` of the grade-1 store root of `w`'s store in
    `W (strictEventIndex rho (domain r .g1))`, the grade-1 frame of the node state staged with `c`
    is `fr` clipped by that node state's finalized block. -/
theorem relAnchor_preparedFrame_g1_eq_storeRoot_at_openingOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (r : Round) (hr : 0 < r) (t : Time) (hw : w ∈ Hs t)
    (hround : (M.round_of S.hc (S.E.slotOf t)) = r)
    (hopen : M.domain S.E S.hc r .g1 = t)
    (hhor : M.domain S.E S.hc r .g1 ≤ rho.horizon)
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
            (W (strictEventIndex rho t) w).record c).st.core.F)) :=
  Restated.fixedRoot_preparedFrame_g1_eq_storeRoot_at_openingOn facts S rho Hs Xb hf w r hr t hw hround hopen
    hhor c hc

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if `w`'s store in
    `W (strictEventIndex rho read)` is a fixed-height justification root (`hfix`) whose justified
    block is graded at round `q − 1` (`hforms`) and stays in the filtered trees of the later reads
    (`hwindow`, `hdomainWindow`, `hactiveAtAction`), the proposer of round `q`'s opening slot is in
    the set for its proposal time `tp` with no `h_max` over that set exceeding the root's height
    (`hproposalCap`), the bounds on `lo` and the awake hypothesis `hA` hold, and `c` is an outcome
    of the proposer's cache update at `tp` (`hc`), then the grade-1 frame of round `q` of the node
    state staged with `c` is some root that is a descendant of the justified block of `w`'s store in
    `W (strictEventIndex rho read)`. -/
theorem proposerFrameG1_of_fixedRootLockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    (hdomainWindow : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core).toFG)
    (hpostRead : lo ≤ read)
    (hpostPreviousAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hactiveAtAction : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG)
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q))))
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hlo₁ : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c) :
    ∃ root : Block V,
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
        some (some root) ∧
      Block.Preceq (W (strictEventIndex rho read) w).st.J root := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hJG1 := Restated.namedG1At_fixedRootTarget_of_retainedPreviousGradeOn facts S Hs Xb hf
    hHs hHsXb hfb hfix hqTwo hforms hwindow hdomainWindow hpostRead hpostPreviousAction hcut
    hactionHor hactiveAtAction hprop hproposalDelay hproposalHor hproposalCap hlo₁ hloOpen hA
  have hrootPre := (Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
    facts S Hs Xb hf hHs hHsXb hf.slashableBound hfix hprop hpostRead hproposalDelay hproposalHor
    hproposalCap).1
  set p := S.E.proposer (M.opening_slot S.hc q) with hp
  set tp := M.proposal_time S.E (M.opening_slot S.hc q) with htp
  set J := (W (strictEventIndex rho read) w).st.J with hJ
  have hopen : M.domain S.E S.hc q .g1 = tp := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hdomainHor : M.domain S.E S.hc q .g1 ≤ rho.horizon := by
    rw [hopen]
    exact hproposalHor
  have hround : (M.round_of S.hc) (S.E.slotOf tp) = q := by
    rw [htp, facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_opening_slot_eq S.hc q
  have hJstrict : J ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho tp) p).st.core).toFG := by
    rw [← hrootPre]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S
      rho tp p _ (mem_stateBeforeTime_along₆₆ hf.sorted hf.onePath tp)
  have hJmemT : J ∈ (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) p).st.core.T := by
    rw [hopen]
    exact Restated.Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree facts hJstrict
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) p).st.core.F S.hc.η_SG q
    (M.early S.E S.hc q .g1) (M.late S.E S.hc q .g1)
  obtain ⟨raw, hraw, hJraw⟩ := facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) p).st.core.F S.hc.η_SG q
    (e := M.early S.E S.hc q .g1) (l := M.late S.E S.hc q .g1)
    (facts.gr.early_le_late S.E S.hc q .g1)
    (by rw [facts.gr.Sts_gradeView_T]; exact hJmemT) true
    (storeGrade_true_of_all₆₆ facts S.E S.hc _ q .g1 J hJG1) rfl fr hfr
  subst hraw
  have hframeStore := Restated.relAnchor_preparedFrame_g1_eq_storeRoot_at_openingOn facts
    S rho Hs Xb hf p q hq tp hprop hround hopen hdomainHor c hc (some raw) hfr
  have hnF : (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
      (W (strictEventIndex rho tp) p).record c).st.core.F =
      (W (strictEventIndex rho tp) p).st.core.F := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_F]
  have hFJ : Block.Preceq (W (strictEventIndex rho tp) p).st.core.F J := by
    have h := facts.fc.q10_filtered_F hJstrict
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  refine ⟨M.clipGrade raw (W (strictEventIndex rho tp) p).st.core.F, ?_, ?_⟩
  · rw [hnF] at hframeStore
    simpa only [Option.map_some] using hframeStore
  · exact (facts.gr.q10_retained_prefix raw _ J (compatible_of_cases (Or.inr hFJ))).mpr hJraw

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades

/-- Under the hypotheses of `proposerFrameG1_of_fixedRootLockOn`, every anchor `X` of round `q` of
    the proposer's node state `n` staged with `c` has every outcome of its grade-1 store grade
    `true` at the proposer's store in `W (strictEventIndex rho (domain q .g1))`, is a descendant of
    the justified block of `w`'s store in `W (strictEventIndex rho read)`, and is in the filtered
    tree of `n`. -/
theorem relativeAnchor_of_fixedRootLockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    (hdomainWindow : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core).toFG)
    (hpostRead : lo ≤ read)
    (hpostPreviousAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hactiveAtAction : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG)
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q))))
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hlo₁ : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).record c
    ∀ X : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n q ⇢ X →
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
          (S.E.proposer (M.opening_slot S.hc q))).st q .g1 X ⇢ b → b = true) ∧
      Block.Preceq (W (strictEventIndex rho read) w).st.J X ∧
      X ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
  intro n X hX
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  obtain ⟨root, hframe, hJroot⟩ :=
    Restated.proposerFrameG1_of_fixedRootLockOn facts S Hs Xb hf hHs hHsXb hfb hfix hqTwo hforms
      hwindow hdomainWindow hpostRead hpostPreviousAction hcut hactionHor
      hactiveAtAction hprop hproposalDelay hproposalHor hproposalCap hlo₁ hloOpen hA c hc
  have hrootPre := (Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
    facts S Hs Xb hf hHs hHsXb hf.slashableBound hfix hprop hpostRead hproposalDelay hproposalHor
    hproposalCap).1
  have hJtree : (W (strictEventIndex rho read) w).st.J ∈
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
    rw [show M.get_filtered_block_tree (M.toHealing n.st.core).toFG = _ from
      stagedNode_filtered₆₆s facts S _ _ c, ← hrootPre]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S
      rho _ _ _ (mem_stateBeforeTime_along₆₆ hf.sorted hf.onePath _)
  obtain ⟨A, hactive, hJA⟩ := facts.gr.activePrefix_covers hJtree hJroot
  have hXA : X = A :=
    Restated.Vocabulary.Proofs.HealingSurface.GradeDeliveryRun.nodeAnchor_eq_of_activePrefix_some facts S
      n (by rw [facts.gr.phaseResult_g1]; exact hframe) hactive X hX
  subst hXA
  have hrootG1 := Restated.namedG1At_of_preparedOpeningFrameOn facts S Hs Xb hf hq hprop hproposalHor
    c hc hframe
  have hAroot : Block.Preceq X root := facts.gr.preceq_of_activePrefix_eq_some hactive
  refine ⟨?_, hJA, facts.gr.activePrefix_mem _ root X hactive⟩
  intro bA hbA
  obtain ⟨bB, hbB⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
      (S.E.proposer (M.opening_slot S.hc q))).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
      (S.E.proposer (M.opening_slot S.hc q))).st.core.F
    S.hc.η_SG q (M.early S.E S.hc q .g1) (M.late S.E S.hc q .g1) root
  exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ q .g1 hAroot bB hbB
    (hrootG1 bB hbB) bA hbA

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`: if `w`'s store in `W (strictEventIndex rho read)` is a fixed-height justification
    root at `H` whose justified block is graded at round `q − 1` (`hforms`) and retained
    (`hwindow`), the opening cone root lock `hlock` holds, the proposer of round `q`'s opening slot
    is in the set for its proposal time `tp` with no `h_max` over that set exceeding `H`, and `A` is
    graded 1 at the proposer's store before `domain q .g1` (`hAG1`), in the filtered tree of its
    prepared read (`hAfiltered`) and a descendant of the justified block (`hJA`), then every
    round-`(q − 1)` action carrier and every block graded 1 at round `q` is an ancestor of the
    parent of every proposal input at the proposer's prepared read, for every outcome of its cache
    update. -/
theorem fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relativeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} {A : Block V} (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    (_hdomainWindow : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core).toFG)
    (_hactiveAtAction : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG)
    {wd : V → M.N}
    (hlock : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
      ((M.opening_slot S.hc q) - 1) wd
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))))
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hpostCone : lo ≤
      M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q))))
    (c : M.Cache)
    (_hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (_hAanchor : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c) q ⇢ A)
    (hAG1 : ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
        (S.E.proposer (M.opening_slot S.hc q))).st q .g1 A ⇢ b → b = true)
    (hAfiltered : A ∈ M.get_filtered_block_tree
      (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c).st.core).toFG)
    (hJA : Block.Preceq (W (strictEventIndex rho read) w).st.J A)
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    Restated.FixedHeightRootOpeningParentRunOn M S rho (fun t => W (strictEventIndex rho t)) Hs q := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  obtain ⟨target, htarget⟩ :=
    Restated.fixedRoot_preparedTargetData_of_fixedRoot_abstractOn facts
      S Hs Xb hf hHs hHsXb hfix (q := q) (W (strictEventIndex rho read) w).st
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st rfl rfl hprop hpostRead hproposalDelay
        hproposalHor hproposalCap
  obtain ⟨C, vC, hvC, hCvC, hupper, hcone, hbelow⟩ :=
    Restated.fixedRoot_namedG1CommonCeiling_publicOn facts S Hs Xb hf hHs hHsXb hcom hfb hfix hqTwo
      hforms hwindow hlock hpostRead hproposalDelay hproposalHor hproposalCap
        hpostPreviousAction hloOpen hA
  have hopen : M.domain S.E S.hc q .g1 =
      M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hpropD : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs (M.domain S.E S.hc q .g1) := by
    rw [hopen]; exact hprop
  have hAC : Block.Preceq A C := hbelow hpropD hAG1
  have hrootC : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st.core).toFG) C := by
    have h1 := htarget.rootAtProposal
    have h2 := htarget.targetErase
    rw [h1, h2]
    exact preceq_trans_Preceq hJA hAC
  have hAfilteredSource : A ∈
      M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc q)))).toFG := by
    have h := hAfiltered
    rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h; rw [facts.hd.setClock_core_eq_store_with_t_s] at h
    exact h
  have hdata : Restated.FixedRootPreparedParentCandidateOn M
      S rho W Hs Xb H q w read A target C C vC
      (W (strictEventIndex rho read) w).st
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) :=
    { targetErase := htarget.targetErase
      targetRun := htarget.targetRun
      targetHeight := htarget.targetHeight
      targetHeightPositive := htarget.targetHeightPositive
      actionWitnessHonest := hvC
      actionCeilingEq := hCvC
      ceilingUpper := hupper
      ceilingCone := hcone
      ceilingRoot := hrootC
      ceilingChoice := Or.inr rfl
      anchorFiltered := hAfilteredSource
      rootAtProposal := htarget.rootAtProposal
      hMaxAtProposal := htarget.hMaxAtProposal }
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ ((q - 1) + 1) ≤
      rho.horizon := by
    rw [Nat.sub_add_cancel hq]
    refine (le_of_lt (Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc
      S.E.Δ_pos q)).trans ?_
    rw [Restated.Vocabulary.Protocol.Γ_0_eq_proposal_time facts]
    exact hproposalHor
  have hparent := Restated.fixedRoot_preparedParent_of_candidate_abstractOn facts
    S Hs Xb hf hHs hHsXb hcom hfb _ _ _ rfl rfl hq hpostCone hproposalHor
      hpostPreviousAction hprop hcut hdata hA
  exact
    { actionTargetParent := fun v hv n hn g hg B hB c' hc' I hI =>
        preceq_trans_Preceq (hupper v hv n hn g hg B hB) (hparent c' hc' I hI)
      liveG1Parent := fun x hx B hG1 c' hc' I hI =>
        preceq_trans_Preceq (hbelow hx hG1) (hparent c' hc' I hI) }

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Internal.PhaseGrades

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`, under the hypotheses of
    `fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relativeOn` and those of
    `openingFrozenVotes_of_fixedJustificationRootParentDataOn` other than the opening parent run,
    with the proposal `P` and the anchor `A` read at the proposer's prepared read `n` with the cache
    `c`: every committee member of round `q`'s opening slot in the set for its vote time has, at
    each of its vote-duty reads `m`, the frozen opening vote for `A` and `P` between `n` and `m`. -/
theorem openingFrozenVotes_of_fixedJustificationRootLock_relativeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} {A : Block V} {P : NamedBlock V}
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
    (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    (hdomainWindow : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core).toFG)
    (hactiveAtAction : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG)
    {wd : V → M.N}
    (hlock : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
      ((M.opening_slot S.hc q) - 1) wd
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))))
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hvoteDelay : read + S.E.Δ ≤
      M.vote_time S.E ((M.opening_slot S.hc q)))
    (hconfirmationDelay : read + S.E.Δ ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)))
    (hconfirmationHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hconfirmationCap : ((Hs (M.confirmation_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H)
    (hpostSource : lo ≤ M.proposal_time S.E
      ((M.opening_slot S.hc q) - 1))
    (hpostCone : lo ≤ M.vote_time S.E
      ((M.opening_slot S.hc q) - 1))
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hAanchor : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c) q ⇢ A)
    (hAG1 : ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
        (S.E.proposer (M.opening_slot S.hc q))).st q .g1 A ⇢ b → b = true)
    (hAfiltered : A ∈ M.get_filtered_block_tree
      (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c).st.core).toFG)
    (hJA : Block.Preceq (W (strictEventIndex rho read) w).st.J A)
    (_of_pivotTransfer : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
      Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho
        ((M.opening_slot S.hc q)) A v P
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c)
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv))
    (_of_frozenSuffix : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
      ∀ vv : Finset (GoldfishVote V),
        M.voter_view S.E
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
            (M.vote_time S.E (M.opening_slot S.hc q)))
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record
              cv).st.core).toFG.toSG.toGoldfishStore
          ((M.opening_slot S.hc q)) ⇢ vv →
      ∀ u, u ∈ vv →
      u ∉ P.erase.gf_votes.toFinset →
      M.equivocates P.erase.gf_votes.toFinset u.val_index = true)
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      v ∈ S.E.committee ((M.opening_slot S.hc q)) →
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
      Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt M S rho
        ((M.opening_slot S.hc q) - 1) A v P
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c)
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv) := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hΔ := S.E.Δ_pos
  have hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E
      ((M.opening_slot S.hc q))).trans hconfirmationHor
  have hloProposal : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    (hpostRead.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)).trans hproposalDelay
  have hproposalConf : M.proposal_time S.E ((M.opening_slot S.hc q)) + S.E.Δ <
      M.confirmation_time S.E ((M.opening_slot S.hc q)) := by
    have h0 := (facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc q)).1
    have h1 := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc q)
    have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc q)
    linarith
  have hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H :=
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloProposal hproposalConf
      hconfirmationHor ⟨_, hprop⟩).trans hconfirmationCap
  have hpropP : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q))) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop
  have hparents := fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relativeOn facts
    S Hs Xb hf hHs hHsXb hcom hfb hfix hqTwo hforms hwindow hdomainWindow hactiveAtAction hlock
    hpostRead hproposalDelay hproposalHor hproposalCap hpostCone
    hpostPreviousAction hpropP c hc hAanchor hAG1 hAfiltered hJA hloOpen hA
  have hopenD : M.domain S.E S.hc q .g1 =
      M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hpropD : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs (M.domain S.E S.hc q .g1) := by
    rw [hopenD]
    exact hpropP
  have hAparent : ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      Block.Preceq A I.parent :=
    fun I hI =>
      hparents.liveG1Parent (S.E.proposer ((M.opening_slot S.hc q))) hpropD A hAG1 c hc I hI
  exact openingFrozenVotes_of_fixedJustificationRootParentDataOn facts
    S Hs Xb hf hHs hHsXb hfb hfix c hc hP hq hpostRead hproposalDelay hvoteDelay
    hconfirmationDelay hconfirmationHor hconfirmationCap hpostSource
    hpostPreviousAction hprop hJA hAparent hparents
    _of_pivotTransfer _of_frozenSuffix hA

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rk3% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf`, if `t ≤ t'` then `v`'s finalized block in
    `W (strictEventIndex rho t)` is an ancestor of its finalized block in
    `W (strictEventIndex rho t')`. -/
theorem relativeSeed_F_monoOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V)
    {t t' : Time} (htt' : t ≤ t') :
    Block.Preceq (W (strictEventIndex rho t) v).st.core.F
      (W (strictEventIndex rho t') v).st.core.F :=
  F_mono_along₆₆ facts S hf.onePath v (Restated.strict_lengths_mono rho htt')

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rk3% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf` and the slashable bound `hsb`: if round
    `r > 0` is ready, the grade-1 store grade of `B` at the source's node state in
    `W (strictEventIndex rho (domain r .g1))` can return `true`, `B` is in the filtered tree of a
    node state `n` of the target's round-`r` action read (`hn`, `hactive`), and
    `lo ≤ opening (r − η_SG)`, then every outcome of the grade-0 store grade of `B` at the target's
    node state in `W (strictEventIndex rho (domain r .g0))` is `true`. -/
theorem storeGrade_g0_of_g1_and_targetActionActiveOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {source target : V} (hsource : source ∈ Hs (M.domain S.E S.hc r .g1))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g0)) {B : Block V}
    (hG1 : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) source).st r .g1 B ⇢ true)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) target) r)
    (hactive : B ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st r .g0 B ⇢ b → b = true := by
  have hactive' : B ∈ M.get_filtered_block_tree (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) target).st.core).toFG := by
    rw [← actionReadFrom_filtered₆₆ facts S _ r n hn]
    exact hactive
  have hFB : Block.Preceq
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) target).st.core.F B := by
    have h := facts.fc.q10_filtered_F hactive'
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  have hF0B : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) target).st.core.F B :=
    preceq_trans_Preceq
      (Restated.relativeSeed_F_monoOn facts S Hs Xb hf target
        (facts.gr.domain_le_a S r .g0))
      hFB
  have hgstG1 : lo ≤ M.early S.E S.hc r .g1 :=
    (facts.gr.lo_le_early_g2_of_window_start S hr hlo).trans
      (facts.gr.early_g2_le_early_g1 S.E S.hc r)
  have hbelow := Restated.g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hsb hgstG1 ready.2 hsource htarget (B := B) (by
      intro sender u root H I _ _ c hc hct hconf hfind
      rw [hconf] at hc
      exact preceq_trans_Preceq hF0B
        (facts.gr.preceq_of_localCovers_of_find c hc hct hfind))
  have hguard := Restated.g1G0CrossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hgstG1 ready.2 hsource htarget hbelow
  exact Restated.storeGrade_g0_of_storeGrade_g1_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb r hlo ready.2 source target hsource htarget B hG1 hguard

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rk3% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf` and the slashable bound `hsb`: if round
    `r > 0` is ready, the grade-2 store grade of `B` at the source's node state in
    `W (strictEventIndex rho (domain r .g2))` can return `true`, `B` is in the filtered tree of a
    node state `n` of the target's round-`r` action read (`hn`, `hactive`), and
    `lo ≤ opening (r − η_SG)`, then every outcome of the grade-1 store grade of `B` at the target's
    node state in `W (strictEventIndex rho (domain r .g1))` is `true`. -/
theorem storeGrade_g1_of_g2_and_targetActionActiveOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {source target : V} (hsource : source ∈ Hs (M.domain S.E S.hc r .g2))
    (htarget : target ∈ Hs (M.domain S.E S.hc r .g1)) {B : Block V}
    (hG2 : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) source).st r .g2 B ⇢ true)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) target) r)
    (hactive : B ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st r .g1 B ⇢ b → b = true := by
  have hactive' : B ∈ M.get_filtered_block_tree (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) target).st.core).toFG := by
    rw [← actionReadFrom_filtered₆₆ facts S _ r n hn]
    exact hactive
  have hFB : Block.Preceq
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) target).st.core.F B := by
    have h := facts.fc.q10_filtered_F hactive'
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  have hF1B : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) target).st.core.F B :=
    preceq_trans_Preceq
      (Restated.relativeSeed_F_monoOn facts S Hs Xb hf target
        (facts.gr.domain_le_a S r .g1))
      hFB
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hbelow := Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hsb hgst ready.2 hsource htarget (B := B) (by
      intro sender u root H I _ _ c hc hct hconf hfind
      rw [hconf] at hc
      exact preceq_trans_Preceq hF1B
        (facts.gr.preceq_of_localCovers_of_find c hc hct hfind))
  have hguard := Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hgst ready.2 hsource htarget hbelow
  exact Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb r hlo ready.2 source target hsource htarget B hG2 hguard

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rk3% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf`: if the grade-0 store grade of `Q` at `w`'s
    node state in `W (strictEventIndex rho (domain r .g0))` can return `true`, `Q` is in that node
    state's tree, `Q` is in the filtered tree of a node state `n` of `w`'s round-`r` action read,
    the clear test of `C` at `n` can return `true`, and `lo ≤ domain r .g0`, then `Q` and `C` are
    compatible. -/
theorem relativeG0_compatible_clearSourceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g0)) {Q C : Block V}
    (hQgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st r .g0 Q ⇢ true)
    (hQtree : Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.T)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hQaction : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hCclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n r C ⇢ true)
    (hgat : lo ≤ M.domain S.E S.hc r .g0) :
    Block.compatible Q C = true := by
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0)
  obtain ⟨raw, hraw, hQraw⟩ := facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F S.hc.η_SG r
    (e := M.early S.E S.hc r .g0) (l := M.late S.E S.hc r .g0)
    (facts.gr.early_le_late S.E S.hc r .g0)
    (by rw [facts.gr.Sts_gradeView_T]; exact hQtree) true hQgrade rfl fr hfr
  subst hraw
  have hactionFrame := Restated.actionFrame_g0On facts S Hs Xb hf hr hactionHor hw hgat
    n hn (some raw) hfr
  have hframe : (M.readFrame n.cache (M.toHealing n.st.core) r).g0 =
      some (some (M.clipGrade raw n.st.core.F)) := by
    simpa only [Option.map_some] using hactionFrame
  have hFQ : Block.Preceq n.st.core.F Q := by
    have h := facts.fc.q10_filtered_F hQaction
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  have hQclip : Block.Preceq Q (M.clipGrade raw n.st.core.F) := by
    apply (facts.gr.q10_retained_prefix raw n.st.core.F Q ?_).mpr hQraw
    exact compatible_of_cases (Or.inr hFQ)
  have hCclip : Block.compatible C (M.clipGrade raw n.st.core.F) = true := by
    obtain ⟨g, hg, hgc⟩ := returns_map_elim₆₆s
      (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.clear C)
      (Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r) true hCclear
    have hg' := (facts.nd.gradeContract_read n.cache S.E S.hc (M.toHealing n.st.core) r g).1 hg
    have hgc' : g.clear C = true := hgc
    rw [facts.gr.frameGradeRead_clear _ _ _ _ _ g hg', facts.gr.clear_of_g0 hframe] at hgc'
    exact hgc'
  rcases compatible_cases hCclip with hCclip | hclipC
  · exact compatible_of_cases (Proofs.ModelProperties.Preceq_linear hQclip hCclip)
  · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hQclip hclipC))

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rk3% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- For every node state `n` of `w`'s round-`r` grade-0 domain read, if the grade-0 store grades of
    `A` and of `Q` at `n` can each return `true`, then `A` and `Q` are compatible. -/
theorem relativeSeed_sameReaderG0_compatible_l66 (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (r : Round) (w : V) {A Q : Block V} :
    ∀ n ∈ Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc r .g0) w,
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st r .g0 A ⇢ true →
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st r .g0 Q ⇢ true →
    Block.compatible A Q = true := by
  intro n _ hA hQ
  have hA' : M.gradeBool S.E (M.gradeView (M.toHealing n.st.core)) n.st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0) A ⇢ true := hA
  have hQ' : M.gradeBool S.E (M.gradeView (M.toHealing n.st.core)) n.st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0) Q ⇢ true := hQ
  exact Restated.Vocabulary.Proofs.HealingSurface.graded_oneChain_at_reader facts S.E
    (M.gradeView (M.toHealing n.st.core)) n.st.core.F S.hc.η_SG r
    (facts.gr.early_le_late S.E S.hc r .g0) true hA' rfl true hQ' rfl

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rk3% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if every member
    of the set for each time from `S.a (c − 1)` to `S.a (c + 1)` has `h_j + 2 ≤ Mh` and `h_max = Mh`
    there (`hframe`), the grade-1 settlement `hsettled` and the selected grade-2 settlement
    `hselected` of round `c` hold, `w` is in the set for the vote time of a slot `d` of round `c`
    after its opening slot, `v` is in the set for `S.a c`, the bounds on `lo` and the awake
    hypothesis `hA` hold, and `cv` is an outcome of `w`'s cache update at `vote_time d`, then every
    anchor of the node state staged with `cv` is compatible with every block that `v`'s round-`c`
    action can select. -/
theorem preparedAnchor_compatible_carrier_of_relativeSettlementOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    (hsettled : ∀ u ∈ Hs (M.domain S.E S.hc c .g1), ∀ B : Block V,
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st c .g1 B ⇢ b → b = true) →
      ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho x
          (Restated.Vocabulary.Execution.Setup.a M S c)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))) B)
    (hselected : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)), ∀ Q : Block V,
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u) c,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n c ⇢ some Q →
      ∀ x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho x
          (Restated.Vocabulary.Execution.Setup.a M S c)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))) Q)
    {w v : V} {d : Slot}
    (hw : w ∈ Hs (M.vote_time S.E d)) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hd1 : (M.opening_slot S.hc c) + 1 ≤ d)
    (hd2 : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)
    (hround : (M.round_of S.hc d) = c)
    (hlo : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core)
      (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cv
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A0 →
    ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
        (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2 →
    ∀ B : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
        (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ B →
    Block.compatible A0 B = true := by
  intro n A0 hA0 na hna A2 hA2 B hB
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haPredC : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon := haCSucc.trans hhorNext
  have hlo' : (M.opening_slot S.hc c) ≤ d := (Nat.le_succ _).trans hd1
  have hopenPos : 0 < M.opening_slot S.hc (c + 1) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (Nat.succ_pos c)
  have hdSucc : d + 1 ≤ M.opening_slot S.hc (c + 1) := by
    have hd2' : d ≤ M.opening_slot S.hc (c + 1) - 1 := hd2
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hd2' (Nat.sub_lt hopenPos Nat.one_pos))
  have hnext : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    have h1 := facts.sch.vote_time_le_view_freeze S.E d
    have h2 := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E d
    have h3 := facts.sch.proposal_time_mono S.E hdSucc
    have hΔ := S.E.Δ_pos
    linarith
  have hvoteHor : M.vote_time S.E d ≤ rho.horizon := by
    have h1 := facts.sch.vote_time_mono_slots S.E (Nat.le_of_succ_le hdSucc)
    have h2 := facts.sch.Protocol_vote_time_le_confirmation_time S.E (M.opening_slot S.hc (c + 1))
    have h3 := facts.sch.a_eq_confirmation_time S.hc S.E (c + 1)
    have h4 : M.a S.hc S.E.Δ (c + 1) ≤ rho.horizon := hhorNext
    rw [h3] at h4
    exact (h1.trans h2).trans h4
  have hloOpenC : lo ≤ M.opening S.E S.hc c :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _))
  have hloG1 : lo ≤ M.domain S.E S.hc c .g1 := by
    rw [facts.gr.Sts_domain_g1_eq_opening]; exact hloOpenC
  have hloG0 : lo ≤ M.domain S.E S.hc c .g0 := by
    have h := facts.gr.domain_g1_add_delta_le_domain_g0 S c
    have hd := S.E.Δ_pos
    linarith
  have hG1le : M.domain S.E S.hc c .g1 ≤ M.vote_time S.E d := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E hlo').trans
      (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d))
  have hwG1 : w ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ hG1le hw
  have hvG2 : v ∈ Hs (M.domain S.E S.hc c .g2) := hHs _ _ (facts.gr.domain_le_a S c .g2) hv
  have hvG1 : v ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ (facts.gr.domain_le_a S c .g1) hv
  have hvG0 : v ∈ Hs (M.domain S.E S.hc c .g0) := hHs _ _ (facts.gr.domain_le_a S c .g0) hv
  rcases Restated.preparedAnchor_compatible_carrier_or_activePrefixOn facts S Hs Xb hf hHsXb hc hframe
      hhorNext hw hv hlo' hd2 hround cv hcv A0 hA0 na hna A2 hA2 B hB with
    hdone | ⟨root, A, hframeG1, hactive, hanchor⟩
  · exact hdone
  rw [hanchor]
  obtain ⟨-, hAG1⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
    S Hs Xb hf hcPos hlo' hround hnext hvoteHor hwG1 cv hcv hframeG1 hactive hloG1
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hprevDelta : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤
      M.domain S.E S.hc c .g2 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hcPos Nat.one_pos)).trans
      (facts.gr.early_le_domain S c)
  have hdomG2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g2 :=
    le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hprevDelta
  have hdomG2hi : M.domain S.E S.hc c .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    (facts.gr.domain_le_a S c .g2).trans haCSucc
  have hraw : Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S na c :=
    Restated.nodeRawG2_of_gateOffFrameOn facts S Hs Xb hf hHs hHsXb hfb hcPos hhorC hpost
      (fun u hu => (hframe _ le_rfl (haPredC.trans haCSucc) u hu).2)
      (fun x hx => (hframe _ hdomG2 hdomG2hi x hx).2)
      (fun x hx => (hframe _ hdomG2 hdomG2hi x hx).1) hA v hvG2 na hna
  have hmemA : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S c) :=
    mem_stateBeforeTime_along₆₆ hf.sorted hf.onePath _
  have hmemG0 : W (strictEventIndex rho (M.domain S.E S.hc c .g0)) v ∈
      Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc c .g0) v :=
    ⟨_, mem_stateBeforeTime_along₆₆ hf.sorted hf.onePath _, rfl⟩
  have hfilt := actionReadFrom_filtered₆₆ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c na hna
  have hrootEq : M.get_fg_root (M.toHealing na.st.core).toFG =
      M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG :=
    Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts S rho v c
      _ hmemA na hna
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract na.cache) S.E S.hc
    (M.toHealing na.st.core) c
  have hgRead : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S na c ⇢ g := hg
  have hAG1t := storeGrade_true_of_all₆₆ facts S.E S.hc _ c .g1 A hAG1
  have hset : Block.Preceq A (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG) ∨
      A ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG :=
    hsettled w hwG1 A hAG1 v hv
  -- an anchor active at `v`'s action read is graded 0 at `v`'s grade-0 domain read
  have hAG0_of : A ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG →
      A ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M na ∧
      Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g0)) v).st c .g0 A ⇢ true := by
    intro hAactive
    have hAaction : A ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M na := by
      show A ∈ M.get_filtered_block_tree (M.toHealing na.st.core).toFG
      rw [hfilt]
      exact hAactive
    exact ⟨hAaction, storeGrade_true_of_all₆₆ facts S.E S.hc _ c .g0 A
      (Restated.storeGrade_g0_of_g1_and_targetActionActiveOn facts
        S Hs Xb hf hHs hHsXb hsb hcPos ready hwG1 hvG0 hAG1t na hna hAaction hlo)⟩
  have hnaAt : na ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v c :=
    (show ∃ wd ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S c),
      na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wd v) c from
      ⟨_, hmemA, hna⟩)
  rcases Restated.Vocabulary.Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers facts S rho v c na hnaAt
      g hgRead A2 hA2 B hB with
    ⟨-, -, hCclear⟩ | ⟨Q, hQ2, hBQ⟩ | ⟨-, -, hBroot⟩ | ⟨-, hno, -⟩
  · -- Case: the carrier is clear at `v`'s action read.
    have hclearRet : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S na c B ⇢ true := by
      have h : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S na c B ⇢ g.clear B :=
        returns_map_intro₆₆ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.clear B) _ g
          hgRead
      rw [hCclear] at h
      exact h
    rcases hset with hAroot | hAactive
    · have hrootB : Block.Preceq (M.get_fg_root (M.toHealing na.st.core).toFG) B :=
        Restated.Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt facts S rho v c
          _ hmemA na hna A2 hA2 B hB
      rw [hrootEq] at hrootB
      exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAroot hrootB))
    · obtain ⟨hAaction, hAG0t⟩ := hAG0_of hAactive
      exact Restated.relativeG0_compatible_clearSourceOn facts S Hs Xb hf hcPos hhorC hvG0
        hAG0t
        (Restated.Vocabulary.Proofs.HealingSurface.storeGrade_g0_mem_domainTree facts S rho _ hmemG0
          hAG0t)
        na hna hAaction hclearRet hloG0
  · -- Case: the carrier is the selected grade-2 block of `v`'s action read.
    subst hBQ
    have hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S na c ⇢ some B := by
      have h := nodeQ2_of_read₆₆ S na c g hg
      rw [hQ2] at h
      exact h
    have hQG2t := storeGrade_true_of_all₆₆ facts S.E S.hc _ c .g2 B
      (Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf na hna hQ)
    have hsel : Block.Preceq B (M.get_fg_root (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG) ∨
        B ∈ M.get_filtered_block_tree (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG :=
      hselected v hv B na hna hQ v hv
    rcases hset with hAroot | hAactive
    · rcases hsel with hQroot | hQactive
      · exact compatible_of_preceq_common_Preceq hAroot hQroot
      · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAroot
          (preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hQactive))))
    · rcases hsel with hQroot | hQactive
      · exact compatible_of_cases (Or.inr (preceq_trans_Preceq hQroot
          (preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hAactive))))
      · obtain ⟨-, hAG0t⟩ := hAG0_of hAactive
        have hQaction : B ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M na := by
          show B ∈ M.get_filtered_block_tree (M.toHealing na.st.core).toFG
          rw [hfilt]
          exact hQactive
        have hQG1t := storeGrade_true_of_all₆₆ facts S.E S.hc _ c .g1 B
          (Restated.storeGrade_g1_of_g2_and_targetActionActiveOn facts
            S Hs Xb hf hHs hHsXb hsb hcPos ready hvG2 hvG1 hQG2t na hna hQaction hlo)
        have hQG0t := storeGrade_true_of_all₆₆ facts S.E S.hc _ c .g0 B
          (Restated.storeGrade_g0_of_g1_and_targetActionActiveOn facts
            S Hs Xb hf hHs hHsXb hsb hcPos ready hvG1 hvG0 hQG1t na hna hQaction hlo)
        exact Restated.relativeSeed_sameReaderG0_compatible_l66 facts S rho c v _ hmemG0 hAG0t hQG0t
  · -- Case: the carrier is the FG root of `v`'s action read.
    subst hBroot
    rw [hrootEq]
    rcases hset with hAroot | hAactive
    · exact compatible_of_cases (Or.inl hAroot)
    · exact compatible_of_cases (Or.inr
        (preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hAactive)))
  · exact absurd (hraw g hgRead) hno

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rk3% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if the frame
    `hframe` holds over rounds `c − 1` to `c + 1`, `lo ≤ S.a (c − 1)`, round `c ≥ 1` is ready,
    `lo ≤ opening (c − η_SG)`, every member of the set for `S.a (c − 1) + Δ` is awake at `c − 1`,
    `w` is in the set for the vote time of a slot `d` of round `c` after its opening slot, `v` is in
    the set for `S.a c`, and `cv` is an outcome of `w`'s cache update at `vote_time d`, then every
    anchor of the node state staged with `cv` is compatible with every block that `v`'s round-`c`
    action can select. -/
theorem preparedAnchor_compatible_carrier_of_gateOff_relativeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhorNext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {w v : V} {d : Slot}
    (hw : w ∈ Hs (M.vote_time S.E d)) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hd1 : (M.opening_slot S.hc c) + 1 ≤ d)
    (hd2 : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c)
    (hround : (M.round_of S.hc d) = c)
    (hlo : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core)
      (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cv) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cv
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A0 →
    ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
        (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2 →
    ∀ B : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
        (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ B →
    Block.compatible A0 B = true := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hpredAction : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hactionNext : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon := hactionNext.trans hhorNext
  have hprevDelta : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤ M.domain S.E S.hc c .g2 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hcPos Nat.one_pos)).trans
      (facts.gr.early_le_domain S c)
  have hdomG2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g2 :=
    le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hprevDelta
  have hdomG1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g1 :=
    hdomG2.trans (le_of_lt (facts.gr.q10_domain_g2_lt_domain_g1 S c))
  have hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = Mh :=
    fun u hu => (hframe _ le_rfl (hpredAction.trans hactionNext) u hu).2
  have hfrontier : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u).st.h_max = Mh :=
    fun u hu => (hframe _ hpredAction hactionNext u hu).2
  have hgate : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u).st.h_j + 2 ≤ Mh :=
    fun u hu => (hframe _ hpredAction hactionNext u hu).1
  have hfrontierG1 : ∀ u ∈ Hs (M.domain S.E S.hc c .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st.h_max = Mh :=
    fun u hu => (hframe _ hdomG1 ((facts.gr.domain_le_a S c .g1).trans hactionNext) u hu).2
  have hgateG1 : ∀ u ∈ Hs (M.domain S.E S.hc c .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st.h_j + 2 ≤ Mh :=
    fun u hu => (hframe _ hdomG1 ((facts.gr.domain_le_a S c .g1).trans hactionNext) u hu).1
  have hfrontierG2 : ∀ u ∈ Hs (M.domain S.E S.hc c .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) u).st.h_max = Mh :=
    fun u hu => (hframe _ hdomG2 ((facts.gr.domain_le_a S c .g2).trans hactionNext) u hu).2
  have hgateG2 : ∀ u ∈ Hs (M.domain S.E S.hc c .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) u).st.h_j + 2 ≤ Mh :=
    fun u hu => (hframe _ hdomG2 ((facts.gr.domain_le_a S c .g2).trans hactionNext) u hu).1
  have hsettled :=
    Restated.namedLiveG1SettledAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hfb hcPos hpost hprev
      hfrontier hgate hfrontierG1 hgateG1 hhorC hA
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1) .g2 :=
    Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hcPos hpost hprev
      hfrontierG2 hgateG2 ((facts.gr.domain_le_a S c .g2).trans hhorC) hA
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs (Hs (M.domain S.E S.hc c .g2)) c :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hcPos
      hprevDelta ((facts.gr.domain_le_a S c .g2).trans hhorC) hpost hA
  have hselected :=
    Restated.selectedG2SettledAt_of_gateOffOn facts S Hs Xb (Hs (M.domain S.E S.hc c .g2)) hf hHs
      hHsXb hcPos hwindow hmajority (Finset.Subset.refl _) hpost hprev hfrontier hgate hhorC
  exact Restated.preparedAnchor_compatible_carrier_of_relativeSettlementOn facts S Hs Xb hf hHs
    hHsXb hfb hc hframe hpost hhorNext ready hsettled hselected hw hv hd1 hd2 hround hlo hA cv hcv

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

end

end DecoupledConsensusModel.Sts.Restated
