import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_51b
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGRepresentation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGTargetCanonicality
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryCapturedActionCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Action SG blocks, the FG root and grade-2 settling along a path

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, under the bundle
`AdmissibleFieldsOn M S rho W Hs Xb lo`: every store is read in a world of the bundle's path `W`, a
store strictly before an instant `t` being the one in `W (strictEventIndex rho t)`. They cover the
blocks the SG selector can return at an action read, the FG root at the frontier, the settling of
selected grade-2 blocks, and the opening cone-root lock from a fixed-height justification root.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ### Helpers -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₀b (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₀b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₀b S rho hsorted]
  exact (hW _).1

/-- Every node state of the round-`r` action read computed from `before` has as core store an
    outcome of the confirmation update of `before`'s store staged at round `r`'s action instant. -/
private theorem actionReadFrom_core₆₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state of the round-`r` action read computed from `before` has the `h_max` of
    `before`'s core store. -/
private theorem actionReadFrom_h_max₆₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₀b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _
      hX₀,
    facts.hd.setClock_toHealing_h_max]

/-- Every node state of the round-`r` action read computed from `before` has the tree of `before`'s
    core store. -/
private theorem actionReadFrom_T₆₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₀b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

/-- Every node state of the round-`r` action read computed from `before` has the FG root of
    `before`'s core store. -/
private theorem actionReadFrom_fgRoot₆₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₀b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- Every node state of the round-`r` action read computed from `before` has the filtered tree of
    `before`'s core store. -/
private theorem actionReadFrom_filtered₆₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
        M.get_filtered_block_tree (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₀b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_filtered_block_tree,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- Every node state of the round-`r` action read computed from `before` holds the bodies `before`
    holds. -/
private theorem actionReadFrom_bodies₆₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- Every node state of the round-`r` action read computed from `before` has the chain-state map of
    `before`'s store. -/
private theorem actionReadFrom_σ₆₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- The round-`r` action read computed from any node state `before` has a node state. -/
private theorem actionReadFrom_nonempty₆₀b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- If every outcome of a store grade is `true`, the store grade can return `true`. -/
private theorem storeGrade_true_of_all₆₀b (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) (B : Block V)
    (h : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ b → b = true) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ true := by
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty E (M.gradeView (M.toHealing st.core)) st.core.F
    hc.η_SG r (M.early E hc r p) (M.late E hc r p) B
  have hbt : b = true := h b hb
  subst hbt
  exact hb

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₀b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- Setting the clock of `st` to `t` does not change the FG root of its core store. -/
private theorem setClock_fgRoot₆₀b (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    M.get_fg_root (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- The store the slot-`s` vote duty reads from `n`'s core store is the core store of `n`'s store
    with its clock set to the slot-`s` vote instant. -/
private theorem voteStore_eq₆₀b (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- If every member of the set for `domain r .g2` has `C` active with every grade-2 outcome `true`
    in `W (strictEventIndex rho (domain r .g2))`, `v` is in the set for `domain r .g0`, and `C` is
    active at a node state `n` of `v`'s round-`r` action read along `W`, then `C` is an ancestor of
    every SG vote `n` can select. -/
private theorem formsW_preceq_actionSGBlockAt₆₀b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
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
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ G : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G → Block.Preceq C G := by
  have hvG2 : v ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hv
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hd
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) C
  have hbtrue : b = true := (hformsW v hvG2).2 b hb
  subst hbtrue
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₆₀b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG
  obtain ⟨Q, hQ, hCQ⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
      (hformsW v hvG2).1 hb n hn hactive _ hGq
  rw [hQ] at hGq
  exact Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hhor
    (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv) hlo n hn hGq hCQ

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle with path `W`, for every node state `n` of `v`'s round-`r` action read along
    `W` and every block `B` the SG selector can return at `n`, `B` is in the filtered tree of `n`'s
    store. -/
theorem actionSGBlockAt_mem_filtered_actionStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
        B ∈ M.get_filtered_block_tree st.toFG := by
  intro n hn gc st k A2 hA2 B hB
  have hw := mem_stateBeforeTime_along₆₀b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hk : k = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n ⟨_, hw, hn⟩
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc st r
  have hA2' : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc st r ⇢ A2 := by
    rw [← hk]; exact hA2
  have hB' : M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc st r A2 ⇢ B := by
    rw [← hk]; exact hB
  have heq : B = M.currentSGVote st G :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc st r A2 hA2' G hG B hB'
  obtain ⟨st₁, hst₁, hcore⟩ := actionReadFrom_core₆₀b facts S _ r n hn
  have hroot : M.get_fg_root st.toFG ∈ M.get_filtered_block_tree st.toFG := by
    show M.get_fg_root (M.toHealing n.st.core).toFG ∈
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG
    rw [actionReadFrom_filtered₆₀b facts S _ r n hn, actionReadFrom_fgRoot₆₀b facts S _ r n hn]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts
      S rho _ v _ hw
  have hlive : st.toFG.toSG.toGoldfishStore.live_confirmed ∈ M.get_filtered_block_tree st.toFG := by
    show (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed ∈ _
    rw [facts.sto.toHealing_live_confirmed]
    exact Restated.liveConfirmed_mem_filtered_actionStoreOn facts S Hs Xb hf v r n hn
  have hanchor : G.anchor ∈ M.get_filtered_block_tree st.toFG ∧
      Block.Preceq (M.get_fg_root st.toFG) G.anchor := by
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc st r (M.readFrame n.cache st r).g1
    rw [facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc st r G hG a ha]
    rcases facts.gr.anchor_cases S.E S.hc st r _ a ha with h | ⟨root, A, -, hp, h⟩
    · rw [h]
      exact ⟨hroot, Proofs.ModelProperties.Preceq_self _⟩
    · rw [h]
      have hA := facts.gr.activePrefix_mem _ root A hp
      exact ⟨hA, Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
        (facts.fc.preceq_get_fg_root_of_mem_filtered hA)⟩
  rw [heq]
  cases hdc : M.deepest_clear (some G.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed
      G.clear with
  | some C =>
      rw [facts.gr.ModelProperties_currentSGVote_of_deepest_clear hdc]
      have hTst : st.toFG.toSG.toGoldfishStore.T =
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
        show (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T = _
        rw [facts.sto.toHealing_T, actionReadFrom_T₆₀b facts S _ r n hn]
      have hcl : ∀ B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T,
          B.parent? = none ∨
            B.parent ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
        have h := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
          (Restated.Vocabulary.Execution.Setup.a M S r) v _ hw
        unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at h
        rw [facts.sto.toHealing_T] at h
        exact h.2
      have hlc : st.toFG.toSG.toGoldfishStore.live_confirmed ∈
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
        rw [← hTst]
        exact facts.fc.get_filtered_block_tree_subset _ hlive
      have hCT : C ∈ st.toFG.toSG.toGoldfishStore.T := by
        rw [hTst]
        exact Proofs.Records.mem_of_preceq hcl C _ hlc (facts.gr.deepest_clear_preceq hdc)
      have hFJ : Block.preceq st.toFG.F st.toFG.J = true := by
        show Block.preceq (M.toHealing n.st.core).toFG.F (M.toHealing n.st.core).toFG.J = true
        rw [hst₁, facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J,
          facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J,
          ← facts.sto.ModelProperties_toHealing_J st₁.core,
          facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ _ hcore,
          facts.hd.setClock_toHealing_J, facts.dt.update_confirmation_with_F _ _ _ _ _ _ hcore,
          facts.hd.setClock_core_F]
        exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
          (Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
            S rho _ v _ hw)
      exact facts.fc.mem_filtered_of_preceq hFJ hlive hCT (facts.gr.deepest_clear_preceq hdc)
        (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
          (Proofs.ModelProperties.Preceq_trans hanchor.2 (facts.gr.deepest_clear_floor_Preceq hdc)))
  | none =>
      cases hQ : G.Q2 with
      | some Q =>
          rw [facts.gr.currentSGVote_of_Q2 hdc hQ]
          obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty st (M.readFrame n.cache st r)
          have hGx := facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc st r G hG x hx
          exact facts.gr.mem_filtered_of_grade2Block x hx (hGx.symm.trans hQ)
      | none =>
          by_cases hraw : G.rawG2
          · rw [facts.gr.currentSGVote_of_rawG2 hdc hQ hraw]
            exact hroot
          · rw [facts.gr.currentSGVote_of_not_rawG2 hdc hQ hraw]
            exact hanchor.1

/-- Under the bundle with path `W` and the slashable bound, if `w ∈ Xb`, `Xn` is a run block along
    `W` erasing to `X` with height at least `Mh − 1`, and `w`'s store in
    `W (strictEventIndex rho read)` has `h_max = Mh` and `h_j + 2 ≤ Mh`, then `w`'s FG root there is
    an ancestor of `X`. -/
theorem frontierRoot_preceq_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {w : V} (hw : w ∈ Xb) {read : Time}
    {X : Block V} {Xn : NamedBlock V} {Mh : Height}
    (hXerase : Xn.erase = X) (hXrun : Restated.RunBlockOn M S rho W Xb Xn)
    (hXh : Mh - 1 ≤ (M.derive_named S.E S.cfg Xn).h)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hgateOff : (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh) :
    Block.Preceq
      (M.get_fg_root (W (strictEventIndex rho read) w).st.toHealing.toFG) X := by
  have hmem := mem_stateBeforeTime_along₆₀b hf.sorted hf.onePath read
  have hnoHigh := Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime
    facts S rho read w _ hmem
  obtain ⟨C, hC, hF, -⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime facts S rho read w _ hmem
  have hCrun : Restated.RunBlockOn M S rho W Xb C :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hC
  have hhjlt : (W (strictEventIndex rho read) w).st.h_j < Mh - 1 := by
    rw [Nat.lt_sub_iff_add_lt]
    exact Nat.lt_of_succ_le (by
      simpa only [Nat.add_assoc] using hgateOff)
  have hcrossed : (M.derive_named S.E S.cfg C).h_F <
      (M.derive_named S.E S.cfg Xn).h := by
    calc
      (M.derive_named S.E S.cfg C).h_F ≤
          (M.derive_named S.E S.cfg C).h_j :=
        (facts.cs.chainOrder_derive_named S.E S.cfg C).heights_ordered
      _ ≤ (W (strictEventIndex rho read) w).st.h_j := hnoHigh C hC
      _ < Mh - 1 := hhjlt
      _ ≤ (M.derive_named S.E S.cfg Xn).h := hXh
  have hFX : Block.Preceq (W (strictEventIndex rho read) w).st.core.F X := by
    have hpre := Restated.finalized_preceq_of_height_ltOn facts
      S rho W Xb Xn C hsb hf.rootCollisionFree hXrun hCrun hcrossed
    rw [hXerase] at hpre
    simp only [hF] at hpre
    exact hpre
  have hgate : ¬ (W (strictEventIndex rho read) w).st.core.h_max =
      (W (strictEventIndex rho read) w).st.core.h_j + 1 := by
    apply Nat.ne_of_gt
    show (W (strictEventIndex rho read) w).st.h_j + 1 < (W (strictEventIndex rho read) w).st.h_max
    rw [hfrontier]
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
  have hroot : M.get_fg_root (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG =
      (W (strictEventIndex rho read) w).st.core.F :=
    facts.fc.get_fg_root_toHealing_of_ne _ hgate
  show Block.Preceq (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) X
  rw [hroot]
  exact hFX

/-- Under the bundle with path `W`, if `v`'s store in `W (strictEventIndex rho (S.a r))` has
    `h_max = Mh`, then for every node state `n` of `v`'s round-`r` action read along `W` and every
    block `B` the SG selector can return at `n`, some named body `Wn` of `n`'s store is a descendant
    of `B` with height at least `Mh − 1`. -/
theorem actionSGBlockAt_frontierWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {Mh : Height}
    (hfrontier : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.h_max = Mh) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      ∃ Wn : NamedBlock V,
        Wn ∈ n.st.bodies ∧ Block.Preceq B Wn.erase ∧
          Mh - 1 ≤ (M.derive_named S.E S.cfg Wn).h := by
  intro n hn gc st k A2 hA2 B hB
  have hw := mem_stateBeforeTime_along₆₀b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hfiltered := Restated.actionSGBlockAt_mem_filtered_actionStoreOn facts S Hs Xb hf v r n hn
    A2 hA2 B hB
  obtain ⟨Wb, hWT, hcarrierW, hheight⟩ := facts.fc.viable_witness_of_mem_get_filtered_block_tree hfiltered
  rw [facts.sto.toHealing_T, actionReadFrom_T₆₀b facts S _ r n hn] at hWT
  rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ,
    actionReadFrom_h_max₆₀b facts S _ r n hn, actionReadFrom_σ₆₀b facts S _ r n hn] at hheight
  obtain ⟨D, hDbody, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v _ hw hWT
  have hsig := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v _ hw D hDbody
  refine ⟨D, ?_, ?_, ?_⟩
  · rw [actionReadFrom_bodies₆₀b facts S _ r n hn]
    exact hDbody
  · simpa only [hDerase] using hcarrierW
  · rw [← hDerase, hsig] at hheight
    rw [← hfrontier]
    exact hheight

/-- Under the bundle with path `W` and the slashable bound, if `0 < r`, `lo ≤ S.a (r − 1)`, every
    member of the set for `S.a (r − 1)` has `h_max = Mh` there, every member of the set for `S.a r`
    has `h_max = Mh` and `h_j + 2 ≤ Mh` there, and `S.a r` is within the horizon, then no block the
    SG selector can return at a node state of a first-set member's round-`(r − 1)` action read
    interferes with the store of a second-set member in `W (strictEventIndex rho (S.a r))`. -/
theorem previousActionCarriersQuietAt_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} (hr : 0 < r) {Mh : Height}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.h_max = Mh)
    (hgateOff : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.h_j + 2 ≤ Mh)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u) (r - 1),
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let k := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
        ∀ A : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ A →
          Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
            (Restated.Vocabulary.Execution.Setup.a M S r)
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) A := by
  intro u hu w hw n hn gc st k A2 hA2 A hA
  have hM : 1 ≤ Mh :=
    le_trans (by decide : (1 : Nat) ≤ 2) ((Nat.le_add_left 2 _).trans (hgateOff w hw))
  obtain ⟨Wn, hWbody, hcarrierW, hWh⟩ :=
    Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf (hprev u hu) n hn A2 hA2 A hA
  have hWpre : Wn ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.bodies := by
    rw [← actionReadFrom_bodies₆₀b facts S _ (r - 1) n hn]
    exact hWbody
  have hWrun : Restated.RunBlockOn M S rho W Xb Wn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hu) hWpre
  have hrootW := Restated.frontierRoot_preceq_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw)
    (X := Wn.erase) (Xn := Wn) rfl hWrun hWh (hfrontier w hw) (hgateOff w hw)
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S r) :=
    Restated.Vocabulary.Protocol.previous_action_add_delta_le_action facts S hr
  have hwRelay : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ) :=
    hHs _ _ hdelay hw
  obtain ⟨hWtarget, -, -⟩ :=
    Restated.actionConeWitness_visibleAtReader_after_gstOn facts S Hs Xb hf hHs hHsXb (r := r - 1)
      hu hwRelay hn hWbody (Proofs.ModelProperties.Preceq_self Wn.erase) hWh hpost hdelay hhor
      hrootW
  have hwmem := mem_stateBeforeTime_along₆₀b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hWtargetCore : Wn.erase ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.core.T := by
    have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st :=
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        (Restated.Vocabulary.Execution.Setup.a M S r) w _ hwmem).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWtarget
  have hWfiltered :=
    Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) hhor
      hWtargetCore rfl hWrun hWh hM (hfrontier w hw) (hgateOff w hw)
  have hWquiet : Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
      (Restated.Vocabulary.Execution.Setup.a M S r)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) Wn.erase :=
    Or.inr hWfiltered
  exact Restated.ancestorOn facts S Hs Xb hf hcarrierW hWquiet

/-- Under the bundle with path `W`, if `0 < r`, the carrier window from round `r − 1` to the grade-2
    readers of round `r` holds, the weight outside `X` with the stale voters is less than the weight
    of the round-`(r − 1)` voters, `X` is inside the set for `domain r g2`, and no block the SG
    selector can return at a round-`(r − 1)` action read of a member of the set for `S.a (r − 1)`
    interferes with the store of a member of the set for `S.a r`, then no block a member of the set
    for `S.a r` selects at grade 2 in its round-`r` action read interferes with the store of any
    member of that set in `W (strictEventIndex rho (S.a r))`. -/
theorem selectedG2SettledAt_of_previousActionCarriersQuietOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {r : Round} (hr : 0 < r)
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (r - 1) .g2)
    (hmajority : Restated.GradeFormingMajorityOn M S rho W Hs X r)
    (hX : X ⊆ Hs (M.domain S.E S.hc r .g2))
    (hquiet : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u) (r - 1),
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let k := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
        ∀ A : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ A →
          Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
            (Restated.Vocabulary.Execution.Setup.a M S r)
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) A) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)), ∀ Q : Block V,
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
          (Restated.Vocabulary.Execution.Setup.a M S r)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) Q := by
  intro u hu Q n hn hQ w hw
  have hpred : r - 1 + 1 = r :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hQgrade := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
  have hQtrue := storeGrade_true_of_all₆₀b facts S.E S.hc _ r .g2 Q hQgrade
  have hgrade' : M.gradeBool S.E
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc ((r - 1) + 1) .g2)) u).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc ((r - 1) + 1) .g2)) u).st.core.F
      S.hc.η_SG ((r - 1) + 1) (M.early S.E S.hc ((r - 1) + 1) .g2)
      (M.late S.E S.hc ((r - 1) + 1) .g2) Q ⇢ true := by
    rw [hpred]
    exact hQtrue
  have hmajority' : Restated.GradeFormingMajorityOn M S rho W Hs X ((r - 1) + 1) := by
    rw [hpred]
    exact hmajority
  have hX' : X ⊆ Hs (M.domain S.E S.hc ((r - 1) + 1) .g2) := by
    rw [hpred]
    exact hX
  have huG2 : u ∈ Hs (M.domain S.E S.hc ((r - 1) + 1) .g2) := by
    rw [hpred]
    exact hHs _ _ (facts.gr.domain_le_a S r .g2) hu
  obtain ⟨v, hv, hQcarrier⟩ := Restated.relativeGrade_has_roundCarrierOn facts
    S Hs Xb X hf hHs hwindow hmajority' hX' huG2 hgrade'
  have hvHon : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) :=
    ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs v (r - 1)).mp hv).1
  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty₆₀b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) v) (r - 1)
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) (M.round_of S.hc (M.toHealing nr.st.core).s)
  obtain ⟨Bk, hBk⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) (M.round_of S.hc (M.toHealing nr.st.core).s) A2
  exact Restated.ancestorOn facts S Hs Xb hf (hQcarrier nr hnr A2 hA2 Bk hBk)
    (hquiet v hvHon w hw nr hnr A2 hA2 Bk hBk)

/-- Under the bundle with path `W`, the carrier window and the grade-forming majority over `X`
    inside the set for `domain r g2`, if `lo ≤ S.a (r − 1)`, every member of the set for
    `S.a (r − 1)` has `h_max = Mh` there, every member of the set for `S.a r` has `h_max = Mh` and
    `h_j + 2 ≤ Mh` there, and `S.a r` is within the horizon, then no block a member of the set for
    `S.a r` selects at grade 2 in its round-`r` action read interferes with the store of any member
    of that set in `W (strictEventIndex rho (S.a r))`. -/
theorem selectedG2SettledAt_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (r - 1) .g2)
    (hmajority : Restated.GradeFormingMajorityOn M S rho W Hs X r)
    (hX : X ⊆ Hs (M.domain S.E S.hc r .g2))
    {Mh : Height} (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.h_max = Mh)
    (hgateOff : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.h_j + 2 ≤ Mh)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)), ∀ Q : Block V,
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
          (Restated.Vocabulary.Execution.Setup.a M S r)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) Q := by
  have hquiet := Restated.previousActionCarriersQuietAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb
    hf.slashableBound hr hpost hprev hfrontier hgateOff hhor
  exact Restated.selectedG2SettledAt_of_previousActionCarriersQuietOn facts
    S Hs Xb X hf hHs hr hwindow hmajority hX hquiet

/-- If more than half of every slot's committee is in the set for its confirmation instant, then the
    set for the confirmation instant of any slot `s` is nonempty. -/
theorem honest_nonempty_of_committeesOn (facts : Record.Facts M)
    (S : Setup V) (Hs : Int → Finset V)
    (hcom : Restated.HonestCommitteesOn M S Hs) (s : Slot) :
    (Hs (M.confirmation_time S.E s)).Nonempty := by
  have hpositive : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    have hc := hcom s
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpositive
  exact ⟨v, (Finset.mem_inter.mp hv).2⟩

/-- Under the bundle with path `W`, if `v ∈ Xb` and `v`'s store in
    `W (strictEventIndex rho (S.a r))` has `h_max = Mh`, then for every node state `n` of `v`'s
    round-`r` action read along `W` and every block `B` the SG selector can return at `n`, some run
    block `Wn` along `W` whose erasure is in `n`'s tree is a descendant of `B` with height at least
    `Mh − 1`. -/
theorem actionCarrierFrontierWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {Mh : Height}
    (hfrontier : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.h_max = Mh) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      ∃ Wn : NamedBlock V,
        Wn.erase ∈ n.st.core.T ∧
          Block.Preceq B Wn.erase ∧
          Restated.RunBlockOn M S rho W Xb Wn ∧
            Mh - 1 ≤ (M.derive_named S.E S.cfg Wn).h := by
  intro n hn gc st k A2 hA2 B hB
  obtain ⟨Wn, hWbody, hBW, hWh⟩ :=
    Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf hfrontier n hn A2 hA2 B hB
  have hWpre : Wn ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.bodies := by
    rw [← actionReadFrom_bodies₆₀b facts S _ r n hn]
    exact hWbody
  have hwmem := mem_stateBeforeTime_along₆₀b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hWT : Wn.erase ∈ n.st.core.T := by
    rw [actionReadFrom_T₆₀b facts S _ r n hn]
    have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st :=
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        (Restated.Vocabulary.Execution.Setup.a M S r) v _ hwmem).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWpre
  exact ⟨Wn, hWT, hBW, Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hWpre, hWh⟩

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

/-- If `w`'s read in the world `wd` holds a fixed-height justification root at `H` along `W`, then
    some run block `J` along `W` erases to the justified block of `w`'s store in `wd` and has height
    `H − 1`. -/
theorem claimOne_fixedHeightJustificationRoot_target_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {W : Nat → V → M.N}
    {H : Height} {w : V} {read : Time} {wd : V → M.N}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read wd) :
    ∃ J : NamedBlock V,
      J.erase = (wd w).st.J ∧
        Restated.RunBlockOn M S rho W Xb J ∧
          (M.derive_named S.E S.cfg J).h = H - 1 :=
  Restated.fixedRoot_namedTarget_of_fixedRootOn facts S Hs Xb h

/-- Under the bundle with path `W`, two run blocks along `W` with the same erasure are equal. -/
theorem claimOne_named_run_eq_of_eraseOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hB : Restated.RunBlockOn M S rho W Xb B)
    (herase : A.erase = B.erase) : A = B :=
  Restated.fixedRoot_runBlock_unique_of_erase_eqOn facts hf hA hB herase

/-- Under the bundle with path `W`, if every member of the set for `domain r g2` has `C` active with
    every outcome of its grade-2 store grade `true` in `W (strictEventIndex rho (domain r g2))`, and
    `v` is in that set, then `C` is in the tree of `v`'s core store in
    `W (strictEventIndex rho (S.a r))`. -/
theorem claimOne_namedGradeProcessedAtActionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {C : Block V}
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 C ⇢ b → b = true)
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc r .g2)) :
    C ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
  Restated.fixedRoot_namedGrade_processedAtActionOn facts S Hs Xb hf hforms hv

/-- Under the bundle with path `W`, the committee majority and the weight bound `hfb`, if `w`'s
    store in `W (strictEventIndex rho read)` holds a fixed-height justification root at `H`, the
    proposer recurrence holds from `t₀` with gap `gap`, and the timing hypotheses on `read`, `lo`
    and `t₀` hold, then either `H` is less than the largest `h_max` over the set for
    `S.a (r + 4 + gap)`, or some round `q` with `r + 3 ≤ q ≤ r + 3 + gap` has the justified block
    formed at grade 2 in round `q − 1` and the opening cone-root lock at `H` holding for round
    `q − 1` at slot `opening_slot q − 1`. -/
theorem fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBoundOn
    (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {r gap : Round} {t₀ : Int}
    (hpost : S.E.t_GST ≤ read) (hreadAction : read ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hrecurrence : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) ≤ rho.horizon)
    (hlo : lo ≤ read) (ht₀ : t₀ ≤ read)
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hloOpen : lo ≤ M.opening S.E S.hc (r + 2 - S.hc.η_SG)) :
    H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max) ∨
      ∃ q : Round,
        r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
          Restated.ProposerCarrierAtOn M S Hs q ∧
            (∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
              (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
                  (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
                ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
                  (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
                    (W (strictEventIndex rho read) w).st.J ⇢ b →
                  b = true) ∧
              Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
                ((M.opening_slot S.hc q) - 1)
                (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))))
                (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) := by
  by_cases hrise : H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max)
  · exact Or.inl hrise
  have hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max)
        ≤ H := Nat.le_of_not_gt hrise
  have hmono := (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
  have hcapAt : ∀ t : Time, (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ t →
      t + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) →
      ((Hs t).sup fun v => (W (inclusiveEventIndex rho t) v).st.core.h_max) ≤ H := by
    intro t h1 h2
    have hloT : lo ≤ t := hlo.trans (hreadAction.trans ((hmono (Nat.le_succ r)).trans h1))
    exact (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloT h2 hendHor
      (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)).trans hcapEnd
  rcases Restated.fixedHeightJustificationRoot_boundedGradeFormsAt_of_proposerRecurrence_of_faultBoundOn
      facts S Hs Xb hf hHs hHsXb hfb h hpost hreadAction hrecurrence hendHor hlo ht₀ hA with
    hcontrary | ⟨q, hqlo, hqhi, hcarrier, hforms⟩
  · exact False.elim (hrise hcontrary)
  right
  refine ⟨q, hqlo, hqhi, hcarrier, hforms, ?_⟩
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.claimOne_fixedHeightJustificationRoot_target_namedOn facts S Hs Xb h
  have hformsNamed : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      Jn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
            Jn.erase ⇢ b → b = true := by
    rw [hJnErase]
    exact hforms
  have hqlo' : r + 1 + 2 ≤ q := by
    simpa only [Nat.add_assoc] using hqlo
  have hqTwo : 2 ≤ q := (Nat.le_add_left 2 (r + 1)).trans hqlo'
  have hqOne : 1 ≤ q := (by decide : 1 ≤ 2).trans hqTwo
  have hqPos : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hqPredPos : 0 < q - 1 := Nat.sub_pos_of_lt (show 1 < q from hqTwo)
  have hqActionLower : r + 1 ≤ q - 2 := Nat.le_sub_of_add_le hqlo'
  have hqActionSucc : q - 2 ≤ q - 1 := Nat.sub_le_sub_left (by decide : 1 ≤ 2) q
  have hqReadyLower : r + 1 ≤ q - 1 := hqActionLower.trans hqActionSucc
  have hqPred : q - 2 + 1 = q - 1 := by
    have hqEq : q - 2 + 2 = q := Nat.sub_add_cancel hqTwo
    rw [← hqEq]
    simp
  have hqPredAdd : q - 1 + 1 = q := Nat.sub_add_cancel hqOne
  have hr2q : r + 2 ≤ q - 1 := by
    simpa only [hqPred] using Nat.add_le_add_right hqActionLower 1
  have hloOpenQ : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hr2q _))
  have hbaseEnd : r + 3 ≤ r + 4 := Nat.add_le_add_left (Nat.le_succ 3) r
  have hqEnd : q ≤ r + 4 + gap := hqhi.trans (Nat.add_le_add_right hbaseEnd gap)
  have hnextAtEnd : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) :=
    hmono ((Nat.sub_le q 1).trans hqEnd)
  have hqAtEnd : (Restated.Vocabulary.Execution.Setup.a M S q) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) := hmono hqEnd
  have hr1Action : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := hmono hqActionLower
  have hr1Next : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) := hmono hqReadyLower
  have hdelayAction : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := by
    calc
      read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ :=
        Int.add_le_add_right hreadAction S.E.Δ
      _ ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) :=
        facts.gr.action_add_delta_le_next_Γ_neg1 S r
      _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r)
      _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := hr1Action
  have hdelayNext : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hdelayAction.trans (hmono hqActionSucc)
  have hnextHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
    hnextAtEnd.trans hendHor
  have hnextCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1))).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core.h_max) ≤ H :=
    hcapAt _ hr1Next (Restated.action_add_delta_lt_action_of_lt_l67 facts S
      (lt_of_lt_of_le (Nat.sub_lt hqPos (by decide : 0 < 1)) hqEnd))
  have hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho (q - 1) := by
    have hrPrev : r ≤ q - 1 - 1 :=
      (Nat.le_succ r).trans (hqActionLower.trans (le_of_eq (Nat.sub_sub q 1 1).symm))
    constructor
    · exact (hpost.trans (hreadAction.trans (hmono hrPrev))).trans
        ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hqPredPos Nat.one_pos)))
    · exact (facts.gr.domain_le_a S (q - 1) .g0).trans hnextHor
  obtain ⟨hslo, hshi, hsucc⟩ := facts.gr.lastInteriorSlot_before_opening S.hc hqPos
  have hslotPrev : (M.opening_slot S.hc (q - 2)) + 2 ≤ (M.opening_slot S.hc (q - 1)) := by
    calc
      (M.opening_slot S.hc (q - 2)) + 2 ≤ (M.opening_slot S.hc (q - 2)) + S.hc.R :=
        Nat.add_le_add_left S.hc.R_ge_two _
      _ = (M.opening_slot S.hc ((q - 2) + 1)) := (facts.gr.opening_slot_succ_eq S.hc (q - 2)).symm
      _ = (M.opening_slot S.hc (q - 1)) := congrArg (M.opening_slot S.hc) hqPred
  have hHone : 1 ≤ H := Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
  have htargetHeightSucc : (M.derive_named S.E S.cfg Jn).h + 1 = H := by
    rw [hJnHeight]
    exact Nat.sub_add_cancel hHone
  have htargetHeightLt : (M.derive_named S.E S.cfg Jn).h < H := by
    rw [hJnHeight]
    exact Nat.sub_lt (Nat.zero_lt_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive))
      (by decide : 0 < 1)
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hactionExact := fun (v : V) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb h hv hlo hdelayNext hnextHor hnextCap
  have hactionRoot : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      M.get_fg_root (M.toHealing n.st.core).toFG = Jn.erase := by
    intro v hv n hn
    rw [actionReadFrom_fgRoot₆₀b facts S _ (q - 1) n hn, hJnErase]
    exact (hactionExact v hv).1
  have hactionCap : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      n.st.core.h_max ≤ (M.derive_named S.E S.cfg Jn).h + 1 := by
    intro v hv n hn
    rw [actionReadFrom_h_max₆₀b facts S _ (q - 1) n hn]
    exact le_of_eq ((hactionExact v hv).2.trans htargetHeightSucc.symm)
  have hvoteAfter : ∀ d : Slot, (M.opening_slot S.hc (q - 1)) + 1 ≤ d →
      (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) ≤ M.vote_time S.E d := by
    intro d hdlo
    have hslot : (M.opening_slot S.hc (q - 2)) + 2 ≤ d :=
      hslotPrev.trans ((Nat.le_succ _).trans hdlo)
    exact (le_of_lt (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S (q - 2))).trans
      (facts.sch.vote_time_mono_slots S.E hslot)
  have hvoteLeActionQ : ∀ d : Slot, d < (M.opening_slot S.hc ((q - 1) + 1)) →
      M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
    intro d hdhi
    have hdhiQ : d < (M.opening_slot S.hc q) := by
      simpa only [hqPredAdd] using hdhi
    exact (facts.sch.vote_time_mono_slots S.E (Nat.le_of_lt hdhiQ)).trans
      (le_of_lt (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S q))
  have hvoteExact := fun (d : Slot) (hdlo : (M.opening_slot S.hc (q - 1)) + 1 ≤ d)
      (hdhi : d < (M.opening_slot S.hc ((q - 1) + 1))) (v : V) (hv : v ∈ Hs (M.vote_time S.E d)) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb h hv hlo (hdelayAction.trans (hvoteAfter d hdlo))
      (((hvoteLeActionQ d hdhi).trans hqAtEnd).trans hendHor)
      (hcapAt _ (hr1Action.trans (hvoteAfter d hdlo))
        (lt_of_lt_of_le
          (Restated.vote_add_delta_lt_action_l53 facts S
            (Nat.le_of_lt (by simpa only [hqPredAdd] using hdhi))) hqAtEnd))
  have hslotHor : M.vote_time S.E ((M.opening_slot S.hc q) - 1) ≤ rho.horizon :=
    ((hvoteLeActionQ _ hshi).trans hqAtEnd).trans hendHor
  have hcanonical : Restated.SGTargetConeCanonicalityOn M S rho W Hs Xb (q - 1)
      ((M.opening_slot S.hc q) - 1)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) :=
    Restated.sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCapOn facts
      S Hs Xb hf hHs hHsXb hcom hqPredPos hready hJnRun hformsNamed hslo hshi hnextHor
        hslotHor hactionRoot hactionCap
        (fun d hdlo hdhi v hv => by
          rw [setClock_fgRoot₆₀b facts S, hJnErase]
          exact (hvoteExact d hdlo hdhi v hv).1)
        (fun d hdlo hdhi v hv => by
          rw [facts.hd.setClock_core_h_max]
          exact le_of_eq ((hvoteExact d hdlo hdhi v hv).2.trans htargetHeightSucc.symm))
        hloOpenQ
  have hwmemQ1 := mem_stateBeforeTime_along₆₀b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (q - 1))
  have hJtarget : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1),
        let gc := M.gradeContract n.cache
        let st := M.toHealing n.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ G → Block.Preceq Jn.erase G := by
    intro u hu n hn gc st kk A2 hA2 G hG
    have huG2 : u ∈ Hs (M.domain S.E S.hc (q - 1) .g2) :=
      hHs _ _ (facts.gr.domain_le_a S (q - 1) .g2) hu
    have huG0 : u ∈ Hs (M.domain S.E S.hc (q - 1) .g0) :=
      hHs _ _ (facts.gr.domain_le_a S (q - 1) .g0) hu
    have hJraw := Restated.claimOne_namedGradeProcessedAtActionOn facts S Hs Xb hf hformsNamed huG2
    have hJB : Block.Preceq (W (strictEventIndex rho read) w).st.J Jn.erase := by
      rw [hJnErase]
      exact Proofs.ModelProperties.Preceq_self _
    have hfilt := Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts
      S Hs Xb hf (hHsXb _ hu) hJnRun hJraw hJB (le_of_eq hJnHeight.symm)
      (hactionExact u hu).1 (hactionExact u hu).2
    have hactive : Jn.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
      Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := u)
        _ hwmemQ1 hfilt n hn
    exact formsW_preceq_actionSGBlockAt₆₀b facts S Hs Xb hf hHs hHsXb hqPredPos hnextHor
      hformsNamed huG0 n hn hactive hloOpenQ A2 hA2 G hG
  have hrq : r < q :=
    (Nat.lt_succ_self r).trans_le (hqActionLower.trans (Nat.sub_le q 2))
  have hopenDelay : read + S.E.Δ ≤ M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) := by
    rw [hsucc]
    exact ((Int.add_le_add_right hreadAction S.E.Δ).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        hrq)).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E ((M.opening_slot S.hc q))))
  have hopenEnd : M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) := by
    rw [hsucc]
    exact (le_of_lt (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S q)).trans hqAtEnd
  have hopenHor : M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) ≤ rho.horizon :=
    hopenEnd.trans hendHor
  have hopenAfter : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
      M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1) := by
    have hqPredLt : q - 1 < q := Nat.sub_lt hqPos (by decide : 0 < 1)
    rw [hsucc]
    exact hr1Next.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      ((Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        hqPredLt).trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E
          ((M.opening_slot S.hc q))))))
  have hopenCap := hcapAt _ hopenAfter
    (lt_of_lt_of_le (Restated.vote_add_delta_lt_action_l53 facts S (le_of_eq hsucc)) hqAtEnd)
  have hfrontier : ∀ v ∈ Hs (M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (((M.opening_slot S.hc q) - 1) + 1))) v).st.core
          (((M.opening_slot S.hc q) - 1) + 1)).h_max = H := by
    intro v hv
    rw [voteStore_eq₆₀b facts, facts.hd.setClock_core_h_max]
    exact (Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
      facts S Hs Xb hf hHs hHsXb hsb h hv hlo hopenDelay hopenHor hopenCap).2
  have hpostSlot : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) :=
    hlo.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelayAction.trans (hvoteAfter _ hslo)))
  have hcertNamed : Restated.CertificateOn M S rho W Xb (H - 1) Jn.root := by
    have hroot : Jn.root = (W (strictEventIndex rho read) w).st.J.root := by
      rw [← Proofs.NamedWire.erase_root Jn, hJnErase]
    rw [hroot]
    exact h.fixedTarget.certificate
  have hrs : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q) - 1) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S (q - 1)]
    apply Restated.confirmationTime_mono_l58 facts S.E
    have hsuccq : M.opening_slot S.hc q = M.opening_slot S.hc (q - 1) + S.hc.R := by
      rw [← facts.gr.opening_slot_succ_eq S.hc (q - 1), hqPredAdd]
    have h1 : M.opening_slot S.hc (q - 1) + 2 ≤ M.opening_slot S.hc q := by
      rw [hsuccq]
      exact Nat.add_le_add_left S.hc.R_ge_two _
    exact Nat.le_sub_of_add_le (le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) h1)
  exact Restated.sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefixOn facts
    S Hs Xb hf hHs hHsXb hcom (hfb _ le_rfl) hrs hcanonical hJnRun hcertNamed htargetHeightLt
      hJtarget hpostSlot hopenHor hfrontier

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

/-! ## Two theorems on the selector cone along the path `W` -/

open scoped DC in
/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₀bp {S : Setup V} {rho : Record.Run V}
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

open scoped DC in
/-- Along a path `W` of a run, for `i ≤ j`, the bodies `v` holds in `W i` it holds in `W j`. -/
private theorem bodies_mono_along₆₀bp (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {i j : Nat} (hij : i ≤ j) : (W i v).st.bodies ⊆ (W j v).st.bodies := by
  have hslice : W j ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) (W i) := by
    have h := onePath_reach₆₀bp W hW i (j - i)
    rwa [Nat.add_sub_of_le hij] at h
  exact Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hij (W i)
    (hW i).1 (W j) hslice

open scoped DC in
/-- If `m` can return `a` and `k a` can return `b`, then `m >>= k` can return `b`. -/
private theorem returns_bind_intro₆₀bp {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (a : α)
    (b : β) (ha : m ⇢ a) (hb : k a ⇢ b) : (m >>= k) ⇢ b := by
  unfold Record.Returns at ha hb ⊢
  simp only [ExceptT.run_bind, Set.bind_def]
  exact Set.mem_iUnion₂.mpr ⟨.ok a, ha, hb⟩

open scoped DC in
/-- If `m >>= k` can return `b`, then `m` can return some `a` for which `k a` can return `b`. -/
private theorem returns_bind_elim₆₀bp {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β)
    (h : (m >>= k) ⇢ b) : ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_bind, Set.bind_def, Set.mem_iUnion] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, hb⟩
  | error err => simp at hb

open scoped DC in
private theorem actionFGSource_cases₆₀bp (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B) :
    ∃ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q ∧
      ((∃ (cv : M.Cache) (Cc : Block V),
          M.onPhaseTick S.E S.hc
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st.core.toHealing
            (M.confirmation_time S.E (M.opening_slot S.hc r))
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).cache ⇢ cv ∧
          Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv) S.E S.hc
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st.core
              (M.confirmation_time S.E (M.opening_slot S.hc r))) (M.opening_slot S.hc r) Cc ∧
          Block.Preceq B Cc) ∨ B = Q) := by
  have hmem := mem_stateBeforeTime_along₆₀b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r := ⟨_, hmem, hn⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hnAt
  have hsrc0 : (do
      let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s)
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some B := hsource
  rw [hround] at hsrc0
  obtain ⟨A2, hA2, hsrc⟩ := returns_bind_elim₆₀bp _ _ _ hsrc0
  obtain ⟨Q2, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGQ : G.Q2 = some Q2 :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q2 := by
    have h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
      returns_map_intro₆₀b (fun g : GradeRead V => g.Q2) _ G hG
    rwa [hGQ] at h
  refine ⟨Q2, hq, ?_⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
      facts S rho v r _ hmem n hn hq hsource with ⟨Cc, hgen, -, -, -, hBC⟩ | hBQ
  · left
    obtain ⟨c, hc, st, hst, rfl⟩ := hn
    rw [facts.nd.mkNode_cache] at hgen
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
      at hgen
    exact ⟨c, Cc, hc, hgen, hBC⟩
  · exact Or.inr hBQ

/-- Under the bundle with path `W`, if the selector cone holds along `W` for `a` with source `Cfg`,
    the named frame over `X` holds along `W` at `blocked` up to `first − 1`, the source round is
    ready, `w` is in the set for the view freeze of the source round's opening slot and
    `lo ≤ early a.round g2`, then every node state of `w`'s round-`a.round` action read along `W`
    holds `Cfg`. -/
theorem PrefixFGSelectorConeAtOn.sourceMem_at_action_of_frame_named (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {w : V} (hw : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc a.round)))
    (hlo : lo ≤ M.early S.E S.hc a.round .g2) :
    ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) w) a.round,
      Cfg ∈ nw.st.bodies := by
  have hlopos : 0 < lo := hf.lo_pos
  have hd := S.E.Δ_pos
  have hactionLt : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < first := by
    have hle : strictEventIndex rho ta ≤ i := by
      by_contra hnot
      have hlt : i < strictEventIndex rho ta := Nat.lt_of_not_ge hnot
      unfold strictEventIndex at hlt
      have hmem : Record.Event.tick a.val_index ta ∈
          rho.events.filter (fun e => decide (e.time < ta)) := by
        rw [Restated.filter_eq_takeOn facts S Hs Xb hf _ (Restated.downward_lt ta)]
        exact List.mem_of_getElem? (by
          rw [List.getElem?_take_of_lt hlt]
          exact hseed.exactTick)
      have himpossible := (List.mem_filter.mp hmem).2
      simp only [decide_eq_true_eq, Record.Event.time] at himpossible
      exact lt_irrefl ta himpossible
    rw [hseed.actionTime_eq] at hle
    exact hle.trans_lt hseed.indexLtStop
  have hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤
      first - 1 := Nat.le_sub_one_of_lt hactionLt
  have hactionHor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon := by
    have h := (hf.in_horizon (Record.Event.tick a.val_index ta)
      (List.mem_of_getElem? hseed.exactTick)).2
    simpa only [Record.Event.time, hseed.actionTime_eq, Record.Event.time] using h
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hsignerG2 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g2) :=
    hHs _ _ (facts.gr.domain_le_a S a.round .g2) hsigner
  have haConf : Restated.Vocabulary.Execution.Setup.a M S a.round =
      M.confirmation_time S.E (M.opening_slot S.hc a.round) :=
    (Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S a.round).symm
  have hsignerSC : a.val_index ∈
      Hs (M.support_cutoff S.E (M.opening_slot S.hc a.round)) := by
    refine hHs _ _ ?_ hsigner
    rw [haConf, facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_mono S.E (Nat.le_succ _)
  have hstartVF : slotStart S.E.Δ (M.opening_slot S.hc a.round) ≤
      M.view_freeze S.E (M.opening_slot S.hc a.round) := by
    have h1 := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc a.round)
    have h2 := Restated.vote_time_lt_support_cutoff_l49 facts S (M.opening_slot S.hc a.round)
    have h3 := facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E (M.opening_slot S.hc a.round)
    linarith
  have hopen : M.opening S.E S.hc a.round = slotStart S.E.Δ (M.opening_slot S.hc a.round) := by
    rw [facts.gr.opening_eq_proposal_time, ← facts.sch.Γ_0_eq_proposal_time]
  have hwG1 : w ∈ Hs (M.domain S.E S.hc a.round .g1) := by
    refine hHs _ _ ?_ hw
    have h1 := facts.gr.domain_g1_add_delta_le_domain_g0 S a.round
    have h0 := facts.gr.domain_g0_eq_opening S a.round
    linarith
  have hwX : w ∈ X := by
    refine hX _ ?_ hw
    have h0 := facts.gr.early_g2_le_opening S a.round
    linarith
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₀b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  have hmemCfg : Cfg ∈ n.st.bodies := hseed.sourceMem n hn
  have hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Cfg.erase := by
    obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
    obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g
    have hso : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o :=
      returns_bind_intro₆₀bp _ _ g o hg ho
    have ho' := hseed.exactFGSource n hn o hso
    rw [ho'] at hso
    exact hso
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index a.round hsigner hactionPrefix hactionHor n hn Cfg hmemCfg
      hsource hseed.sourceDerivedHeight
  have hfloor : Restated.FinalityFloorAtOn M S rho W X Xb blocked (first - 1) Tprev.erase := by
    intro v hv k hk Y hYrun hYheight hTY
    exact hframe.floor v hv k hk Y hYrun hYheight
      (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hframe.prevRun hYrun hTY)
  obtain ⟨Q, hQ, hcases⟩ := actionFGSource_cases₆₀bp facts S hf n hn hsource
  rcases hcases with ⟨cv, B, -, hgenuine, hCfgB⟩ | hselected
  · have hvoteBody := Restated.ancestorGenuineConfirmation_body_at_nextVote_of_floorOn facts
      S Hs Xb X hf hHs hHsXb ready hsignerSC hgenuine hCfgB hn hmemCfg
        hfloor hseed.sourceDerivedHeight (Proofs.NamedWire.erase_preceq hTprevCfg)
        hactionPrefix hactionHor hw hwX hlo
    rw [facts.hd.ModelProperties_setClock_bodies] at hvoteBody
    have hactionPre := bodies_mono_along₆₀bp facts S hf.onePath w
      (strictEventIndex_mono rho
        (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S a.round).le) hvoteBody
    intro nw hnw
    rw [actionReadFrom_bodies₆₀b facts S _ a.round nw hnw]
    exact hactionPre
  · rw [← hselected] at hQ
    exact (Restated.selectedQ2_body_at_action_and_openingVote_of_floorOn facts
      S Hs Xb X hf hHs hHsXb ready hsignerG2 hn hQ hmemCfg
        hfloor hseed.sourceDerivedHeight (Proofs.NamedWire.erase_preceq hTprevCfg)
        hactionPrefix hwG1 hwX hlo).1

/-- Under the hypotheses of `PrefixFGSelectorConeAtOn.sourceMem_at_action_of_frame_named`, for every
    instant `read` from `S.a a.round` on, `w`'s store in `W (strictEventIndex rho read)` has `h_max`
    at least `blocked + 1`. -/
theorem PrefixFGSelectorConeAtOn.localFrontier_ge_from_source_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ read)
    {w : V} (hw : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc a.round)))
    (hlo : lo ≤ M.early S.E S.hc a.round .g2) :
    blocked + 1 ≤ (W (strictEventIndex rho read) w).st.core.h_max := by
  obtain ⟨nw, hnw⟩ := actionReadFrom_nonempty₆₀b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) w) a.round
  have hsource := hseed.sourceMem_at_action_of_frame_named facts hf hHs hHsXb hX hframe
    ready hw hlo nw hnw
  rw [actionReadFrom_bodies₆₀b facts S _ a.round nw hnw] at hsource
  have hCfgRead := bodies_mono_along₆₀bp facts S hf.onePath w
    (strictEventIndex_mono rho hread) hsource
  have hheight := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts
    S rho (strictEventIndex rho read) w _ (hf.onePath _).1 Cfg hCfgRead
  rw [hseed.sourceDerivedHeight] at hheight
  exact hheight

end

end DecoupledConsensusModel.Sts.Restated
