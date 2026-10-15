import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_66
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_SeedCommonRootComplement
import Proofs.Claims.Restated.Vocabulary_Execution_StoreFinalityCore
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeSeedK3
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ConfirmationScore
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedConfirmationWalk
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Carrier windows, FG sources and the lifecycle packet

Theorems over a model `M : Record.Model V` and its facts, read along a path `W` of a run with the
admissible fields `hf`; `W (strictEventIndex rho t)` is the world strictly before `t` and
`W (inclusiveEventIndex rho t)` the world at `t`. They give the relative carrier window under a
fixed-height justification root, the confirmation recorded at its event, the place of a member's FG
source in its action store and its compatibility with prepared anchors, the opening proposal of a
round as an ancestor of a later opening's parent, and the lifecycle packet of a round at a round
ceiling.
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
private theorem stateBeforeTime_eq_strict₆₆b (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₆b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₆b S rho hsorted]
  exact (hW _).1

/-- On a path `W` of a run sorted by key, the finalized block of `v`'s core store in
    `W (strictEventIndex rho t)` is an ancestor of that store's FG root. -/
private theorem F_preceq_fgRoot_along₆₆b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
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
          S rho t v _ (mem_stateBeforeTime_along₆₆b hsorted hW t)))
  rw [facts.sto.Sts_toHealing_F] at hFroot
  exact preceq_eq_true_iff_Preceq.mp hFroot

/-- On a path `W` of a run sorted by key, a node state of the round-`r` action read from `v`'s node
    state in `W (strictEventIndex rho (S.a r))` is one of `v`'s round-`r` action reads. -/
private theorem mem_actionReadAt_along₆₆b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (r : Round) {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r) :
    n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
  ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)),
    mem_stateBeforeTime_along₆₆b hsorted hW _, hn⟩

/-- Every node state `n` of the round-`r` action read from `before` has a store `st` such that
    `n.st` is `st` with `n`'s cache written in, and `st`'s core store is an outcome of the
    confirmation update of `before`'s store staged at `S.a r`. -/
private theorem actionReadFrom_core₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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
private theorem actionReadFrom_h_max₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₆b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _
      hX₀,
    facts.hd.setClock_toHealing_h_max]

/-- Every node state of the round-`r` action read from `before` has the tree of `before`'s core
    store. -/
private theorem actionReadFrom_T₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₆b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

/-- Every node state of the round-`r` action read from `before` has the FG root of `before`'s core
    store. -/
private theorem actionReadFrom_fgRoot₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₆b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- Every node state of the round-`r` action read from `before` has the filtered tree of `before`'s
    core store. -/
private theorem actionReadFrom_filtered₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
        M.get_filtered_block_tree (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₆b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_filtered_block_tree,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- Every node state of the round-`r` action read from `before` holds the bodies `before` holds. -/
private theorem actionReadFrom_bodies₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The round-`r` action read from `M.wake n` gives exactly the node states it gives from `n`. -/
private theorem actionReadFrom_wake₆₆b (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

/-- Every node state of the round-`r` action read from `before` has the chain-state map of
    `before`'s store. -/
private theorem actionReadFrom_σ₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- The round-`r` action read from any node state `before` has a node state. -/
private theorem actionReadFrom_nonempty₆₆b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₆b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₆₆b {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- If the contract's grade read at `n` can return `G`, `n`'s candidate read can return `G`'s
    candidate. -/
private theorem nodeQ2_of_read₆₆b (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₆b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

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
open DecoupledConsensusModel.Internal.NamedOutageEntry

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if `w`'s store in
    `W (strictEventIndex rho read)` has a fixed-height justification root at height `H` (`hfix`),
    `lo ≤ read`, `lo ≤ S.a (r − 1)`, `read + Δ ≤ S.a (r − 1)`, `S.a (r − 1)` and `S.a r` are in the
    horizon with the largest `h_max` over their sets at those times at most `H` (`hprevCap`,
    `hactionCap`), round `r`'s phase-`p` domain time is in the horizon, and every member of the set
    for `S.a (r − 1) + Δ` is awake at `r − 1`, then the relative carrier window holds along `W` at
    round `r − 1` and phase `p`. -/
theorem relativeCarrierWindowAt_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs) {r : Round} (hr : 0 < r) {p : Phase}
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    (hpostRead : lo ≤ read)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hprevDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hprevHor : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ rho.horizon)
    (hprevCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r - 1))).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) x).st.core.h_max)
        ≤ H)
    (_hactionDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hactionCap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S r)).sup fun x =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) x).st.core.h_max) ≤ H)
    (hhor : M.domain S.E S.hc r p ≤ rho.horizon)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) → M.awake_for_grade2 S u (W j u) (r - 1)) :
    Restated.RelativeCarrierWindowAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs
      (r - 1) p := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hqr : r - 1 < r := Nat.sub_lt hr (by decide)
  have hk : r - 1 ∈ M.latest_window S.hc.η_SG r := by
    apply facts.fc.mem_latest_window
    · exact Nat.sub_le_sub_left S.hc.η_SG_ge_one r
    · exact hqr
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hactionDelta : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ ≤
      M.early S.E S.hc r p := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hqr
    have h2 := facts.gr.early_g2_add_delta_le_early_g1 S r
    have h3 := facts.gr.early_g1_add_delta_le_early_g0 S r
    have hΔ := S.E.Δ_pos
    show M.a S.hc S.E.Δ (r - 1) + S.E.Δ ≤ M.early S.E S.hc r p
    cases p <;> linarith
  have hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) lo + S.E.Δ ≤
      M.early S.E S.hc r p := by
    rw [max_eq_left hpost]
    exact hactionDelta
  have horder : M.early S.E S.hc r p ≤ M.domain S.E S.hc r p := by
    have h := facts.gr.early_add_two_delta_le_domain S r p
    linarith [S.E.Δ_pos]
  have hcut : M.early S.E S.hc r p ≤ rho.horizon := horder.trans hhor
  have hprevDomain : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ M.domain S.E S.hc r p :=
    (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hactionDelta).trans horder
  have hsourceHor : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ rho.horizon := hprevHor
  have hprevPkg := fun x (hx : x ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hx hpostRead hprevDelay hprevHor hprevCap
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S r))).Nonempty :=
    nonempty_of_honestWeightMajority_l54
      (honestWeightMajorityOn_of_belowOneThirdOn hfb _ hactionHor)
  have hdomainCap : ((Hs (M.domain S.E S.hc r p)).sup fun x =>
      (W (inclusiveEventIndex rho (M.domain S.E S.hc r p)) x).st.core.h_max) ≤ H :=
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb (hpost.trans hprevDomain)
      (Restated.domain_add_delta_lt_action_l56 facts S r p) hactionHor hne).trans hactionCap
  have hdomainPkg := fun x (hx : x ∈ Hs (M.domain S.E S.hc r p)) =>
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hx hpostRead (hprevDelay.trans hprevDomain) hhor hdomainCap
  rw [Restated.RelativeCarrierWindowAtOn, hpred]
  intro v hv u hu huEarly na hna g2 hg2 A hAsel I hI
  have huDelta : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ) :=
    hHs _ _ hactionDelta huEarly
  have huHon : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) :=
    ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u (r - 1)).mp hu).1
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hvEarly : v ∈ Hs (M.early S.E S.hc r p) := hHs _ _ horder hv
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache) S.E S.hc (S.node u)
    na.st na.record
  set a := D.2.2 with ha
  have hshape : a.val_index = u ∧ a.round = r - 1 ∧ a.confirmed = some A.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u (r - 1) na
      (mem_actionReadAt_along₆₆b hf.sorted hf.onePath u (r - 1) hna) D hD g2 hg2 A hAsel
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest a)
      ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf (r - 1) huHon hsourceHor hpost
      (hA u huDelta) (fun j hj => hf.tick_outcome j _ _ hj) na hna D hD
  obtain ⟨i, hi, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath hemit
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W i u) a.round := by
    rw [hshape.2.1]
    rcases Restated.action_read_indexOn facts S rho Hs Xb hf i u (r - 1) hi with hstate | hstate
    · rw [hstate]
      exact hna
    · rw [hstate, actionReadFrom_wake₆₆b facts]
      exact hna
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hna'
  obtain ⟨Wn, hWnBody, hcarrierW, -⟩ :=
    Restated.actionSGBlockAt_frontierWitnessOn facts S Hs Xb hf (hprevPkg u huHon).2 na hna g2 hg2
      A hAsel
  have hbodies := actionReadFrom_bodies₆₆b facts S _ (r - 1) na hna
  have hWsource : Wn ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.bodies := by
    rw [← hbodies]
    exact hWnBody
  have hWnRun : Restated.RunBlockOn M S rho W Xb Wn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb hWsource
  have hHrun : Restated.RunBlockOn M S rho W Xb Hb :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hHb)
  -- The fixed target is an ancestor of the carrier, hence of the frontier witness.
  have hcarrierFiltered : A ∈ M.get_filtered_block_tree (M.toHealing na.st.core).toFG :=
    Restated.actionSGBlockAt_mem_filtered_actionStoreOn facts S Hs Xb hf u (r - 1) na hna g2 hg2
      A hAsel
  have hrootCarrier : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.core).toFG) A := by
    have hmem := preceq_eq_true_iff_Preceq.mp
      (facts.fc.preceq_get_fg_root_of_mem_filtered hcarrierFiltered)
    rwa [actionReadFrom_fgRoot₆₆b facts S _ (r - 1) na hna] at hmem
  have hprevRoot : M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.core).toFG =
        (W (strictEventIndex rho read) w).st.J := (hprevPkg u huHon).1
  have hJcarrier : Block.Preceq (W (strictEventIndex rho read) w).st.J A := by
    rw [← hprevRoot]
    exact hrootCarrier
  have hJW : Block.Preceq (W (strictEventIndex rho read) w).st.J Wn.erase :=
    preceq_trans_Preceq hJcarrier hcarrierW
  have hdomainRoot : M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core).toFG =
        (W (strictEventIndex rho read) w).st.J := (hdomainPkg v hv).1
  have hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.F Wn.erase := by
    have h := F_preceq_fgRoot_along₆₆b facts S hf.sorted hf.onePath v (M.domain S.E S.hc r p)
    rw [hdomainRoot] at h
    exact preceq_trans_Preceq h hJW
  -- the head `Hb` erases to the SG block `A`
  obtain ⟨Gp, hGpW, hGpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Wn hcarrierW
  have hGpRun : Restated.RunBlockOn M S rho W Xb Gp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hWnRun hGpW
  have hroot : Gp.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root Gp, hGpErase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hGpH : Gp = Hb :=
    hf.rootCollisionFree.root_injective Gp Hb
      hGpRun hHrun Gp Hb (Or.inl (Proofs.NamedAncestry.named_self Gp))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHErase : Hb.erase = A := by
    rw [← hGpH, hGpErase]
  have hHC : Block.Preceq Hb.erase Wn.erase := by
    rw [hHErase]
    exact hcarrierW
  have hpostA : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [hshape.2.1]
    exact hpost
  have hdeadlineA : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.early S.E S.hc r p := by
    rw [hshape.2.1]
    exact hdeadline
  have hinput :=
    Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb (t := M.domain S.E S.hc r p) p hk huEarly hvEarly
      ⟨hshape.1, hshape.2.1, hemit⟩
      ⟨i, hi, ⟨na, hna', hHb⟩, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  have huSource : u ∈ Hs (max ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) lo) := by
    rw [max_eq_left hpost]
    exact huHon
  have hWtarget := Restated.healthy_head_body_at_read_after_gst_admitOn facts
    S rho Hs Xb hf hHs hHsXb u v Wn ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (M.early S.E S.hc r p) (M.domain S.E S.hc r p) huSource hvEarly hWsource hdeadline horder hcut
    hFC
  have hwmem := mem_stateBeforeTime_along₆₆b hf.sorted hf.onePath (M.domain S.E S.hc r p)
  have htargetCore : Wn.erase ∈ (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.T := by
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.domain S.E S.hc r p) v _ hwmem).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWtarget.1
  have hcarrierTarget : A ∈ (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.T := by
    have hclosed := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.domain S.E S.hc r p) v _ hwmem
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hclosed
    rw [facts.sto.toHealing_gs_T] at hclosed
    exact Proofs.Records.mem_of_preceq hclosed.2 _ _
      htargetCore (preceq_eq_true_iff_Preceq.2 hcarrierW)
  have hfind : Block.find? (W (strictEventIndex rho (M.domain S.E S.hc r p)) v).st.core.T A.root =
      some A := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hcarrierTarget
    intro Y hY hYroot
    obtain ⟨Yn, hYerase, hYrun⟩ :=
      Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hv)
        (M.domain S.E S.hc r p) hY
    have hYHroot : Yn.root = Hb.root := by
      rw [← Proofs.NamedWire.erase_root Yn, hYerase, hYroot, ← hHErase,
        Proofs.NamedWire.erase_root Hb]
    have hYH := hf.rootCollisionFree.root_injective
      Yn Hb hYrun hHrun Yn Hb (Or.inl (Proofs.NamedAncestry.named_self Yn))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hYHroot
    rw [← hYerase, hYH, hHErase]
  refine ⟨M.sgVote a.erase, hinput I hI, ?_, ?_, hfind⟩
  · rw [facts.sto.sgVote_round]
    exact hshape.2.1
  · rw [facts.sto.sgVote_confirmed, hshape.2.2]

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₆₆b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- Read aloud: the late confirmation vote set of the core store of a store with a cache written in
    is the store's own. -/
private theorem confirmationLate_swc₆₆b (facts : Record.Facts M) (st : M.NS) (c : M.Cache)
    (E : Env V) (s : Slot) :
    Restated.Vocabulary.Internal.confirmationLate M E (M.store_with_cache st c).core s =
      Restated.Vocabulary.Internal.confirmationLate M E st.core s := by
  unfold Restated.Vocabulary.Internal.confirmationLate
  rw [facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_store_pool]

/-- Read aloud: the confirmation vote set of the core store of a store with a cache written in is
    the store's own. -/
private theorem confirmationVotes_swc₆₆b (facts : Record.Facts M) (st : M.NS) (c : M.Cache)
    (E : Env V) (s : Slot) :
    Restated.Vocabulary.Internal.confirmationVotes M E (M.store_with_cache st c).core s =
      Restated.Vocabulary.Internal.confirmationVotes M E st.core s := by
  unfold Restated.Vocabulary.Internal.confirmationVotes Restated.Vocabulary.Internal.confirmationEarly
  simp only [confirmationLate_swc₆₆b facts, facts.nd.store_with_cache_core_tau,
    facts.nd.store_with_cache_store_pool]

/-- The SG root read under the grade contract of any cache `c'` from the healing view of a store
    with a cache `c` written in is the one read from the store's own healing view. -/
private theorem sgRoot_store_with_cache₆₆b (facts : Record.Facts M) {E : Env V}
    {hc : Protocol.HealConfig} {st : M.NS} {c c' : M.Cache} {r : Round} {x : Block V} :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

/-- Read aloud: every outcome `X` of the named confirmation votes of `st` at slot `s` is the set
    of the votes of `st`'s slot-`s` pool stamped under an outcome `τ` of `st`'s resolution times
    before the support cutoff, with no second vote among the late votes; and that set is an
    outcome of the confirmation votes `confVotes`. -/
private theorem confirmationVotes_shape₆₆b (E : Env V) (st : M.S) (s : Slot)
    (X : Finset (GoldfishVote V))
    (hX : Restated.Vocabulary.Internal.confirmationVotes M E st s ⇢ X) :
    ∃ τ, st.tau ⇢ τ ∧
      X = (beforeCutoff τ (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true) ∧
      Restated.Vocabulary.Protocol.confVotes M E st s ⇢ X := by
  unfold Restated.Vocabulary.Internal.confirmationVotes at hX
  obtain ⟨early, hearly, hpure⟩ := (returns_bind_iff₆₆b _ _ _).1 hX
  unfold Restated.Vocabulary.Internal.confirmationEarly at hearly
  obtain ⟨τ, hτ, hpure'⟩ := (returns_bind_iff₆₆b _ _ _).1 hearly
  have hearlyEq := (Record.returns_pure _ _).1 hpure'
  have hXEq := (Record.returns_pure _ _).1 hpure
  subst hearlyEq
  subst hXEq
  refine ⟨τ, hτ, rfl, ?_⟩
  unfold Restated.Vocabulary.Protocol.confVotes Restated.Vocabulary.Protocol.confEarly
  exact returns_map_intro₆₆b _ _ _ (returns_map_intro₆₆b _ _ _ hτ)

/-- Along the path `W` with the admissible fields `hf`: if `v` is in the set for slot `s`'s
    confirmation time `tc`, `lo ≤ tc ≤ horizon`, for every outcome of the cache update at `tc` on
    `v`'s node state in `W` before `tc` the prepared confirmation of `s` confirms `P` (`h`), and `v`
    passes the grade-2 awake test at its ticks at `tc` (`hrun`), then `v`'s confirmation of `s` at
    the event confirms `P`, and `v`'s store in `W` at `tc` has `live_confirmed = P`. -/
theorem genuineConfirmationAt_of_withOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {P : Block V}
    (h : ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
        (M.confirmation_time S.E s)
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ c →
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M
        (M.gradeContract
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st
              (M.confirmation_time S.E s))
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c).cache)
        S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)) s P)
    (hgat : lo ≤ M.confirmation_time S.E s)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E s)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) v (W j v) (M.round_of S.hc (s + 1))) :
    Restated.Vocabulary.Internal.GenuineConfirmationAt M S rho v s
        (W (strictEventIndex rho (M.confirmation_time S.E s)))
        (W (inclusiveEventIndex rho (M.confirmation_time S.E s))) ∧
      (W (inclusiveEventIndex rho (M.confirmation_time S.E s)) v).st.live_confirmed = P := by
  -- the recorded confirmation is `P`, for every outcome of the cache update
  have hrecord : ∀ c : M.Cache, M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s)
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ c →
      (W (inclusiveEventIndex rho (M.confirmation_time S.E s)) v).st.live_confirmed = P := by
    intro c hc
    obtain ⟨D, hD⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
      S.hc (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st
        (M.confirmation_time S.E s)) s
    obtain ⟨X0, hX0⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st
        (M.confirmation_time S.E s)).core s
    have hDX : D.core = X0 := facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X0 hX0
    have hlive := Restated.live_confirmed_eq_updateOn facts S Hs Xb hf s hv hhor hgat
      (fun j hj => hf.tick_outcome j _ _ hj) hrun c hc D hD
    have hsel := (h c hc).selected X0 (by
      rewrite [facts.nd.mkNode_cache, ← setClock_core_tickStore₆₆b facts S]
      exact hX0)
    rw [hlive]
    show D.core.live_confirmed = P
    rw [hDX]
    exact hsel
  obtain ⟨c0, hc0⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
    (M.confirmation_time S.E s)
    (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache
  refine ⟨?_, hrecord c0 hc0⟩
  unfold Restated.Vocabulary.Internal.GenuineConfirmationAt
  dsimp only
  rintro n ⟨c, hc, rfl⟩ A hA X hX sc hsc W' hW'
  have hG := h c hc
  rw [facts.nd.mkNode_cache] at hG
  simp only [facts.nd.mkNode_st, facts.nd.mkNode_cache, sgRoot_store_with_cache₆₆b facts,
    confirmationVotes_swc₆₆b facts, confirmationLate_swc₆₆b facts, facts.nd.store_with_cache_core_T,
    facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_get_filtered_block_tree,
    setClock_core_tickStore₆₆b facts S] at hA hX hsc hW' ⊢
  obtain ⟨τ, hτ, hXeq, hXconf⟩ := confirmationVotes_shape₆₆b S.E _ s X hX
  have helig := hG.genuine A hA X hXconf sc hsc W' hW'
  refine ⟨?_, helig⟩
  subst hXeq
  obtain ⟨st', hst'⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s
  have hW := facts.hd.update_confirmation_with_live_confirmed_of_eligible _ S.E S.hc _ s τ hτ
    A hA sc hsc W' hW' helig st' hst'
  rw [hrecord c hc, ← hG.selected st' hst']
  exact hW

end

/-! ## FG sources, prepared anchors and the opening proposal -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

/-- Along the path `W` with the admissible fields `hf`, for every node state `n` of `v`'s round-`r`
    action read, if `n`'s FG source read can return `some C`, then `C` is in the filtered tree of
    `n`'s store. -/
theorem freshFGSource_mem_filtered_actionStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) {C : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some C) :
    C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
  have hw := mem_stateBeforeTime_along₆₆b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsource
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₆b _ _ _).1 hsource
  obtain ⟨Q, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGQ : G.Q2 = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q := by
    have h := nodeQ2_of_read₆₆b S n r G hG
    rwa [hGQ] at h
  have hQmem : Q ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
    Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho v r _ hw n hn hq
  have hrootQ : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) Q :=
    preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hQmem)
  cases hwalk : M.deepest_clear (some Q)
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | none =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hwalk _ hsrc
      rw [Option.some_inj.mp h]
      exact hQmem
  | some B =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hwalk _ hsrc
      have hCB : C = B := Option.some_inj.mp h
      subst hCB
      obtain ⟨st₁, hst₁, hcore⟩ := actionReadFrom_core₆₆b facts S _ r n hn
      have hlive : (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed ∈
          M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
        rw [facts.sto.toHealing_live_confirmed]
        exact Restated.liveConfirmed_mem_filtered_actionStoreOn facts S Hs Xb hf v r n hn
      have hTst : (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T =
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
        rw [facts.sto.toHealing_T, actionReadFrom_T₆₆b facts S _ r n hn]
      have hcl : ∀ B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T,
          B.parent? = none ∨
            B.parent ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
        have h := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
          (Restated.Vocabulary.Execution.Setup.a M S r) v _ hw
        unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at h
        rw [facts.sto.toHealing_T] at h
        exact h.2
      have hlc : (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed ∈
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
        rw [← hTst]
        exact facts.fc.get_filtered_block_tree_subset _ hlive
      have hCT : C ∈ (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T := by
        rw [hTst]
        exact Proofs.Records.mem_of_preceq hcl C _ hlc (facts.gr.deepest_clear_preceq hwalk)
      have hFJ : Block.preceq (M.toHealing n.st.core).toFG.F (M.toHealing n.st.core).toFG.J = true := by
        rw [hst₁, facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J,
          facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J,
          ← facts.sto.ModelProperties_toHealing_J st₁.core,
          facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ _ hcore,
          facts.hd.setClock_toHealing_J, facts.dt.update_confirmation_with_F _ _ _ _ _ _ hcore,
          facts.hd.setClock_core_F]
        exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
          (Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
            S rho _ v _ hw)
      exact facts.fc.mem_filtered_of_preceq hFJ hlive hCT (facts.gr.deepest_clear_preceq hwalk)
        (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
          (Proofs.ModelProperties.Preceq_trans hrootQ (facts.gr.deepest_clear_floor_Preceq hwalk)))

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

/-- Along the path `W` with the admissible fields `hf`, for every node state `n` of `v`'s round-`r`
    action read, if `n`'s FG source read can return `some C` and `v`'s store in
    `W (strictEventIndex rho (S.a r))` has `h_max = Mh`, then some named body `Wn` of `n`'s store is
    a descendant of `C` of height at least `Mh − 1`. -/
theorem freshFGSource_frontierWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {Mh : Height} {C : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some C)
    (hfrontier : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.h_max = Mh) :
    ∃ Wn : NamedBlock V,
      Wn ∈ n.st.bodies ∧ Block.Preceq C Wn.erase ∧
        Mh - 1 ≤ (M.derive_named S.E S.cfg Wn).h := by
  have hw := mem_stateBeforeTime_along₆₆b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hfiltered := Restated.freshFGSource_mem_filtered_actionStoreOn facts S Hs Xb hf v r n hn
    hsource
  obtain ⟨Wb, hWT, hCW, hheight⟩ := facts.fc.viable_witness_of_mem_get_filtered_block_tree hfiltered
  rw [facts.sto.toHealing_T, actionReadFrom_T₆₆b facts S _ r n hn] at hWT
  rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ,
    actionReadFrom_h_max₆₆b facts S _ r n hn, actionReadFrom_σ₆₆b facts S _ r n hn] at hheight
  obtain ⟨D, hDbody, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v _ hw hWT
  have hsig := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S r) v _ hw D hDbody
  refine ⟨D, ?_, ?_, ?_⟩
  · rw [actionReadFrom_bodies₆₆b facts S _ r n hn]
    exact hDbody
  · simpa only [hDerase] using hCW
  · rw [← hDerase, hsig] at hheight
    rw [← hfrontier]
    exact hheight

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every outcome of a store grade is `true`, the store grade can return `true`. -/
private theorem storeGrade_true_of_all₆₆b (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) (B : Block V)
    (h : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ b → b = true) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ true := by
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty E (M.gradeView (M.toHealing st.core)) st.core.F
    hc.η_SG r (M.early E hc r p) (M.late E hc r p) B
  have hbt : b = true := h b hb
  subst hbt
  exact hb

/-- The node state staged at slot `d`'s vote time from `b` with the cache `cv` has slot `d` and the
    FG root of `b`'s core store. -/
private theorem dutyNode_parts₆₆b (facts : Record.Facts M) (S : Setup V) (b : M.N) (d : Slot)
    (cv : M.Cache) :
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core.s = d ∧
    M.get_fg_root (M.toHealing
        (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cv).st.core).toFG =
      M.get_fg_root (M.toHealing b.st.core).toFG := by
  refine ⟨?_, ?_⟩
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  · rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s]
    exact facts.fc.get_fg_root_toHealing_clock _ _ _

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if the frame
    `hframe` holds over rounds `c − 1` to `c + 1`, `lo ≤ S.a (c − 1)`, round `c ≥ 1` is ready, `w`
    is in the set for the vote time of a slot `d` of round `c` after its opening slot, `v` is in the
    set for `S.a c`, the FG source read of a node state `nv` of `v`'s round-`c` action read can
    return `some C`, `lo ≤ opening (c − η_SG)`, every member of the set for `S.a (c − 1) + Δ` is
    awake at `c − 1`, and `cv` is an outcome of `w`'s cache update at `vote_time d`, then every
    anchor of the node state staged with `cv` is compatible with `C`. -/
theorem preparedAnchor_compatible_freshFGSource_of_gateOff_relativeOn (facts : Record.Facts M)
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
    (hround : (M.round_of S.hc d) = c) {C : Block V}
    (nv : M.N)
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S nv c ⇢ some C)
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
    Block.compatible A0 C = true := by
  intro n A0 hA0
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haPredC : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S c) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have haCSucc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon := haCSucc.trans hhorNext
  have hlod : (M.opening_slot S.hc c) ≤ d := (Nat.le_succ _).trans hd1
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
  have hvoteHi : M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    have h1 := facts.sch.vote_time_mono_slots S.E (Nat.le_of_succ_le hdSucc)
    have h2 := facts.sch.Protocol_vote_time_le_confirmation_time S.E (M.opening_slot S.hc (c + 1))
    have h3 := facts.sch.a_eq_confirmation_time S.hc S.E (c + 1)
    show M.vote_time S.E d ≤ M.a S.hc S.E.Δ (c + 1)
    rw [h3]
    exact h1.trans h2
  have hvoteHor : M.vote_time S.E d ≤ rho.horizon := hvoteHi.trans hhorNext
  have hvoteLo : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.vote_time S.E d := by
    have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
      facts S hpredLt
    exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((facts.sch.proposal_time_mono S.E hlod).trans
        (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d)))
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
    exact (facts.sch.proposal_time_mono S.E hlod).trans
      (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E d))
  have hwG1 : w ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ hG1le hw
  have hvG2 : v ∈ Hs (M.domain S.E S.hc c .g2) := hHs _ _ (facts.gr.domain_le_a S c .g2) hv
  have hvG1 : v ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ (facts.gr.domain_le_a S c .g1) hv
  have hvG0 : v ∈ Hs (M.domain S.E S.hc c .g0) := hHs _ _ (facts.gr.domain_le_a S c .g0) hv
  have hprevDelta : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤
      M.domain S.E S.hc c .g2 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hcPos Nat.one_pos)).trans
      (facts.gr.early_le_domain S c)
  have hdomG2 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g2 :=
    le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hprevDelta
  have hdomG1 : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc c .g1 :=
    hdomG2.trans (le_of_lt (facts.gr.q10_domain_g2_lt_domain_g1 S c))
  have hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = Mh :=
    fun u hu => (hframe _ le_rfl (haPredC.trans haCSucc) u hu).2
  have hfrontier : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u).st.h_max = Mh :=
    fun u hu => (hframe _ haPredC haCSucc u hu).2
  have hgate : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u).st.h_j + 2 ≤ Mh :=
    fun u hu => (hframe _ haPredC haCSucc u hu).1
  have hfrontierG1 : ∀ u ∈ Hs (M.domain S.E S.hc c .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st.h_max = Mh :=
    fun u hu => (hframe _ hdomG1 ((facts.gr.domain_le_a S c .g1).trans haCSucc) u hu).2
  have hgateG1 : ∀ u ∈ Hs (M.domain S.E S.hc c .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st.h_j + 2 ≤ Mh :=
    fun u hu => (hframe _ hdomG1 ((facts.gr.domain_le_a S c .g1).trans haCSucc) u hu).1
  have hsettled :=
    Restated.namedLiveG1SettledAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hfb hcPos hpost hprev
      hfrontier hgate hfrontierG1 hgateG1 hhorC hA
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmemA : W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S c) :=
    mem_stateBeforeTime_along₆₆b hf.sorted hf.onePath _
  have hmemG0 : W (strictEventIndex rho (M.domain S.E S.hc c .g0)) v ∈
      Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc c .g0) v :=
    ⟨_, mem_stateBeforeTime_along₆₆b hf.sorted hf.onePath _, rfl⟩
  have hfilt := actionReadFrom_filtered₆₆b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c nv hnv
  have hrootEq := actionReadFrom_fgRoot₆₆b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c nv hnv
  -- the vote-duty read of `w`
  obtain ⟨hgateRead, hfrontierRead⟩ := hframe (M.vote_time S.E d) hvoteLo hvoteHi w hw
  have hparts := dutyNode_parts₆₆b facts S (W (strictEventIndex rho (M.vote_time S.E d)) w) d cv
  have hnS : n.st.core.s = d := hparts.1
  have hnRoot : M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core).toFG :=
    hparts.2
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      mem_stateBeforeTime_along₆₆b hf.sorted hf.onePath _, cv, hcv, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w d n hnmem A0 hA0 with
    hfgAnchor | ⟨root, A, hframeG1, hactive, hanchor⟩
  · -- Case: the anchor is the FG root of the vote-duty read.
    have hrootF : M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core).toFG =
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F :=
      Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts
        (st := (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core) hgateRead hfrontierRead
    obtain ⟨Wn, hWbody, hCW, hWh⟩ :=
      Restated.freshFGSource_frontierWitnessOn facts S Hs Xb hf nv hnv hsource (hfrontier v hv)
    have hWpre : Wn ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c))
        v).st.bodies := by
      rw [← actionReadFrom_bodies₆₆b facts S _ _ nv hnv]
      exact hWbody
    have hWrun : Restated.RunBlockOn M S rho W Xb Wn :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hWpre
    have hFW : Block.Preceq (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F Wn.erase :=
      Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hw hgateRead hWrun hWh
    rw [hfgAnchor, hnRoot, hrootF]
    exact compatible_of_preceq_common_Preceq hFW hCW
  -- Case: the anchor is an active prefix of the grade-1 frame root.
  have hroundRead : M.round_of S.hc n.st.core.s = c := by
    rw [hnS]
    exact hround
  rw [hroundRead] at hframeG1
  rw [hanchor]
  obtain ⟨-, hAG1⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
    S Hs Xb hf hcPos hlod hround hnext hvoteHor hwG1 cv hcv hframeG1 hactive hloG1
  have hAG1t := storeGrade_true_of_all₆₆b facts S.E S.hc _ c .g1 A hAG1
  have hset : Block.Preceq A (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG) ∨
      A ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG :=
    hsettled w hwG1 A hAG1 v hv
  -- an anchor active at `v`'s action read is graded 0 at `v`'s grade-0 domain read
  have hAG0_of : A ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG →
      A ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nv ∧
      Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g0)) v).st c .g0 A ⇢ true := by
    intro hAactive
    have hAaction : A ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nv := by
      show A ∈ M.get_filtered_block_tree (M.toHealing nv.st.core).toFG
      rw [hfilt]
      exact hAactive
    exact ⟨hAaction, storeGrade_true_of_all₆₆b facts S.E S.hc _ c .g0 A
      (Restated.storeGrade_g0_of_g1_and_targetActionActiveOn facts
        S Hs Xb hf hHs hHsXb hsb hcPos ready hwG1 hvG0 hAG1t nv hnv hAaction hlo)⟩
  -- the FG source of `nv`: the selected candidate `Q`, or a cleared descendant of it
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsource
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₆b _ _ _).1 hsource
  obtain ⟨Q, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing nv.st.core) c
  have hGQ : G.Q2 = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nv c ⇢ some Q := by
    have h := nodeQ2_of_read₆₆b S nv c G hG
    rwa [hGQ] at h
  have hQaction : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nv :=
    Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho v c _ hmemA nv hnv hq
  have hrootQ : Block.Preceq (M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core).toFG) Q := by
    rw [← hrootEq]
    exact preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hQaction)
  cases hwalk : M.deepest_clear (some Q)
      (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | none =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hwalk _ hsrc
      have hCQ : C = Q := Option.some_inj.mp h
      subst hCQ
      rcases hset with hAroot | hAactive
      · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAroot hrootQ))
      · obtain ⟨-, hAG0t⟩ := hAG0_of hAactive
        have hQG2t := storeGrade_true_of_all₆₆b facts S.E S.hc _ c .g2 C
          (Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf nv hnv hq)
        have hQG1t := storeGrade_true_of_all₆₆b facts S.E S.hc _ c .g1 C
          (Restated.storeGrade_g1_of_g2_and_targetActionActiveOn facts
            S Hs Xb hf hHs hHsXb hsb hcPos ready hvG2 hvG1 hQG2t nv hnv hQaction hlo)
        have hQG0t := storeGrade_true_of_all₆₆b facts S.E S.hc _ c .g0 C
          (Restated.storeGrade_g0_of_g1_and_targetActionActiveOn facts
            S Hs Xb hf hHs hHsXb hsb hcPos ready hvG1 hvG0 hQG1t nv hnv hQaction hlo)
        exact Restated.relativeSeed_sameReaderG0_compatible_l66 facts S rho c v _ hmemG0 hAG0t hQG0t
  | some B =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hwalk _ hsrc
      have hCB : C = B := Option.some_inj.mp h
      subst hCB
      have hQC : Block.Preceq Q C := facts.gr.deepest_clear_floor_Preceq hwalk
      have hclearRet : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nv c C ⇢ true := by
        have h' : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nv c C ⇢ G.clear C :=
          returns_map_intro₆₆b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.clear C) _ G
            hG
        rw [facts.gr.deepest_clear_test hwalk] at h'
        exact h'
      rcases hset with hAroot | hAactive
      · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAroot
          (preceq_trans_Preceq hrootQ hQC)))
      · obtain ⟨hAaction, hAG0t⟩ := hAG0_of hAactive
        exact Restated.relativeG0_compatible_clearSourceOn facts S Hs Xb hf hcPos hhorC hvG0
          hAG0t
          (Restated.Vocabulary.Proofs.HealingSurface.storeGrade_g0_mem_domainTree facts S rho _ hmemG0
            hAG0t)
          nv hnv hAaction hclearRet hloG0

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read and the
    SG vote selector each can return a value. -/
private theorem exists_actionSG₆₆b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₆b facts S before r
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g
  exact ⟨n, hn, g, hg, B, hB⟩

/-- If every member of the set for `domain r .g2` has `C` active, with every outcome of its grade-2
    store grade `true`, in its node state in `W (strictEventIndex rho (domain r .g2))`, `v` is in
    the set for `domain r .g0`, and `C` is active at a node state `n` of `v`'s round-`r` action
    read, then `C` is an ancestor of every SG vote `n` can select. -/
private theorem formsW_preceq_actionSGBlockAt₆₆b (facts : Record.Facts M) (S : Setup V)
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
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
    nodeQ2_of_read₆₆b S n r G hG
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
local macro "spa% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Execution.SeedPromotionAncestor)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`: if the opening window `hwindow'` of round `q'` holds for `B'` with its carrier
    round `hcarrier'` and round ceiling `hceiling'`, every member of the set for round `q + 1`'s
    grade-2 domain time has `B`'s block active in `W` before that time with every outcome of its
    grade-2 store grade `true` (`hgradeNext`), `B` is a run block of height `Mh − 1` with `1 ≤ Mh`,
    `q + 2 ≤ q'`, every member of the set for each time from `S.a (q + 1)` to `S.a (q' − 1)` has
    `h_j + 2 ≤ Mh` and `h_max = Mh` there (`hframe`), and the bounds on `lo` and the awake
    hypothesis `hA` hold, then `B` is an ancestor of `B'`'s parent. -/
theorem seedOpeningProposal_preceq_nextOpeningParent_of_gradeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q q' : Round} {C' B B' : NamedBlock V}
    (hwindow' : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q' B')
    (hcarrier' : Restated.ProposerCarrierAtOn M S Hs q')
    (hceiling' : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb
      Mh q' C')
    (hgradeNext : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) v).st (q + 1) .g2 B.erase ⇢ b →
          b = true)
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hBheight : (M.derive_named S.E S.cfg B).h = Mh - 1)
    (hM : 1 ≤ Mh)
    (hqq' : q + 2 ≤ q')
    (hpostNext : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
    (hhorPrev' : (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)) ≤ rho.horizon)
    (hframe : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)) → ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q + 1 - S.hc.η_SG))
    (hloVote' : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q') - 1))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ Parent : NamedBlock V, NamedBlock.parent? B' = some Parent →
      NamedBlock.Preceq B Parent := by
  obtain ⟨hspan, hq'PredPos⟩ :=
    (spa% seedPromotionAncestor_rounds_nat) hqq'
  have hformsAt := Restated.namedGradeFormsAt_persists_through_gateOffActionWindowOn facts
    S Hs Xb hf hHs hHsXb hfb (r0 := q + 1) (q := q' - 1) (Nat.succ_pos q) hgradeNext hBrun
    (by simpa only [hBheight] using (Nat.le_refl (Mh - 1))) hM hpostNext hhorPrev'
    (fun read hlo hhi w hw =>
      let h := hframe read hlo hhi w hw
      ⟨h.2, h.1⟩)
    hlo hloOpen (fun k hk _ _ => hA k hk)
  have hforms := hformsAt (q' - 1) hspan (le_refl _)
  have hloOpen' : lo ≤ M.opening S.E S.hc (q' - 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hspan _))
  obtain ⟨_, _, _, _, hal5⟩ := Restated.openingAnchorsAligned_of_roundCeilingOn facts
    S Hs Xb hf hHs hHsXb hcom hcarrier' hceiling' hloVote'
  obtain ⟨x, hxConf⟩ := Restated.honest_nonempty_of_committeesOn facts S Hs hcom
    ((M.opening_slot S.hc (q' - 1)))
  have hx : x ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S (q' - 1)]
    exact hxConf
  -- one carrier of `x`'s round-`(q' − 1)` action read along `W`
  obtain ⟨n, hn, g, hg, A, hAsel⟩ := exists_actionSG₆₆b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) x) (q' - 1)
  have hBA0 : Block.Preceq B.erase A :=
    formsW_preceq_actionSGBlockAt₆₆b facts S Hs Xb hf hHs hHsXb hq'PredPos hhorPrev'
      hforms.1 (hHs _ _ (facts.gr.domain_le_a S (q' - 1) .g0) hx) n hn (hforms.2 x hx n hn)
      hloOpen' g hg A hAsel
  -- the opening proposal of round `q'`, read at the proposer's read on `W`
  have hs' : 0 < (M.opening_slot S.hc q') :=
    facts.gr.opening_slot_pos_of_round_pos S.hc hwindow'.roundPositive
  have hproposalB' : ∃ cp : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q'))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).cache ⇢ cp ∧
      M.proposal_with (M.gradeContract cp)
        Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q')))
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).st (M.proposal_time S.E (M.opening_slot S.hc q')))
        ⇢ some B' := hwindow'.proposal
  obtain ⟨cp, hcp, ho⟩ := hproposalB'
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    (S.node (S.E.proposer (M.opening_slot S.hc q')))
    (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
        (S.E.proposer (M.opening_slot S.hc q'))).st (M.proposal_time S.E (M.opening_slot S.hc q')))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
        (S.E.proposer (M.opening_slot S.hc q'))).record cp).st.core)
  have hI' : M.with_proposal_input (M.gradeContract cp) S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q')))
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).st
        (M.proposal_time S.E (M.opening_slot S.hc q'))) cp).core) id ⇢ I := by
    have h := hI
    rewrite [facts.nd.mkNode_st] at h
    exact h
  have hbelow : Block.Preceq B.erase I.parent :=
    preceq_trans_Preceq hBA0 (hal5 x hx n hn g hg A hAsel cp hcp I hI)
  intro Parent hParent
  obtain ⟨p, hp, hparentErase⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ B' _
      (by rw [facts.dt.proposal_with_store_with_cache]; exact ho) rfl I hI'
  have hparentEq : B'.parent = p := by
    cases B' with
    | genesis => cases hp
    | node parent slot root votes support rows proposer =>
        rw [namedBlock_parent_node]
        exact Option.some.inj hp
  have hParentEq : Parent = p := Option.some.inj (hParent.symm.trans hp)
  have hbelowParent : Block.Preceq B.erase B'.parent.erase := by
    rw [hparentEq, hparentErase]
    exact hbelow
  obtain ⟨A', hAparent, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift
    B'.parent hbelowParent
  have hB'run : Restated.RunBlockOn M S rho W Xb B' := by
    have hproposalHor' : M.proposal_time S.E
        ((M.opening_slot S.hc q')) ≤ rho.horizon :=
      (facts.sch.proposal_time_le_confirmation_time S.E _).trans
        (by
          rw [← Restated.a_eq_confirmation_opening_l58 facts S q']
          exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q')).trans
            hwindow'.nextActionInHorizon)
    have hsPred : (M.opening_slot S.hc q') - 1 + 1 = (M.opening_slot S.hc q') := Nat.sub_add_cancel hs'
    have hloProp' : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q')) := by
      refine hloVote'.trans ?_
      have h1 := facts.sch.vote_time_le_view_freeze S.E ((M.opening_slot S.hc q') - 1)
      have h2 := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E
        ((M.opening_slot S.hc q') - 1)
      rw [hsPred] at h2
      linarith [S.E.Δ_pos]
    have hprop' : S.E.proposer ((M.opening_slot S.hc q')) ∈
        Hs (M.confirmation_time S.E ((M.opening_slot S.hc q'))) := by
      simpa only [Nat.add_zero] using hcarrier' 0 (by decide)
    -- The opening proposer of `q'` passes the grade-1 awake test at its proposal ticks.
    have hrunP' : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
        (S.E.proposer (M.opening_slot S.hc q')) (M.proposal_time S.E (M.opening_slot S.hc q'))) →
        M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q'))
          (W j (S.E.proposer (M.opening_slot S.hc q'))) (M.round_of S.hc (M.opening_slot S.hc q')) := by
      have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q')) .g1 - S.E.Δ := by
        rw [facts.gr.round_of_opening_slot_eq S.hc q']
        have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
          (show q + 1 < q' from Nat.lt_of_lt_of_le (Nat.lt_succ_self (q + 1)) hqq')
        have h2 := facts.gr.q10_early_g2_le_early_g1 S q'
        have h3 : lo ≤ M.a S.hc S.E.Δ (q + 1) := hlo
        linarith
      intro j hj
      exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
        (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop') hwin
    exact Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      ((M.opening_slot S.hc q')) hs' hprop' hproposalHor' hloProp'
      (fun j hj => hf.tick_outcome j _ _ hj) hrunP' cp hcp ho
  have hparentRun : Restated.RunBlockOn M S rho W Xb B'.parent :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hB'run
      ((spa% seedPromotionAncestor_namedParent_preceq) B')
  have hArun : Restated.RunBlockOn M S rho W Xb A' :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hparentRun hAparent
  have hBA : B = A' := by
    apply hf.rootCollisionFree.root_injective B A' hBrun hArun B A'
      (Or.inl (Proofs.NamedAncestry.named_self B))
      (Or.inr (Proofs.NamedAncestry.named_self A'))
    rw [← Proofs.NamedWire.erase_root B, ← Proofs.NamedWire.erase_root A', hAerase]
  have hnamed : NamedBlock.Preceq B B'.parent := by
    rw [hBA]
    exact hAparent
  have hBParent : B'.parent = Parent := hparentEq.trans hParentEq.symm
  simpa only [hBParent] using hnamed

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
local macro "spa% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Execution.SeedPromotionAncestor)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`: if round `q` is a carrier round (`hcarrier`), `C` is its round ceiling at `Mh`
    (`hceiling`), the opening window `hwindow` holds for `P`, every member of the set for
    `S.a (q − 1)` has `h_max = Mh` there, every member of the sets for round `q`'s grade-1 and
    grade-0 domain times has `h_max = Mh` and `h_j + 2 ≤ Mh` there, `P`'s block is active at round
    `q + 1`'s grade-2 domain read of every member of the set for that time, and the bounds
    `hloPrev`, `hloFrozen` and the awake hypotheses `hA`, `hAprev` hold, then the lifecycle packet
    of round `q − 1` at the slot before round `q`'s opening holds for `P`. -/
theorem seedLifecyclePacket_of_roundCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hceiling : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb
      Mh q C)
    (hwindow : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q P)
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.h_max = Mh)
    (hnext : ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w))
    (hfrontierG1 : ∀ w ∈ Hs (M.domain S.E S.hc q .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.h_max = Mh)
    (hgateOffG1 : ∀ w ∈ Hs (M.domain S.E S.hc q .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.h_j + 2 ≤ Mh)
    (hfrontierG0 : ∀ w ∈ Hs (M.domain S.E S.hc q .g0),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) w).st.h_max = Mh)
    (hgateOffG0 : ∀ w ∈ Hs (M.domain S.E S.hc q .g0),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) w).st.h_j + 2 ≤ Mh)
    (hloPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloFrozen : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    Restated.NamedSGProposalLifecyclePacketOn M S rho W (fun t => W (strictEventIndex rho t))
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))))
      (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))))
      Hs Xb (q - 1) ((M.opening_slot S.hc q) - 1) P := by
  have hq : 0 < q := hwindow.roundPositive
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hs : 0 < (M.opening_slot S.hc q) := facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hsPred : (M.opening_slot S.hc q) - 1 + 1 = (M.opening_slot S.hc q) :=
    Nat.sub_add_cancel hs
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans hwindow.nextActionInHorizon
  have hconfEq : (Restated.Vocabulary.Execution.Setup.a M S q) = M.confirmation_time S.E ((M.opening_slot S.hc q)) :=
    Restated.a_eq_confirmation_opening_l58 facts S q
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon := by
    rw [← hconfEq]; exact hactionHor
  have hloVotePrev : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) :=
    hloFrozen.trans (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hloProp : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    hloFrozen.trans (facts.sch.proposal_time_mono S.E (Nat.sub_le _ _))
  have hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q)) :=
    hloProp.trans (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hloConf : lo ≤ M.confirmation_time S.E ((M.opening_slot S.hc q)) :=
    hloVote.trans (facts.sch.Protocol_vote_time_le_confirmation_time S.E _)
  have hrelG1 : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (q - 1) .g1 :=
    Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hq hloPrev
      hprev hfrontierG1 hgateOffG1 ((facts.gr.domain_le_a S q .g1).trans hactionHor)
      hAprev
  have hrelG0 : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (q - 1) .g0 :=
    Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hq hloPrev
      hprev hfrontierG0 hgateOffG0 ((facts.gr.domain_le_a S q .g0).trans hactionHor)
      hAprev
  have hprevDelta : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤ M.domain S.E S.hc q .g1 := by
    have h := Restated.action_add_delta_le_domain_g2_succ_l54 facts S (q - 1)
    rw [hqPred] at h
    exact h.trans (le_of_lt (facts.gr.q10_domain_g2_lt_domain_g1 S q))
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs (Hs (M.domain S.E S.hc q .g1)) q :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hq
      hprevDelta ((facts.gr.domain_le_a S q .g1).trans hactionHor) hloPrev hAprev
  -- the opening proposal, read at the proposer's read on `W`
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
    rw [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact ho
  have haligned := Restated.openingAnchorsAligned_of_roundCeilingOn facts S Hs Xb hf hHs hHsXb
    hcom hcarrier hceiling hloVotePrev
  have hadopt := Restated.gateOff_openingLifecycle_of_roundCeilingOn facts
    S Hs Xb hf hHs hHsXb hcom hfb hcarrier hceiling hwindow hprev hnext hfrontierG0 hgateOffG0
    hloPrev hloFrozen hA hAprev
  have hlifecycle := hadopt.lifecycle
  have hheight : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h :=
    hwindow.parentHeight.trans
      (facts.cs.derive_height_mono S.E S.cfg
        ((spa% seedPromotionAncestor_namedParent_preceq) P))
  have hM : 1 ≤ Mh :=
    (by decide : (1 : Nat) ≤ 2).trans ((Nat.le_add_left 2 _).trans hwindow.proposerGateOff)
  -- The awake tests at round `q`'s opening slot: grade 1 for the proposer and the committee, grade
  -- 2 for the confirmers.
  have hwinG2 : lo ≤ M.early S.E S.hc q .g2 - S.E.Δ := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hq Nat.one_pos)
    have h3 : lo ≤ M.a S.hc S.E.Δ (q - 1) := hloPrev
    linarith
  have hwinG1 : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc q]
    have h2 := facts.gr.q10_early_g2_le_early_g1 S q
    linarith
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
      (S.E.proposer (M.opening_slot S.hc q)) (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q)) := by
    intro j hj
    have hprop : S.E.proposer (M.opening_slot S.hc q) ∈
        Hs (M.confirmation_time S.E (M.opening_slot S.hc q)) := by
      simpa only [Nat.add_zero] using hcarrier 0 (by decide)
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop) hwinG1
  have hrunV : ∀ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)),
      v ∈ S.E.committee (M.opening_slot S.hc q) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S v (W j v) (M.round_of S.hc (M.opening_slot S.hc q)) :=
    fun v hv _ j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hv hwinG1
  have hrunC : ∀ v ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc q)),
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade2 (Setup.alwaysAwake S) v (W j v)
          (M.round_of S.hc (M.opening_slot S.hc q + 1)) := by
    intro v hv j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q + 1)) .g2 - S.E.Δ := by
      rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc q]
      exact hwinG2
    exact hf.awake_g2 _ _ j hj hv hwin
  have hstores := Restated.proposalWalkTransferred_of_roundCeilingOn facts S Hs Xb hf hHs hHsXb
    hcom hcarrier cp hcp hP' hceiling haligned hwindow.nextActionInHorizon hheight hM
    hwindow.proposalAtVote hwindow.voteFrontier hwindow.voteGateOff
    hloFrozen hwindow.proposerFrontier hrunP
  have hnames : Restated.NamedHonestVotesNameOn M S rho W Hs ((M.opening_slot S.hc q)) P.erase :=
    Restated.honestVotesName_of_voteStoresExtendOn facts S Hs Xb hf hs
      ((facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor) hloVote hstores
      (fun _ _ _ j hj => hf.tick_outcome j _ _ hj) hrunV
  obtain ⟨_hal1, _hal2, _hal3, _hal4, hal5⟩ := haligned
  have hclear := Restated.g0ClearAtAction_of_relativeCarrierWindowOn facts S Hs Xb hf hHs hfb
    hq hactionHor ((facts.gr.domain_le_a S q .g2).trans hactionHor) hloPrev hrelG0 cp hcp ho
    (fun u hu n' hn' A2 hA2 G hG I hI => hal5 u hu n' hn' A2 hA2 G hG cp hcp I hI) hAprev
  refine
    { openingSlot := by rw [hqPred]; exact hsPred
      proposal := by rw [hqPred]; exact hwindow.proposal
      actionTargetParent := by rw [hqPred]; exact hal5
      liveG1Parent := ?_
      honestVotes := by rw [hqPred]; exact hnames
      genuineConfirmation := ?_
      g0ClearAtAction := ?_
      lifecycle := by rw [hqPred]; exact hlifecycle }
  · rw [hqPred]
    intro w hw X hG1 c hc I hI
    obtain ⟨u, hu, hBu⟩ := Restated.relativeGrade_has_roundCarrierOn facts
      S Hs Xb (Hs (M.domain S.E S.hc q .g1)) hf hHs hrelG1
        (by rw [hqPred]; exact hmajority)
        (by simp only [hqPred]; exact Finset.Subset.refl _)
        (w := w) (by rw [hqPred]; exact hw) (B := X)
        (by rw [hqPred]; exact storeGrade_true_of_all₆₆b facts S.E S.hc _ q .g1 X hG1)
    have huHon : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
      ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u (q - 1)).mp hu).1
    obtain ⟨n, hn, A2, hA2, G, hG⟩ := exists_actionSG₆₆b facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u) (q - 1)
    exact preceq_trans_Preceq (hBu n hn A2 hA2 G hG) (hal5 u huHon n hn A2 hA2 G hG c hc I hI)
  · rw [hqPred]
    intro v hv
    exact Restated.genuineConfirmationAt_of_withOn facts S Hs Xb hf hv
      hconfHor (hadopt.genuineConfirmation v hv) hloConf (hrunC v hv)
  · rw [hqPred]
    intro v hv
    exact hclear v (hHs _ _ (facts.gr.domain_le_a S q .g0) hv)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

end

end DecoupledConsensusModel.Sts.Restated
