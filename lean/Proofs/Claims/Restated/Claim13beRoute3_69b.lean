import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_56b
import Proofs.Claims.Restated.Claim13beRoute3_66
import Proofs.Claims.Restated.Claim13beRoute3_68b
import Proofs.Claims.Restated.Claim13beRoute3_69
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_CarrierFirst
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradePersistence
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Height progress from a fixed-height justification root

The theorems saying that the largest `h_max` over the set of a late enough round's action instant
exceeds the height of a fixed-height justification root, and the run-scoped named height regimes
they use, stated over a model `M : Record.Model V` along the path `W` of the bundle
`AdmissibleFieldsOn`.
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

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₉b (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₉b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₉b S rho hsorted]
  exact (hW _).1

/-- Every node state of the round-`r` action read computed from `before` has as its core store an
    outcome of the confirmation update of `before`'s store staged at round `r`'s action instant. -/
private theorem actionReadFrom_core₆₉b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state of the round-`r` action read computed from `before` has the FG root of
    `before`'s core store. -/
private theorem actionReadFrom_fgRoot₆₉b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₉b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- The round-`r` action read computed from any node state has a node state. -/
private theorem actionReadFrom_nonempty₆₉b (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- The round-`r` action read from `before` has a node state `n` on which the grade-2 block read
    returns some `g` and the SG vote selector on `g` some block `B`. -/
private theorem exists_actionSG₆₉b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₉b facts S before r
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g
  exact ⟨n, hn, g, hg, B, hB⟩

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₉b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If the grade read at `n` for round `r` can return `G`, the grade-2 candidate read there can
    return `G.Q2`. -/
private theorem nodeQ2_of_read₆₉b (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₉b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

/-- The anchor of a node state `n` at round `r` has an outcome. -/
private theorem nodeAnchor_nonempty₆₉b (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  refine ⟨G.anchor, ?_⟩
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₉b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hG

/-- The store a tick at `t` hands its first duty, staged from `st`, has the FG root of `st`. -/
private theorem tickStore_fgRoot₆₉b (facts : Record.Facts M) {S : Setup V} (st : M.S) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t)).toFG =
      M.get_fg_root (M.toHealing st).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the `h_max` of
    `n`'s core store. -/
private theorem tickStore_h_max₆₉b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- If every member of the set for `domain r .g2` has `C` in its filtered tree with every grade-2
    store grade outcome `true` in the world of `W` before that instant, `v` is in the set for
    `domain r .g0`, and `C` is active at a node state `n` of `v`'s round-`r` action read, then `C`
    is an ancestor of every SG vote `n` can select. -/
private theorem formsW_preceq_actionSGBlockAt₆₉b (facts : Record.Facts M) (S : Setup V)
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
    nodeQ2_of_read₆₉b S n r G hG
  obtain ⟨Q, hQ, hCQ⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
      (hformsW v hvG2).1 hb n hn hactive _ hGq
  rw [hQ] at hGq
  exact Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hhor
    (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv) hlo n hn hGq hCQ

/-- Along `W`, for every outcome `c` of the cache update at slot `s`'s proposal instant on the
    proposer's node state, the proposal duty with `c`'s grade contract can return some block. -/
private theorem proposal_some_along₆₉b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c) :
    ∃ P : NamedBlock V, M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P := by
  have hn : M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
    ⟨_, mem_stateBeforeTime_along₆₉b hf.sorted hf.onePath (M.proposal_time S.E s), c, hc, rfl⟩
  have hinv := Restated.Vocabulary.Proofs.HealingSurface.proposerReadAt_invariant facts S rho s _ hn
  rewrite [facts.nd.mkNode_st] at hinv; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hinv
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract c)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (M.store_with_cache
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) c)
  obtain ⟨P, hoP⟩ := facts.dt.proposal_with_gradeContract_isSome c .poolAndCarried S.E S.hc S.cfg
    (S.node (S.E.proposer s)) _ hinv o ho
  have ho' := hoP ▸ ho
  rw [facts.dt.proposal_with_store_with_cache] at ho'
  exact ⟨P, ho'⟩

/-- Along `W`, a block the proposal duty of slot `s`'s proposer can return with a cache outcome `c`
    is a value of `proposedBlockAt`. -/
private theorem some_mem_proposedBlockAt₆₉b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    some B ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s :=
  ⟨M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c,
    ⟨_, mem_stateBeforeTime_along₆₉b hf.sorted hf.onePath (M.proposal_time S.E s), c, hc, rfl⟩,
    by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact hB⟩

/-- If `P` is a proposal the proposer's duty of slot `s` can return on `wp`'s store staged to `t`
    with the grade contract of `c`, then some proposal input `I` and some named block `par` are such
    that `par` is `P`'s parent and `par`'s block is `I`'s parent. -/
private theorem proposalParentInput₆₉b (facts : Record.Facts M) (S : Setup V) (wp : M.N)
    (s : Slot) (t : Time) (c : M.Cache) {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E wp.st t) ⇢ some P) :
    ∃ (I : Protocol.ProposalInput V) (par : NamedBlock V),
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer s))
        (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st t) wp.record c).st.core) ⇢ I ∧
      NamedBlock.parent? P = some par ∧ par.erase = I.parent := by
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
  exact ⟨I, par, hI, hpar, hparE⟩

omit [DecidableEq V] [Fintype V] in
/-- A named block whose named parent is `P` has `P` as its parent block. -/
private theorem parent_eq_of_parent?₆₉b {B P : NamedBlock V}
    (h : NamedBlock.parent? B = some P) : B.parent = P := by
  cases B with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at h
  | node q' _ _ _ _ _ _ =>
    simp only [NamedBlock.parent?, Option.some.injEq] at h
    subst h
    exact Proofs.ModelProperties.named_parent_node ..

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
local macro "hpf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ValidatorClient.HeightProgressFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))
/-- `omega` after unfolding `Round`, `Height` and `Slot` to `Nat`. -/
local macro "romega" : tactic => `(tactic| (dsimp only [Round, Height, Slot] at *; omega))

/-- Under the bundle with path `W`, the committee majority, the weight bound, the carrier recurrence
    within `gap` rounds from `t₀`, the timeout delay bound, the grade-2 awake condition `hA`, and
    the hypotheses `_of_lifecycle` and `_of_sourceToParent`: if `u`'s store in the world of `W`
    before `read` holds a fixed-height justification root at `Mh`, `t_GST ≤ read ≤ S.a r`, the
    endpoint round is at least `r + 3·gap + 8 + 2·delayExtra` with its action instant in the
    horizon, the largest `h_max` over the set for that action instant is at most `Mh`, `lo ≤ read`,
    `t₀ ≤ read` and `lo ≤ opening (r + 2 − η_SG)`, then that largest `h_max` is greater than `Mh`. -/
theorem fixedRootProgress_of_lifecycleOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (_of_lifecycle : ∀ {H : Height} {w : V} {read0 : Time} {base : Round},
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read0
        (W (strictEventIndex rho read0)) →
      S.E.t_GST ≤ read0 →
      read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S base) →
      (Restated.Vocabulary.Execution.Setup.a M S (base + 4 + gap)) ≤ rho.horizon →
      lo ≤ read0 → t₀ ≤ read0 →
      lo ≤ M.opening S.E S.hc (base + 2 - S.hc.η_SG) →
      H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (base + 4 + gap))).sup fun v =>
          (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (base + 4 + gap))) v).st.core.h_max) ∨
        ∃ q : Round, base + 3 ≤ q ∧ q ≤ base + 3 + gap ∧
          Restated.ProposerCarrierAtOn M S Hs q ∧
            (∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
              (W (strictEventIndex rho read0) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
                  (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
                ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
                  (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
                    (W (strictEventIndex rho read0) w).st.J ⇢ b →
                  b = true) ∧
              Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
                ((M.opening_slot S.hc q) - 1)
                (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))))
                (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))) ∧
                ∃ P : NamedBlock V,
                  (∃ c : M.Cache, M.onPhaseTick S.E S.hc
                      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
                        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
                      (M.proposal_time S.E (M.opening_slot S.hc q))
                      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
                        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c ∧
                    M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried
                      S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
                      (M.ns_setClock S.E
                        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
                          (S.E.proposer (M.opening_slot S.hc q))).st
                        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P) ∧
                  Restated.NamedSGProposalLifecyclePacketOn M S rho W
                    (fun t => W (strictEventIndex rho t))
                    (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))))
                    (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))))
                    Hs Xb (q - 1) ((M.opening_slot S.hc q) - 1) P)
    (_of_sourceToParent : ∀ {H : Height} {w : V} {read0 : Time} {r endpointRound q1 q' : Round} {B1 B2 : NamedBlock V}, Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read0 (W (strictEventIndex rho read0)) → lo ≤ read0 → read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) → r + 3 ≤ q1 → read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q1) → 0 < q1 → q1 < q' → q' ≤ endpointRound → Restated.ProposerCarrierAtOn M S Hs q1 → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q1) → (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon → ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x => (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) ≤ H → (∃ Bplus : NamedBlock V, (∃ cp : M.Cache, M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)) (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).cache ⇢ cp ∧ M.proposal_with (M.gradeContract cp) Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer ((M.opening_slot S.hc q1) + 2))) (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) ⇢ some Bplus) ∧ Restated.RunBlockOn M S rho W Xb Bplus ∧ S.E.proposer ((M.opening_slot S.hc q1) + 2) ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q1) + 2)) ∧ M.proposal_time S.E ((M.opening_slot S.hc q1) + 2) ≤ rho.horizon ∧ M.get_fg_root (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.toHealing.toFG = (W (strictEventIndex rho read0) w).st.J ∧ (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.h_max = H) → Restated.NamedSGProposalLifecyclePacketOn M S rho W (fun t => W (strictEventIndex rho t)) (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q1)))) (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q1)))) Hs Xb (q1 - 1) ((M.opening_slot S.hc q1) - 1) B1 → Restated.NamedSGProposalLifecyclePacketOn M S rho W (fun t => W (strictEventIndex rho t)) (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q')))) (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q')))) Hs Xb (q' - 1) ((M.opening_slot S.hc q') - 1) B2 → (M.derive_named S.E S.cfg B1).h = H - 1 → Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q1 - 1) ((M.opening_slot S.hc q1) - 1) (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q1) - 1 + 1)))) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q1 - 1)))) → Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q' - 1) ((M.opening_slot S.hc q') - 1) (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q') - 1 + 1)))) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)))) → (∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound → ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)), M.get_fg_root (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.toHealing.toFG = (W (strictEventIndex rho read0) w).st.J ∧ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.h_max = H) → M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q'))) (S.E.proposer (M.opening_slot S.hc q'))).st.core (M.proposal_time S.E (M.opening_slot S.hc q')))).toFG = (W (strictEventIndex rho read0) w).st.J → (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q'))) (S.E.proposer (M.opening_slot S.hc q'))).st.core (M.proposal_time S.E (M.opening_slot S.hc q'))).h_max = H → (∀ v ∈ Hs (M.domain S.E S.hc (q' - 1) .g2), B1.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) .g2)) v) ∧ ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) .g2)) v).st (q' - 1) .g2 B1.erase ⇢ b → b = true) → (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))), ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v) (q' - 1), B1.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) → Block.Preceq B1.erase B2.parent.erase → (∀ P : NamedBlock V, NamedBlock.parent? B2 = some P → (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q') → q1 + 2 + delayExtra ≤ q' → lo ≤ M.opening S.E S.hc (q' - 1 - S.hc.η_SG) → (∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) → ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))), ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v) (q' - 1), ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n (q' - 1) ⇢ some Q → ((M.toHealing n.st.core).σ Q).h ≤ (M.derive_named S.E S.cfg B2.parent).h) :
    ∀ {Mh : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read)) →
      S.E.t_GST ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) ≤ Mh →
      lo ≤ read → t₀ ≤ read →
      lo ≤ M.opening S.E S.hc (r + 2 - S.hc.η_SG) →
      Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) := by
  intro Mh u read r endpointRound hfix hpost hreadAction hbound hendHor hcapEnd hlo ht₀ hloOpen
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  have hmem : ∀ t : Time, W (strictEventIndex rho t) ∈
      Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t :=
    fun t => mem_stateBeforeTime_along₆₉b hf.sorted hf.onePath t
  have hmono : ∀ {k k' : Round}, k ≤ k' →
      (Restated.Vocabulary.Execution.Setup.a M S k) ≤ (Restated.Vocabulary.Execution.Setup.a M S k') :=
    fun h => Restated.Vocabulary.Proofs.Assembly.a_mono facts S h
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.fixedRootJustificationRoot_target_namedOn facts S Hs Xb hfix
  have hneEnd : (Hs ((Restated.Vocabulary.Execution.Setup.a M S endpointRound))).Nonempty :=
    Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _
  have hcapR : ∀ t : Time, lo ≤ t → t + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S endpointRound) →
      ((Hs t).sup fun x => (W (inclusiveEventIndex rho t) x).st.core.h_max) ≤ Mh :=
    fun t h1 h2 =>
      (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb h1 h2 hendHor hneEnd).trans hcapEnd
  have hliftR : ∀ t : Time, lo ≤ t → t + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S endpointRound) →
      Mh < ((Hs t).sup fun x => (W (inclusiveEventIndex rho t) x).st.core.h_max) →
      Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) :=
    fun t h1 h2 hrise =>
      hrise.trans_le (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb h1 h2 hendHor hneEnd)
  have hactionMono : ∀ {k : Round}, r ≤ k → k ≤ endpointRound →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) x).st.core.h_max) ≤
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) :=
    fun hk hkend => Restated.honestHMaxAtOn_action_mono_l56 facts S Hs Xb hf hHs hHsXb hcom hkend
      (hlo.trans (hreadAction.trans (hmono hk))) hendHor
  have hcapA : ∀ {k : Round}, r ≤ k → k ≤ endpointRound →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) x).st.core.h_max) ≤ Mh :=
    fun hk hkend => (hactionMono hk hkend).trans hcapEnd
  have hliftA : ∀ {k : Round}, r ≤ k → k ≤ endpointRound →
      Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) x).st.core.h_max) →
      Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) :=
    fun hk hkend hrise => hrise.trans_le (hactionMono hk hkend)
  have hhorAt : ∀ {k : Round}, k ≤ endpointRound →
      (Restated.Vocabulary.Execution.Setup.a M S k) ≤ rho.horizon :=
    fun hk => (hmono hk).trans hendHor
  have hloAt : ∀ t : Time, read ≤ t → lo ≤ t := fun t ht => hlo.trans ht
  have hloOpenAt : ∀ k : Round, r + 2 ≤ k →
      lo ≤ M.opening S.E S.hc (k - S.hc.η_SG) :=
    fun k hk => hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hk _))
  have hactionDelay : ∀ {k : Round}, r < k →
      read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S k) := by
    intro k hk
    have h := Restated.action_add_delta_lt_action_of_lt_l67 facts S hk
    linarith
  have hpropDelay : ∀ {q : Round}, r < q →
      read + S.E.Δ ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    fun hq => (Int.add_le_add_right hreadAction S.E.Δ).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hq)
  have hpropLo : ∀ {q : Round}, r < q → lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    intro q hq
    have h := hpropDelay hq
    linarith
  have hpropRun : ∀ {q : Round}, r < q →
      S.E.proposer (M.opening_slot S.hc q) ∈ Hs (M.proposal_time S.E (M.opening_slot S.hc q)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q)) := by
    intro q hq hprop j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc q]
      have h1 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (hlo.trans hreadAction) hq
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj hprop hwin
  have hpropAction : ∀ q : Round, M.proposal_time S.E ((M.opening_slot S.hc q)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S q) := by
    intro q
    have h := Restated.openingProposal_add_delta_lt_action_l56 facts S q
    linarith
  have hpropCap : ∀ {q : Round}, r < q → q ≤ endpointRound →
      ((Hs (M.proposal_time S.E ((M.opening_slot S.hc q)))).sup fun x =>
        (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q)))) x).st.core.h_max) ≤ Mh :=
    fun hq hqEnd => hcapR _ (hpropLo hq)
      (lt_of_lt_of_le (Restated.openingProposal_add_delta_lt_action_l56 facts S _) (hmono hqEnd))
  have hpropPick : ∀ {q : Round}, Restated.ProposerCarrierAtOn M S Hs q → ∀ t : Time,
      t ≤ M.confirmation_time S.E ((M.opening_slot S.hc q)) →
      S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs t := by
    intro q hcarrier t ht
    exact hHs _ _ ht (hcarrier 0 (by decide))
  have hproposalConf : ∀ s : Slot,
      M.proposal_time S.E s ≤ M.confirmation_time S.E s :=
    fun s => facts.sch.proposal_time_le_confirmation_time S.E s
  have haConf : ∀ q : Round, (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)) := by
    intro q
    rw [← Restated.a_eq_confirmation_opening_l58 facts S q]
    exact hmono (Nat.sub_le q 1)
  have hfixedAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        M.get_fg_root
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.toHealing.toFG =
          (W (strictEventIndex rho read) u).st.J ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.h_max = Mh := by
    intro k hrk hkend v hv
    exact
      Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
        S Hs Xb hf hHs hHsXb hsb hfix hv hlo (hactionDelay (Nat.lt_of_succ_le hrk)) (hhorAt hkend)
        (hcapA (Nat.le_of_succ_le hrk) hkend)
  have hfixedCore : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        M.get_fg_root
            (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core).toFG =
          (W (strictEventIndex rho read) u).st.J ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core.h_max = Mh :=
    fun hrk hkend v hv => hfixedAt hrk hkend v hv
  have htargetActiveAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        (W (strictEventIndex rho read) u).st.J ∈
          M.get_filtered_block_tree
            (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core).toFG := by
    intro k hrk hkend v hv
    rw [← (hfixedCore hrk hkend v hv).1]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S rho
      ((Restated.Vocabulary.Execution.Setup.a M S k)) v _ (hmem _)
  have hdomDelay : ∀ {k : Round}, r < k → read + S.E.Δ ≤ M.domain S.E S.hc k .g2 := by
    intro k hk
    have h : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.domain S.E S.hc k .g2 :=
      (facts.gr.action_delta_le_early S S.hc.R_ge_three hk).trans (facts.gr.early_le_domain S k)
    linarith
  have hdomHor : ∀ {k : Round}, k ≤ endpointRound → M.domain S.E S.hc k .g2 ≤ rho.horizon := by
    intro k hk
    have h1 := Restated.domain_add_delta_lt_action_l56 facts S k .g2
    have h2 := hhorAt hk
    linarith
  have hdomainActiveAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ Hs (M.domain S.E S.hc k .g2),
        (W (strictEventIndex rho read) u).st.J ∈
          M.get_filtered_block_tree
            (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v).st.core).toFG := by
    intro k hrk hkend v hv
    have hdelayDomain := hdomDelay (Nat.lt_of_succ_le hrk)
    have hdomainCap : ((Hs (M.domain S.E S.hc k .g2)).sup fun x =>
        (W (inclusiveEventIndex rho (M.domain S.E S.hc k .g2)) x).st.core.h_max) ≤ Mh :=
      hcapR _ (by linarith)
        (lt_of_lt_of_le (Restated.domain_add_delta_lt_action_l56 facts S k .g2) (hmono hkend))
    have hroot : M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v).st.core).toFG =
        (W (strictEventIndex rho read) u).st.J :=
      (Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
        S Hs Xb hf hHs hHsXb hsb hfix hv hlo hdelayDomain (hdomHor hkend) hdomainCap).1
    rw [← hroot]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S rho
      (M.domain S.E S.hc k .g2) v _ (hmem _)
  have hcutAt : ∀ k : Round, k + 1 ≤ endpointRound →
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (k + 1) ≤ rho.horizon := by
    intro k hk
    show slotStart S.E.Δ (M.opening_slot S.hc (k + 1)) - S.E.Δ ≤ rho.horizon
    rw [facts.gr.gammaNeg1_eq_domain_g2_succ S k]
    exact hdomHor hk
  have hgradeAt : ∀ {k : Round}, r + 2 ≤ k → k ≤ endpointRound →
      ∀ v ∈ Hs (M.domain S.E S.hc k .g2),
        (W (strictEventIndex rho read) u).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v).st k .g2
              (W (strictEventIndex rho read) u).st.J ⇢ b → b = true := by
    intro k hrk hkend
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by romega⟩
    have hrk' : r + 1 ≤ k' := by romega
    have hk'end : k' ≤ endpointRound := by romega
    have hrk'' : r ≤ k' := by romega
    have hcover : Restated.ActionCarriersCoverOn M S rho Hs k'
        (W (strictEventIndex rho read) u).st.J
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k'))) := by
      intro v hv n hn A2 hA2 G hG
      have hroot : M.get_fg_root (M.toHealing n.st.core).toFG =
          (W (strictEventIndex rho read) u).st.J :=
        (actionReadFrom_fgRoot₆₉b facts S _ k' n hn).trans (hfixedCore hrk' hk'end v hv).1
      have h := Restated.Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt facts S rho
        v k' _ (hmem _) n hn A2 hA2 G hG
      rw [hroot] at h
      exact h
    exact Restated.namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn facts
      S Hs Xb hf hHs hHsXb hmajority hcover
      (hpost.trans (hreadAction.trans (hmono hrk'')))
      (hcutAt k' hkend)
      (htargetActiveAt (k := k' + 1) (by romega) hkend)
      (hdomainActiveAt (k := k' + 1) (by romega) hkend)
      (hA k' (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (hlo.trans hreadAction)
        (Nat.lt_of_succ_le hrk'))) (hlo.trans (hreadAction.trans (hmono hrk'')))
      (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)
  have htimeoutAt : ∀ {entry q : Round} {B : NamedBlock V},
      Restated.NamedRawOpeningLifecycleAtOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs Xb entry B →
      r + 1 ≤ entry →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S entry) →
      S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (entry + 1)) →
      entry + 2 + delayExtra ≤ q →
      r + 3 ≤ q →
      q ≤ endpointRound →
      Restated.ProposerCarrierAtOn M S Hs q →
      Block.Preceq (W (strictEventIndex rho read) u).st.J B.erase →
      (M.derive_named S.E S.cfg B).h = Mh →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c →
      ∀ Q : NamedBlock V, M.proposal_with (M.gradeContract c)
          Protocol.ProposalRowSource.poolAndCarried S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q)))
          (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
              (S.E.proposer (M.opening_slot S.hc q))).st
            (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some Q →
      ∀ P' : NamedBlock V, NamedBlock.parent? Q = some P' →
        (M.derive_named S.E S.cfg P').T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q := by
    intro entry q B hlifecycle hrEntry hreadBase hpostNext hspace hqlo hqEnd
      hcarrier hJB hBheight c hc Q hQ P' hP'
    have hq : 0 < q := by romega
    have hprevLower : entry + 1 ≤ q - 1 := by romega
    have hprevAdd : q - 1 + 1 = q := by romega
    have hrq : r < q := by romega
    have hlockGrade : r + 2 ≤ q - 1 := by romega
    have hqPredPos : 0 < q - 1 := by romega
    have hqPredEnd : q - 1 ≤ endpointRound := by romega
    have hqTwo : 2 ≤ q := by romega
    have hr1Q : r + 1 ≤ q := by romega
    have hr1QPred : r + 1 ≤ q - 1 := by romega
    have hthin : Mh - 1 ≤ (M.derive_named S.E S.cfg B).h := by
      rw [hBheight]
      exact Nat.sub_le Mh 1
    obtain ⟨hformsAll, hwindowPrev⟩ := Restated.gradeFormsAt_persist_of_fixedRoot_noRiseOn facts
      S Hs Xb hf hHs hHsXb hfb hfix hlifecycle.gradeNext hlifecycle.runBlock hpost hreadBase
        hprevLower (hhorAt hqPredEnd)
        (hcapA (Nat.le_of_succ_le hr1QPred) hqPredEnd) hJB hthin
        (fun r' hlo' hhi => hfixedCore (k := r') (by romega) (by romega))
        hlo (hloOpenAt _ (by romega)) hA
    have hformsPrev := hformsAll (q - 1) hprevLower (Nat.le_refl _)
    have hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
      hpostNext.trans (hmono hprevLower)
    have hloPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
      hloAt _ (hreadBase.trans (hmono ((Nat.le_succ entry).trans hprevLower)))
    have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon := by
      have h := hcutAt (q - 1) (by romega)
      rwa [hprevAdd] at h
    have hactionB : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w) (q - 1),
        B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
      fun w hw => Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S
        (v := w) _ (hmem _) (hwindowPrev w hw)
    have hproposalHor : M.proposal_time S.E
        ((M.opening_slot S.hc q)) ≤ rho.horizon :=
      (hpropAction q).trans (hhorAt hqEnd)
    have hproposalDelay := hpropDelay hrq
    have hproposalCap := hpropCap hrq hqEnd
    have hgatQ := hpropLo hrq
    obtain ⟨hpostCone, hlock⟩ := Restated.fixedRootConeRootLock_at_windowRoundOn facts
      S Hs Xb hf hHs hHsXb hcom hfb hfix hpost hreadAction hqlo hqEnd hendHor hcapEnd
        (hgradeAt hlockGrade hqPredEnd) hlo hloOpen
    have hformsJ := hgradeAt hlockGrade hqPredEnd
    have hwindowJ := htargetActiveAt hr1QPred hqPredEnd
    have hdomainWindowJ := hdomainActiveAt hr1Q hqEnd
    have hactiveActionJ := htargetActiveAt hr1Q hqEnd
    have hpropProposal : S.E.proposer ((M.opening_slot S.hc q)) ∈
        Hs (M.proposal_time S.E ((M.opening_slot S.hc q))) :=
      hpropPick hcarrier _ (hproposalConf _)
    have hpropConf : S.E.proposer ((M.opening_slot S.hc q)) ∈
        Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) :=
      hpropPick hcarrier _ le_rfl
    have hpropPrev : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :=
      hpropPick hcarrier _ (haConf q)
    have hloOpenQ := hloOpenAt (q - 1) hlockGrade
    obtain ⟨X, hX⟩ := nodeAnchor_nonempty₆₉b facts S
      (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c) q
    obtain ⟨hXG1, hJX, hXfiltered⟩ :=
      Restated.relativeAnchor_of_fixedRootLockOn facts S Hs Xb hf hHs hHsXb hfb hfix hqTwo
        hformsJ hwindowJ hdomainWindowJ hlo hpostPrev hcut (hhorAt hqEnd) hactiveActionJ
        hpropProposal hproposalDelay hproposalHor hproposalCap hloPrev hloOpenQ
        (hA (q - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (hlo.trans hreadAction)
          (Nat.lt_of_succ_le hr1QPred)))
        c hc X hX
    have hparents :=
      Restated.fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relativeOn facts
        S Hs Xb hf hHs hHsXb hcom hfb hfix hqTwo hformsJ hwindowJ hdomainWindowJ
          hactiveActionJ hlock hlo hproposalDelay hproposalHor hproposalCap
            hpostCone hloPrev hpropProposal c hc hX hXG1 hXfiltered hJX hloOpenQ
            (hA (q - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
              (hlo.trans hreadAction) (Nat.lt_of_succ_le hr1QPred)))
    obtain ⟨n, hn, A2, hA2, G, hG⟩ := exists_actionSG₆₉b facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
        (S.E.proposer ((M.opening_slot S.hc q)))) (q - 1)
    have hBG : Block.Preceq B.erase G :=
      formsW_preceq_actionSGBlockAt₆₉b facts S Hs Xb hf hHs hHsXb
        (r := q - 1) hqPredPos (hhorAt hqPredEnd) hformsPrev
        (hHs _ _ (facts.gr.domain_le_a S (q - 1) .g0) hpropPrev) n hn
        (hactionB _ hpropPrev n hn) hloOpenQ A2 hA2 G hG
    obtain ⟨I, P, hI, hPparent, hPerase⟩ := proposalParentInput₆₉b facts S
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q)))
      (M.opening_slot S.hc q) (M.proposal_time S.E (M.opening_slot S.hc q)) c hQ
    have hGP : Block.Preceq G P.erase := by
      rw [hPerase]
      exact hparents.actionTargetParent _ hpropPrev n hn A2 hA2 G hG c hc I hI
    have hBParentErase : Block.Preceq B.erase P.erase := preceq_trans_Preceq hBG hGP
    obtain ⟨B', hB'P, hB'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift P hBParentErase
    have hspos : 0 < (M.opening_slot S.hc q) :=
      facts.gr.opening_slot_pos_of_round_pos S.hc hq
    have hQRun : Restated.RunBlockOn M S rho W Xb Q :=
      Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
        ((M.opening_slot S.hc q)) hspos hpropConf hproposalHor hgatQ
        (fun j hj => hf.tick_outcome j _ _ hj) (hpropRun hrq hpropProposal) c hc hQ
    have hPRun : Restated.RunBlockOn M S rho W Xb P :=
      Restated.blockInRun_of_ancestorOn facts S rho W Xb hQRun
        ((hpf% fixedRootNamedParent_preceq_of_parent?) hPparent)
    have hB'eq : B' = B :=
      Restated.fixedRootNamed_run_eq_of_eraseOn facts hf
        (Restated.blockInRun_of_ancestorOn facts S rho W Xb hPRun hB'P)
        hlifecycle.runBlock hB'erase
    have hBP : NamedBlock.Preceq B P := by
      simpa only [hB'eq] using hB'P
    have hlowerP : Mh ≤ (M.derive_named S.E S.cfg P).h := by
      rw [← hBheight]
      exact facts.cs.derive_height_mono S.E S.cfg hBP
    have hupperP : (M.derive_named S.E S.cfg P).h ≤ Mh :=
      (facts.cs.derive_height_mono S.E S.cfg
        ((hpf% fixedRootNamedParent_preceq_of_parent?) hPparent)).trans
        ((Restated.honestProposedBlock_height_le_honestHMaxAtOn facts
          S Hs Xb hf hHs hspos hpropConf hproposalHor c hc hQ hgatQ
          (fun j hj => hf.tick_outcome j _ _ hj) (hpropRun hrq hpropProposal)).trans hproposalCap)
    have hsameHeight : (M.derive_named S.E S.cfg P).h =
        (M.derive_named S.E S.cfg B).h := by
      rw [hBheight]
      exact Nat.le_antisymm hupperP hlowerP
    obtain ⟨ce, hce, hBe⟩ := hlifecycle.proposal
    exact Restated.laterOpening_timeoutMature_of_sameHeightOn facts
      S Hs Xb hf hdelay hlifecycle.roundPositive hspace
        (some_mem_proposedBlockAt₆₉b facts S hf (M.opening_slot S.hc entry) ce hce hBe)
        (hmem _) c hc hQ hPparent hBP hsameHeight P' hP'
  have hclaimOneRound : r + 4 + gap ≤ endpointRound := by romega
  rcases _of_lifecycle hfix hpost hreadAction (hhorAt hclaimOneRound) hlo ht₀ hloOpen with
    hrise | ⟨q1, hq1lo, hq1hi, hcarrier1, _hformsJ1, hlock1, B1, _hB1, hpacket1⟩
  · exact hliftA (by romega) hclaimOneRound hrise
  · have hq1pos : 0 < q1 := by romega
    have hq1End : q1 ≤ endpointRound := by romega
    have hq1PredLower : r + 1 ≤ q1 - 1 := by romega
    have hrOneQ1 : r + 1 ≤ q1 := by romega
    have hrQ1 : r ≤ q1 := by romega
    have hrltQ1 : r < q1 := by romega
    have hclaimTwoRound : q1 + delayExtra + 4 + gap ≤ endpointRound := by romega
    have hq1PredAdd : q1 - 1 + 1 = q1 := by romega
    have hq1PredEnd : q1 - 1 ≤ endpointRound := by romega
    have hactionExact1 := hfixedAt hq1PredLower hq1PredEnd
    have hlifecycle1 : Restated.NamedRawOpeningLifecycleAtOn M S rho W
        (fun t => W (strictEventIndex rho t)) Hs Xb q1 B1 := by
      have h := hpacket1.lifecycle
      rw [hq1PredAdd] at h
      exact h
    have hreadAction2 : read ≤ (Restated.Vocabulary.Execution.Setup.a M S q1) :=
      hreadAction.trans (hmono hrQ1)
    obtain ⟨hJB1, hB1pred | hB1exact⟩ :=
      Restated.fixedRootClaimFour_height_pred_or_currentOn facts
        S Hs Xb hf hHs hfix hq1pos hpacket1 hactionExact1
          (hpropCap hrltQ1 hq1End) (hpropLo hrltQ1)
          (hpropRun hrltQ1 (hpropPick hcarrier1 _ (hproposalConf _)))
    ·
      have hpostQ1 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q1) := hpost.trans hreadAction2
      have hreadAction2Wait : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q1 + delayExtra)) :=
        hreadAction2.trans (hmono (Nat.le_add_right q1 delayExtra))
      rcases _of_lifecycle hfix hpost hreadAction2Wait
          (hhorAt hclaimTwoRound) hlo ht₀ (hloOpenAt (q1 + delayExtra + 2) (by romega)) with
        hrise2 |
          ⟨q2, hq2lo, hq2hi, hcarrier2, _hformsJ2, hlock2, B2, _hB2, hpacket2⟩
      · exact hliftA (by romega) hclaimTwoRound hrise2
      · have hq2pos : 0 < q2 := by romega
        have hq1q2 : q1 < q2 := by romega
        have hq2End : q2 ≤ endpointRound := by romega
        have hq2PredLower : r + 1 ≤ q2 - 1 := by romega
        have hrQ2 : r ≤ q2 := by romega
        have hrltQ2 : r < q2 := by romega
        have hq2PrevLower : q1 + 1 ≤ q2 - 1 := by romega
        have hq2PredPos : 0 < q2 - 1 := by romega
        have hq2Spacing : q1 + 2 + delayExtra ≤ q2 := by romega
        have hq2PredEnd : q2 - 1 ≤ endpointRound := by romega
        have hq2PredAdd : q2 - 1 + 1 = q2 := by romega
        have hr2Q2Pred : r + 2 ≤ q2 - 1 := by romega
        have hactionExact2 := hfixedAt hq2PredLower hq2PredEnd
        have hlifecycle2 : Restated.NamedRawOpeningLifecycleAtOn M S rho W
            (fun t => W (strictEventIndex rho t)) Hs Xb q2 B2 := by
          have h := hpacket2.lifecycle
          rw [hq2PredAdd] at h
          exact h
        have hloProposal2 := hpropLo hrltQ2
        have hcapProposal2 := hpropCap hrltQ2 hq2End
        obtain ⟨hJB2, hB2cases⟩ :=
          Restated.fixedRootClaimFour_height_pred_or_currentOn facts
            S Hs Xb hf hHs hfix hq2pos hpacket2 hactionExact2 hcapProposal2 hloProposal2
            (hpropRun hrltQ2 (hpropPick hcarrier2 _ (hproposalConf _)))
        have hreadAction3 : read ≤ (Restated.Vocabulary.Execution.Setup.a M S q2) :=
          hreadAction.trans (hmono hrQ2)
        have hprop2 : S.E.proposer ((M.opening_slot S.hc q2)) ∈
            Hs (M.proposal_time S.E ((M.opening_slot S.hc q2))) :=
          hHs _ _ (hproposalConf _) hlifecycle2.proposerHonest
        have hfixedProposal2 :=
          Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
            S Hs Xb hf hHs hHsXb hsb hfix hprop2 hlo (hpropDelay hrltQ2)
              hlifecycle2.proposalInHorizon hcapProposal2
        have hrootDuty2 : M.get_fg_root
            (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q2)))
                (S.E.proposer (M.opening_slot S.hc q2))).st.core
              (M.proposal_time S.E (M.opening_slot S.hc q2)))).toFG =
              (W (strictEventIndex rho read) u).st.J :=
          (tickStore_fgRoot₆₉b facts _ _).trans hfixedProposal2.1
        have hmaxDuty2 : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q2)))
              (S.E.proposer (M.opening_slot S.hc q2))).st.core
            (M.proposal_time S.E (M.opening_slot S.hc q2))).h_max = Mh :=
          (tickStore_h_max₆₉b facts _ _).trans hfixedProposal2.2
        have hcontinue : (M.derive_named S.E S.cfg B2).h = Mh →
            Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
              (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) := by
          intro hB2exact
          have hpostB2 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q2 + 1)) :=
            hpost.trans (hreadAction.trans (hmono (by romega)))
          have htrigger3 : q2 + 1 < q2 + 2 + delayExtra := by romega
          have hwindow3 : q2 + 2 + delayExtra + gap ≤ endpointRound := by romega
          obtain ⟨q3, hq3lo, hq3hi, hcarrier3⟩ := hrec (q2 + 2 + delayExtra)
            ((ht₀.trans (hreadAction3.trans (hmono (Nat.le_succ q2)))).trans
              ((Int.le_add_of_nonneg_right hΔ.le).trans
                (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S htrigger3)))
            ((Restated.Vocabulary.Proofs.HealingLemmas.openingProposal_window_le_action facts S (q2 + 2 + delayExtra) gap).trans
              ((hmono hwindow3).trans hendHor))
          have hq3End : q3 ≤ endpointRound := by romega
          have hrThreeQ3 : r + 3 ≤ q3 := by romega
          obtain ⟨c3, hc3⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q3)))
              (S.E.proposer (M.opening_slot S.hc q3))).st.core.toHealing
            (M.proposal_time S.E (M.opening_slot S.hc q3))
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q3)))
              (S.E.proposer (M.opening_slot S.hc q3))).cache
          obtain ⟨Q3, hQ3⟩ := proposal_some_along₆₉b facts S hf (M.opening_slot S.hc q3) c3 hc3
          have hmature3 := htimeoutAt hlifecycle2 (by romega) hreadAction3 hpostB2
            hq3lo hrThreeQ3 hq3End hcarrier3 hJB2 hB2exact c3 hc3 Q3 hQ3
          exact Restated.exactHeightAttempt_rise_of_rebased_of_fixedRoot_noRiseOn facts
            S Hs Xb hf hHs hHsXb hfb hfix hlifecycle2.gradeNext hlifecycle2.runBlock hpost
              hreadAction3 (by romega) hcarrier3
              hmature3 hB2exact hJB2
              (fun r' hlo' hhi => hfixedCore (k := r') (by romega) (by romega))
              (hmono hq3End) hendHor hcapEnd
              hlo (hloOpenAt _ (by romega)) hA c3 hc3 hQ3
        rcases hB2cases with hB2pred | hB2exact
        ·
          have hthinB1 : Mh - 1 ≤
              (M.derive_named S.E S.cfg B1).h := by
            rw [hB1pred]
          obtain ⟨hformsB1, hactiveB1⟩ :=
            Restated.gradeFormsAt_persist_of_fixedRoot_noRiseOn facts
              S Hs Xb hf hHs hHsXb hfb hfix hlifecycle1.gradeNext hlifecycle1.runBlock
                hpost hreadAction2 hq2PrevLower (hhorAt hq2PredEnd)
                (hcapA (Nat.le_of_succ_le hq2PredLower) hq2PredEnd)
                hJB1 hthinB1
                (fun r' hlo' hhi => hfixedCore (k := r') (by romega) (by romega))
                hlo (hloOpenAt _ (by romega)) hA
          have hformsB1Prev := hformsB1 (q2 - 1) hq2PrevLower (Nat.le_refl _)
          have hactionB1 : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q2 - 1))),
              ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
                (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q2 - 1))) v) (q2 - 1),
              B1.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
            fun v hv => Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S
              (v := v) _ (hmem _) (hactiveB1 v hv)
          obtain ⟨c2, hc2, hP2⟩ := hlifecycle2.proposal
          obtain ⟨I2, P2, hI2, hP2parent, hP2erase⟩ := proposalParentInput₆₉b facts S
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q2)))
              (S.E.proposer (M.opening_slot S.hc q2)))
            (M.opening_slot S.hc q2) (M.proposal_time S.E (M.opening_slot S.hc q2)) c2 hP2
          obtain ⟨v0, hv0⟩ : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q2 - 1)))).Nonempty :=
            Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _
          obtain ⟨n0, hn0, A2, hA2, G, hG⟩ := exists_actionSG₆₉b facts S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q2 - 1))) v0) (q2 - 1)
          have hB1Carrier : Block.Preceq B1.erase G :=
            formsW_preceq_actionSGBlockAt₆₉b facts S Hs Xb hf hHs hHsXb
              (r := q2 - 1) hq2PredPos (hhorAt hq2PredEnd) hformsB1Prev
              (hHs _ _ (facts.gr.domain_le_a S (q2 - 1) .g0) hv0) n0 hn0
              (hactionB1 v0 hv0 n0 hn0) (hloOpenAt _ hr2Q2Pred) A2 hA2 G hG
          have hCarrierParent : Block.Preceq G P2.erase := by
            have h := hpacket2.actionTargetParent v0 hv0 n0 hn0 A2 hA2 G hG
            rw [hq2PredAdd] at h
            rw [hP2erase]
            exact h c2 hc2 I2 hI2
          have hB1Parent : Block.Preceq B1.erase P2.erase :=
            preceq_trans_Preceq hB1Carrier hCarrierParent
          obtain ⟨B1', hB1'P, hB1'erase⟩ :=
            Proofs.NamedAncestry.erased_ancestor_lift P2 hB1Parent
          have hP2Run : Restated.RunBlockOn M S rho W Xb P2 :=
            Restated.blockInRun_of_ancestorOn facts S rho W Xb hlifecycle2.runBlock
              ((hpf% fixedRootNamedParent_preceq_of_parent?) hP2parent)
          have hB1'Run : Restated.RunBlockOn M S rho W Xb B1' :=
            Restated.blockInRun_of_ancestorOn facts S rho W Xb hP2Run hB1'P
          have hB1'eq : B1' = B1 :=
            Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hB1'Run hlifecycle1.runBlock hB1'erase
          have hlowerP2 : (M.derive_named S.E S.cfg B1).h ≤
              (M.derive_named S.E S.cfg P2).h := by
            have hstep := facts.cs.derive_height_mono S.E S.cfg hB1'P
            rwa [hB1'eq] at hstep
          have hupperP2 : (M.derive_named S.E S.cfg P2).h ≤
              (M.derive_named S.E S.cfg B2).h :=
            facts.cs.derive_height_mono S.E S.cfg
              ((hpf% fixedRootNamedParent_preceq_of_parent?) hP2parent)
          have hsameHeight2 :
              (M.derive_named S.E S.cfg P2).h =
                (M.derive_named S.E S.cfg B1).h := by romega
          have hprop2Prev : S.E.proposer ((M.opening_slot S.hc q2)) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q2 - 1))) :=
            hpropPick hcarrier2 _ (haConf q2)
          obtain ⟨c1, hc1, hP1⟩ := hlifecycle1.proposal
          have hmature2 := Restated.opening_timeoutMature_of_persistedGradeOn facts
            S Hs Xb hf hHs hHsXb hdelay hq1pos hq2Spacing
              (some_mem_proposedBlockAt₆₉b facts S hf (M.opening_slot S.hc q1) c1 hc1 hP1)
              hlifecycle1.runBlock hformsB1Prev (hactionB1 _ hprop2Prev)
              (hhorAt hq2PredEnd) hpacket2 hP2parent hsameHeight2 (hloOpenAt _ hr2Q2Pred)
          have hJnEntry : (M.derive_named S.E S.cfg Jn).T_h.root =
              (W (strictEventIndex rho read) u).st.J.root :=
            Restated.namedJustification_targetRoot_of_fixedRootOn facts S Hs Xb hf
              hfix hJnErase hJnRun hJnHeight
          have hJnB1 : NamedBlock.Preceq Jn B1 := by
            obtain ⟨Jn', hJn'B1, hJn'erase⟩ :=
              Proofs.NamedAncestry.erased_ancestor_lift B1
                (show Block.Preceq Jn.erase B1.erase by
                  rw [hJnErase]; exact hJB1)
            have hJn'eq : Jn' = Jn :=
              Restated.fixedRootNamed_run_eq_of_eraseOn facts hf
                (Restated.blockInRun_of_ancestorOn facts S rho W Xb hlifecycle1.runBlock hJn'B1) hJnRun
                hJn'erase
            simpa only [hJn'eq] using hJn'B1
          have hB1entry :
              (M.derive_named S.E S.cfg B1).T_h.root =
                (W (strictEventIndex rho read) u).st.J.root := by
            rw [← hJnEntry]
            exact congrArg Block.root
              (facts.cs.entry_eq_on_plateau S.E S.cfg hJnB1
                (by rw [hJnHeight, hB1pred])).symm
          have hdelayPlusTwo : read + S.E.Δ ≤
              M.proposal_time S.E
                ((M.opening_slot S.hc q1) + 2) :=
            (Int.add_le_add_right hreadAction2 S.E.Δ).trans
              (Restated.Vocabulary.Proofs.HealingSurface.action_add_delta_le_plusTwo_proposal_time facts S q1)
          have hrunPlusTwo : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
              (S.E.proposer ((M.opening_slot S.hc q1) + 2))
              (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) →
              M.awake_for_grade1 S (S.E.proposer ((M.opening_slot S.hc q1) + 2))
                (W j (S.E.proposer ((M.opening_slot S.hc q1) + 2)))
                (M.round_of S.hc ((M.opening_slot S.hc q1) + 2)) := by
            intro j hj
            have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc ((M.opening_slot S.hc q1) + 2)) .g1 -
                S.E.Δ := by
              rw [facts.gr.round_of_opening_slot_add S.hc q1
                (Nat.lt_of_lt_of_le (by decide : 2 < 3) S.hc.R_ge_three)]
              have h1 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
                (hlo.trans hreadAction) hrltQ1
              have h2 := facts.gr.q10_early_g2_le_early_g1 S q1
              linarith
            exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
              (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _)
                (hcarrier1 2 (by decide))) hwin
          have hplusTwoAll := Restated.fixedRoot_plusTwoProposal_factsOn facts
            S Hs Xb hf hHs hHsXb hcom hfix hlo hdelayPlusTwo hcarrier1
              (show q1 + 1 ≤ endpointRound by romega) hendHor hcapEnd
              (fun j hj => hf.tick_outcome j _ _ hj) hrunPlusTwo
          obtain ⟨cp, hcp⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
            (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
              (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.core.toHealing
            (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))
            (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
              (S.E.proposer ((M.opening_slot S.hc q1) + 2))).cache
          obtain ⟨op, hop⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp)
            Protocol.ProposalRowSource.poolAndCarried S.E S.hc
            (S.node (S.E.proposer ((M.opening_slot S.hc q1) + 2)))
            (M.ns_setClock S.E
              (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
                (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st
              (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)))
          obtain ⟨Bplus, rfl, hBplusRun, hBplusProp, hBplusHor, hBplusRoot, hBplusMax⟩ :=
            hplusTwoAll cp hcp op hop
          have hB1ParentRows : Block.Preceq B1.erase B2.parent.erase := by
            rw [parent_eq_of_parent?₆₉b hP2parent]
            exact hB1Parent
          have hsourceToParent :=
            _of_sourceToParent hfix hlo hreadAction hq1lo hreadAction2 hq1pos
              hq1q2 hq2End
              hcarrier1 hpostQ1 hendHor hcapEnd
              ⟨Bplus, ⟨cp, hcp, hop⟩, hBplusRun, hBplusProp, hBplusHor, hBplusRoot, hBplusMax⟩
              hpacket1 hpacket2
              hB1pred hlock1 hlock2 (@hfixedAt) hrootDuty2 hmaxDuty2 hformsB1Prev
              hactionB1 hB1ParentRows hmature2 hq2Spacing (hloOpenAt _ hr2Q2Pred) hA
          have hloQ2Pred : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q2 - 1)) :=
            hloAt _ (hreadAction2.trans (hmono ((Nat.le_succ q1).trans hq2PrevLower)))
          have hB1ParentNamed : NamedBlock.Preceq B1 B2.parent := by
            have h := Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf
              hlifecycle1.runBlock hP2Run hB1Parent
            rw [parent_eq_of_parent?₆₉b hP2parent]
            exact h
          rcases Restated.fixedRootFresh_predLifecycle_promotion_namedOn facts S Hs Xb hf hHs hHsXb hfb hfix
              hq2pos hq2PredPos hlifecycle1.runBlock hB1pred hB1entry hB1ParentNamed
              hsourceToParent hformsB1Prev hactiveB1 hpacket2 hmature2 hloQ2Pred
              (hloOpenAt _ hr2Q2Pred)
              (hA (q2 - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
                (hlo.trans hreadAction) (Nat.lt_of_succ_le hq2PredLower))) with
            hB2exact | hrise2
          · exact hcontinue hB2exact
          · exact hliftR _ hloProposal2
              (lt_of_lt_of_le (Restated.openingProposal_add_delta_lt_action_l56 facts S q2) (hmono hq2End))
              hrise2
        · exact hcontinue hB2exact
    ·
      have htrigger2 : q1 < q1 + 2 + delayExtra := by romega
      have hwindow2 : q1 + 2 + delayExtra + gap ≤ endpointRound := by romega
      obtain ⟨q2, hq2lo, hq2hi, hcarrier2⟩ := hrec (q1 + 2 + delayExtra)
        ((ht₀.trans hreadAction2).trans
          ((Int.le_add_of_nonneg_right hΔ.le).trans
            (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S htrigger2)))
        ((Restated.Vocabulary.Proofs.HealingLemmas.openingProposal_window_le_action facts S (q1 + 2 + delayExtra) gap).trans
          ((hmono hwindow2).trans hendHor))
      have hq2End : q2 ≤ endpointRound := by romega
      have hrThreeQ2 : r + 3 ≤ q2 := by romega
      have hpostB1 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q1 + 1)) :=
        hpost.trans (hreadAction.trans (hmono (by romega)))
      obtain ⟨c2, hc2⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q2)))
          (S.E.proposer (M.opening_slot S.hc q2))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q2))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q2)))
          (S.E.proposer (M.opening_slot S.hc q2))).cache
      obtain ⟨Q2, hQ2⟩ := proposal_some_along₆₉b facts S hf (M.opening_slot S.hc q2) c2 hc2
      have hmature2 := htimeoutAt hlifecycle1 hrOneQ1 hreadAction2 hpostB1
        hq2lo hrThreeQ2 hq2End hcarrier2 hJB1 hB1exact c2 hc2 Q2 hQ2
      exact Restated.exactHeightAttempt_rise_of_rebased_of_fixedRoot_noRiseOn facts
        S Hs Xb hf hHs hHsXb hfb hfix hlifecycle1.gradeNext hlifecycle1.runBlock hpost
          hreadAction2 (by romega) hcarrier2
          hmature2 hB1exact hJB1
          (fun r' hlo' hhi => hfixedCore (k := r') (by romega) (by romega))
          (hmono hq2End) hendHor hcapEnd
          hlo (hloOpenAt _ (by romega)) hA c2 hc2 hQ2

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

/-- Under the premises of `fixedRootProgress_of_lifecycleOn` without its bounded-lifecycle
    hypothesis `_of_lifecycle`, the same conclusion: the largest `h_max` over the set for the
    endpoint's action instant in the world of `W` at that instant is greater than `Mh`. -/
theorem fixedRootProgress_of_rowsOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (_of_sourceToParent : ∀ {H : Height} {w : V} {read0 : Time} {r endpointRound q1 q' : Round} {B1 B2 : NamedBlock V}, Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read0 (W (strictEventIndex rho read0)) → lo ≤ read0 → read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) → r + 3 ≤ q1 → read0 ≤ (Restated.Vocabulary.Execution.Setup.a M S q1) → 0 < q1 → q1 < q' → q' ≤ endpointRound → Restated.ProposerCarrierAtOn M S Hs q1 → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q1) → (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon → ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x => (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) ≤ H → (∃ Bplus : NamedBlock V, (∃ cp : M.Cache, M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2)) (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).cache ⇢ cp ∧ M.proposal_with (M.gradeContract cp) Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer ((M.opening_slot S.hc q1) + 2))) (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) ⇢ some Bplus) ∧ Restated.RunBlockOn M S rho W Xb Bplus ∧ S.E.proposer ((M.opening_slot S.hc q1) + 2) ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q1) + 2)) ∧ M.proposal_time S.E ((M.opening_slot S.hc q1) + 2) ≤ rho.horizon ∧ M.get_fg_root (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.toHealing.toFG = (W (strictEventIndex rho read0) w).st.J ∧ (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q1) + 2))) (S.E.proposer ((M.opening_slot S.hc q1) + 2))).st.h_max = H) → Restated.NamedSGProposalLifecyclePacketOn M S rho W (fun t => W (strictEventIndex rho t)) (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q1)))) (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q1)))) Hs Xb (q1 - 1) ((M.opening_slot S.hc q1) - 1) B1 → Restated.NamedSGProposalLifecyclePacketOn M S rho W (fun t => W (strictEventIndex rho t)) (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q')))) (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q')))) Hs Xb (q' - 1) ((M.opening_slot S.hc q') - 1) B2 → (M.derive_named S.E S.cfg B1).h = H - 1 → Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q1 - 1) ((M.opening_slot S.hc q1) - 1) (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q1) - 1 + 1)))) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q1 - 1)))) → Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q' - 1) ((M.opening_slot S.hc q') - 1) (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q') - 1 + 1)))) (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)))) → (∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound → ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)), M.get_fg_root (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.toHealing.toFG = (W (strictEventIndex rho read0) w).st.J ∧ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.h_max = H) → M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q'))) (S.E.proposer (M.opening_slot S.hc q'))).st.core (M.proposal_time S.E (M.opening_slot S.hc q')))).toFG = (W (strictEventIndex rho read0) w).st.J → (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q'))) (S.E.proposer (M.opening_slot S.hc q'))).st.core (M.proposal_time S.E (M.opening_slot S.hc q'))).h_max = H → (∀ v ∈ Hs (M.domain S.E S.hc (q' - 1) .g2), B1.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) .g2)) v) ∧ ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) .g2)) v).st (q' - 1) .g2 B1.erase ⇢ b → b = true) → (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))), ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v) (q' - 1), B1.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) → Block.Preceq B1.erase B2.parent.erase → (∀ P : NamedBlock V, NamedBlock.parent? B2 = some P → (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q') → q1 + 2 + delayExtra ≤ q' → lo ≤ M.opening S.E S.hc (q' - 1 - S.hc.η_SG) → (∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) → ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))), ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))) v) (q' - 1), ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n (q' - 1) ⇢ some Q → ((M.toHealing n.st.core).σ Q).h ≤ (M.derive_named S.E S.cfg B2.parent).h) :
    ∀ {Mh : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read)) →
      S.E.t_GST ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) ≤ Mh →
      lo ≤ read → t₀ ≤ read →
      lo ≤ M.opening S.E S.hc (r + 2 - S.hc.η_SG) →
      Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun x =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpointRound)) x).st.core.h_max) :=
  Restated.fixedRootProgress_of_lifecycleOn facts S Hs Xb hf hHs hHsXb hcom hfb hrec hdelay hA
    (fun hfix hpost hreadAction hendHor hlo ht₀ hloOpen =>
      Restated.fixedHeightJustificationRoot_boundedProposalLifecycle_closedOn facts
        S Hs Xb hf hHs hHsXb hcom hfb hfix hpost hreadAction hrec hendHor hlo ht₀ hA hloOpen)
    _of_sourceToParent

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
open DecoupledConsensusModel.Proofs.Optimistic

/-- `omega` after unfolding `Round`, `Height` and `Slot` to `Nat`. -/
local macro "romega" : tactic => `(tactic| (dsimp only [Round, Height, Slot] at *; omega))

end

/-! ## Theorems named under the run-scoped height regimes -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every node state of the round-`r` action read computed from `before` holds `before`'s bodies. -/
private theorem actionReadFrom_bodies₆₉bn (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The round-`r` action read computed from any node state has a node state. -/
private theorem actionReadFrom_nonempty₆₉bn (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the events strictly before `t` are the first `strictEventIndex rho t`
    events. -/
private theorem strictFilter_eq_take₆₉bn (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
    (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
  · exact List.takeWhile_prefix _
  · intro e f hk hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, a tick at `t` has an index at least the number of events strictly before
    `t`. -/
private theorem strictEventIndex_le_tickIndex₆₉bn {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (Record.Event.tick v t)) :
    strictEventIndex rho t ≤ i := by
  by_contra hnot
  have hlt : i < strictEventIndex rho t := Nat.lt_of_not_ge hnot
  unfold strictEventIndex at hlt
  have hmem : Record.Event.tick v t ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [strictFilter_eq_take₆₉bn rho hsorted t]
    exact List.mem_of_getElem? (by
      rw [List.getElem?_take_of_lt hlt]
      exact hi)
  have himpossible := (List.mem_filter.mp hmem).2
  simp only [decide_eq_true_eq] at himpossible
  exact lt_irrefl t himpossible

/-- A named regime base along the path `W`, with the worlds `Wt` before each instant, is a
    run-scoped named regime base along `W` with the same `Wt`. -/
theorem NamedHeightRegimeBaseRunOn.ofNamed
    {S : Setup V} {rho : Record.Run V} {W : Nat → V → M.N} {Wt : Time → V → M.N}
    {Hs : Int → Finset V} {X Xb : Finset V}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (h : Restated.NamedHeightRegimeBaseOn M S rho W Wt Hs X Xb r0 blocked first Tprev) :
    Restated.NamedHeightRegimeBaseRunOn M S rho W Wt Hs X Xb r0 blocked first Tprev :=
  { crossing := h.crossing
    start := h.start
    positive := h.positive
    frame := h.frame
    oldRoot := fun a ta ha hemit hbefore R _ => h.oldRoot a ta ha hemit hbefore R }

/-- Under the bundle with path `W`, if `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read
    computed from `W (strictEventIndex rho (S.a r))`, and `D` is a body of `n`'s store, then `D` is
    a run block read through `Xb` along `W`. -/
theorem NamedHeightRegimeRunOn.actionBody_runBlock (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlockOn facts S Hs Xb hf hv hn hD

/-- Under the bundle with path `W`, the checkpoint `T` of a run-scoped named regime along `W` is a
    run block read through `Xb` along `W`, at height `blocked + 1`. -/
theorem NamedHeightRegimeRunOn.checkpoint_runBlock (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb r0
      blocked first i a ta Cfg T Tprev c0) :
    Restated.RunBlockOn M S rho W Xb T ∧
      (M.derive_named S.E S.cfg T).h = blocked + 1 := by
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₉bn facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  have hCfgRun : Restated.RunBlockOn M S rho W Xb Cfg :=
    Restated.NamedHeightRegimeRunOn.actionBody_runBlock facts S Hs Xb hf
      (hHsXb _ h.seed.signerHonest) hn (h.seed.sourceMem n hn)
  have hTrun : Restated.RunBlockOn M S rho W Xb T :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hCfgRun h.checkpointPreceq
  obtain ⟨K, hKCfg, hKerase, hKheight⟩ := facts.cs.entry_ancestor_same_height S.E S.cfg Cfg
  have hKrun : Restated.RunBlockOn M S rho W Xb K :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hCfgRun hKCfg
  have hTK : T = K :=
    Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hTrun hKrun
      (h.checkpointErase.trans hKerase.symm)
  refine ⟨hTrun, ?_⟩
  rw [hTK, hKheight, h.seed.sourceDerivedHeight]

/-- Under the bundle with path `W`, if `p ∈ X`, `n` is a node state of `p`'s round-`r` action read
    computed from `W (strictEventIndex rho (S.a r))`, and `n`'s store holds a body at height
    `blocked + 2`, then `r` is after the regime's source round. -/
theorem NamedHeightRegimeRunOn.round_succ_le_of_higherBlock (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (h : Restated.NamedHeightRegimeRunOn M S rho W Wt Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {p : V} (hp : p ∈ X) {r : Round} {B : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hBmem : B ∈ n.st.bodies)
    (hBh : (M.derive_named S.E S.cfg B).h = blocked + 1 + 1) :
    a.round + 1 ≤ r := by
  by_contra hnot
  have hle : r ≤ a.round := Nat.le_of_lt_succ (Nat.lt_of_not_le hnot)
  rw [actionReadFrom_bodies₆₉bn facts S _ _ n hn] at hBmem
  have hmaxB : blocked + 1 + 1 ≤
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.core.h_max := by
    have hbound := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p _ (hf.onePath _).1 B hBmem
    rw [hBh] at hbound
    exact hbound
  have hprefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < first := by
    have hle' := strictEventIndex_le_tickIndex₆₉bn hf.sorted h.seed.exactTick
    rw [h.seed.actionTime_eq] at hle'
    exact hle'.trans_lt h.seed.indexLtStop
  have hfrontier :
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.h_max ≤
        blocked + 1 :=
    (Restated.localHMax_le_honestHMaxBeforeIndexOn facts S rho X _ hp _ (hf.onePath _).1).trans
      (h.crossing.before _
        ((strict_filter_length_mono rho (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hle)).trans_lt
          hprefix))
  exact Nat.not_succ_le_self (blocked + 1) (hmaxB.trans hfrontier)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Under the bundle with path `W` and the weight bound, if `X` contains every set of the family
    from instant `0` and is inside `Xb`, `gstLagged S ≤ Γ_neg1 r0`,
    `lo + 4Δ·(R·readyLag) ≤ Γ_neg1 r0`, `lo ≤ opening (r0 − η_SG)` and a run-scoped named base holds
    along `W` at `blocked` with first crossing index `first`, then some attestation `a` sent at an
    index `i` starts a run-scoped named regime along `W` with source `Cfg`, checkpoint `T` and
    previous root `Tprev`, from round `a.round`. -/
theorem NamedHeightRegimeBaseRunOn.exists_regime_closed (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG)) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time) (Cfg T : NamedBlock V),
      Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs X Xb r0 blocked first i a ta Cfg T Tprev a.round := by
  classical
  have hcross : Restated.PrefixHeightCrossingWitnessOn M S rho W X Xb first blocked :=
    Restated.prefixHeightCrossingWitness_of_frontier_eqOn facts
      S Hs Xb X hf hXXb h.positive h.crossing.frontier
  have hT : ∀ (j : Nat) (e : Record.Event V), j < first → rho.events[j]? = some e →
      e.time ≤ rho.horizon := by
    intro j e _ hj
    exact (hf.in_horizon e (List.mem_of_getElem? hj)).2
  obtain ⟨i0, a0, t0, _hiStart0, hiStop0, haHon0, hiEvent0, hiOutput0, _hemit0, _hta0, hwit0⟩ :=
    Restated.prefixHeightCrossing_exactFGSelectorWitnessOn facts
      S Hs Xb X hf hHs (hbelow _ le_rfl) hT hcross
      (Restated.noLocalHeightPairBefore_of_frontier_ltOn facts S Hs Xb X hf hX h.start)
  have hrow0' : a0.height_pair.erase.height? = some (blocked + 1) := by
    obtain ⟨n0, hn0⟩ := (p63% actionReadFrom_nonempty₆₃w) facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a0.round)) a0.val_index)
      a0.round
    obtain ⟨o0, ho0⟩ := (p63% actionFGSource_nonempty₆₃w) facts S n0
    obtain ⟨B0, J0, -, -, -, -, -, hrow0⟩ := (hwit0 n0 hn0).2 o0 ho0
    rcases hrow0 with ht | ht <;> exact ht ▸ rfl
  have ht0Hor : t0 ≤ rho.horizon :=
    (hf.in_horizon _ (List.mem_of_getElem? hiEvent0)).2
  have haHonT0 : a0.val_index ∈ Hs t0 := hHs _ _ ht0Hor haHon0
  let P : Round → Prop := fun r =>
    ∃ (j : Nat) (a : NamedAttestation V) (ta : Time),
      a.round = r ∧ j < first ∧ a.val_index ∈ Hs ta ∧
        rho.events[j]? = some (Record.Event.tick a.val_index ta) ∧
        (∃ out : M.N × List (NamedObject V),
          M.tick S a.val_index (W j a.val_index) ta ⇢ out ∧ W (j + 1) a.val_index = out.1 ∧
            Object.attest a ∈ out.2) ∧
        a.height_pair.erase.height? = some (blocked + 1)
  have hex : ∃ r, P r :=
    ⟨a0.round, i0, a0, t0, rfl, hiStop0, haHonT0, hiEvent0, hiOutput0, hrow0'⟩
  obtain ⟨i, a, ta, har, hi, haHon, hevent, hout, hrow⟩ := Nat.find_spec hex
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index
      (Object.attest a) ta := ⟨i, hevent, hout⟩
  have htime : ta = Restated.Vocabulary.Execution.Setup.a M S a.round :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
  have hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round := by
    intro b tb hbHon hbemit hbrow
    by_contra hnot
    have hlt : b.round < a.round := Nat.lt_of_not_ge hnot
    have htb : tb < ta := by
      rw [(Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hbemit).2,
        htime]
      exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S hlt
    obtain ⟨j, hj, hbout⟩ := hbemit
    have hjFirst : j < first :=
      (Restated.attestationIndex_lt_of_time_ltOn facts hf hj hevent htb).trans hi
    have hPb : P b.round := ⟨j, b, tb, rfl, hjFirst, hbHon, hj, hbout, hbrow⟩
    have hle := Nat.find_min' hex hPb
    rw [← har] at hle
    exact (not_le_of_gt hlt) hle
  have hiStart : inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ i := by
    by_contra hnot
    obtain ⟨out, hout1, hout2, hout3⟩ := hout
    exact Restated.noLocalHeightPairBefore_of_frontier_ltOn facts S Hs Xb X hf hX
      (h.start.trans_le (Nat.le_succ blocked)) (Nat.lt_of_not_ge hnot) haHon hevent out hout1
      hout2 hout3 hrow
  have hr0Round : r0 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < Restated.Vocabulary.Execution.Setup.a M S r0 := by
      rw [htime]
      exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_of_not_ge hnot)
    have htimeLe : Restated.Vocabulary.Execution.Setup.a M S r0 ≤ ta :=
      Restated.le_time_of_index_ge_of_sorted hf.sorted
        ((strictEventIndex_le_inclusiveEventIndex rho _).trans hiStart) hevent
    exact (not_le_of_gt htimeLt) htimeLe
  have hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev a.round := h.frame a.round hminimal
  have hfrontierAt : (X.sup fun u => (W i u).st.h_max) < blocked + 2 :=
    Nat.lt_succ_of_le (h.crossing.before i hi)
  obtain ⟨Cfg, T0, hseed, hpostPrev, hG1⟩ :=
    Restated.honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrameOn
      facts S Hs Xb X hf hHs hHsXb hX hXXb hgst hframe hiStart hi haHon hevent hout hrow
      hfrontierAt hgstLo (hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
        (Nat.sub_le_sub_right hr0Round _)))
  have ready := hseed.ready_of_postGSTStart facts hf hgst
    (strictEventIndex_le_inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0))
  obtain ⟨n, hn⟩ := (p63% actionReadFrom_nonempty₆₃w) facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Cfg.erase := by
    obtain ⟨oa, hoa⟩ := (p63% actionFGSource_nonempty₆₃w) facts S n
    have hoa' := hseed.exactFGSource n hn oa hoa
    rw [hoa'] at hoa
    exact hoa
  obtain ⟨K, _hKmem, hKerase, hKheight, hKCfg, hKrun⟩ :=
    Restated.action_named_checkpointOn facts S Hs Xb hf (hHsXb _ hseed.signerHonest) hn
      (hseed.sourceMem n hn)
  have hKT0 : K.erase = T0 := hKerase.trans hseed.checkpointDerived.symm
  have hseedK : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) first blocked i
      a ta Cfg K.erase := by
    rw [hKT0]
    exact hseed
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index a.round hsigner
      (Nat.le_sub_one_of_lt ((p63% actionPrefix_lt₆₃w) facts hf hseed))
      ((p63% actionHorizon₆₃w) hf hseed) n hn Cfg (hseed.sourceMem n hn) hsrc
      hseed.sourceDerivedHeight
  have hTprevK : NamedBlock.Preceq Tprev K := by
    rcases preceq_linear_Preceq (Proofs.NamedWire.erase_preceq hTprevCfg)
        (Proofs.NamedWire.erase_preceq hKCfg) with hprevK | hKprev
    · obtain ⟨Q, hQK, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift K hprevK
      have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
        Restated.blockInRun_of_ancestorOn facts S rho W Xb hKrun hQK
      have hQTprev : Q = Tprev :=
        Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hQrun hframe.prevRun hQerase
      rw [← hQTprev]
      exact hQK
    · obtain ⟨Q, hQTprev, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift Tprev hKprev
      have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
        Restated.blockInRun_of_ancestorOn facts S rho W Xb hframe.prevRun hQTprev
      have hQK : Q = K :=
        Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hQrun hKrun hQerase
      have hKTprev : NamedBlock.Preceq K Tprev := by
        rw [← hQK]
        exact hQTprev
      have hmono := facts.cs.derive_height_mono S.E S.cfg hKTprev
      rw [hKheight, hseed.sourceDerivedHeight] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
  have hKsourceHeight : (M.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight.trans hseed.sourceDerivedHeight
  refine ⟨i, a, ta, Cfg, K, {
    seed := hseedK
    checkpointPreceq := hKCfg
    checkpointErase := hKerase
    crossing := Restated.FirstHeightProgressAtOn.toWindow h.crossing
    frame := hframe
    c0le := Nat.le_refl _
    ready := ready
    postPrev := hpostPrev
    g1 := hG1
    pred := ?_
    minimal := hminimal }⟩
  intro b tb hb hbemit hbefore R hRrun hRh hpair nb hnb hR w hw time hfrontier hroot
  exact h.oldRoot b tb hb hbemit hbefore R hRrun hRh hpair nb hnb hR w hw time
    hfrontier hroot K hKrun hKsourceHeight hTprevK

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
