import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_StoreFinalityCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The proposer's read and its proposal

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a proposer's read
satisfies the named-store root invariant, the proposal reader is total, and the proposed block has
the slot, proposer, parent, height and included attestations that the read and the proposal input
give. Also when the block handler keeps a fresh block as a named body, and the SG root and the
finalized block as ancestors of the head.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- Every node state slot `s`'s proposer can hold at slot `s`'s proposal time satisfies the
    named-store root invariant. -/
theorem Vocabulary.Proofs.HealingSurface.proposerReadAt_invariant (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) : ∀ w₁ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant M S.E S.cfg w₁.st := by
  rintro _ ⟨w, hw, c, -, rfl⟩
  rewrite [facts.nd.mkNode_st]
  have h := Restated.Vocabulary.Proofs.NamedStoreRoots.invariant_clock facts S.E S.cfg
    (w (S.E.proposer s)).st (M.proposal_time S.E s)
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      (M.proposal_time S.E s) (S.E.proposer s) w hw).1.1
  unfold Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant
    Restated.Vocabulary.Proofs.NamedStore.Coherent Restated.Vocabulary.Proofs.NamedStore.TreeView
    Restated.Vocabulary.Proofs.NamedStore.ErasureUnique
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed
    Restated.Vocabulary.Proofs.NamedStore.PoolView Restated.Vocabulary.Proofs.NamedStore.DerivedView
    Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree at h ⊢
  simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView, facts.nd.store_with_cache_bodies,
    facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_sg_votes,
    facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau,
    facts.nd.store_with_cache_core_attestations]
  exact h

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- Every value of the proposal reader at slot `s` is `some B` for some named block `B`. -/
theorem Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    ∀ p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s,
      ∃ B : NamedBlock V, p = some B := by
  rintro p ⟨n, hn, hp⟩
  exact facts.dt.proposal_with_gradeContract_isSome n.cache .poolAndCarried S.E S.hc S.cfg
    (S.node (S.E.proposer s)) n.st
    (Restated.Vocabulary.Proofs.HealingSurface.proposerReadAt_invariant facts S rho s n hn) p hp

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, and every
    outcome `input` of the proposal input computed from `n`, the parent field of `input` is in the
    tree of `n`'s store. -/
theorem Vocabulary.Proofs.HealingSurface.proposedParent_mem (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    input.parent ∈ n.st.core.T := by
  intro n hn input hinput
  obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core)
    (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s).toFinset L.toFinset
    ((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s - 1)
  rw [facts.dt.with_proposal_input_id_parent _ _ _ _ _ input hinput L hL H hH]
  have hT : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_T _
  have hroot := Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts _
    (Restated.Vocabulary.Proofs.HealingSurface.proposerReadAt_invariant facts S rho s n hn).2
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc (M.toHealing n.st.core).s)
    (M.readFrame n.cache (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)).g1
  have hanchor : G.anchor ∈ (M.toHealing n.st.core).T := by
    rw [facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc _ _ G hG a ha]
    exact Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc _ _ _
      (by rw [hT]; exact hroot) a ha
  rw [← hT]
  exact Restated.Vocabulary.Proofs.NamedProposalParent.get_head_with_mem facts _ S.E S.hc _ _ _ _ G hG
    hanchor H hH

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every value `p` of the proposal reader at slot `s`, if `p` is `some B` then `B`'s slot is
    `s`. -/
theorem Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s,
      p = some B → B.slot = s :=
  Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts S rho s

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every value `p` of the proposal reader at slot `s`, if `p` is `some B` then `B` names slot
    `s`'s proposer. -/
theorem Vocabulary.Proofs.HealingSurface.proposedBlockAt_proposer (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s,
      p = some B → B.proposer? = some (S.E.proposer s) := by
  rintro p ⟨n, hnmem, hp⟩ hB
  subst hB
  have _hr : M.reachedNode n := by
    obtain ⟨w, hw, c, hc, rfl⟩ := hnmem
    exact facts.nd.reachedNode_confirmationRead S.E S.hc (w _) _ c hc
      (Record.reachedNode_stateBeforeTime facts S rho _ w hw _)
  have _hrs : M.reachedStore n.st := facts.nd.reachedStore_of_node n _hr
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing n.st.core)
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc n.st
  have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts
    (M.gradeContract n.cache) .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) n.st B hp
    input hinput L hL
  rw [hpay.2.2.2.2.2.2.2, facts.dt.with_proposal_input_id_proposer _ _ _ _ _ input hinput]
  exact congrArg some (S.node_val_index (S.E.proposer s))

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, if the
    proposal duty run on `n` can return the named block `B`, then for every outcome `input` of the
    proposal input computed from `n`, `B` has a named parent whose erasure is the parent field of
    `input`. -/
theorem Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some B →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧ p.erase = input.parent := by
  intro n _ hB input hinput
  exact facts.dt.proposal_with_parent? (M.gradeContract n.cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) n.st B (some B) hB rfl input hinput

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- If `B`'s named parent is among `st`'s bodies, `B`'s erasure is not in `st`'s tree, and the
    checked core handler inserts `B`'s erasure into the tree, then `B` is among the bodies of the
    store the block handler returns on `B`. -/
theorem Vocabulary.Proofs.HealingSurface.mem_bodies_on_block_with (facts : Record.Facts M) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V)
    (hp : B.parent ∈ st.bodies) (hnew : B.erase ∉ st.core.T)
    (hins : B.erase ∈ (M.on_block_checked_using
      (fun current => M.on_block_using E current B.erase
        (fun parentState => M.named_transition E cfg parentState B)) hc st.core
      B.erase).T) (hn : M.reachedStore st := by trivial) :
    B ∈ (M.on_block_with .alsoCarried E hc cfg st B).bodies := by
  have hmem : B ∈ (M.ns_process_block_core E hc cfg st B).bodies := by
    rw [facts.hd.process_block_core_bodies_eq_commit E hc cfg hp]
    refine facts.hd.mem_commitBlock_bodies_of_fresh E hc cfg rfl ⟨hnew, ?_⟩
    rw [facts.hd.sameCore_T (facts.hd.process_block_core_of_parent_mem E hc cfg hp),
      facts.hd.commit_core _ _ B (facts.hd.on_block_checked_using_store_part E hc cfg st B)]
    exact hins
  by_cases hold : B ∉ st.bodies
  · rw [facts.hd.on_block_with_of_new .alsoCarried E hc cfg st B hold hmem,
      (facts.hd.admit_rows_bodies_and_core_T hc _ _).1]
    exact hmem
  · rw [facts.hd.on_block_with_of_not_new .alsoCarried E hc cfg st B (fun h => hold h.1)]
    exact hmem

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- If `p` is `B`'s named parent, the height derived for `B` is the height derived for `p` or one
    more. -/
theorem Vocabulary.Proofs.HealingSurface.derive_named_height_cases (facts : Record.Facts M) (E : Env V) (cfg : Protocol.HeightConfig)
    {B p : NamedBlock V} (hp : NamedBlock.parent? B = some p) :
    (M.derive_named E cfg B).h =
        (M.derive_named E cfg p).h + 1 ∨
      (M.derive_named E cfg B).h = (M.derive_named E cfg p).h := by
  cases B with
  | genesis => exact absurd hp (by simp [NamedBlock.parent?])
  | node q s root votes support rows proposer =>
    have hq : q = p := Option.some.inj hp
    subst hq
    rw [facts.csAdded.derive_named_node]
    rcases facts.csAdded.transition_height_entry_cases E cfg (M.derive_named E cfg q)
        (q.node s root votes support rows proposer) with ⟨hh, -⟩ | ⟨hh, -⟩
    · exact Or.inr hh
    · exact Or.inl hh

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, if the
    proposal duty run on `n` can return `B`, then for every outcome `input` of the proposal input
    computed from `n`, `B` has a named parent `p` whose erasure is the parent field of `input`, and
    the height derived for `B` is the height derived for `p` or one more. -/
theorem Vocabulary.Proofs.HealingSurface.proposedBlockAt_height (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some B →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧
      p.erase = input.parent ∧
      ((M.derive_named S.E S.cfg B).h =
          (M.derive_named S.E S.cfg p).h + 1 ∨
        (M.derive_named S.E S.cfg B).h =
          (M.derive_named S.E S.cfg p).h) := by
  intro n hn hB input hinput
  obtain ⟨p, hp, hpe⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho s n hn hB
    input hinput
  exact ⟨p, hp, hpe, Restated.Vocabulary.Proofs.HealingSurface.derive_named_height_cases facts S.E S.cfg hp⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every outcome `R` of the SG root under `contract` at `st` and the round of `st`'s slot, and
    every outcome `X` of the head under `contract` at `st` over `votes`, `support` and slot `k`, `R`
    is an ancestor of, or the same block as, `X`. -/
theorem Vocabulary.Proofs.HealingSurface.get_sg_root_with_preceq_get_head_with (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (votes support : Finset (GoldfishVote V)) (k : Slot) :
    ∀ R : Block V, M.get_sg_root_with contract E hc st ((M.round_of hc st.s)) ⇢ R →
    ∀ X : Block V, M.get_head_with contract E hc st votes support k ⇢ X →
      Block.Preceq R X := by
  intro R hR X hX
  rw [facts.gr.get_head_with_eq_fork_choice contract E hc st votes support k R hR X] at hX
  have hscore := fun B => facts.fc.goldfish_score_nonempty E st.toFG.toSG.toGoldfishStore.T votes support k B
  choose score hscore using hscore
  have helig := fun B => facts.fc.goldfish_eligible_nonempty E st.toFG.σ st.toFG.h_max
    st.toFG.toSG.toGoldfishStore.T st.toFG.toSG.toGoldfishStore.s votes support k B
  choose elig helig using helig
  rw [facts.fc.goldfish_fork_choice_eq_ghost _ _ _ _ _ _ _ _ _ _ score hscore elig helig X] at hX
  exact facts.fc.ghost_preceq _ _ _ _ X hX

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, and every
    outcome `input` of the proposal input computed from `n`, the finalized block of `n`'s store is
    an ancestor of, or the same block as, the parent field of `input`. -/
theorem Vocabulary.Proofs.HealingSurface.finalized_preceq_proposedParent (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    Block.Preceq n.st.core.F input.parent := by
  intro n hn input hinput
  have hFJ : Block.preceq n.st.core.F n.st.core.J = true := by
    obtain ⟨w, hw, c, -, rfl⟩ := hn
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
      (Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts S rho
        (M.proposal_time S.E s) (S.E.proposer s) w hw)
  have hroot := Restated.Vocabulary.Proofs.StoreFinality.finalized_preceq_fgRoot facts (st := n.st.core) hFJ
  obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core)
    (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s).toFinset L.toFinset
    ((M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s - 1)
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  rw [facts.dt.with_proposal_input_id_parent _ _ _ _ _ input hinput L hL H hH]
  exact Proofs.ModelProperties.Preceq_trans hroot
    (Proofs.ModelProperties.Preceq_trans
      (facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract n.cache S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) R hR)
      (Restated.Vocabulary.Proofs.HealingSurface.get_sg_root_with_preceq_get_head_with facts
        (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) _ _ _ R hR H hH))

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every value `p` of the proposal reader at slot `s`, if `p` is `some B` then the attestations
    included in `B`'s erasure pass the round test `M.carried_attestations_admissible`. -/
theorem Vocabulary.Proofs.HealingSurface.proposedBlockErased_carried_admissible (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot)
    {B : NamedBlock V} :
    ∀ p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s,
      p = some B → M.carried_attestations_admissible S.hc B.erase = true := by
  rintro p ⟨n, -, hp⟩ hB
  exact facts.dt.proposal_with_carried_admissible_inclG2 (M.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) n.st p hp hB

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- If `B`'s erasure is not in `st`'s tree but its parent is, its slot is at most `st`'s slot,
    `st`'s finalized block is its ancestor, it names its slot's proposer, its parent's slot is
    earlier than its own, its included attestations pass the round test, and no block of the tree
    has its root unless it is that erasure, then the checked core handler inserts `B`'s erasure into
    the tree. -/
theorem Vocabulary.Proofs.HealingSurface.erased_handler_inserts (facts : Record.Facts M) (S : Setup V) (st : M.NS) (B : NamedBlock V)
    (hparentTree : B.erase.parent ∈ st.core.T) (hfresh : B.erase ∉ st.core.T)
    (hslot : B.erase.slot ≤ st.core.s) (hF : Block.Preceq st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparent : B.erase.parent.slot < B.erase.slot)
    (hcarried : M.carried_attestations_admissible S.hc B.erase = true)
    -- no block of `st`'s tree has `B.erase`'s root unless it is `B.erase`
    (hroot : M.rootFresh st.core B.erase) :
    B.erase ∈ (M.on_block_checked_using
      (fun current => M.on_block_using S.E current B.erase
        (fun parentState => M.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase).T := by
  rw [facts.hd.on_block_checked_using_of_admissible _ S.hc st.core hcarried]
  exact facts.hd.mem_T_on_block_using S.E st.core B.erase _ hslot hfresh hparentTree
    (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hF) hproposer hparent hroot

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, if the
    proposal duty run on `n` can return `B`, then for every outcome `input` of the proposal input
    computed from `n`, the parent of `B`'s erasure is the parent field of `input`. -/
theorem Vocabulary.Proofs.HealingSurface.proposedBlockErased_parent (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (s : Slot)
    {B : NamedBlock V} :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some B →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    B.erase.parent = input.parent := by
  intro n hn hB input hinput
  obtain ⟨p, hp, hpe⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho s n hn hB
    input hinput
  rw [Proofs.NamedWire.erase_parent]
  cases B with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node q _ _ _ _ _ _ =>
    simp only [NamedBlock.parent?, Option.some.injEq] at hp
    subst hp
    rw [Proofs.ModelProperties.named_parent_node]
    exact hpe

end

end DecoupledConsensusModel.Sts.Restated
