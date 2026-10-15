import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_57b
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_63
import Proofs.Claims.Restated.Claim13beRoute3_64
import Proofs.Claims.Restated.Claim13beRoute3_66
import Proofs.Claims.Restated.Claim13beRoute3_66b
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Objects_ActionRound
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
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
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedConfirmationWalk
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SGOpeningFrozenSuffix
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Opening proposals under a fixed-height justification root

Theorems on the opening proposal of a round under a fixed-height justification root: its place in
the filtered trees of the opening voters, the bounded proposal lifecycle, the selected-Q2 inputs and
the prefix FG selector cone of a height row, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`. Every theorem reads the run along the path `W` of
`Restated.AdmissibleFieldsOn`.
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
private theorem stateBeforeTime_eq_strict₆₈b (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₈b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₈b S rho hsorted]
  exact (hW _).1

/-- For `r + 3 ≤ q ≤ r + 3 + gap` over `Nat`, the order facts about `q − 1`, `q − 2`, `r` and
    `r + 4 + gap` that the lifecycle theorem uses. -/
private theorem round_facts₆₈b {r gap q : Nat} (h1 : r + 3 ≤ q) (h2 : q ≤ r + 3 + gap) :
    2 ≤ q ∧ 0 < q ∧ q - 1 + 1 = q ∧ q - 2 + 1 = q - 1 ∧ r + 2 ≤ q - 1 ∧ q ≤ r + 4 + gap ∧
      q + 1 ≤ r + 4 + gap ∧ r + 1 ≤ q - 1 ∧ r ≤ q - 1 ∧ r + 1 ≤ q - 2 ∧ q - 2 ≤ q - 1 ∧ r < q ∧
      q - 1 < q ∧ r < q - 1 ∧ q - 2 < q := by
  omega

/-- Over `Nat`, if `2 ≤ R`, `o = o₁ + R` and `o₁ = o₂ + R`, then `0 < o`, `o − 1 + 1 = o`,
    `0 < o − 1`, `o₂ + 2 ≤ o − 1` and `o₁ ≤ o − 1`. -/
private theorem slot_facts₆₈b {o o₁ o₂ R : Nat} (hR : 2 ≤ R) (h1 : o = o₁ + R) (h2 : o₁ = o₂ + R) :
    0 < o ∧ o - 1 + 1 = o ∧ 0 < o - 1 ∧ o₂ + 2 ≤ o - 1 ∧ o₁ ≤ o - 1 := by
  omega

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₈b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₈b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- The anchor of a node state `n` at a round `r` has an outcome. -/
private theorem nodeAnchor_nonempty₆₈b (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  refine ⟨G.anchor, ?_⟩
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₈b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hG

/-- The anchor of a node state `n` at a round `r` has at most one outcome. -/
private theorem nodeAnchor_unique₆₈b (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round)
    {A A' : Block V}
    (hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A)
    (hA' : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A') : A' = A := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA hA'
  obtain ⟨G, hG, hGA⟩ := returns_map_elim₆₈b _ _ _ hA
  obtain ⟨G', hG', hGA'⟩ := returns_map_elim₆₈b _ _ _ hA'
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc n.st.core.toHealing r
    (M.readFrame n.cache n.st.core.toHealing r).g1
  have h1 : G.anchor = a := facts.nd.Sts_gradeContract_read_anchor n.cache S.E S.hc _ r G hG a ha
  have h2 : G'.anchor = a := facts.nd.Sts_gradeContract_read_anchor n.cache S.E S.hc _ r G' hG' a ha
  rw [← hGA, ← hGA']
  exact h2.trans h1.symm

/-- Every SG root the grade contract of `n`'s cache can return for `n`'s healing store at round `r`
    is an outcome of `n`'s anchor at `r`. -/
private theorem nodeAnchor_of_sgRoot₆₈b (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round)
    {R : Block V}
    (hR : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ R) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ R := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  have hanchor := (facts.nd.gradeContract_sgRoot_eq_frameAnchor n.cache S.E S.hc _ r R).1 hR
  have hGR : G.anchor = R := facts.nd.Sts_gradeContract_read_anchor n.cache S.E S.hc _ r G hG R hanchor
  rw [← hGR]
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₆₈b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hG

/-- For every outcome `c` of the cache update at slot `s`'s proposer's node state in
    `W (strictEventIndex rho (proposal_time s))`, the proposal duty with `c`'s grade contract can
    return some block. -/
private theorem proposal_some_along₆₈b (facts : Record.Facts M) (S : Setup V)
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
    ⟨_, mem_stateBeforeTime_along₆₈b hf.sorted hf.onePath (M.proposal_time S.E s), c, hc, rfl⟩
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

/-- If `P` is a proposal slot `s`'s proposer can return on the store of `wp` staged to `t` with the
    grade contract of `c`, then some proposal input at the node state staged from `wp` with `c` has
    its parent an ancestor of `P`'s block. -/
private theorem proposalInputParent₆₈b (facts : Record.Facts M) (S : Setup V) (wp : M.N)
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
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Along `W`, if `w`'s store in `W (strictEventIndex rho read)` holds a fixed-height justification
    root at `H`, `P` is a proposal the opening proposer of round `q` can return at its read with the
    cache `c`, the opening vote and confirmation instants are at least one delay after `read`, no
    `h_max` over the confirmation instant's set exceeds `H`, and the root's justified block is an
    ancestor of `P` and of the parent of every proposal input, then for every member `v` of the set
    for the opening vote instant, every block `C` between the justified block and `P`, and every
    cache outcome `cv` at `v`'s vote read, `C` is in the filtered block tree and in every outcome of
    the voter's filtered block tree of the node state staged with `cv`. -/
theorem openingProposal_mem_filteredTree_voteRead_of_fixedRootOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} {P : NamedBlock V}
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
    (hvoteDelay : read + S.E.Δ ≤
      M.vote_time S.E ((M.opening_slot S.hc q)))
    (_hconfirmationDelay : read + S.E.Δ ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)))
    (hconfirmationHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hconfirmationCap : ((Hs (M.confirmation_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H)
    (hpostProposal : lo ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hJparent : ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      Block.Preceq (W (strictEventIndex rho read) w).st.J I.parent)
    (hJP : Block.Preceq (W (strictEventIndex rho read) w).st.J P.erase)
    (hpostSource : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))), ∀ C : Block V,
      Block.Preceq (W (strictEventIndex rho read) w).st.J C →
      Block.Preceq C P.erase →
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc q))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
        let m := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
            (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv
        C ∈ M.get_filtered_block_tree (M.toHealing m.st.core).toFG ∧
          ∀ T : Finset (Block V),
            M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T → C ∈ T := by
  have hopenPos : 0 < (M.opening_slot S.hc q) := facts.gr.opening_slot_pos_of_round_pos S.hc hq
  have hopen : ((M.opening_slot S.hc q) - 1) + 1 = (M.opening_slot S.hc q) :=
    Nat.sub_add_cancel hopenPos
  have hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E
      ((M.opening_slot S.hc q))).trans hconfirmationHor
  have hvoteHor : M.vote_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E
      ((M.opening_slot S.hc q))).trans hconfirmationHor
  have hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q)) :=
    hpostProposal.trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _))
  have hvoteConf : M.vote_time S.E ((M.opening_slot S.hc q)) + S.E.Δ <
      M.confirmation_time S.E ((M.opening_slot S.hc q)) := by
    have h1 := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc q)
    have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc q)
    linarith [S.E.Δ_pos]
  have hvoteCap : ((Hs (M.vote_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) u).st.core.h_max)
        ≤ H :=
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloVote hvoteConf hconfirmationHor
      ⟨_, hprop⟩).trans hconfirmationCap
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) → ∃ out : M.N × List (NamedObject V),
      M.tick S (S.E.proposer (M.opening_slot S.hc q)) (W j (S.E.proposer (M.opening_slot S.hc q)))
        (M.proposal_time S.E (M.opening_slot S.hc q)) ⇢ out :=
    fun j hj => hf.tick_outcome j _ _ hj
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      ((M.opening_slot S.hc q)) hopenPos hprop hproposalHor hpostProposal hneTick hrun c hc hP
  obtain ⟨B0, hB0, hPslot, _hemit0⟩ :=
    Restated.proposedBlockAt_emits_of_honestOn facts S Hs Xb hf hHs (M.opening_slot S.hc q)
      hopenPos hprop hproposalHor hpostProposal hneTick hrun c hc (some P) hP
  cases hB0
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.fixedRoot_namedTarget_of_fixedRootOn facts S Hs Xb hfix
  obtain ⟨Jp, hJpP, hJpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift P hJP
  have hJpRun : Restated.RunBlockOn M S rho W Xb Jp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hPrun hJpP
  have hJpEq : Jp = Jn := by
    apply hf.rootCollisionFree.root_injective
      Jp Jn hJpRun hJnRun Jp Jn
      (Or.inl (Proofs.NamedAncestry.named_self Jp))
      (Or.inr (Proofs.NamedAncestry.named_self Jn))
    rw [← Proofs.NamedWire.erase_root Jp, ← Proofs.NamedWire.erase_root Jn,
      hJpErase, hJnErase]
  have hPheight : H - 1 ≤ (M.derive_named S.E S.cfg P).h := by
    rw [← hJnHeight, ← hJpEq]
    exact facts.cs.derive_height_mono S.E S.cfg hJpP
  have hadmit := Restated.openingProposalAdmittedBeforeVote_atVote_l66 facts
    S Hs Xb hf hHs hHsXb hfix c hc hP hq hpostRead hvoteDelay hvoteHor hvoteCap hpostProposal
    hprop (Proofs.ModelProperties.Preceq_self _) hJparent hrun
  intro v hv C hJC hCP cv hcv m
  have hmst : m.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st (M.vote_time S.E (M.opening_slot S.hc q))) _ := facts.nd.mkNode_st _ _ _
  rw [hmst]
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  have hwd := mem_stateBeforeTime_along₆₈b hf.sorted hf.onePath (S := S)
    (M.vote_time S.E (M.opening_slot S.hc q))
  have hrootMax :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hv hpostRead hvoteDelay hvoteHor hvoteCap
  have hPtree : P.erase ∈
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.T :=
    (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf (hadmit v hv) (le_refl _)).1
  have hraw : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core).toFG :=
    Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts S Hs Xb hf (hHsXb _ hv) hPrun
      hPtree hJP hPheight hrootMax.1 hrootMax.2
  have hdutyEq : (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core =
      M.store_with_t_s
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.vote_time S.E (M.opening_slot S.hc q))
        (S.E.slotOf (M.vote_time S.E (M.opening_slot S.hc q))) :=
    facts.hd.setClock_core_eq_store_with_t_s S.E _ _
  have hfilt : M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core).toFG =
      M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core).toFG := by
    rw [hdutyEq]
    exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _
  have hrootD : M.get_fg_root (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core).toFG =
      (W (strictEventIndex rho read) w).st.J := by
    rw [hdutyEq]
    exact (facts.fc.get_fg_root_set_clock_slot _ _ _).trans hrootMax.1
  have hslotD : (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core.s = M.opening_slot S.hc q := by
    rw [facts.hd.Sts_setClock_core_s]
    exact facts.sch.slotOf_vote_time S.E _
  have hPfiltered : P.erase ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core).toFG := by
    rw [hfilt]
    exact hraw
  have hFJ : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.F
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.J :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.vote_time S.E ((M.opening_slot S.hc q))) v _ hwd
  have hpc : Restated.Vocabulary.Internal.ParentClosed M
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts
      S rho (M.vote_time S.E ((M.opening_slot S.hc q))) v _ hwd
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  have hCT : C ∈
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.T :=
    Proofs.Records.mem_of_preceq hpc.2 C P.erase hPtree
      (preceq_eq_true_iff_Preceq.mpr hCP)
  have hrootC : Block.Preceq
      (M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
        (M.vote_time S.E (M.opening_slot S.hc q))).core).toFG) C := by
    rw [hrootD]
    exact hJC
  have hCfiltered : C ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core).toFG :=
    facts.fc.mem_filtered_of_preceq
      (by rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J,
            facts.hd.setClock_core_F, facts.hd.setClock_core_J]
          exact preceq_eq_true_iff_Preceq.mpr hFJ)
      hPfiltered
      (by rw [facts.sto.toHealing_T, facts.hd.Sts_setClock_core_T]; exact hCT)
      (preceq_eq_true_iff_Preceq.mpr hCP) (preceq_eq_true_iff_Preceq.mpr hrootC)
  refine ⟨hCfiltered, ?_⟩
  intro T hT
  obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core).toFG.toSG.toGoldfishStore
    (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core).s
  have hPQ : P.erase ∈ Q := by
    refine facts.fc.mem_voter_processed_block_tree_of_slot S.E _ _ ?_ ?_ Q hQ
    · rw [facts.sto.toHealing_gs_T, facts.hd.Sts_setClock_core_T]
      exact hPtree
    · rw [Proofs.NamedWire.erase_slot, hPslot]
      exact ((facts.sto.toHealing_s _).trans hslotD).symm
  have hmaxP : (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))).core.h_max ≤
      (M.derive_named S.E S.cfg P).h + 1 := by
    rw [facts.hd.setClock_core_h_max]
    have hmaxW : (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.h_max
        = H := hrootMax.2
    rw [hmaxW]
    have hHone : 1 ≤ H :=
      Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hHone).symm
      _ ≤ (M.derive_named S.E S.cfg P).h + 1 :=
        Nat.add_le_add_right hPheight 1
  have hvFreeze : v ∈ Hs (M.view_freeze S.E ((M.opening_slot S.hc q) - 1)) := by
    have hle : M.view_freeze S.E ((M.opening_slot S.hc q) - 1) ≤
        M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1) :=
      le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E _)
    exact hHs _ _ (hle.trans (le_of_eq (congrArg (M.vote_time S.E) hopen))) hv
  have hgatFreeze : lo ≤ M.view_freeze S.E ((M.opening_slot S.hc q) - 1) :=
    hpostSource.trans (by
      have h3 := (facts.sch.slot_instants_l55 S.E ((M.opening_slot S.hc q) - 1)).2.2.1
      linarith [S.E.Δ_pos])
  have hcand := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts
    S Hs Xb hf hHsXb (s := (M.opening_slot S.hc q) - 1) hvFreeze (C := C) (H := P)
  rw [hopen] at hcand
  have hCQ := hcand Q hQ hPQ hPrun hCP hCfiltered hmaxP hgatFreeze
  rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E _ Q hQ T hT] at hCQ
  exact hCQ

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The SG root read under any grade contract from the healing view of a store with a cache written
    in is the one read from the store's own healing view. -/
private theorem sgRoot_store_with_cache₆₈b (facts : Record.Facts M) {E : Env V}
    {hc : Protocol.HealConfig} {st : M.NS} {c c' : M.Cache} {r : Round} {x : Block V} :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

/-- Along `W`, under the committee majority and the weight bound, if `w`'s store in
    `W (strictEventIndex rho read)` holds the fixed-height justification root at `H`,
    `t_GST ≤ read ≤ S.a r`, carrier rounds recur from `t₀`, `S.a (r + 4 + gap)` is in the horizon,
    `lo ≤ read`, `t₀ ≤ read`, the awake conditions hold and `lo ≤ opening (r + 2 − η_SG)`, then
    either `H` is less than the largest `h_max` over the set for `S.a (r + 4 + gap)`, or some
    carrier round `q` with `r + 3 ≤ q ≤ r + 3 + gap` has the justified block graded 2 at round
    `q − 1`, the opening cone-root lock at `H` for round `q − 1`, and an opening proposal `P` with
    the proposal lifecycle packet of round `q − 1`. -/
theorem fixedHeightJustificationRoot_boundedProposalLifecycle_closedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {r gap : Round} {t₀ : Int}
    (hpost : S.E.t_GST ≤ read)
    (hreadAction : read ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hrecurrence : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) ≤ rho.horizon)
    (hlo : lo ≤ read) (ht₀ : t₀ ≤ read)
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hloOpen : lo ≤ M.opening S.E S.hc (r + 2 - S.hc.η_SG)) :
    H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max) ∨
      ∃ q : Round, r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
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
                  Hs Xb (q - 1) ((M.opening_slot S.hc q) - 1) P := by
  by_cases hrise : H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max)
  · exact Or.inl hrise
  have hcapEnd := Nat.le_of_not_gt hrise
  have hamono : ∀ {x y : Round}, x ≤ y →
      (Restated.Vocabulary.Execution.Setup.a M S x) ≤ (Restated.Vocabulary.Execution.Setup.a M S y) :=
    fun h => Restated.Vocabulary.Proofs.Assembly.a_mono facts S h
  have hlastLt := Restated.action_add_delta_lt_action_of_lt_l67 facts S
    (Nat.add_lt_add_right (Nat.add_lt_add_left (by decide : 3 < 4) r) gap)
  have hcapAt : ∀ t : Time, (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ t →
      t ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 3 + gap)) →
      ((Hs t).sup fun v => (W (inclusiveEventIndex rho t) v).st.core.h_max) ≤ H := by
    intro t h1 h2
    have hloT : lo ≤ t := hlo.trans (hreadAction.trans ((hamono (Nat.le_succ r)).trans h1))
    exact (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloT
      (lt_of_le_of_lt (Int.add_le_add_right h2 S.E.Δ) hlastLt) hendHor
      (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)).trans hcapEnd
  rcases Restated.fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBoundOn
      facts S Hs Xb hf hHs hHsXb hcom hfb hfix hpost hreadAction hrecurrence hendHor hlo ht₀ hA
      hloOpen with hcontrary | ⟨q, hqlo, hqhi, hcarrier, hforms, hlock⟩
  · exact False.elim (hrise hcontrary)
  right
  obtain ⟨hqTwo, hqPos, hqPredAdd, hqPred, hr2q, hqEnd, hqNextEnd, hr1q1, hrq1, hr1q2, hq2q1, hrq,
    hq1q, hrq1lt, hq2q⟩ := round_facts₆₈b hqlo hqhi
  have hR2 : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hoEq : M.opening_slot S.hc q = M.opening_slot S.hc (q - 1) + S.hc.R := by
    have h := facts.gr.opening_slot_succ S.hc (q - 1)
    rw [hqPredAdd] at h
    exact h
  have hoEqPrev : M.opening_slot S.hc (q - 1) = M.opening_slot S.hc (q - 2) + S.hc.R := by
    have h := facts.gr.opening_slot_succ S.hc (q - 2)
    rw [hqPred] at h
    exact h
  obtain ⟨hopenPosQ, hsucc, hspos, hslotTwo, hslotPrev⟩ := slot_facts₆₈b hR2 hoEq hoEqPrev
  have hloOpenQ : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right hr2q _))
  have hr2pos : 0 < r + 2 := Nat.succ_pos (r + 1)
  have hAprev := hA (q - 1)
    (Restated.lo_le_early_g2_sub_delta_of_opening facts S hr2pos hloOpen hr2q)
  have hAboundQ : lo ≤ M.early S.E S.hc q .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_opening facts S hr2pos hloOpen
      (hr2q.trans (Nat.sub_le q 1))
  have hwinQ : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc q]
    have h2 := facts.gr.q10_early_g2_le_early_g1 S q
    linarith
  have hconfEq : (Restated.Vocabulary.Execution.Setup.a M S q) =
      M.confirmation_time S.E (M.opening_slot S.hc q) :=
    Restated.a_eq_confirmation_opening_l58 facts S q
  have hactionQHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (hamono hqEnd).trans hendHor
  have hactionNextHor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon :=
    (hamono hqNextEnd).trans hendHor
  have hprevActionLe : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S q) := hamono (Nat.sub_le q 1)
  have hprevActionHor := hprevActionLe.trans hactionQHor
  have hr1Prev : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) := hamono hr1q1
  have hqAtLast : (Restated.Vocabulary.Execution.Setup.a M S q) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 3 + gap)) := hamono hqhi
  have hactionQCap := hcapAt _ (hr1Prev.trans hprevActionLe) hqAtLast
  have hprevActionCap := hcapAt _ hr1Prev (hprevActionLe.trans hqAtLast)
  have hreadPrev : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hreadAction.trans (hamono hrq1)
  have hpostPreviousAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hpost.trans hreadPrev
  have hloPrevAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hlo.trans hreadPrev
  have hdelayAction : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) :=
    (Int.add_le_add_right hreadAction S.E.Δ).trans
      ((le_of_lt (Restated.action_add_delta_lt_action_of_lt_l67 facts S (Nat.lt_succ_self r))).trans
        (hamono hr1q2))
  have hprevActionDelay : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hdelayAction.trans (hamono hq2q1)
  have hproposalDelay : read + S.E.Δ ≤ M.proposal_time S.E (M.opening_slot S.hc q) :=
    (Int.add_le_add_right hreadAction S.E.Δ).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        hrq)
  have hproposalLeConf : M.proposal_time S.E (M.opening_slot S.hc q) ≤
      M.confirmation_time S.E (M.opening_slot S.hc q) :=
    facts.sch.proposal_time_le_confirmation_time S.E _
  have hproposalLeAction : M.proposal_time S.E (M.opening_slot S.hc q) ≤
      (Restated.Vocabulary.Execution.Setup.a M S q) := hproposalLeConf.trans (le_of_eq hconfEq.symm)
  have hprevLeProposal : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      M.proposal_time S.E (M.opening_slot S.hc q) :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        hq1q)
  have hproposalHor : M.proposal_time S.E (M.opening_slot S.hc q) ≤ rho.horizon :=
    hproposalLeAction.trans hactionQHor
  have hproposalCap := hcapAt _ (hr1Prev.trans hprevLeProposal) (hproposalLeAction.trans hqAtLast)
  have hconfirmationDelay : read + S.E.Δ ≤ M.confirmation_time S.E (M.opening_slot S.hc q) :=
    hproposalDelay.trans hproposalLeConf
  have hconfirmationHor : M.confirmation_time S.E (M.opening_slot S.hc q) ≤ rho.horizon :=
    (le_of_eq hconfEq.symm).trans hactionQHor
  have hconfirmationCap := hcapAt _ ((hr1Prev.trans hprevActionLe).trans (le_of_eq hconfEq))
    ((le_of_eq hconfEq.symm).trans hqAtLast)
  have hproposalLtVote : M.proposal_time S.E (M.opening_slot S.hc q) <
      M.vote_time S.E (M.opening_slot S.hc q) := facts.sch.proposal_time_lt_vote_time S.E _
  have hvoteDelay : read + S.E.Δ ≤ M.vote_time S.E (M.opening_slot S.hc q) :=
    hproposalDelay.trans (le_of_lt hproposalLtVote)
  have hvoteLeConf : M.vote_time S.E (M.opening_slot S.hc q) ≤
      M.confirmation_time S.E (M.opening_slot S.hc q) :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E _
  have hvoteHor : M.vote_time S.E (M.opening_slot S.hc q) ≤ rho.horizon :=
    hvoteLeConf.trans hconfirmationHor
  have hvoteCap := hcapAt _ ((hr1Prev.trans hprevLeProposal).trans (le_of_lt hproposalLtVote))
    ((hvoteLeConf.trans (le_of_eq hconfEq.symm)).trans hqAtLast)
  have hreadDelay : read ≤ read + S.E.Δ := le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hvoteDelayPrev : read + S.E.Δ ≤ M.vote_time S.E (M.opening_slot S.hc q - 1) :=
    hdelayAction.trans
      ((le_of_lt (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S (q - 2))).trans
        (facts.sch.vote_time_mono_slots S.E hslotTwo))
  have hproposalDelaySource : read + S.E.Δ ≤ M.proposal_time S.E (M.opening_slot S.hc q - 1) :=
    ((Int.add_le_add_right hreadAction S.E.Δ).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        hrq1lt)).trans (facts.sch.proposal_time_mono S.E hslotPrev)
  have hloSource : lo ≤ M.proposal_time S.E (M.opening_slot S.hc q - 1) :=
    hlo.trans (hreadDelay.trans hproposalDelaySource)
  have hloOpeningProposal : lo ≤ M.proposal_time S.E (M.opening_slot S.hc q) :=
    hloSource.trans (facts.sch.proposal_time_mono S.E (Nat.sub_le _ _))
  have hloCone : lo ≤ M.vote_time S.E (M.opening_slot S.hc q - 1) :=
    hlo.trans (hreadDelay.trans hvoteDelayPrev)
  have hloVote : lo ≤ M.vote_time S.E (M.opening_slot S.hc q) :=
    hlo.trans (hreadDelay.trans hvoteDelay)
  have hloConf : lo ≤ M.confirmation_time S.E (M.opening_slot S.hc q) := hloVote.trans hvoteLeConf
  have hloQ : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := hloPrevAction.trans hprevActionLe
  have hactionDelayQ : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hproposalDelay.trans hproposalLeAction
  have hcutQ : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon := by
    have h := Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S (q - 1)
    rw [hqPredAdd] at h
    exact (le_of_lt h).trans hactionQHor
  have hcutNext : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q)).trans
      hactionNextHor
  have hdomainAction : M.domain S.E S.hc q .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    facts.gr.domain_le_a S q .g2
  have hdomainHor := hdomainAction.trans hactionQHor
  have hdomainDelay : read + S.E.Δ ≤ M.domain S.E S.hc q .g2 :=
    hdelayAction.trans
      (Restated.Vocabulary.Proofs.NamedOutageClosure.action_le_domain facts S S.hc.R_ge_three
        hq2q)
  have hprevLeDomain : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤
      M.domain S.E S.hc q .g2 := by
    have h := Restated.action_add_delta_le_domain_g2_succ_l54 facts S (q - 1)
    rw [hqPredAdd] at h
    exact le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) h
  have hdomainCap := hcapAt _ (hr1Prev.trans hprevLeDomain) (hdomainAction.trans hqAtLast)
  have hdomainG0Hor : M.domain S.E S.hc q .g0 ≤ rho.horizon :=
    (facts.gr.domain_le_a S q .g0).trans hactionQHor
  have hconfPrevHor : M.confirmation_time S.E (M.opening_slot S.hc q - 1) ≤ rho.horizon := by
    rw [facts.sch.confirmation_time_eq_support_cutoff_succ, hsucc]
    exact (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _).trans hconfirmationHor
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hpropConf : S.E.proposer (M.opening_slot S.hc q) ∈
      Hs (M.confirmation_time S.E (M.opening_slot S.hc q)) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  have hpropProposal : S.E.proposer (M.opening_slot S.hc q) ∈
      Hs (M.proposal_time S.E (M.opening_slot S.hc q)) := hHs _ _ hproposalLeConf hpropConf
  have hpropVote : S.E.proposer (M.opening_slot S.hc q) ∈
      Hs (M.vote_time S.E (M.opening_slot S.hc q)) := hHs _ _ hvoteLeConf hpropConf
  have hpropA : S.E.proposer (M.opening_slot S.hc q) ∈
      Hs (Restated.Vocabulary.Execution.Setup.a M S q) := by
    rw [hconfEq]; exact hpropConf
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
      (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q)) :=
    fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj hpropProposal hwinQ
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
    exact hAboundQ
  have hopenG1 : M.domain S.E S.hc q .g1 = M.proposal_time S.E (M.opening_slot S.hc q) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hpropG1 : S.E.proposer (M.opening_slot S.hc q) ∈ Hs (M.domain S.E S.hc q .g1) := by
    rw [hopenG1]; exact hpropProposal
  have hrootMaxAt : ∀ {t : Time} {v : V}, v ∈ Hs t → read + S.E.Δ ≤ t → t ≤ rho.horizon →
      ((Hs t).sup fun u => (W (inclusiveEventIndex rho t) u).st.core.h_max) ≤ H →
      M.get_fg_root (M.toHealing (W (strictEventIndex rho t) v).st.core).toFG =
          (W (strictEventIndex rho read) w).st.J ∧
        (W (strictEventIndex rho t) v).st.core.h_max = H :=
    fun hv hd hh hcp =>
      Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn
        facts S Hs Xb hf hHs hHsXb hsb hfix hv hlo hd hh hcp
  have hJfiltered : ∀ {t : Time} {v : V}, v ∈ Hs t → read + S.E.Δ ≤ t → t ≤ rho.horizon →
      ((Hs t).sup fun u => (W (inclusiveEventIndex rho t) u).st.core.h_max) ≤ H →
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho t) v).st.core).toFG := by
    intro t v hv hd hh hcp
    rw [← (hrootMaxAt hv hd hh hcp).1]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S
      rho t v _ (mem_stateBeforeTime_along₆₈b hf.sorted hf.onePath t)
  have hactiveAtAction : ∀ v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG :=
    fun v hv => hJfiltered hv hactionDelayQ hactionQHor hactionQCap
  have hwindowPrev : ∀ v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1)),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG :=
    fun v hv => hJfiltered hv hprevActionDelay hprevActionHor hprevActionCap
  have hdomainWindow : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core).toFG :=
    fun v hv => hJfiltered hv hdomainDelay hdomainHor hdomainCap
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc q))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))).cache
  obtain ⟨P, hP⟩ := proposal_some_along₆₈b facts S hf (M.opening_slot S.hc q) c hc
  obtain ⟨I, hI, hIP⟩ := proposalInputParent₆₈b facts S
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q)))
    (M.opening_slot S.hc q) (M.proposal_time S.E (M.opening_slot S.hc q)) c hP
  obtain ⟨A, hAanchor⟩ := nodeAnchor_nonempty₆₈b facts S
    (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).record c) q
  have hJG1 := Restated.namedG1At_fixedRootTarget_of_retainedPreviousGradeOn facts S Hs Xb hf
    hHs hHsXb hfb hfix hqTwo hforms hwindowPrev hdomainWindow hlo hpostPreviousAction hcutQ
    hactionQHor hactiveAtAction hpropProposal hproposalDelay hproposalHor hproposalCap
    hloPrevAction hloOpenQ hAprev
  obtain ⟨hAG1, hJA, hAfiltered⟩ := Restated.relativeAnchor_of_fixedRootLockOn facts S Hs Xb hf
    hHs hHsXb hfb hfix hqTwo hforms hwindowPrev hdomainWindow hlo hpostPreviousAction hcutQ
    hactionQHor hactiveAtAction hpropProposal hproposalDelay hproposalHor hproposalCap
    hloPrevAction hloOpenQ hAprev c hc A hAanchor
  have hconcentration := Restated.namedG1Concentration_of_fixedRootLockOn facts S Hs Xb hf
    hHs hHsXb hcom hfb hfix hqTwo hforms hwindowPrev hlock hlo hproposalDelay hproposalHor
    hproposalCap hloPrevAction hloOpenQ hAprev
  have hparents :=
    Restated.fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relativeOn facts S Hs Xb
      hf hHs hHsXb hcom hfb hfix hqTwo hforms hwindowPrev hdomainWindow hactiveAtAction hlock
      hlo hproposalDelay hproposalHor hproposalCap hloCone hloPrevAction hpropProposal c hc
      hAanchor hAG1 hAfiltered hJA hloOpenQ hAprev
  have hbatch := Restated.actionBatchAlignedAt_of_fixedRootOn facts S Hs Xb hf hHs hHsXb hqPos
    hfix hlo hloPrevAction hprevActionDelay hprevActionHor hprevActionCap hactionDelayQ
    hactionQHor hactionQCap c hc hP hparents hAprev
  have hJparent : ∀ I' : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I' →
      Block.Preceq (W (strictEventIndex rho read) w).st.J I'.parent :=
    fun I' hI' => hparents.liveG1Parent _ hpropG1 _ hJG1 c hc I' hI'
  have hJB : Block.Preceq (W (strictEventIndex rho read) w).st.J P.erase :=
    preceq_trans_Preceq (hJparent I hI) hIP
  have hAP : Block.Preceq A P.erase :=
    preceq_trans_Preceq (hparents.liveG1Parent _ hpropG1 A hAG1 c hc I hI) hIP
  have hconfirmation := Restated.sgOpeningConfirmationReads_of_fixedJustificationRootNoRiseOn facts
    S Hs Xb hf hHs hHsXb hfb hfix c hc hP hqPos hlo hconfirmationDelay hconfirmationHor
    hconfirmationCap hloOpeningProposal hloPrevAction hpropConf
    (Proofs.ModelProperties.Preceq_self _) hJparent hparents hAprev
  have hvoteData := Restated.openingProposal_mem_filteredTree_voteRead_of_fixedRootOn facts S Hs Xb
    hf hHs hHsXb hfix c hc hP hqPos hlo hvoteDelay hconfirmationDelay hconfirmationHor
    hconfirmationCap hloOpeningProposal hpropConf hJparent hJB hloSource hrunP
  have hP' : M.proposal_with
      (M.gradeContract (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c).st ⇢ some P := by
    rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
    exact hP
  have hnround : M.round_of S.hc
      (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c).st.core.s = q := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time,
      facts.gr.round_of_opening_slot_eq]
  have hmaxProposer :
      (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st
          (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record c).st.core.h_max = H := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_h_max]
    exact (hrootMaxAt hpropProposal hproposalDelay hproposalHor hproposalCap).2
  have hrawExtra := fun (v : V) (hv : v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)))
      (cv : M.Cache) (hcv : M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc q))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv) =>
    Restated.voter_raw_extra_equivocates_proposal_afterGSTOn facts S Hs Xb hf hHs hopenPosQ
      hloSource hpropVote hv hproposalHor c hc hP' cv hcv
      (hvoteData v hv P.erase hJB (Proofs.ModelProperties.Preceq_self _) cv hcv).1
  have hpivotTransfer : ∀ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)),
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
      Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho
        (M.opening_slot S.hc q) A v P
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
            (S.E.proposer (M.opening_slot S.hc q))).record c)
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv) := by
    intro v hv cv hcv
    have hrm := hrootMaxAt hv hvoteDelay hvoteHor hvoteCap
    have hanchorP := Restated.voterAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs
      hHsXb hfb (q := q - 1) (s := M.opening_slot S.hc q - 1) (C := P.erase) (w := v)
      (by rw [hsucc, hqPredAdd]; exact facts.gr.round_of_opening_slot_eq S.hc q)
      hloPrevAction (by rw [hqPredAdd]; exact hcutQ) (by rw [hsucc]; exact hvoteHor)
      (fun u hu n hn g hg B hB =>
        preceq_trans_Preceq (hparents.actionTargetParent u hu n hn g hg B hB c hc I hI) hIP)
      (by rw [hsucc]; exact hv)
      (by
        rw [hsucc]
        exact (congrArg (fun X => Block.Preceq X P.erase)
          ((facts.fc.get_fg_root_set_clock_slot _ _ _).trans hrm.1)).mpr hJB)
      hAprev cv (by rw [hsucc]; exact hcv)
    rw [hsucc] at hanchorP
    exact Restated.namedProposalPivotSuffixTransfer_of_frozenProposalNoRiseOn facts S Hs Xb hf
      hHs hHsXb hopenPosQ hloSource hpropVote hv hvoteHor c hc hP' cv hcv
      { sourceAnchor := fun A' hA' => by
          rw [hnround] at hA'
          rw [nodeAnchor_unique₆₈b facts S _ q hAanchor hA']
          exact Proofs.ModelProperties.Preceq_self _
        pivotTarget := (hvoteData v hv A hJA hAP cv hcv).1
        proposalCandidate :=
          (hvoteData v hv P.erase hJB (Proofs.ModelProperties.Preceq_self _) cv hcv).2
        pivotAnchorCompatible := fun A0 hA0 =>
          compatible_of_preceq_common_Preceq (hanchorP A0 hA0) hAP
        proposalAnchorCompatible := fun A0 hA0 =>
          compatible_of_preceq_common_Preceq (hanchorP A0 hA0)
            (Proofs.ModelProperties.Preceq_self _)
        sameHMax := by
          rewrite [hmaxProposer, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_h_max]
          exact hrm.2.symm }
  have hfrozen := Restated.openingFrozenVotes_of_fixedJustificationRootLock_relativeOn facts S Hs Xb
    hf hHs hHsXb hcom hfb hfix c hc hP hqTwo hforms hwindowPrev hdomainWindow hactiveAtAction
    hlock hlo hproposalDelay hvoteDelay hconfirmationDelay hconfirmationHor hconfirmationCap
    hloSource hloCone hloPrevAction hpropConf hAanchor hAG1 hAfiltered hJA hpivotTransfer
    hrawExtra hloOpenQ hAprev
  rcases Restated.fixedHeightJustificationRoot_namedOpeningProposal_nextActive_or_hMaxRiseOn facts
      S Hs Xb hf hHs hHsXb hfb hfix hlo hreadAction hqlo hqhi hcarrier c hc hP hJB hendHor with
    hnextRise | hnextActive
  · exact False.elim (hrise hnextRise)
  have hconeA : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc q - 1)
      (fun X => Block.Preceq A X) :=
    hconcentration.supported (w := S.E.proposer (M.opening_slot S.hc q))
      (by rw [hqPredAdd]; exact hpropG1) (by rw [hqPredAdd]; exact hAG1)
  have hstoresPre := Restated.fixedHeightJustificationRoot_namedOpeningVoteStoresExtendOn facts S Hs
    Xb hf hHs hHsXb hcom (s := M.opening_slot S.hc q - 1) (A := A) (P := P) hspos hloCone
    hconfPrevHor c (by rw [hsucc]; exact hc)
  simp only [hsucc] at hstoresPre
  have hstores : Restated.VoteStoresExtendOn M S rho Hs (M.opening_slot S.hc q)
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q)))) P := by
    refine hstoresPre hP' (hHsXb _ hpropConf) hconeA ?_ ?_ hfrozen ?_
    · intro R hR
      rw [hnround] at hR
      rw [nodeAnchor_unique₆₈b facts S _ q hAanchor (nodeAnchor_of_sgRoot₆₈b facts S _ q hR)]
      exact Proofs.ModelProperties.Preceq_self _
    · intro I' hI'
      rw [facts.nd.mkNode_cache] at hI'
      exact hparents.liveG1Parent _ hpropG1 A hAG1 c hc I' hI'
    · intro v hv cv hcv T₀ hT₀ psv hpsv srcScore hsrc vv hvv vsv hvsv tgtScore htgt C' hC'n hC'T
      have hms : (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv).st.core.s =
          M.opening_slot S.hc q := by
        rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
      have hvv' := hvv
      rw [hms] at hvv'
      have hsc := Restated.namedWalkScore_target_eq_source_of_proposalCandidateOn facts Hs Xb hf hHs
        hHsXb (s := M.opening_slot S.hc q - 1) (P := P) (v := v)
      simp only [hsucc] at hsc
      exact hsc c hc cv hcv hP' hloSource hpropConf hvoteHor hproposalHor hv T₀ hT₀
        ((hvoteData v hv P.erase hJB (Proofs.ModelProperties.Preceq_self _) cv hcv).2 T₀ hT₀) vv hvv
        (hrawExtra v hv cv hcv vv hvv') vsv hvsv psv hpsv C' hC'n hC'T _ (htgt C') _ (hsrc C')
  have hnames := Restated.namedHonestVotesName_of_namedVoteStoresExtendOn facts S Hs Xb hf
    hopenPosQ hvoteHor hstores hloVote hrunV
  have hrun := Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
    (M.opening_slot S.hc q) hopenPosQ hpropConf hproposalHor hloOpeningProposal
    (fun j hj => hf.tick_outcome j _ _ hj) hrunP c hc hP
  have hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc q)
      (fun X => Block.Preceq P.erase X) :=
    Restated.honestVotesCone_preceqOn facts S rho W Hs Xb (M.opening_slot S.hc q) hrun hnames
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
    intro v hv cc hcc
    exact hconfirmation v (by rw [← hconfEq]; exact hv) cc hcc
  have hlive := Restated.openingProposal_liveConfirmed_actionStore_after_gst_of_localReadsOn facts
    S Hs Xb hf hHs hHsXb hcom hqPos hloVote hactionQHor hpropA c hc hP hstores hreadBody
    hloOpeningProposal hrunV hrunP hrunConf
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S q)) - 1 =
      (M.opening_slot S.hc q) := by
    have hsc : (Restated.Vocabulary.Execution.Setup.a M S q) =
        M.support_cutoff S.E ((M.opening_slot S.hc q) + 1) :=
      Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts S.hc S.E q
    rw [hsc, facts.sch.slotOf_support_cutoff]
    exact Nat.add_sub_cancel ((M.opening_slot S.hc q)) 1
  have hgenuine : ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
      ∀ cc : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st.core.toHealing
          (M.confirmation_time S.E ((M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).cache ⇢ cc →
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M
        (M.gradeContract
          (M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st
              (M.confirmation_time S.E ((M.opening_slot S.hc q))))
            (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).record cc).cache)
        S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc q)))) ((M.opening_slot S.hc q)) P.erase := by
    intro v hv cc hcc
    have hvA : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)) := by rw [hconfEq]; exact hv
    obtain ⟨hroot, hanchor, hcand⟩ := hreadBody v hvA cc hcc
    obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract cc) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E ((M.opening_slot S.hc q)))) v).st.core
        (M.confirmation_time S.E ((M.opening_slot S.hc q)))) (M.opening_slot S.hc q)
    have hall := Restated.genuineConfirmationAndPreceq_of_postHealingConeOn facts
      S Hs Xb hf hHs hHsXb hcom hopenPosQ hloVote hconfirmationHor
      (hHs _ _ (facts.sch.Sts_support_cutoff_le_confirmation_time S.E _) hv) hvotes
      cc hcc hroot hanchor hcand D hD
    have hcc' : M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S q)
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).cache ⇢ cc := by
      rw [hconfEq]; exact hcc
    obtain ⟨st', hst'⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract cc) S.E
      S.hc (M.ns_setClock S.E (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st
        (Restated.Vocabulary.Execution.Setup.a M S q))
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S q) - 1)
    have hD' : M.update_confirmation_with (M.gradeContract cc) S.E S.hc
        (M.ns_setClock S.E (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st
          (Restated.Vocabulary.Execution.Setup.a M S q)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S q) - 1) ⇢ D := by
      rw [hslot, hconfEq, facts.hd.setClock_core_eq_store_with_t_s]
      exact hD
    have hcore : st'.core = D :=
      facts.dt.named_update_confirmation_with_core _ _ _ _ _ st' hst' D hD'
    have hliveD := hlive v hvA
      (M.mkNode st' (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).record cc)
      ⟨cc, hcc', st', hst', rfl⟩
    rewrite [facts.nd.mkNode_st] at hliveD; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hliveD; rw [hcore] at hliveD
    rw [facts.nd.mkNode_cache, ← hliveD]
    exact hall.1
  have hwindow := Restated.relativeCarrierWindowAt_of_fixedRootOn facts S Hs Xb hf hHs hHsXb
    hfb hqPos (p := .g0) hfix hlo hloPrevAction hprevActionDelay hprevActionHor hprevActionCap
    hactionDelayQ hactionQHor hactionQCap hdomainG0Hor hAprev
  have hg0 := Restated.g0ClearAtAction_of_relativeCarrierWindow_of_openingParentRunOn facts S Hs Xb
    hf hHs hfb hqPos hactionQHor hdomainHor hloPrevAction hwindow hparents c hc hP
    hAprev
  have hcover : Restated.ActionCarriersCoverOn M S rho Hs q P.erase
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))) := by
    unfold Restated.ActionCarriersCoverOn
    intro v hv n hn g hg A' hAsel
    obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) q
    have hGread : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n q ⇢ G := by
      unfold Restated.Vocabulary.Internal.PhaseGrades.nodeRead
      exact hG
    have hGanchor : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n q ⇢ G.anchor := by
      unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      exact returns_map_intro₆₈b
        (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hGread
    have hGclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n q P.erase ⇢
        G.clear P.erase := by
      unfold Restated.Vocabulary.Internal.PhaseGrades.nodeClear
      exact returns_map_intro₆₈b
        (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.clear P.erase) _ G hGread
    have hwmem := mem_stateBeforeTime_along₆₈b hf.sorted hf.onePath (S := S)
      (Restated.Vocabulary.Execution.Setup.a M S q)
    have hnmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v q :=
      ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)), hwmem, hn⟩
    have hGP : Block.Preceq G.anchor P.erase := by
      have hconfA := (Restated.Vocabulary.Proofs.w4_confAnchorWith_eq_nodeAnchor facts S rho v q _
        hwmem n hn G.anchor).2 hGanchor
      obtain ⟨c', hc', st', hst', rfl⟩ := hn
      have hc'' : M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.confirmation_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c' := by
        rw [← hconfEq]; exact hc'
      refine (hconfirmation v (by rw [← hconfEq]; exact hv) c' hc'').2.1 G.anchor ?_
      rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st, sgRoot_store_with_cache₆₈b facts,
        facts.nd.store_with_cache_core_s]
      rw [facts.nd.mkNode_cache, hconfEq] at hconfA
      unfold Restated.Vocabulary.Protocol.confAnchorWith
        Restated.Vocabulary.Proofs.Optimistic.tickStore at hconfA
      rw [← facts.hd.setClock_core_eq_store_with_t_s] at hconfA
      exact hconfA
    have hWb := Restated.actionSGBlockAt_eq_liveConfirmed_of_batchAlignedOn facts S
      (Hs ((Restated.Vocabulary.Execution.Setup.a M S q))) (Can := P.erase) (D := P.erase)
      (A := G.anchor) n hnmem (hlive v hv n hn) (hbatch v hv n hn)
      (Proofs.ModelProperties.Preceq_self _) G hGread rfl hGP
      (hg0 v (hHs _ _ (facts.gr.domain_le_a S q .g0) hv) n hn _ hGclear) g hg A' hAsel
    rw [hWb]
    exact Proofs.ModelProperties.Preceq_self _
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))).Nonempty :=
    nonempty_of_honestWeightMajority_l54 (hmajority _ hactionNextHor)
  have hnextGrade := Restated.namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn facts
    S Hs Xb hf hHs hHsXb hmajority hcover (hpostPreviousAction.trans hprevActionLe) hcutNext
    hnextActive.1 hnextActive.2 (hA q hAboundQ) hloQ hne
  have hlifecycle : Restated.NamedRawOpeningLifecycleAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb q P :=
    { roundPositive := hqPos
      proposal := ⟨c, hc, hP⟩
      proposerHonest := hpropConf
      proposalInHorizon := hproposalHor
      runBlock := hrun
      liveConfirmed := hlive
      actionCover := hcover
      gradeNext := hnextGrade }
  refine ⟨q, hqlo, hqhi, hcarrier, hforms, hlock, P, ⟨c, hc, hP⟩, ?_⟩
  refine
    { openingSlot := by rw [hqPredAdd]; exact hsucc
      proposal := by rw [hqPredAdd]; exact ⟨c, hc, hP⟩
      actionTargetParent := by rw [hqPredAdd]; exact hparents.actionTargetParent
      liveG1Parent := by rw [hqPredAdd]; exact hparents.liveG1Parent
      honestVotes := by rw [hqPredAdd]; exact hnames
      genuineConfirmation := ?_
      g0ClearAtAction := ?_
      lifecycle := by rw [hqPredAdd]; exact hlifecycle }
  · rw [hqPredAdd]
    intro v hv
    exact Restated.genuineConfirmationAt_of_withOn facts S Hs Xb hf hv hconfirmationHor
      (hgenuine v hv) hloConf (hrunConf v (by rw [hconfEq]; exact hv))
  · rw [hqPredAdd]
    intro v hv
    exact hg0 v (hHs _ _ (facts.gr.domain_le_a S q .g0) hv)

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Along `W`, if round `r` is ready, the named height-regime frame over `X` holds at `H` up to
    `stop`, the event index before `S.a r` is at most `stop`, the largest height maximum over `X` in
    `W stop` is less than `H + 2`, `S.a r` is in the horizon and `lo ≤ early r .g2`, then for every
    `p` in the set for `S.a r`, every node state `n` of its round-`r` action read and every body `B`
    at height `H + 1` such that the action FG source and the Q2 of `n` can return `some B.erase`,
    `B.erase` is in the filtered tree of every member of the set for `domain r g1`, and of every
    member of the set for `vote_time (opening_slot r)` at its store staged to that instant. -/
theorem voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ stop)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < H + 2)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∀ {p : V} (B : NamedBlock V),
      p ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r) →
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r,
      B ∈ n.st.bodies →
      (M.derive_named S.E S.cfg B).h = H + 1 →
      Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B.erase →
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some B.erase →
      (∀ w ∈ Hs (M.domain S.E S.hc r .g1),
        B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w)) ∧
      ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r)),
        B.erase ∈ M.get_filtered_block_tree
          (M.toHealing (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r))) w).st
            (M.vote_time S.E (M.opening_slot S.hc r))).core).toFG := by
  intro p B hp n hn hBmem hBheight hsource hselected
  exact Restated.voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_sourceOn facts
    S Hs Xb X hf hHs hHsXb hX hXXb ready hframe hactionPrefix hfrontier hactionHor hp B hn
    hselected hsource hBmem hBheight hlo

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
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

/-! ## The prefix FG selector cone of a height row -/

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

local macro "p45% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_45)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p50% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_50)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p64% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "pLad% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p48b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_48b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Two outcomes of the confirmation write on one store, under two grade contracts whose SG roots at
    that store have the same outcomes, confirm the same block. -/
private theorem update_confirmation_live_confirmed_agree₆₈b (facts : Record.Facts M)
    (gc gc' : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (hroot : ∀ R : Block V,
      M.get_sg_root_with gc E hc st.toHealing (M.round_of hc st.s) ⇢ R →
        M.get_sg_root_with gc' E hc st.toHealing (M.round_of hc st.s) ⇢ R)
    (st' st'' : M.S) (hst' : M.update_confirmation_with gc E hc st s ⇢ st')
    (hst'' : M.update_confirmation_with gc' E hc st s ⇢ st'') :
    st'.live_confirmed = st''.live_confirmed := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty gc E hc st.toHealing (M.round_of hc st.s)
  have hR' := hroot R hR
  choose score hscore using fun B => facts.fc.goldfish_score_nonempty E st.T
    ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff
        st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
    ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff
        st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true)) s B
  obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R (M.get_filtered_block_tree st.toHealing.toFG) score
    (fun B => decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff
      st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score B))
  by_cases helig : decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff
      st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score W) = true
  · rw [facts.hd.update_confirmation_with_live_confirmed_of_eligible gc E hc st s tm htm R hR
        score hscore W hW helig st' hst',
      facts.hd.update_confirmation_with_live_confirmed_of_eligible gc' E hc st s tm htm R hR'
        score hscore W hW helig st'' hst'']
  · have h1 : st'.live_confirmed = M.get_fg_root (M.toHealing st).toFG := by
      rcases facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot gc E hc st s tm
          htm R hR score hscore W hW st' hst' with ⟨C, -, hC⟩ | h
      · exact absurd hC helig
      · exact h
    have h2 : st''.live_confirmed = M.get_fg_root (M.toHealing st).toFG := by
      rcases facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot gc' E hc st s tm
          htm R hR' score hscore W hW st'' hst'' with ⟨C, -, hC⟩ | h
      · exact absurd hC helig
      · exact h
    rw [h1, h2]

/-- Along `W`, if `v` is in the set for `domain r .g0` and round `r`'s window opens at or after
    `lo`, then for two node states `n`, `n'` of `v`'s round-`r` action read, if the action FG source
    of `n` can return `some B`, every outcome of the action FG source of `n'` is `some B`. -/
private theorem actionFGSource_some_agree₆₈b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (n' : M.N)
    (hn' : n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {B : Block V}
    (ho : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    (o' : Option (Block V))
    (ho' : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n' ⇢ o') :
    o' = some B := by
  set before := W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v
    with hbefore
  obtain ⟨fr2, hfr2⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2)
  obtain ⟨fr1, hfr1⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  obtain ⟨fr0, hfr0⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0)
  have hF : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      m.st.core.F = before.st.core.F := (p48b% actionReadFrom_F₄₈b) facts S before r
  have hg0 : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      (M.readFrame m.cache (M.toHealing m.st.core) r).g0 =
        some (fr0.map (fun X => M.clipGrade X before.st.core.F)) := by
    intro m hm
    rw [← hF m hm]
    exact Restated.actionFrame_g0On facts S Hs Xb hf hr hhor hv
      (facts.gr.lo_le_domain_of_window_start S hr hlo _) m hm fr0 hfr0
  have hg1 : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      (M.readFrame m.cache (M.toHealing m.st.core) r).g1 =
        some (fr1.map (fun X => M.clipGrade X before.st.core.F)) := by
    intro m hm
    rw [← hF m hm]
    exact Restated.actionFrame_g1On facts S Hs Xb hf hr hhor
      (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv)
      (facts.gr.lo_le_domain_of_window_start S hr hlo _) m hm fr1 hfr1
  have hg2 : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      (M.readFrame m.cache (M.toHealing m.st.core) r).g2 =
        some (fr2.map (fun X => M.clipGrade X before.st.core.F)) := by
    intro m hm
    rw [← hF m hm]
    exact Restated.actionFrame_g2On facts S Hs Xb hf hr hhor
      (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hv)
      (facts.gr.lo_le_domain_of_window_start S hr hlo _) m hm fr2 hfr2
  have hround : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.round_of S.hc (M.toHealing m.st.core).s = r := by
    intro m hm
    have hs : (M.toHealing m.st.core).s = m.st.core.s := facts.sto.toHealing_s _
    rw [hs, (p48b% actionReadFrom_s₄₈b) facts S before r m hm]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r
  have htree : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_filtered_block_tree (M.toHealing m.st.core).toFG =
        M.get_filtered_block_tree (M.toHealing before.st.core).toFG :=
    (p48b% actionReadFrom_filtered₄₈b) facts S before r
  have hclear : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∀ m' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.clear (M.readFrame m.cache (M.toHealing m.st.core) r) =
        M.clear (M.readFrame m'.cache (M.toHealing m'.st.core) r) := by
    intro m hm m' hm'
    funext X
    cases hfr : fr0.map (fun X => M.clipGrade X before.st.core.F) with
    | none =>
        rw [facts.gr.clear_of_g0_some_none ((hg0 m hm).trans (congrArg some hfr)),
          facts.gr.clear_of_g0_some_none ((hg0 m' hm').trans (congrArg some hfr))]
    | some root =>
        rw [facts.gr.clear_of_g0 ((hg0 m hm).trans (congrArg some hfr)),
          facts.gr.clear_of_g0 ((hg0 m' hm').trans (congrArg some hfr))]
  have hlive : n.st.core.live_confirmed = n'.st.core.live_confirmed := by
    obtain ⟨st₁, hst₁, hcore⟩ := (p48b% actionReadFrom_core₄₈b) facts S before r n hn
    obtain ⟨st₂, hst₂, hcore'⟩ := (p48b% actionReadFrom_core₄₈b) facts S before r n' hn'
    rw [hst₁, hst₂, facts.nd.store_with_cache_core_live_confirmed,
      facts.nd.store_with_cache_core_live_confirmed]
    have hs0 : M.round_of S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core.s = r := by
      rw [facts.hd.setClock_core_eq_store_with_t_s, facts.sto.store_with_t_s_s]
      exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r
    refine update_confirmation_live_confirmed_agree₆₈b facts _ _ S.E S.hc _ _ ?_ _ _ hcore hcore'
    intro R hR
    rw [hs0] at hR ⊢
    rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor] at hR ⊢
    have hfr : ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
        (M.readFrame m.cache (M.toHealing (M.ns_setClock S.E before.st
          (Restated.Vocabulary.Execution.Setup.a M S r)).core) r).g1 =
          some (fr1.map (fun X => M.clipGrade X before.st.core.F)) := by
      intro m hm
      rw [← facts.gr.phaseResult_g1, ← (p48b% actionReadFrom_readFrame₄₈b) facts S before r r m hm,
        facts.gr.phaseResult_g1]
      exact hg1 m hm
    rw [show (M.readFrame n.cache (M.ns_setClock S.E before.st
      (Restated.Vocabulary.Execution.Setup.a M S r)).core.toHealing r).g1 = _ from hfr n hn] at hR
    rw [show (M.readFrame n'.cache (M.ns_setClock S.E before.st
      (Restated.Vocabulary.Execution.Setup.a M S r)).core.toHealing r).g1 = _ from hfr n' hn']
    exact hR
  unfold Restated.Vocabulary.Proofs.HealingSurface.actionFGSource at ho ho'
  simp only [hround n hn, hround n' hn'] at ho ho'
  obtain ⟨g, hg, hgo⟩ := ((p64% returns_bind_iff₆₄) _ _ _).1 ho
  obtain ⟨g', hg', hgo'⟩ := ((p64% returns_bind_iff₆₄) _ _ _).1 ho'
  obtain ⟨q, rfl, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hgo rfl
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  obtain ⟨G', hG'⟩ := facts.gr.read_nonempty (M.gradeContract n'.cache) S.E S.hc
    (M.toHealing n'.st.core) r
  obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
    (M.readFrame n.cache (M.toHealing n.st.core) r)
  obtain ⟨x', hx'⟩ := facts.gr.grade2Block_nonempty (M.toHealing n'.st.core)
    (M.readFrame n'.cache (M.toHealing n'.st.core) r)
  have hGQ : G.Q2 = some q := (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hg).symm
  have hxq : x = some q := (facts.nd.Sts_gradeContract_read_Q2 _ _ _ _ _ G hG x hx).symm.trans hGQ
  have hG'Q : g' = G'.Q2 := facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G' hG' _ hg'
  have hx'Q : G'.Q2 = x' := facts.nd.Sts_gradeContract_read_Q2 _ _ _ _ _ G' hG' x' hx'
  obtain ⟨clipped, hclipped, hqclipped⟩ := facts.gr.grade2Block_some x hx hxq
  have hqtree : q ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
    facts.gr.mem_filtered_of_grade2Block x hx hxq
  have hclipped' : (M.readFrame n'.cache (M.toHealing n'.st.core) r).g2 = some (some clipped) :=
    (hg2 n' hn').trans ((hg2 n hn).symm.trans hclipped)
  obtain ⟨q', hx'q', hqq'⟩ := facts.gr.preceq_grade2Block_of_g2 (hg0 n' hn') (hg1 n' hn')
    hclipped' (by rw [htree n' hn', ← htree n hn]; exact hqtree) hqclipped x' hx'
  obtain ⟨clipped'', hclipped'', hq'clipped⟩ := facts.gr.grade2Block_some x' hx' hx'q'
  have hcc : clipped'' = clipped :=
    Option.some.inj (Option.some.inj (hclipped''.symm.trans hclipped'))
  have hq'tree : q' ∈ M.get_filtered_block_tree (M.toHealing n'.st.core).toFG :=
    facts.gr.mem_filtered_of_grade2Block x' hx' hx'q'
  obtain ⟨q'', hxq'', hq'q''⟩ := facts.gr.preceq_grade2Block_of_g2 (hg0 n hn) (hg1 n hn)
    hclipped (by rw [htree n hn, ← htree n' hn']; exact hq'tree) (hcc ▸ hq'clipped) x hx
  have hq''q : q'' = q := Option.some.inj (hxq''.symm.trans hxq)
  have hqeq : q' = q := ModelProperties.Preceq_antisymm (hq''q ▸ hq'q'') hqq'
  have hg'q : g' = some q := by rw [hG'Q, hx'Q, hx'q', hqeq]
  subst hg'q
  have hGclear : G.clear = M.clear (M.readFrame n.cache (M.toHealing n.st.core) r) :=
    facts.gr.frameGradeRead_clear _ _ _ _ _ G ((facts.nd.gradeContract_read _ _ _ _ _ G).1 hG)
  have hG'clear : G'.clear = M.clear (M.readFrame n.cache (M.toHealing n.st.core) r) :=
    (facts.gr.frameGradeRead_clear _ _ _ _ _ G'
      ((facts.nd.gradeContract_read _ _ _ _ _ G').1 hG')).trans (hclear n' hn' n hn)
  have hlc : (M.toHealing n'.st.core).toFG.toSG.toGoldfishStore.live_confirmed =
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed := by
    rw [facts.sto.toHealing_live_confirmed, facts.sto.toHealing_live_confirmed, hlive]
  cases hdc : M.deepest_clear (some q)
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | none =>
      have hB := facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hdc _ hgo
      have hdc' : M.deepest_clear (some q)
          (M.toHealing n'.st.core).toFG.toSG.toGoldfishStore.live_confirmed G'.clear = none := by
        rw [hlc, hG'clear, ← hGclear]
        exact hdc
      rw [facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G' hG' hdc' _ hgo']
      exact hB.symm
  | some Wd =>
      have hB := facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hdc _ hgo
      have hdc' : M.deepest_clear (some q)
          (M.toHealing n'.st.core).toFG.toSG.toGoldfishStore.live_confirmed G'.clear =
            some Wd := by
        rw [hlc, hG'clear, ← hGclear]
        exact hdc
      rw [facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G' hG' hdc' _ hgo']
      exact hB.symm

/-- Under the hypotheses of `actionFGSource_some_agree₆₈b`, any two outcomes of the action FG
    source, over any two node states of `v`'s round-`r` action read, are equal. -/
private theorem actionFGSource_agree₆₈b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) {v : V}
    {r : Round} (hr : 0 < r) (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ o o' : Option (Block V),
      Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
      Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n' ⇢ o' → o = o' := by
  intro n hn n' hn' o o' ho ho'
  cases o with
  | some B =>
      exact (actionFGSource_some_agree₆₈b facts S Hs Xb hf hHs hr hhor hv hlo n hn n' hn'
        ho o' ho').symm
  | none =>
      cases o' with
      | none => rfl
      | some B' =>
          exact actionFGSource_some_agree₆₈b facts S Hs Xb hf hHs hr hhor hv hlo n' hn' n hn
            ho' none ho

/-- Along `W`, if `gstLagged ≤ Γ_neg1 r0`, the named height-regime frame over `X` holds at `H` up to
    `stop − 1`, event `i` is a tick of `a`'s signer at `ta` whose outcome lists the attestation `a`
    with height `H + 1`, the signer is in the set for `ta`, the largest `h_max` over `X` in `W i` is
    less than `H + 2`, and the bounds on `lo` hold, then some named block `Cfg` and block `T` give
    the prefix FG selector cone at `i`, `t_GST ≤ S.a (a.round − 1)`, and every member of the set for
    round `a.round`'s grade-1 domain instant grades some block `Q` 1 at that round. -/
theorem honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {r0 : Round}
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    {stop : Nat} {H : Height} {Prev : NamedBlock V}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb H (stop - 1) Prev a.round)
    (hiStart : inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ i)
    (hiStop : i < stop) (haHon : a.val_index ∈ Hs ta)
    (hiEvent : rho.events[i]? = some (Record.Event.tick a.val_index ta))
    (hiOutput : ∃ out : M.N × List (NamedObject V),
      M.tick S a.val_index (W i a.val_index) ta ⇢ out ∧ W (i + 1) a.val_index = out.1 ∧
        Object.attest a ∈ out.2)
    (hrow : a.height_pair.erase.height? = some (H + 1))
    (hfrontier : (X.sup fun u => (W i u).st.h_max) < H + 2)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    ∃ (Cfg : NamedBlock V) (T : Block V),
      Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb
        (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) stop H i a ta Cfg T ∧
      S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1) ∧
      ∀ w ∈ Hs (M.domain S.E S.hc a.round Phase.g1), ∃ Q : Block V, ∀ b : Bool,
        Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc a.round Phase.g1)) w).st a.round Phase.g1 Q ⇢ b →
            b = true := by
  have hΔ := S.E.Δ_pos
  obtain ⟨out0, hout0, hstep0, hmem0⟩ := hiOutput
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index
      (Object.attest a) ta := ⟨i, hiEvent, out0, hout0, hstep0, hmem0⟩
  have hsel := Restated.honestEmittedHeightRow_exactFGSelectorWitnessOn facts
    S Hs Xb (Hs ta) hf haHon hemit hrow
  obtain ⟨n, hn⟩ := (p63% actionReadFrom_nonempty₆₃w) facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  obtain ⟨hta, haAction, hwit⟩ := hsel n hn
  obtain ⟨o0, ho0⟩ := (p63% actionFGSource_nonempty₆₃w) facts S n
  obtain ⟨B, J, rfl, hBmem, hBstoredHeight, hBderivedHeight, hJderived, hshape⟩ := hwit o0 ho0
  have hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B.erase := ho0
  have hbodies : ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round, n'.st.bodies = n.st.bodies := fun n' hn' =>
    ((p50% actionReadFrom_bodies₅₀) facts S _ a.round n' hn').trans
      ((p50% actionReadFrom_bodies₅₀) facts S _ a.round n hn).symm
  have hσ : ∀ n' ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round, n'.st.core.σ B.erase = M.derive_named S.E S.cfg B := by
    intro n' hn'
    rw [(p45% actionReadFrom_σ₄₅) facts S _ a.round n' hn']
    have hBpre : B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
        a.val_index).st.bodies := by
      rw [← (p50% actionReadFrom_bodies₅₀) facts S _ a.round n hn]
      exact hBmem
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho _
      a.val_index _ (hf.onePath _).1 B hBpre
  have hiEvent' : rho.events[i]? =
      some (Record.Event.tick a.val_index (Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [hiEvent, hta]
  have hstateI : W i a.val_index =
      W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index ∨
      W i a.val_index =
        M.wake (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) :=
    Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hiEvent'
  have hstrictAction : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ i := by
    by_contra hnot
    have hlt : i < strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
      Nat.lt_of_not_ge hnot
    unfold strictEventIndex at hlt
    have hmem : Record.Event.tick a.val_index (Restated.Vocabulary.Execution.Setup.a M S a.round) ∈
        rho.events.filter (fun e => decide (e.time <
          Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
      rw [Restated.filter_eq_takeOn facts S Hs Xb hf _ (Restated.downward_lt _)]
      exact List.mem_of_getElem? (by
        rw [List.getElem?_take_of_lt hlt]
        exact hiEvent')
    have himpossible := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, Record.Event.time] at himpossible
    exact lt_irrefl _ himpossible
  have hactionHorizon : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon := by
    have hin := (hf.in_horizon (Record.Event.tick a.val_index ta)
      (List.mem_of_getElem? hiEvent)).2
    simpa only [Record.Event.time, hta, Record.Event.time] using hin
  have hroundFromStart : r0 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < Restated.Vocabulary.Execution.Setup.a M S r0 := by
      rw [hta]
      exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_of_not_ge hnot)
    have hstartCursor : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ i :=
      (strictEventIndex_le_inclusiveEventIndex rho _).trans hiStart
    have htimeLe : Restated.Vocabulary.Execution.Setup.a M S r0 ≤ ta :=
      Restated.le_time_of_index_ge_of_sorted hf.sorted hstartCursor hiEvent
    exact (not_le_of_gt htimeLt) htimeLe
  have ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round :=
    Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_action_horizon facts
      S hgst hroundFromStart hactionHorizon
  obtain ⟨A, hA⟩ := (p64% nodeQ2_some_of_actionFGSource₆₄) facts S hf n hn hsource
  have hr : 0 < a.round := Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn hA
  have haAct : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [← hta]
    exact haHon
  have haG0 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g0) :=
    hHs _ _ (facts.gr.domain_le_a S a.round .g0) haAct
  have haG2 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g2) :=
    hHs _ _ (facts.gr.domain_le_a S a.round .g2) haAct
  have hloEarly : lo ≤ M.early S.E S.hc a.round .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hloOpen
  have hiFrame : i ≤ stop - 1 := Nat.le_sub_one_of_lt hiStop
  have hframeAtSelector : Restated.NamedHeightRegimeFrameOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb H i Prev a.round := {
    floor := fun v hv m hm Y hYrun hYheight hPrevY =>
      hframe.floor v hv m (hm.trans hiFrame) Y hYrun hYheight hPrevY
    prevRun := hframe.prevRun
    prevHeight := hframe.prevHeight
    rootBelow := fun v hv m hm Q hQmem hQheight hPrevQ =>
      hframe.rootBelow v hv m (hm.trans hiFrame) Q hQmem hQheight hPrevQ
    sourceAbove := fun p r hp hprefix hhor =>
      hframe.sourceAbove p r hp (hprefix.trans hiFrame) hhor }
  have hfrontier' : (X.sup fun u => (W i u).st.core.h_max) < H + 2 := hfrontier
  have hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1) := by
    have hcut : gstLagged S ≤
        Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ ((a.round - 1) + 1) := by
      rw [Nat.sub_add_cancel hr]
      exact hgst.trans
        (Restated.Vocabulary.Proofs.HealingSurface.Γ_neg1_mono facts S.hc S.E.Δ_pos hroundFromStart)
    rw [(pLad% Γ_neg1_add_rounds') facts S.hc S.E.Δ (a.round - 1) 1] at hcut
    simp only [gstLagged, readyLag] at hcut
    have hprevCut : S.E.t_GST ≤
        Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (a.round - 1) := by
      linarith
    have hg0 := (Restated.openingInstants_l63 facts S (a.round - 1)).1
    have hdom := facts.gr.domain_add_five_delta_le_action S (a.round - 1) .g0
    have hprop := facts.sch.Γ_0_eq_proposal_time S.hc S.E (a.round - 1)
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 at hprevCut
    unfold Restated.Vocabulary.Execution.Setup.a
    linarith
  have hguard := Restated.crossReaderBodyReadyGuard_of_namedHeightRegimeFrameOn facts
    S Hs Xb hf hHs hHsXb (X := X) hgstLo hframe hiStart hiStop haG0 hiEvent
      ⟨out0, hout0, hstep0, hmem0⟩ hrow hfrontier
  have hpreparedG1 := Restated.actionFGSource_rawG1_at_firstInteriorOn facts
    S Hs Xb hf hHs hHsXb ready hactionHorizon haG2 n hn hsource (hguard n hn) hloOpen
  have hG1 : ∀ w ∈ Hs (M.domain S.E S.hc a.round Phase.g1), ∃ Q : Block V, ∀ b : Bool,
      Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc a.round Phase.g1)) w).st a.round Phase.g1 Q ⇢ b →
          b = true := by
    intro w hw
    obtain ⟨Q, -, hQ⟩ := hpreparedG1 w hw _ hA
    exact ⟨Q, hQ⟩
  have hcone :
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc a.round)
          (fun Y => Block.Preceq B.erase Y) ∨
        Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc a.round + 1)
          (fun Y => Block.Preceq B.erase Y) := by
    by_cases hlocal : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ some B.erase
    · have hK6 := Restated.voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrameOn facts
        S Hs Xb X hf hHs hHsXb hX hXXb ready hframeAtSelector hstrictAction hfrontier'
          hactionHorizon hloEarly B haAct n hn hBmem hBderivedHeight hsource hlocal
      exact Or.inl
        (Restated.selectedQ2_openingVotesConeOn facts S Hs Xb hf hHs hHsXb hr ready haAct hn
          hlocal hK6 hloOpen)
    · have hmemA := (p63% mem_stateBeforeTime_along₆₃) hf.sorted hf.onePath
        (Restated.Vocabulary.Execution.Setup.a M S a.round)
      rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
          facts S rho a.val_index a.round _ hmemA n hn hA hsource with
        ⟨C, hgenuine, -, -, -, hBC⟩ | hsourceQ2
      · have hmain := Restated.voterAnchorSourceClearInputsMain_of_namedFrame_sourceOn facts
          S Hs Xb X hf hHs hHsXb hX hXXb hr ready hpostPrev hframeAtSelector hstrictAction
            hfrontier' hactionHorizon hloOpen A B haAct n hn hA hsource hBmem hBderivedHeight
            hlocal
        have hca := Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action
          facts S a.round
        rw [← hca] at hgenuine
        rcases Restated.genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputsOn
            facts S Hs Xb hf hHs hHsXb ready haAct hgenuine hBC hn
            hBmem hBderivedHeight hactionHorizon hmain.1 hmain.2
            (through := M.vote_time S.E (M.opening_slot S.hc a.round + 1)) (le_refl _) hloEarly with
          hprogress | hprotected
        · obtain ⟨w, hw, u, hu, hmax⟩ := hprogress
          exfalso
          have hpt := facts.sch.Optimistic_proposal_time_nonneg S.E (M.opening_slot S.hc a.round)
          obtain ⟨hg0, hvt, hsc, hvf, hnext, hact⟩ := Restated.openingInstants_l63 facts S a.round
          have hwX : w ∈ X :=
            hX (M.vote_time S.E (M.opening_slot S.hc a.round + 1)) (by linarith) hw
          have huAction : u < Restated.Vocabulary.Execution.Setup.a M S a.round :=
            hu.trans_lt (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S a.round)
          have hcursor : inclusiveEventIndex rho u ≤
              strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
            rw [strictEventIndex_eq_inclusiveEventIndex_pred]
            exact inclusiveEventIndex_mono rho (Int.le_sub_one_iff.mpr huAction)
          have hmono : (W (inclusiveEventIndex rho u) w).st.core.h_max ≤ (W i w).st.core.h_max :=
            (p59% hMax_mono_along₅₉) facts S hf.onePath w (hcursor.trans hstrictAction)
          have hsup : (W i w).st.core.h_max ≤ (X.sup fun u => (W i u).st.core.h_max) :=
            Finset.le_sup (f := fun u => (W i u).st.core.h_max) hwX
          have hmax' : H + 1 + 2 ≤ (W (inclusiveEventIndex rho u) w).st.core.h_max := hmax
          have hnat : ∀ x y : Nat, x + 1 + 2 ≤ y → y < x + 2 → False := by
            intro x y h1 h2
            omega
          exact hnat _ _ (hmax'.trans (hmono.trans hsup)) hfrontier'
        · exact Or.inr hprotected.2
      · exact False.elim (hlocal (hsourceQ2 ▸ hA))
  refine ⟨B, J, ?_, hpostPrev, hG1⟩
  exact {
    startLeIndex := hiStart
    indexLtStop := hiStop
    signerHonest := haHon
    exactTick := hiEvent
    tickOutput := by
      intro out hout
      obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) S.E S.hc
        (S.node a.val_index) n.st n.record
      have haD := haAction D hD
      have hta' := hta
      subst hta'
      have h0 := Restated.action_emissionOn facts S rho Hs Xb hf i a.val_index a.round hiEvent
        out0 hout0 n hn D hD
      have h1 := Restated.action_emissionOn facts S rho Hs Xb hf i a.val_index a.round hiEvent
        out hout n hn D hD
      rcases h1 with ⟨_, h1⟩ | ⟨hasleep, _⟩
      · rw [h1, ← haD]
        exact List.mem_singleton_self _
      · rcases h0 with ⟨hawake0, _⟩ | ⟨_, h0⟩
        · exact absurd hawake0 hasleep
        · rw [h0] at hmem0
          exact absurd hmem0 (List.not_mem_nil)
    emitted := hemit
    actionTime_eq := hta
    exactAction := fun n' hn' => (hsel n' hn').2.1
    exactFGSource := fun n' hn' o ho => actionFGSource_agree₆₈b facts S Hs Xb hf hHs hr
      hactionHorizon haG0 hloOpen n' hn' n hn o _ ho hsource
    sourceMem := fun n' hn' => by rw [hbodies n' hn']; exact hBmem
    sourceStoredHeight := fun n' hn' => by rw [hσ n' hn']; exact hBderivedHeight
    sourceDerivedHeight := hBderivedHeight
    checkpointStored := fun n' hn' => by rw [hσ n' hn']; exact hJderived
    checkpointDerived := hJderived
    targetOrTimeout := hshape
    cone := hcone }

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
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pD42b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Model.Conditions.Claim13beRoute3_42b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
