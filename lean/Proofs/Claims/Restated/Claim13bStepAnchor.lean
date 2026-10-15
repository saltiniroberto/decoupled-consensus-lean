import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bDirection
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_MaximumCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepAnchor

/-!
# The anchor of the next round

The facts about the round-`(r + 1)` anchor: its height, its specification when the honest heights
moved, that it is in play, and the height votes and bodies its definition reads; stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of sts steps, every validator's store holds a named body whose replay stands at
    exactly the store's maximum height. -/
theorem hMax_attained_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (m : Nat) (v : V) :
    ∃ B : NamedBlock V, B ∈ (x[m][v].st).st.bodies ∧
      (M.derive_named S.E S.cfg B).h = (x[m][v].st).st.core.h_max := by
  obtain ⟨w, hw, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v m
  have h := Restated.Vocabulary.Proofs.NamedMaximumCarrier.maximum_carrier_stateBefore facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v m) (Record.veventsOf M S Sched x v m).length v
    w hw
  rwa [hwv] at h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A height is one of the fresh honest attesters' vote heights read along `att` exactly when some
    member `q` of `freshAttestersW S Sched x (r + 1) (n' + 1)` has in `att q` a height vote at it. -/
theorem mem_freshVoteHeights (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {n' : Nat}
    {att : V → NamedAttestation V} {h₀ : Height} :
    h₀ ∈ Restated.freshVoteHeights M S Sched x r n' att ↔
      ∃ q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1), ∃ (entry : BlockId) (tmo : Bool),
        (att q).height_pair = NamedHeightPair.vote h₀ entry tmo := by
  classical
  simp only [Restated.freshVoteHeights, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hmem⟩
    refine ⟨q, hq, ?_⟩
    rcases hp : (att q).height_pair with _ | ⟨h', entry, tmo⟩
    · rw [hp] at hmem
      simp at hmem
    · rw [hp] at hmem
      simp only [Finset.mem_singleton] at hmem
      exact ⟨entry, tmo, by rw [hmem]⟩
  · rintro ⟨q, hq, entry, tmo, hp⟩
    refine ⟨q, hq, ?_⟩
    rw [hp]
    exact Finset.mem_singleton_self _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the old anchor's height is less than the new anchor's height read along `att`, some member
    `q` of `freshAttestersW S Sched x (r + 1) (n' + 1)` has in `att q` a height vote at exactly that
    height. -/
theorem exists_fresh_at_newAnchorHeight (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat}
    {att : V → NamedAttestation V} {h : Height}
    (hmove : h < Restated.newAnchorHeight M S Sched x r n' att h) :
    ∃ q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1), ∃ (entry : BlockId) (tmo : Bool),
      (att q).height_pair
        = NamedHeightPair.vote (Restated.newAnchorHeight M S Sched x r n' att h) entry tmo := by
  classical
  have hm : h < max h ((Restated.freshVoteHeights M S Sched x r n' att).sup id) := hmove
  have hsup : Restated.newAnchorHeight M S Sched x r n' att h
      = (Restated.freshVoteHeights M S Sched x r n' att).sup id := by
    show max h ((Restated.freshVoteHeights M S Sched x r n' att).sup id)
      = (Restated.freshVoteHeights M S Sched x r n' att).sup id
    rcases le_total h ((Restated.freshVoteHeights M S Sched x r n' att).sup id) with hle | hge
    · exact max_eq_right hle
    · exfalso
      rw [max_eq_left hge] at hm
      exact absurd hm (lt_irrefl h)
  have hne : (Restated.freshVoteHeights M S Sched x r n' att).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Restated.freshVoteHeights M S Sched x r n' att) with hemp | hne
    · exfalso
      have hz : (Restated.freshVoteHeights M S Sched x r n' att).sup id = 0 := by
        rw [hemp, Finset.sup_empty]
        rfl
      rw [hz, max_eq_left (Nat.zero_le h)] at hm
      exact absurd hm (lt_irrefl h)
    · exact hne
  obtain ⟨h₀, hmem, heq⟩ :=
    Finset.exists_mem_eq_sup (Restated.freshVoteHeights M S Sched x r n' att) hne id
  have hna : Restated.newAnchorHeight M S Sched x r n' att h = h₀ := by rw [hsup, heq]; rfl
  rw [hna]
  exact (Restated.mem_freshVoteHeights facts).mp hmem

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_anchor {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- Every node state the round-`r` action read from `before` can give has the chain-state map of
    `before`'s store. -/
private theorem actionReadFrom_σ_anchor (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.σ = before.st.core.σ := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_σ _ _ _ _ _ X hX, facts.hd.ModelProperties_setClock_core_σ]

/-- If the named store `st` satisfies the confirmation-membership invariant, so does `st` with the
    grade cache `c` written into it. -/
private theorem invariant_store_with_cache_anchor (facts : Record.Facts M) (E : Env V)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : M.NS) (c : M.Cache)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st) :
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg
      (M.store_with_cache st c) := by
  simp only [Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant,
    Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant, Restated.Vocabulary.Proofs.NamedStore.Coherent,
    Restated.Vocabulary.Proofs.NamedStore.TreeView, Restated.Vocabulary.Proofs.NamedStore.ErasureUnique,
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed, Restated.Vocabulary.Proofs.NamedStore.PoolView,
    Restated.Vocabulary.Proofs.NamedStore.DerivedView, Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree,
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Confirmed,
    facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView, facts.nd.store_with_cache_bodies,
    facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_sg_votes,
    facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau,
    facts.nd.store_with_cache_core_attestations] at h ⊢
  exact h

/-- For every world `w` that can hold strictly before round `r`'s action instant and every node
    state `n` the action read can build from `v`'s node state in `w`, if the finality-gadget source
    at `n` can return `Q`, then `Q` is in the block tree of `v`'s store in `w`. -/
theorem fgSource_mem_stateBeforeTime' (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round)
    {Q : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Q →
    Q ∈ (w v).st.core.T := by
  intro w hw n hn hsource
  have hnmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r :=
    ⟨w, hw, hn⟩
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
    obtain ⟨c, -, st, hst, rfl⟩ := hn
    rewrite [facts.nd.mkNode_st]
    exact invariant_store_with_cache_anchor facts S.E S.cfg st c <|
      facts.dt.invariant_update_gradeContract c S.E S.hc S.cfg _ _
      (facts.hd.invariant_clock S.E S.cfg _ ((Restated.Vocabulary.Execution.Setup.a M S r))
        (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
          ((Restated.Vocabulary.Execution.Setup.a M S r)) v w hw).1) st hst
  have hround := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r _ hnmem
  have hdec : ∃ A2, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 ∧
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ some Q := by
    exact (returns_bind_iff_anchor _ _ _).1 hsource
  obtain ⟨A2, hA2, hF⟩ := hdec
  have hround' : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact hround
  rw [hround'] at hA2 hF
  have hT : n.st.core.T = (w v).st.core.T := by
    obtain ⟨c, -, D, hD, rfl⟩ := hn
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX,
      facts.dt.update_confirmation_with_T _ _ _ _ _ X hX, facts.hd.ModelProperties_setClock_core_T]
  rw [← hT]
  exact Restated.Vocabulary.Proofs.NamedActionSources.frame_fg_source_mem facts S n.cache n.st r
    hinv A2 hA2 hF

end

section
set_option autoImplicit false

/-- If a store's bodies are parent-closed, every named ancestor of a body is itself a body. -/
theorem mem_bodies_of_preceq {st : M.NS}
    (hcl : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst hAB
      exact hcl.1
  | node parent s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · have hp := hcl.2 _ hB
        rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.named_parent_node] at hp
        exact ih hp (by simpa only [NamedBlock.Preceq] using hparent)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If an attestation `a` that `q`'s round-`(r + 1)` action duty can compute from the node state `q`
    holds at step `n'` carries a height vote for height `h₀` with root `entry`, then some block
    `Cfg` has, in the chain state `q`'s store at step `n'` records for it, height `h₀` and a height
    target with root `entry`, and that height target is the erasure of a named body `C` of the same
    store, a block at height `h₀` whose own replay names it as its height's entry. -/
theorem vote_entry_of_fresh (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n' : Nat}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {q : V}
    (hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1))
    {h₀ : Height} {entry : BlockId} {tmo : Bool} {a : NamedAttestation V}
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q (r + 1))
    (hvote : a.height_pair = NamedHeightPair.vote h₀ entry tmo) :
    ∃ Cfg : Block V, ((x[n'][q].st).st.core.σ Cfg).h = h₀ ∧
      ((x[n'][q].st).st.core.σ Cfg).T_h.root = entry ∧
      ∃ C : NamedBlock V, C ∈ (x[n'][q].st).st.bodies ∧ C.root = entry ∧
        (M.derive_named S.E S.cfg C).h = h₀ ∧
        (M.derive_named S.E S.cfg C).T_h = C.erase := by
  classical
  -- one world before the action instant holds at `q` the node state `x` gives `q` at `n'`
  obtain ⟨w, hw, hwq⟩ := Restated.stateBeforeTime_runOf_action facts S Sched x hn' q
  -- the node state of the action read the attestation was computed from
  obtain ⟨n, hn, ns, rec, hD⟩ := ha
  rw [← hwq] at hn
  have hnmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M (Setup.alwaysAwake S)
        (Record.runOfM M S Sched x q (n' + 1)) q (r + 1) := ⟨w, hw, hn⟩
  -- an outcome of the finality-gadget source at that node state
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing n.st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ o :=
    (returns_bind_iff_anchor _ _ _).2 ⟨A2, hA2, ho⟩
  obtain ⟨Cfg, rfl, hCfgh, hCfgroot⟩ :=
    Restated.source_of_actionAttestation_heightPair facts (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x q (n' + 1)) q (r + 1) n hnmem (ns, rec, a) hD hvote o hsrc
  -- the source block is a named body of the store read strictly before the action instant
  have hCfgT := Restated.fgSource_mem_stateBeforeTime' facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x q (n' + 1)) q (r + 1) w hw n hn hsrc
  have hco := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x q (n' + 1)) _ q w hw).1.1.1
  have hσr : n.st.core.σ = (w q).st.core.σ :=
    actionReadFrom_σ_anchor facts (Setup.alwaysAwake S) (w q) (r + 1) n hn
  have hCfgh' : ((w q).st.core.σ Cfg).h = h₀ := by rw [← hσr]; exact hCfgh
  have hCfgroot' : ((w q).st.core.σ Cfg).T_h.root = entry := by rw [← hσr]; exact hCfgroot
  rw [hwq] at hCfgT hco hCfgh' hCfgroot'
  rw [hco.1] at hCfgT
  obtain ⟨Cfgn, hCfgnMem, hCfgnErase⟩ := Finset.mem_image.mp hCfgT
  have hσ : (x[n'][q].st).st.core.σ Cfg = M.derive_named S.E S.cfg Cfgn := by
    have hd := hco.2.2.2.2 Cfgn hCfgnMem
    rw [hCfgnErase] at hd
    exact hd
  have hCfgnh : (M.derive_named S.E S.cfg Cfgn).h = h₀ := by rw [← hσ]; exact hCfgh'
  -- the height target is the erasure of a named ancestor that is its own height's entry
  obtain ⟨C, hCle, hCerase, hCheight⟩ :=
    facts.cs.entry_ancestor_same_height S.E S.cfg Cfgn
  have hCself : (M.derive_named S.E S.cfg C).T_h = C.erase := by
    rw [facts.cs.entry_eq_on_plateau S.E S.cfg hCle hCheight]
    exact hCerase.symm
  have hCmem : C ∈ (x[n'][q].st).st.bodies :=
    Restated.mem_bodies_of_preceq hco.2.2.1 hCfgnMem hCle
  have hCroot : C.root = entry := by
    rw [← Proofs.NamedWire.erase_root C, hCerase, ← hσ]
    exact hCfgroot'
  exact ⟨Cfg, hCfgh', hCfgroot', C, hCmem, hCroot, hCheight.trans hCfgnh, hCself⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `att` gives every fresh honest attester of round `r + 1` an attestation its action duty can
    compute at step `n'`, and the old anchor's height is less than the new anchor's height read
    along `att`, then the new anchor read along `att` satisfies `NewAnchorSpec` along `att`. -/
theorem newAnchor_spec_of_move (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n' : Nat}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    {T : NamedBlock V}
    (hmove : (M.derive_named S.E S.cfg T).h
      < Restated.newAnchorHeight M S Sched x r n' att (M.derive_named S.E S.cfg T).h) :
    Restated.NewAnchorSpec M S Sched x r n' att T (Restated.newAnchor M S Sched x r n' att T) := by
  classical
  have hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C := by
    obtain ⟨q, hq, entry, tmo, hvote⟩ := Restated.exists_fresh_at_newAnchorHeight facts S Sched x hmove
    obtain ⟨-, -, -, C, hCmem, hCroot, hCh, hCself⟩ := Restated.vote_entry_of_fresh facts S Sched x
      hn' (Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hq)
      (hatt q hq) hvote
    refine ⟨C, ⟨q, hq, hCmem⟩, hCh, hCself, q, hq, hCmem, Restated.newAnchorHeight M S Sched x r n'
      att (M.derive_named S.E S.cfg T).h, tmo, ?_⟩
    rw [hCroot]
    exact hvote
  show Restated.NewAnchorSpec M S Sched x r n' att T
    (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
  rw [dif_pos hex]
  exact hex.choose_spec

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `att` gives every fresh honest attester of round `r + 1` an attestation its action duty can
    compute at step `n'`, the chain-state height of the round-`(r + 1)` anchor read along `att` is
    the largest of the old anchor's height and the heights the attestations `att q` of the fresh
    honest attesters `q` vote at. -/
theorem newAnchor_height (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n' : Nat}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (T : NamedBlock V) :
    (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h
      = Restated.newAnchorHeight M S Sched x r n' att (M.derive_named S.E S.cfg T).h := by
  classical
  by_cases hmove : (M.derive_named S.E S.cfg T).h
      < Restated.newAnchorHeight M S Sched x r n' att (M.derive_named S.E S.cfg T).h
  · exact (Restated.newAnchor_spec_of_move facts S Sched x hn' hatt hmove).2.1
  · have hnot : Restated.newAnchorHeight M S Sched x r n' att (M.derive_named S.E S.cfg T).h
        = (M.derive_named S.E S.cfg T).h := by
      have hm : ¬ ((M.derive_named S.E S.cfg T).h
          < max (M.derive_named S.E S.cfg T).h
            ((Restated.freshVoteHeights M S Sched x r n' att).sup id)) := hmove
      show max (M.derive_named S.E S.cfg T).h
        ((Restated.freshVoteHeights M S Sched x r n' att).sup id) = (M.derive_named S.E S.cfg T).h
      exact le_antisymm (not_lt.mp hm) (le_max_left _ _)
    by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
    · have : Restated.newAnchor M S Sched x r n' att T = hex.choose := by
        show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
          then h.choose else T) = hex.choose
        rw [dif_pos hex]
      rw [this]
      exact hex.choose_spec.2.1
    · have : Restated.newAnchor M S Sched x r n' att T = T := by
        show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
          then h.choose else T) = T
        rw [dif_neg hex]
      rw [this, hnot]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of attestations, the round-`(r + 1)` anchor read along `att` is one of
    the blocks some message in the sent log contains or some honest validator holds. -/
theorem newAnchor_blockInLog (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat}
    {att : V → NamedAttestation V} {T : NamedBlock V}
    (hT : Restated.blockInLog M S Sched x T) :
    Restated.blockInLog M S Sched x (Restated.newAnchor M S Sched x r n' att T) := by
  classical
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = hex.choose := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
        then h.choose else T) = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hq, hmem⟩ := hex.choose_spec.1
    have hhon : Restated.HonestThrough M Sched x n' q := by
      intro t ht
      exact Restated.honestThrough_of_mem_freshAttestersW facts hq t
        (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
    rw [hchoice]
    exact Restated.blockInLog_of_mem_bodies facts S Sched hhon hmem
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = T := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
        then h.choose else T) = T
      rw [dif_neg hex]
    rw [hchoice]
    exact hT

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a validator's store holds a named body whose chain state stands at a height of at least `2`,
    then some quorum of the electorate has, for each of its members, an attestation included in a
    body of that same store, signed under that member's name, whose height pair is a vote at the
    body's height minus one. -/
theorem carried_vote_of_tree_block (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat} {v : V}
    {B : NamedBlock V} (hB : B ∈ (x[m][v].st).st.bodies)
    (hpos : 2 ≤ (M.derive_named S.E S.cfg B).h) :
    ∃ Q : Finset V, S.E.electorate.IsQuorum Q ∧ ∀ signer ∈ Q,
      ∃ (carrier : NamedBlock V) (a : NamedAttestation V) (entry : BlockId) (tmo : Bool),
        carrier ∈ (x[m][v].st).st.bodies ∧ a ∈ carrier.attestations ∧
        a.val_index = signer ∧
        a.height_pair
          = NamedHeightPair.vote ((M.derive_named S.E S.cfg B).h - 1) entry tmo := by
  classical
  have hcl : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (x[m][v].st).st :=
    (Restated.nodeInvariant_sts facts S Sched x m v).1.1.1.2.2.1
  obtain ⟨N, hNle, hNh, hNstep⟩ := facts.csAdded.exists_crossing_ancestor S.E S.cfg B hpos
  have hNmem : N ∈ (x[m][v].st).st.bodies := Restated.mem_bodies_of_preceq hcl hB hNle
  cases N with
  | genesis =>
      exfalso
      have hone : (M.derive_named S.E S.cfg (NamedBlock.genesis : NamedBlock V)).h = 1 :=
        facts.cs.derive_named_genesis_h S.E S.cfg
      have hpar : (NamedBlock.genesis : NamedBlock V).parent = NamedBlock.genesis :=
        Sts.namedBlock_parent_genesis
      rw [hpar, hone] at hNstep
      exact absurd hNstep (by decide)
  | node parent s root votes support rows proposer =>
      have hpar : (NamedBlock.node parent s root votes support rows proposer).parent
          = parent := Sts.namedBlock_parent_node parent s root votes support rows proposer
      rw [hpar] at hNstep
      have hAdvance : (M.derive_named S.E S.cfg
            (NamedBlock.node parent s root votes support rows proposer)).h
          ≠ (M.derive_named S.E S.cfg parent).h := by
        rw [hNstep]
        exact Nat.succ_ne_self _
      have hBeq : (M.derive_named S.E S.cfg B).h
          = (M.derive_named S.E S.cfg parent).h + 1 := by rw [← hNh, hNstep]
      have hparh : (M.derive_named S.E S.cfg parent).h
          = (M.derive_named S.E S.cfg B).h - 1 := by
        rw [hBeq, Nat.add_sub_cancel]
      obtain ⟨Q, hQ, hsign⟩ := facts.csAdded.crossing_matching_quorum
        S.E S.cfg parent s root votes support rows proposer hAdvance
      refine ⟨Q, hQ, ?_⟩
      intro signer hsigner
      obtain ⟨carrier, a, hcle, hrow, hval, hmatch⟩ := hsign signer hsigner
      have hcmem : carrier ∈ (x[m][v].st).st.bodies :=
        Restated.mem_bodies_of_preceq hcl hNmem hcle
      obtain ⟨tmo, hp⟩ := Sts.vote_of_matchesEntry hmatch
      refine ⟨carrier, a, (M.derive_named S.E S.cfg parent).T_h.root, tmo, hcmem, hrow,
        hval, ?_⟩
      rw [hp, hparh]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a validator's store holds a body that includes an attestation whose signer is honest through
    that step, then the sent log `x[m].sent` holds that signer's own signed message for that
    attestation. -/
theorem carried_vote_in_log (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {v : V}
    {carrier : NamedBlock V} (hc : carrier ∈ (x[m][v].st).st.bodies)
    {a : NamedAttestation V} (ha : a ∈ carrier.attestations)
    (hq : Restated.HonestThrough M Sched x m a.val_index) :
    (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[m].sent := by
  classical
  have hnotgen : carrier ≠ NamedBlock.genesis := by
    intro hgen
    rw [hgen, Sts.named_genesis_attestations] at ha
    exact List.not_mem_nil ha
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][v].st).st
      (NamedObject.block carrier) = false := by
    rw [Record.st_zero M S Sched x v]
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
    exact fun h => hnotgen (facts.nd.initial_body_eq_genesis _ _ h)
  have hm : Restated.Vocabulary.Execution.Object.processed M (x[m][v].st).st
      (NamedObject.block carrier) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    exact hc
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_first_flip facts S Sched x v (NamedObject.block carrier) m h0 hm
  have hcarries : carries (NamedObject.block carrier) (NamedObject.attest a) :=
    Or.inr ⟨a, ha, rfl⟩
  have hauthor : NamedObject.author (NamedObject.attest a) = some a.val_index :=
    Sts.author_attest a
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, out₁, hout₁, hst₁, hem⟩
  · have hsm : sm ∈ x[i].sent := (Restated.sent_of_deliver facts S Sched x hlbl).1
    have hmsg : sm.msg = NamedObject.block carrier := by
      rcases hpay with h | ⟨Bl, -, hcc⟩
      · exact h
      · exact hcc.elim
    have hhon : Restated.HonestThrough M Sched x i a.val_index := fun t ht =>
      hq t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt him)))
    have hres := hexec.carried i sm (NamedObject.attest a) a.val_index hsm
      (by rw [hmsg]; exact hcarries) hauthor hhon
    exact Restated.mem_sent_of_le facts x (le_of_lt him) hres
  · rcases hem with hmem | ⟨Bl, -, hcc⟩
    · have hsend := facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v
        (Record.wakeStage M Sched (τ : Int) x[i] v) (τ : Int)
      have hsent := Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd hsend hout₁
        hst₁ hmem
      have hhon : Restated.HonestThrough M Sched x (i + 1) a.val_index := fun t ht =>
        hq t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt him)))
      have hres := hexec.carried (i + 1) ⟨v, NamedObject.block carrier⟩
        (NamedObject.attest a) a.val_index hsent hcarries hauthor hhon
      exact Restated.mem_sent_of_le facts x (Nat.succ_le_of_lt him) hres
    · exact hcc.elim

end

end DecoupledConsensusModel.Sts.Restated
