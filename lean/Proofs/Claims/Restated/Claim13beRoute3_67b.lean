import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_66
import Proofs.Claims.Restated.Claim13beRoute3_66b
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_SeedFreshRowRenewal
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecordClean
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
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
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_67b

/-!
# The height-progress seed over the record

Theorems that build the height-progress seed from a post-GST base round: the opening proposals of
carrier rounds, their grades, the fresh predecessor rows and the closer at the exact frontier
height, stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`. Every
theorem that takes `Restated.AdmissibleFieldsOn` reads the run along that bundle's path `W`; the
height written `M` in prose is named `Mh`, since `M` names the model.
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
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₇b (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₇b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₇b S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k − 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₇b {S : Setup V} {rho : Record.Run V}
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

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n − 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₆₇b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₇b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
/-- For `t ≤ t'`, at most as many events of `rho` are strictly before `t` as before `t'`. -/
private theorem strict_mono₆₇b (rho : Record.Run V) {t t' : Time} (h : t ≤ t') :
    strictEventIndex rho t ≤ strictEventIndex rho t' :=
  Restated.strict_lengths_mono rho h

/-- The field `proposal` of an opening window read at the worlds of `W`: some outcome `c` of the
    cache update at slot `s`'s proposal instant on the proposer's node state in
    `W (strictEventIndex rho (proposal_time s))` makes the proposal duty return `some B`. -/
private theorem proposal_along₆₇b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) {B : NamedBlock V}
    (h : ∃ c : M.Cache,
      M.onPhaseTick S.E S.hc
        ((fun t => W (strictEventIndex rho t)) (M.proposal_time S.E s) (S.E.proposer s)).st.core.toHealing
        (M.proposal_time S.E s)
        ((fun t => W (strictEventIndex rho t)) (M.proposal_time S.E s) (S.E.proposer s)).cache ⇢ c ∧
      M.proposal_with (M.gradeContract c)
        Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
        (M.ns_setClock S.E
          ((fun t => W (strictEventIndex rho t)) (M.proposal_time S.E s) (S.E.proposer s)).st
          (M.proposal_time S.E s)) ⇢ some B) :
    ∃ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
        (M.proposal_time S.E s)
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c ∧
      M.proposal_with (M.gradeContract c)
        Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s)) ⇢ some B :=
  h

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the tree of
    `n`'s core store. -/
private theorem tickStore_T₆₇b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- A named block's parent is an ancestor of it. -/
private theorem parent_preceq_self₆₇b (B : NamedBlock V) : NamedBlock.Preceq B.parent B :=
  (priv% Proofs.Vocabulary.Execution.SeedFreshPromotion
    DecoupledConsensusModel.Proofs.HealingSurface.seedFresh_parent_preceq_self) B

/-- Round `q`'s action instant is at most the vote instant of round `q`'s last slot. -/
private theorem action_le_seedRoundLastSlotVote₆₇b (facts : Record.Facts M) (S : Setup V)
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

/-- A block the proposal duty can return has a parent, the block its `parent` field names. -/
private theorem proposal_parent?₆₇b (facts : Record.Facts M) (S : Setup V) (gc : M.Contract)
    (p : V) (st : M.NS) {P : NamedBlock V}
    (hP : M.proposal_with gc Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node p) st ⇢
      some P) :
    P.parent? = some P.parent := by
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty gc S.E S.hc (S.node p)
    (M.toHealing st.core)
  obtain ⟨parent, hparent, -⟩ := facts.dt.proposal_with_parent? _ _ _ _ _ _ P _ hP rfl I hI
  cases P with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hparent
  | node parent' slot root votes support rows proposer =>
      rw [Proofs.ModelProperties.named_parent_node]
      rfl

/-- A block the proposal duty can return at slot `s`'s proposer's read staged from `W`, with a cache
    outcome `c` of the cache update there, is a value of `proposedBlockAt M S rho s`. -/
private theorem some_mem_proposedBlockAt₆₇b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some P) :
    some P ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s :=
  ⟨M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c,
    ⟨_, mem_stateBeforeTime_along₆₇b hf.sorted hf.onePath (M.proposal_time S.E s), c, hc, rfl⟩,
    by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact hP⟩

/-- For every outcome `c` of the cache update at slot `s`'s proposal instant on the proposer's node
    state in `W`, the proposal duty with `c`'s grade contract can return some block. -/
private theorem proposal_some_along₆₇b (facts : Record.Facts M) (S : Setup V)
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
    ⟨_, mem_stateBeforeTime_along₆₇b hf.sorted hf.onePath (M.proposal_time S.E s), c, hc, rfl⟩
  have hinv := Restated.Vocabulary.Proofs.HealingSurface.proposerReadAt_invariant facts S rho s _ hn
  rewrite [facts.nd.mkNode_st] at hinv; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hinv
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract c)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
  obtain ⟨P, hoP⟩ := facts.dt.proposal_with_gradeContract_isSome c .poolAndCarried S.E S.hc S.cfg
    (S.node (S.E.proposer s)) _ hinv o (by rw [facts.dt.proposal_with_store_with_cache]; exact ho)
  exact ⟨P, hoP ▸ ho⟩

/-- If round `r` acts at or after `t_GST`, round `r + 1` acts at or after `gstLagged S`. -/
private theorem gstLagged_le_a_succ₆₇b (facts : Record.Facts M) (S : Setup V) {r : Round}
    (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r) :
    gstLagged S ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
  have hlag : gstLagged S = S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) := by
    simp [gstLagged, readyLag]
  rw [facts.gr.action_succ_eq_add_rounds S r, hlag]
  have hmul : (4 * S.E.Δ * (S.hc.R : Nat) : Int) = 4 * (S.hc.R : Int) * S.E.Δ := by ring
  rw [hmul]
  exact Int.add_le_add_right hgst _

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

/-- Along `W`, if the largest `h_max` over the set for `S.a base` is `Mh ≥ 2`,
    `S.E.t_GST ≤ S.a base`, the largest over the endpoint's set is at most `Mh`, the endpoint's
    action instant is in the horizon and `lo ≤ S.a base`, then either some member of the set for a
    read `t` with `S.E.t_GST ≤ t ≤ S.a endpoint` and `S.a (base + 1) ≤ t` holds the fixed-height
    justification root at `Mh` in `W (strictEventIndex rho t)`, or every member of the set for each
    read of the window from `S.a (base + 1)` has `h_j + 2 ≤ Mh` and `h_max = Mh` in its store before
    that read. -/
theorem seedBaseFixedRoot_or_gateOffWindowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {base endpoint : Round}
    (hM : ((Hs (Restated.Vocabulary.Execution.Setup.a M S base)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S base)) u).st.core.h_max) = Mh)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (h2 : 2 ≤ Mh)
    (hcap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpoint)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpoint)) u).st.core.h_max) ≤ Mh)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S endpoint) ≤ rho.horizon)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base)) :
    (∃ (u : V) (read : Time), u ∈ Hs read ∧ S.E.t_GST ≤ read ∧
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S endpoint) ∧ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read ∧
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read))) ∨
    (∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S endpoint) →
      ∀ w ∈ Hs read, (read + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S endpoint) ∨ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S endpoint))) →
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh) := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hfbHor : Execution.BelowOneThird S (Hs rho.horizon) := hfb rho.horizon le_rfl
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S endpoint))).Nonempty :=
    Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _
  have hbase1 : (Restated.Vocabulary.Execution.Setup.a M S base) ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ base)
  have hstep : (Restated.Vocabulary.Execution.Setup.a M S base) + 1 + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) :=
    Restated.action_add_one_add_delta_le_next_action_l52 facts S base
  have hpoint : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read → read + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S endpoint) →
      (∃ u ∈ Hs read, Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read))) ∨
      (∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.core.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.core.h_max = Mh) := by
    intro read hlo1 hlt
    have hloRead : lo ≤ read := hlo.trans (hbase1.trans hlo1)
    have hcapRead : ((Hs read).sup fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) ≤ Mh :=
      (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloRead hlt hhor hne).trans hcap
    have hreadHor : read ≤ rho.horizon :=
      (le_of_lt (lt_of_le_of_lt (Int.le_add_of_nonneg_right S.E.Δ_pos.le) hlt)).trans hhor
    exact Restated.frontierRegime_at_read_l56 facts S Hs Xb hf hHs hHsXb hfbHor hsb hM hlo
      (hstep.trans hlo1) hcapRead hreadHor h2
  have hwin := Restated.frontierRegime_window_after_oneDelayOn facts S Hs Xb hf hHs hHsXb hfbHor hsb
    (lo := (Restated.Vocabulary.Execution.Setup.a M S (base + 1))) (hi := (Restated.Vocabulary.Execution.Setup.a M S endpoint)) hM hlo hstep hcap hhor h2
  by_cases hex : ∃ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read ∧ read ≤ (Restated.Vocabulary.Execution.Setup.a M S endpoint) ∧
      ∃ u ∈ Hs read, Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read))
  · obtain ⟨read, hlo1, hhi, u, hu, hfix⟩ := hex
    exact Or.inl ⟨u, read, hu, hpost.trans (hbase1.trans hlo1), hhi, hlo1, hfix⟩
  · refine Or.inr ?_
    intro read hlo1 hhi w hw hcase
    rcases hcase with hlt | hwEnd
    · rcases hpoint read hlo1 hlt with hfixed | hgate
      · exact absurd ⟨read, hlo1, hhi, hfixed⟩ hex
      · exact hgate w hw
    · rcases hwin with ⟨u, hu, read', hlo', hhi', hfix⟩ | hgate
      · exact absurd ⟨read', hlo', hhi', u, hHs _ _ hhi' hu, hfix⟩ hex
      · exact hgate read hlo1 hhi w hwEnd

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

/-- Along `W`, if round `q` is a carrier round, `P` is its named opening at `Mh`
    (`NamedGateOffOpeningWindowAtOn`), `lo` is at most the opening's proposal instant and the
    opening proposer passes the grade-1 awake test at its proposal ticks, then `P` is at height
    `Mh − 1` or `Mh`, or the largest `h_max` over the set for the opening's proposal instant exceeds
    `Mh`. -/
theorem namedGateOffOpening_pred_or_exact_or_hMaxRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {Mh : Height} {q : Round} {P : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hwindow : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q P)
    (hgat : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    (M.derive_named S.E S.cfg P).h = Mh - 1 ∨
      (M.derive_named S.E S.cfg P).h = Mh ∨
      Mh < ((Hs (M.proposal_time S.E ((M.opening_slot S.hc q)))).sup fun u =>
        (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q)))) u).st.core.h_max) := by
  have hconfEq : (Restated.Vocabulary.Execution.Setup.a M S q) =
      M.confirmation_time S.E ((M.opening_slot S.hc q)) :=
    Restated.a_eq_confirmation_opening_l58 facts S q
  have hproposalHor : M.proposal_time S.E ((M.opening_slot S.hc q)) ≤
      rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E _).trans
      (by
        rw [← hconfEq]
        exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans
          hwindow.nextActionInHorizon)
  have hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  have hs : 0 < (M.opening_slot S.hc q) := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hwindow.roundPositive
  obtain ⟨c, hc, hP⟩ := proposal_along₆₇b facts S hf (M.opening_slot S.hc q) hwindow.proposal
  have hlower : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h :=
    hwindow.parentHeight.trans
      (facts.cs.derive_height_mono S.E S.cfg (parent_preceq_self₆₇b P))
  by_cases hrise : Mh < ((Hs (M.proposal_time S.E ((M.opening_slot S.hc q)))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q)))) u).st.core.h_max)
  · exact Or.inr (Or.inr hrise)
  · have hupper : (M.derive_named S.E S.cfg P).h ≤ Mh :=
      (Restated.honestProposedBlock_height_le_honestHMaxAtOn facts S Hs Xb hf hHs hs hprop hproposalHor
        c hc hP hgat (fun j hj => hf.tick_outcome j _ _ hj) hrun).trans (Nat.le_of_not_gt hrise)
    rcases Nat.eq_or_lt_of_le hupper with heq | hlt
    · exact Or.inr (Or.inl heq)
    · exact Or.inl (Nat.le_antisymm (Nat.le_pred_of_lt hlt) hlower)

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

/-- Along `W`, if `t ≤ u`, then the processed tree of `v`'s store in `W (strictEventIndex rho t)` is
    inside the processed tree of its store in `W (strictEventIndex rho u)`. -/
theorem seedStore_T_subsetOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) {t u : Time} (htu : t ≤ u) :
    (W (strictEventIndex rho t) v).st.T ⊆ (W (strictEventIndex rho u) v).st.T :=
  Restated.Vocabulary.Proofs.stateBefore_T_subset facts S rho v (W (strictEventIndex rho t))
    (hf.onePath _).1 (strictEventIndex rho u) (strict_mono₆₇b rho htu) (W (strictEventIndex rho u))
    (onePath_slice₆₇b W hf.onePath (strict_mono₆₇b rho htu))

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

/-- Along `W`, if round `q` is a carrier round with the named opening `P` at `Mh`, every member of
    the set for `Γ_neg1 (q + 1)` has `h_max = Mh` and `h_j + 2 ≤ Mh` before that instant, and
    `lo ≤ S.a (q − 1)`, then `P` is in the filtered tree of the node state in
    `W (strictEventIndex rho (domain (q + 1) .g2))` of every member of the set for
    `domain (q + 1) .g2`. -/
theorem seedOpeningProposal_nextActiveDomainOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {P : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hwindow : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q P)
    (hframe : ∀ w ∈ Hs (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1)),
      (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))) w).st.h_j + 2 ≤ Mh)
    (hloPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) :
    ∀ w ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
      P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) w) := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hs : 0 < (M.opening_slot S.hc q) := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hwindow.roundPositive
  have hconfEq : (Restated.Vocabulary.Execution.Setup.a M S q) =
      M.confirmation_time S.E ((M.opening_slot S.hc q)) :=
    Restated.a_eq_confirmation_opening_l58 facts S q
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans hwindow.nextActionInHorizon
  have hproposalHor : M.proposal_time S.E ((M.opening_slot S.hc q)) ≤
      rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E _).trans
      (by rw [← hconfEq]; exact hactionHor)
  have hgat : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    hloPrev.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        (Nat.sub_lt hwindow.roundPositive Nat.one_pos)))
  have hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  obtain ⟨c, hc, hP⟩ := proposal_along₆₇b facts S hf (M.opening_slot S.hc q) hwindow.proposal
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
      (S.E.proposer (M.opening_slot S.hc q)) (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q)) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc q]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
        (Nat.sub_lt hwindow.roundPositive Nat.one_pos)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q
      have h3 : lo ≤ M.a S.hc S.E.Δ (q - 1) := hloPrev
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop) hwin
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlock_runBlockOn facts S Hs Xb hf hHs hHsXb hs hprop hproposalHor hgat
      (fun j hj => hf.tick_outcome j _ _ hj) hrunP c hc hP
  have hM : 1 ≤ Mh := by
    have htwo : 2 ≤ Mh := (Nat.le_add_left 2 _).trans hwindow.proposerGateOff
    exact (by decide : (1 : Nat) ≤ 2).trans htwo
  have hheight : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h :=
    hwindow.parentHeight.trans
      (facts.cs.derive_height_mono S.E S.cfg (parent_preceq_self₆₇b P))
  have hcutLo : (Restated.Vocabulary.Execution.Setup.a M S q) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) :=
    le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (facts.gr.action_add_delta_le_next_Γ_neg1 S q)
  have hcutHor : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q)).trans hwindow.nextActionInHorizon
  have hdom : M.domain S.E S.hc (q + 1) .g2 =
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) :=
    (facts.gr.gammaNeg1_eq_domain_g2_succ S q).symm
  intro w hw
  rw [hdom] at hw ⊢
  have hwConf : w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    rw [← hconfEq]
    exact hHs _ _ hcutLo hw
  have hconf : P.erase ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.T := by
    have h : P.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q))).T :=
      hwindow.proposalAtConfirmation w hwConf
    rw [tickStore_T₆₇b facts, ← hconfEq] at h
    exact h
  have hproc : P.erase ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))) w).st.T :=
    Restated.seedStore_T_subsetOn facts S Hs Xb hf w hcutLo hconf
  exact Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw) hcutHor hproc rfl
    hPrun hheight hM (hframe w hw).1 (hframe w hw).2

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

/-- Along `W`, under the committees condition and the weight bound, if round `q` is a carrier round
    with round ceiling `C` and named opening `P` at `Mh`, the members of the sets for `S.a (q − 1)`,
    `Γ_neg1 (q + 1)` and round `q`'s grade-0 domain instant have `h_max = Mh` (and the last two
    `h_j + 2 ≤ Mh`) before those instants, the bounds on `lo` hold and the awake conditions hold,
    then `Restated.GateOffOpeningAdoptionOn` holds for round `q` and `P`. -/
theorem seedOpeningLifecycle_of_inputsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hceiling : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hwindow : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q P)
    (hprevFrontier : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.h_max = Mh)
    (hframe : ∀ w ∈ Hs (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1)),
      (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))) w).st.h_j + 2 ≤ Mh)
    (hfrontierG0 : ∀ w ∈ Hs (M.domain S.E S.hc q .g0),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) w).st.h_max = Mh)
    (hgateOffG0 : ∀ w ∈ Hs (M.domain S.E S.hc q .g0),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g0)) w).st.h_j + 2 ≤ Mh)
    (hloPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloFrozen : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    Restated.GateOffOpeningAdoptionOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb q P :=
  Restated.gateOff_openingLifecycle_of_roundCeilingOn facts S Hs Xb hf hHs hHsXb hcom hfb hcarrier hceiling
    hwindow hprevFrontier
    (Restated.seedOpeningProposal_nextActiveDomainOn facts S Hs Xb hf hHs hHsXb hcarrier hwindow hframe hloPrev)
    hfrontierG0 hgateOffG0 hloPrev hloFrozen hA hAprev

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

/-- If `b < q`, then `S.a b ≤ vote_time (opening_slot q − 1)`. -/
theorem action_le_vote_openingPred_l67 (facts : Record.Facts M) (S : Setup V) {b q : Round} (hbq : b < q) :
    (Restated.Vocabulary.Execution.Setup.a M S b) ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) := by
  have h := action_le_seedRoundLastSlotVote₆₇b facts S (q - 1)
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le b) hbq))
  unfold Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot at h
  rw [hq] at h
  exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_sub_one_of_lt hbq)).trans h

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

/-- An opening's proposal instant plus one delay is strictly before the round's action instant. -/
theorem proposal_add_delta_lt_action_l67 (facts : Record.Facts M) (S : Setup V) (q : Round) :
    M.proposal_time S.E ((M.opening_slot S.hc q)) + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S q) :=
  Restated.openingProposal_add_delta_lt_action_l56 facts S q

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
local macro "shp% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.SeedHeightProgress)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))
local macro "p52% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_52)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along `W`, under the committees condition and the weight bound, if `2 ≤ Mh`, `base + 1 ≤ entry`,
    `entry + 2 + delayExtra ≤ q ≤ endpoint`, the frontier over the endpoint's set is at most `Mh`,
    every member of the set for each read from `S.a (base + 1)` to `S.a (q − 1)` has `h_j + 2 ≤ Mh`
    and `h_max = Mh`, rounds `entry` and `q` are carrier rounds with openings `Pentry` and `Pq`, `q`
    has round ceiling `C`, `Pentry` is at height `Mh` and graded 2 at round `entry + 1`, and the
    bounds on `lo` and the awake conditions hold, then the seed outcome at `Mh` from `base` to
    `endpoint` holds at the worlds of `W`. -/
theorem seedExactOpening_outcomeOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {base endpoint entry q : Round} {C Pentry Pq : NamedBlock V}
    (hM : 2 ≤ Mh)
    (hbaseEntry : base + 1 ≤ entry)
    (hentryQ : entry + 2 + delayExtra ≤ q)
    (hqEnd : q ≤ endpoint)
    (hpostBase : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hhorEnd : (Restated.Vocabulary.Execution.Setup.a M S endpoint) ≤ rho.horizon)
    (hcap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpoint)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpoint)) u).st.core.h_max) ≤ Mh)
    (hwindow : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) → ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hcarrierEntry : Restated.ProposerCarrierAtOn M S Hs entry)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hceiling : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (ce : M.Cache)
    (hce : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc entry)))
        (S.E.proposer (M.opening_slot S.hc entry))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc entry))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc entry)))
        (S.E.proposer (M.opening_slot S.hc entry))).cache ⇢ ce)
    (hPentry : M.proposal_with (M.gradeContract ce)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc entry)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc entry)))
        (S.E.proposer (M.opening_slot S.hc entry))).st
        (M.proposal_time S.E (M.opening_slot S.hc entry))) ⇢ some Pentry)
    (cq : M.Cache)
    (hcq : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ cq)
    (hPq : M.proposal_with (M.gradeContract cq)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some Pq)
    (hgradeNext : ∀ v ∈ Hs (M.domain S.E S.hc (entry + 1) Phase.g2),
      Pentry.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (entry + 1) Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (entry + 1) Phase.g2)) v).st (entry + 1) Phase.g2
            Pentry.erase ⇢ b → b = true)
    (hexact : (M.derive_named S.E S.cfg Pentry).h = Mh)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hloOpen : lo ≤ M.opening S.E S.hc (entry + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.HeightProgressSeedOutcomeOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb Mh base endpoint delayExtra := by
  obtain ⟨hentryPos, hqPos, hentryEnd, _hentry1End, hqPredEnd, hbaseEntry1,
    _hbaseQPred, hspan, hbaseEntry'⟩ :=
    (shp% seedLeafRounds_nat) (delayExtra := delayExtra) hbaseEntry hentryQ hqEnd
  have hM1 : 1 ≤ Mh := (by decide : (1 : Nat) ≤ 2).trans hM
  have hhorAt : ∀ {k : Round}, k ≤ endpoint → (Restated.Vocabulary.Execution.Setup.a M S k) ≤ rho.horizon := by
    intro k hk
    exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk).trans hhorEnd
  have hopenPos : 0 < (M.opening_slot S.hc entry) := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hentryPos
  have hproposalHorEntry : M.proposal_time S.E
      ((M.opening_slot S.hc entry)) ≤ rho.horizon := by
    refine (facts.sch.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Restated.a_eq_confirmation_opening_l58 facts S entry]
    exact hhorAt hentryEnd
  have hloEntry : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc entry)) :=
    hlo.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
        (Nat.lt_of_succ_le hbaseEntry)))
  have hrunAt : ∀ k : Round, base < k →
      S.E.proposer (M.opening_slot S.hc k) ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc k)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
        (S.E.proposer (M.opening_slot S.hc k)) (M.proposal_time S.E (M.opening_slot S.hc k))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc k))
        (W j (S.E.proposer (M.opening_slot S.hc k))) (M.round_of S.hc (M.opening_slot S.hc k)) := by
    intro k hbk hprop j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc k)) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc k]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hbk
      have h2 := facts.gr.q10_early_g2_le_early_g1 S k
      have h3 : lo ≤ M.a S.hc S.E.Δ base := hlo
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop) hwin
  have hPrun : Restated.RunBlockOn M S rho W Xb Pentry :=
    Restated.proposedBlock_runBlockOn facts S Hs Xb hf hHs hHsXb hopenPos
      (by simpa only [Nat.add_zero] using hcarrierEntry 0 (by decide))
      hproposalHorEntry hloEntry (fun j hj => hf.tick_outcome j _ _ hj)
      (hrunAt entry (Nat.lt_of_succ_le hbaseEntry)
        (by simpa only [Nat.add_zero] using hcarrierEntry 0 (by decide))) ce hce hPentry
  have hactionRead : ∀ k : Round, entry + 1 ≤ k → k ≤ q - 1 →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.h_max = Mh := by
    intro k hklo hkhi w hw
    exact hwindow ((Restated.Vocabulary.Execution.Setup.a M S k)) (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (hbaseEntry1.trans hklo))
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hkhi) w hw
  have hpostEntryNext : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (entry + 1)) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (hbaseEntry'.trans (Nat.le_succ _)))
  have hloEntryNext : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (entry + 1)) :=
    hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (hbaseEntry'.trans (Nat.le_succ _)))
  have hopenPosQ : 0 < (M.opening_slot S.hc q) := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hqPos
  have hproposalHorQ : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon := by
    refine (facts.sch.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Restated.a_eq_confirmation_opening_l58 facts S q]
    exact hhorAt hqEnd
  have hbaseQ : base < q :=
    (Nat.lt_of_succ_le hbaseEntry).trans_le
      (((Nat.le_add_right entry 2).trans (Nat.le_add_right (entry + 2) delayExtra)).trans
        hentryQ)
  have hloQ : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    hlo.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hbaseQ))
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S endpoint))).Nonempty :=
    Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _
  have hparentCap : (M.derive_named S.E S.cfg Pq.parent).h ≤ Mh := by
    have hupper := Restated.honestProposedBlock_height_le_honestHMaxAtOn facts
      S Hs Xb hf hHs hopenPosQ (by simpa only [Nat.add_zero] using hcarrier 0 (by decide))
      hproposalHorQ cq hcq hPq hloQ (fun j hj => hf.tick_outcome j _ _ hj)
      (hrunAt q hbaseQ (by simpa only [Nat.add_zero] using hcarrier 0 (by decide)))
    refine le_trans (facts.cs.derive_height_mono S.E S.cfg (parent_preceq_self₆₇b Pq)) ?_
    refine hupper.trans ?_
    refine le_trans (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloQ ?_ hhorEnd hne)
      hcap
    exact lt_of_lt_of_le (Restated.proposal_add_delta_lt_action_l67 facts S q) (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqEnd)
  have hactionFrontier : ∀ k, entry + 1 ≤ k → k ≤ q - 1 → ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w) k,
      n.st.core.h_max = Mh := by
    intro k hklo hkhi w hw n hn
    rw [(p52% actionReadFrom_h_max₅₂b) facts S _ k n hn]
    exact (hactionRead k hklo hkhi w hw).2
  have hactionGate : ∀ k, entry + 1 ≤ k → k ≤ q - 1 → ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w) k,
      n.st.core.h_j + 2 ≤ Mh := by
    intro k hklo hkhi w hw n hn
    rw [(p52% actionReadFrom_h_j₅₂b) facts S _ k n hn]
    exact (hactionRead k hklo hkhi w hw).1
  have hframeRead : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (entry + 1)) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) → ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh := by
    intro read hlo' hhi w hw
    exact hwindow read ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseEntry1).trans hlo') hhi w hw
  have hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) :=
    hlo.trans (Restated.action_le_vote_openingPred_l67 facts S hbaseQ)
  obtain ⟨-, -, -, -, hanchors⟩ := Restated.openingAnchorsAligned_of_roundCeilingOn facts
    S Hs Xb hf hHs hHsXb hcom hcarrier hceiling hloVote
  have hloOpenQ : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hspan _))
  obtain ⟨hforms, hbelow, hheights⟩ := Restated.seedExactOpening_gradePackageOn facts
    S Hs Xb hf hHs hHsXb hcom ce hce hPentry cq hcq hPq hcarrier hceiling hgradeNext hPrun
    hexact hM1 ((Nat.le_add_right _ delayExtra).trans hentryQ)
    hloEntryNext (hhorAt hqPredEnd) hactionFrontier hactionGate
    (Restated.namedGradeFormsAt_persists_through_gateOffActionWindowOn facts S Hs Xb hf hHs hHsXb
      hfb (r0 := entry + 1) (q := q - 1) (Nat.succ_pos entry) hgradeNext hPrun
      (by rw [hexact]; exact Nat.sub_le Mh 1) hM1 hpostEntryNext
      (hhorAt hqPredEnd)
      (fun read hlo' hhi w hw =>
        ⟨(hframeRead read hlo' hhi w hw).2, (hframeRead read hlo' hhi w hw).1⟩)
      hloEntryNext hloOpen (fun k hk _ _ => hA k hk)
      (q - 1) hspan (le_refl _))
    (fun w hw n hn A2 hA2 G hG I hI => hanchors w hw n hn A2 hA2 G hG cq hcq I hI)
    hparentCap hloOpenQ
  exact Or.inr (Or.inr ⟨entry, q, Pentry, Pq, Pq.parent, hbaseEntry, hentryQ,
    hqEnd, hcarrier, ⟨ce, hce, hPentry⟩, hforms, hPrun, hexact, ⟨cq, hcq, hPq⟩,
    proposal_parent?₆₇b facts S _ _ _ hPq, hbelow, hheights⟩)

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

/-- If `b + 1 < q`, then `S.a b ≤ proposal_time (opening_slot q − 1)`. -/
theorem action_le_proposal_openingPred_l67 (facts : Record.Facts M) (S : Setup V) {b q : Round} (hbq : b + 1 < q) :
    (Restated.Vocabulary.Execution.Setup.a M S b) ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1) := by
  have h1 : (Restated.Vocabulary.Execution.Setup.a M S b) + S.E.Δ ≤ M.proposal_time S.E ((M.opening_slot S.hc (b + 1))) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S (Nat.lt_succ_self b)
  have hslot : (M.opening_slot S.hc (b + 1)) ≤ (M.opening_slot S.hc q) - 1 := by
    apply Nat.le_sub_of_add_le
    have hR : 1 ≤ S.hc.R := (by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two
    calc
      (M.opening_slot S.hc (b + 1)) + 1 ≤ (M.opening_slot S.hc (b + 1)) + S.hc.R :=
          Nat.add_le_add_left hR _
      _ = (M.opening_slot S.hc (b + 1 + 1)) :=
          (facts.gr.opening_slot_succ S.hc (b + 1)).symm
      _ ≤ (M.opening_slot S.hc q) :=
          facts.gr.opening_slot_le_of_le S.hc (Nat.succ_le_of_lt hbq)
  exact ((le_add_of_nonneg_right S.E.Δ_pos.le).trans h1).trans
    (facts.sch.proposal_time_mono S.E hslot)

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
local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p54b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_54b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p66b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_66b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along `W`, if `0 < r`, `B0` is a run block at height `Mh − 1` graded 2 by every member of the
    set for `domain r .g2`, and for every member of the set for `S.a r` the block of `B0` is in its
    filtered tree, every FG source of its round-`r` action read is at height at most `Mh − 1` and
    `h_j + 2 ≤ Mh`, then every outcome of the attestation duty at every node state of that action
    read carries the height vote `(Mh − 1, T)`, `T` being the root of `B0`'s height entry. -/
theorem seedFreshActionRows_atAction_l67 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {r : Round} {B0 : NamedBlock V}
    (hr : 0 < r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hB0run : Restated.RunBlockOn M S rho W Xb B0)
    (hB0height : (M.derive_named S.E S.cfg B0).h = Mh - 1)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc r Phase.g2),
      B0.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v).st r Phase.g2 B0.erase ⇢ b →
          b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      B0.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG)
    (hsourceUpper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
        ((M.toHealing n.st.core).σ Q).h ≤ Mh - 1)
    (hgateOff : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.h_j + 2 ≤ Mh)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      D.2.2.height_pair =
          NamedHeightPair.vote (Mh - 1)
            (M.derive_named S.E S.cfg B0).T_h.root false ∨
      D.2.2.height_pair =
          NamedHeightPair.vote (Mh - 1)
            (M.derive_named S.E S.cfg B0).T_h.root true := by
  intro v hv n hn D hD
  have hvDom : v ∈ Hs (M.domain S.E S.hc r .g0) :=
    hHs _ _ (facts.gr.domain_le_a S r .g0) hv
  have hwmem := mem_stateBeforeTime_along₆₇b hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)), hwmem, hn⟩
  have hactive : B0.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v)
      _ hwmem (hwindow v hv) n hn
  have hround' : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hmem
  have hsrcEq : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n =
      Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r := by
    simp only [Restated.Vocabulary.Proofs.HealingSurface.actionFGSource,
      Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource]
    rw [hround']
    rfl
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts S n
  rw [hsrcEq] at ho
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
    (p66b% nodeQ2_of_read₆₆b) S n r G hG
  obtain ⟨Q2, hQ2, hCQ2⟩ := (p54b% formsW_preceq_actionQ2₅₄b) facts S Hs Xb hf hHs hr hhor
    hforms hvDom n hn hactive hlo _ hGq
  rw [hQ2] at hGq
  obtain ⟨Q, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.exists_actionFGSource_of_actionQ2 facts
    S rho v r _ hwmem n hn hGq o ho
  have hsource := ho
  obtain ⟨Qn, hQnbody, hQnerase, hQnrun, hσ0⟩ :=
    Restated.seedFresh_namedSource_witnessOn facts S Hs Xb hf (hHsXb _ hv) n hn hsource
  have hσ : (M.toHealing n.st.core).σ Q = M.derive_named S.E S.cfg Qn := hσ0
  have hB0Q : Block.Preceq B0.erase Q :=
    Restated.Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 facts S rho v r _
      hwmem n hn hGq hCQ2 hsource
  have hB0QnErase : Block.Preceq B0.erase Qn.erase := by
    rw [hQnerase]
    exact hB0Q
  obtain ⟨A, hAQn, hAerased⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift Qn hB0QnErase
  have hArun : Restated.RunBlockOn M S rho W Xb A :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hQnrun hAQn
  have hroot : A.root = B0.root := by
    rw [← Proofs.NamedWire.erase_root A, hAerased, Proofs.NamedWire.erase_root]
  have hAB0 : A = B0 :=
    hf.rootCollisionFree.root_injective A B0 hArun hB0run A B0
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B0)) hroot
  have hB0Qn : NamedBlock.Preceq B0 Qn := by
    simpa only [hAB0] using hAQn
  have hDheightUpper : (M.derive_named S.E S.cfg Qn).h ≤ Mh - 1 := by
    have hsourceHeightUpper := hsourceUpper v hv n hn Q hsource
    rw [hσ] at hsourceHeightUpper
    exact hsourceHeightUpper
  have hDheightLower : Mh - 1 ≤
      (M.derive_named S.E S.cfg Qn).h := by
    have hmono := facts.cs.derive_height_mono S.E S.cfg hB0Qn
    rw [hB0height] at hmono
    exact hmono
  have hQnheight : (M.derive_named S.E S.cfg Qn).h = Mh - 1 :=
    Nat.le_antisymm hDheightUpper hDheightLower
  have hsameHeight : (M.derive_named S.E S.cfg B0).h =
      (M.derive_named S.E S.cfg Qn).h := by
    rw [hB0height, hQnheight]
  have hentry : (M.derive_named S.E S.cfg B0).T_h =
      (M.derive_named S.E S.cfg Qn).T_h :=
    facts.cs.entry_eq_on_plateau S.E S.cfg hB0Qn hsameHeight
  have hsourceHeight :
      ((M.toHealing n.st.core).σ Q).h = Mh - 1 := by
    rw [hσ, hQnheight]
  have hsourceEntry :
      ((M.toHealing n.st.core).σ Q).T_h.root =
        (M.derive_named S.E S.cfg B0).T_h.root := by
    calc
      ((M.toHealing n.st.core).σ Q).T_h.root =
          (M.derive_named S.E S.cfg Qn).T_h.root :=
        congrArg (fun x : M.CS => x.T_h.root) hσ
      _ = (M.derive_named S.E S.cfg B0).T_h.root :=
        congrArg (fun x : Block V => x.root) hentry.symm
  obtain ⟨A', hA'⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  have hDA : D.2.2 = A'.2 := facts.dt.attest_with_row _ _ _ _ _ _ D hD A' hA'
  have hlock := Restated.gateOff_actionOwnLock_at_pred_noneOn facts S Hs Xb hf v r n hn D hD
    (hgateOff v hv)
  have hlock' : M.own_lock n.record.legacy ((M.toHealing n.st.core).σ Q).h
      A'.2.finality_pair = none := by
    rw [hsourceHeight, ← hDA]
    exact hlock
  exact Restated.Vocabulary.Proofs.HealingSurface.seedFreshActionRow_of_source facts S n hmem A' hA'
    hsource hsourceHeight hsourceEntry hlock' D hD

/-- Along `W`, under the hypotheses of `seedFreshActionRows_atAction_l67`, if the opening proposer
    of round `r + 1` can propose `B` whose parent is at height `Mh − 1` and a named descendant of
    `C`, then for every member `v` of the set for that proposal instant, every outcome of the
    attestation duty at every node state of `v`'s round-`r` action read is covered by `B` and
    carries the height vote `(Mh − 1, T)`, `T` being the root of `C`'s height entry. -/
theorem seedFreshProposalCoverage_atAction_l67 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {r : Round} {C B : NamedBlock V}
    (hr : 0 < r)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : (M.derive_named S.E S.cfg C).h = Mh - 1)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc r Phase.g2),
      C.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v).st r Phase.g2 C.erase ⇢ b →
          b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      C.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG)
    (hsourceToParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
        ((M.toHealing n.st.core).σ Q).h ≤ (M.derive_named S.E S.cfg B.parent).h)
    (hgateOff : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.h_j + 2 ≤ Mh)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))) ⇢ some B)
    (hCP : NamedBlock.Preceq C B.parent)
    (hparentHeight : (M.derive_named S.E S.cfg B.parent).h = Mh - 1)
    (hprop : S.E.proposer ((M.opening_slot S.hc (r + 1))) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc (r + 1))) ≤ rho.horizon)
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ v ∈ Hs (M.proposal_time S.E ((M.opening_slot S.hc (r + 1)))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      ((D.2.2 ∈ named_chain_attestations B.parent ∧
          v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
          (D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
              (M.derive_named S.E S.cfg C).T_h.root false →
            v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
        D.2.2 ∈ B.attestations) ∧
      (D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
          (M.derive_named S.E S.cfg C).T_h.root false ∨
        D.2.2.height_pair = NamedHeightPair.vote (Mh - 1)
          (M.derive_named S.E S.cfg C).T_h.root true) := by
  have hsourceUpper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
        ((M.toHealing n.st.core).σ Q).h ≤ Mh - 1 := by
    intro v hv n hn Q hQ
    have h := hsourceToParent v hv n hn Q hQ
    simpa only [hparentHeight] using h
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E
      ((M.opening_slot S.hc (r + 1))) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S (Nat.lt_succ_self r)
  have hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hproposalHor)
  have hrows := Restated.seedFreshActionRows_atAction_l67 facts S Hs Xb hf hHs hHsXb
    hr hhor hCrun hCheight hforms hwindow hsourceUpper hgateOff hlo
  have hround : M.round_of S.hc (M.opening_slot S.hc (r + 1)) = r + 1 :=
    facts.gr.round_of_opening_slot_eq S.hc (r + 1)
  have hinWindow : M.inWindow S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))).core r = true := by
    rw [facts.dt.inWindow_iff, facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time,
      hround]
    have heta := S.hc.η_SG_ge_one
    exact ⟨(Nat.sub_le_sub_left heta (r + 1)).trans (Nat.le_of_eq (Nat.add_sub_cancel r 1)),
      Nat.le_succ r⟩
  intro v hvp n hn D hD
  have hvDelta : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ hdelay hvp
  have hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    hHs _ _ (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hvDelta
  have hpair := hrows v hv n hn D hD
  refine ⟨?_, hpair⟩
  exact (p54b% windowW_actionAttestationAt_coveredAtProposal₅₄b) facts S Hs Xb hf hHs hHsXb
    hCrun hCheight rfl c hc hB hCP hparentHeight hprop hproposalHor hpost hdelay hvp
    (hwindow v hv) hinWindow
    (hA r (Restated.lo_le_early_g2_sub_delta_of_opening facts S hr hlo le_rfl) v hvDelta)
    n hn D hD hpair

/-- Along `W`, under the hypotheses of `seedFreshProposalCoverage_atAction_l67` with `B`'s parent at
    height at most `Mh`, the proposer in the set for its confirmation instant, the validators
    outside the set for the proposal instant weighing less than a third, `2 ≤ Mh`, and a mature
    timeout for every named parent of `B` when that parent is at height `Mh − 1`: `B` is at height
    `Mh`, or the largest `h_max` over the set for the proposal instant exceeds `Mh`. -/
theorem seedFreshOpening_promotion_atAction_l67 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {r : Round} {C B : NamedBlock V}
    (hfb : Execution.BelowOneThird S
      (Hs (M.proposal_time S.E ((M.opening_slot S.hc (r + 1))))))
    (hM : 2 ≤ Mh)
    (hr : 0 < r)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : (M.derive_named S.E S.cfg C).h = Mh - 1)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc r Phase.g2),
      C.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r Phase.g2)) v).st r Phase.g2 C.erase ⇢ b →
          b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      C.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG)
    (hsourceToParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q →
        ((M.toHealing n.st.core).σ Q).h ≤ (M.derive_named S.E S.cfg B.parent).h)
    (hgateOff : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.h_j + 2 ≤ Mh)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))) ⇢ some B)
    (hCP : NamedBlock.Preceq C B.parent)
    (hparentCap : (M.derive_named S.E S.cfg B.parent).h ≤ Mh)
    (hprop : S.E.proposer ((M.opening_slot S.hc (r + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc (r + 1))) ≤ rho.horizon)
    (hpostMature_of_parentPred :
      (M.derive_named S.E S.cfg B.parent).h = Mh - 1 →
        ∀ P : NamedBlock V, NamedBlock.parent? B = some P →
          (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc (r + 1))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    (M.derive_named S.E S.cfg B).h = Mh ∨
      Mh < ((Hs (M.proposal_time S.E ((M.opening_slot S.hc (r + 1))))).sup fun u =>
        (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc (r + 1))))) u).st.core.h_max) := by
  have hM1 : 1 ≤ Mh := (by decide : (1 : Nat) ≤ 2).trans hM
  have hparentLower : Mh - 1 ≤
      (M.derive_named S.E S.cfg B.parent).h := by
    rw [← hCheight]
    exact facts.cs.derive_height_mono S.E S.cfg hCP
  have hparentCases :
      (M.derive_named S.E S.cfg B.parent).h = Mh - 1 ∨
        (M.derive_named S.E S.cfg B.parent).h = Mh := by
    rcases Nat.eq_or_lt_of_le hparentCap with hEq | hLt
    · exact Or.inr hEq
    · exact Or.inl (Nat.le_antisymm (Nat.le_pred_of_lt hLt) hparentLower)
  have hspos : 0 < (M.opening_slot S.hc (r + 1)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (Nat.succ_pos r)
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E
      ((M.opening_slot S.hc (r + 1))) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S (Nat.lt_succ_self r)
  have hpropConf : M.proposal_time S.E ((M.opening_slot S.hc (r + 1))) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) :=
    facts.sch.proposal_time_le_confirmation_time S.E _
  have hpropDelta : S.E.proposer ((M.opening_slot S.hc (r + 1))) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) :=
    hHs _ _ (hdelay.trans hpropConf) hprop
  have hgat : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc (r + 1))) :=
    hpost.trans ((Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay)
  by_cases hrise : Mh < ((Hs (M.proposal_time S.E ((M.opening_slot S.hc (r + 1))))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc (r + 1))))) u).st.core.h_max)
  · exact Or.inr hrise
  left
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
      (S.E.proposer (M.opening_slot S.hc (r + 1))) (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc (r + 1)))
        (W j (S.E.proposer (M.opening_slot S.hc (r + 1))))
        (M.round_of S.hc (M.opening_slot S.hc (r + 1))) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (r + 1))) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc (r + 1)]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
      have h2 := facts.gr.q10_early_g2_le_early_g1 S (r + 1)
      have h3 : lo ≤ M.a S.hc S.E.Δ r := hpost
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop) hwin
  have hproposalUpper : (M.derive_named S.E S.cfg B).h ≤ Mh :=
    (Restated.honestProposedBlock_height_le_honestHMaxAtOn facts S Hs Xb hf hHs hspos hprop
      hproposalHor c hc hB hgat (fun j hj => hf.tick_outcome j _ _ hj) hrunP).trans
      (Nat.le_of_not_gt hrise)
  rcases hparentCases with hparentPred | hparentExact
  · have hsame : (M.derive_named S.E S.cfg C).h =
        (M.derive_named S.E S.cfg B.parent).h := by
      rw [hCheight, hparentPred]
    have hparentTarget : (M.derive_named S.E S.cfg B.parent).T_h.root =
        (M.derive_named S.E S.cfg C).T_h.root := by
      exact congrArg (fun x : Block V => x.root)
        (facts.cs.entry_eq_on_plateau S.E S.cfg hCP hsame).symm
    have hcoverage := Restated.seedFreshProposalCoverage_atAction_l67 facts S Hs Xb hf hHs
      hHsXb hr hpost hCrun hCheight hforms hwindow hsourceToParent hgateOff c hc hB hCP
      hparentPred hpropDelta hproposalHor hA hlo
    have hwr := mem_stateBeforeTime_along₆₇b hf.sorted hf.onePath
      (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
    have hBmem : some B ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho
        (M.opening_slot S.hc (r + 1)) :=
      ⟨M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
            (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
          (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c,
        ⟨_, hwr, c, hc, rfl⟩,
        by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact hB⟩
    have hheight := (p54b% named_proposedBlock_height_eq_succ_along₅₄b) facts S _ hfb hBmem
      (hpostMature_of_parentPred hparentPred) _
      (mem_stateBeforeTime_along₆₇b hf.sorted hf.onePath (Restated.Vocabulary.Execution.Setup.a M S r))
      hcoverage hparentPred hparentTarget
    calc
      (M.derive_named S.E S.cfg B).h = Mh - 1 + 1 := hheight
      _ = Mh := Nat.sub_add_cancel hM1
  · have hproposalLower : Mh ≤ (M.derive_named S.E S.cfg B).h := by
      rw [← hparentExact]
      exact facts.cs.derive_height_mono S.E S.cfg (parent_preceq_self₆₇b B)
    exact Nat.le_antisymm hproposalUpper hproposalLower

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
local macro "shp% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.SeedHeightProgress)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))
local macro "p54% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_54)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along `W`, under the committees condition, the weight bound, the timeout-delay bound and the
    promotion inputs from `r0`, if proposer carriers recur within `gap` from `t₀` to the horizon,
    `lo ≤ S.a r0`, `lo ≤ opening (r0 + 1 − η_SG)`, `t₀ ≤ S.a r0` and the awake conditions hold, then
    the `Mh − 1` closer from `r0` holds at the worlds of `W`. -/
theorem seedPredCloser_of_timeoutDelayOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (hdelayBound : TimeoutDelayBound S delayExtra)
    {r0 gap : Round} {t₀ : Int}
    (hpromotion : Restated.SeedPredPromotionInputsOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb r0 delayExtra)
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.SeedPredCloserFromOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb r0 gap delayExtra := by
  intro base q Cq Pq hr0 hbaseq hbudget hpostBase hhorEnd Mh hMdef hcap hM hgateWindow
    hgradedQ hcarrier hceiling hwindowQ hpred
  set endpoint : Round := base + seedLag gap delayExtra with hendpoint
  have hloBase : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)
  have hloOpenAt : ∀ k : Round, r0 + 1 ≤ k → lo ≤ M.opening S.E S.hc (k - S.hc.η_SG) :=
    fun k hk => hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hk _))
  have hloVoteAt : ∀ k : Round, base < k →
      lo ≤ M.vote_time S.E ((M.opening_slot S.hc k) - 1) :=
    fun k hk => hloBase.trans (Restated.action_le_vote_openingPred_l67 facts S hk)
  have hselect (k : Round) (hbk : base < k) (hk : k + gap ≤ endpoint) :
      ∃ c : Round, k ≤ c ∧ c ≤ k + gap ∧ Restated.ProposerCarrierAtOn M S Hs c :=
    hrec k
      ((ht₀.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hbk)))
      ((Restated.Vocabulary.Proofs.HealingLemmas.openingProposal_window_le_action facts S k gap).trans
        ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk).trans hhorEnd))
  obtain ⟨h4base, h4end⟩ := (shp% seedCloserSelectRound4_nat) hbaseq hbudget
  obtain ⟨q4, hq4lo, hq4hi, hcar4⟩ := hselect (q + 2 + delayExtra)
    h4base h4end
  obtain ⟨h5base, h5end⟩ := (shp% seedCloserSelectRound5_nat) hbaseq hbudget hq4lo hq4hi
  obtain ⟨q5, hq5lo, hq5hi, hcar5⟩ := hselect (q4 + 2 + delayExtra)
    h5base h5end
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,
    m16⟩ :=
    (shp% seedCloserRounds_nat) (delayExtra := delayExtra) hbaseq hbudget hq4lo hq4hi hq5lo
      hq5hi
  have hqPlusTwo : q + 2 ≤ q4 :=
    (Nat.le_add_right (q + 2) delayExtra).trans m14
  obtain ⟨hbq, hr0q, hbq1, hbq4, hbq41, hr0q1, hr0q4p, hr0q4s, hr0q4⟩ :=
    seedCloserLaterRounds_nat_l67 hr0 hbaseq hqPlusTwo
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ :=
    seedCloserReadsStrict_nat_l67 hbaseq hbudget hq4lo hq4hi hq5lo hq5hi
  obtain ⟨c4, hc4⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q4)))
      (S.E.proposer (M.opening_slot S.hc q4))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc q4))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q4)))
      (S.E.proposer (M.opening_slot S.hc q4))).cache
  obtain ⟨P4, hP4⟩ := proposal_some_along₆₇b facts S hf (M.opening_slot S.hc q4) c4 hc4
  obtain ⟨c5, hc5⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q5)))
      (S.E.proposer (M.opening_slot S.hc q5))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc q5))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q5)))
      (S.E.proposer (M.opening_slot S.hc q5))).cache
  obtain ⟨P5, hP5⟩ := proposal_some_along₆₇b facts S hf (M.opening_slot S.hc q5) c5 hc5
  have hpostBase1 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ base))
  have hpostBase1L : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) :=
    gstLagged_le_a_succ₆₇b facts S hpostBase
  have hloBase1 : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) :=
    hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ base))
  have hhorAt : ∀ {k : Round}, k ≤ endpoint → (Restated.Vocabulary.Execution.Setup.a M S k) ≤ rho.horizon := by
    intro k hk
    exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk).trans hhorEnd
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S endpoint))).Nonempty :=
    Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _
  have hwindowAt : ∀ (k : Round), k < endpoint →
      ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S k) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh := by
    intro k hk read hlo' hhi w hw
    exact hgateWindow read hlo' (hhi.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk.le)) w hw
      (Or.inl (lt_of_le_of_lt (Int.add_le_add_right hhi _)
        (Restated.action_add_delta_lt_action_of_lt_l67 facts S hk)))
  have hAbase1 := hA (base + 1)
    (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase (Nat.lt_succ_self base))
  obtain ⟨B4, hceil4, -⟩ := Restated.roundCeiling_through_of_windowOn facts S Hs Xb hf hHs hHsXb hcom hfb
    (base := base + 1) (first := q) (last := q4) (C := Cq)
    hpostBase1L m1 (hhorAt m4)
    (fun read hlo' hhi w hw => hwindowAt (q4 + 1) s2 read hlo' hhi w hw)
    hceiling hloBase1 (hloVoteAt q hbq) (hloOpenAt q hr0q) hA hAbase1 q4 m2 (le_refl _)
  obtain ⟨B5, hceil5, -⟩ := Restated.roundCeiling_through_of_windowOn facts S Hs Xb hf hHs hHsXb hcom hfb
    (base := base + 1) (first := q) (last := q5) (C := Cq)
    hpostBase1L m1 (hhorAt m7)
    (fun read hlo' hhi w hw => hwindowAt (q5 + 1) s6 read hlo' hhi w hw)
    hceiling hloBase1 (hloVoteAt q hbq) (hloOpenAt q hr0q) hA hAbase1 q5 m3 (le_refl _)
  have hprop4 : S.E.proposer ((M.opening_slot S.hc q4)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q4))) := by
    simpa only [Nat.add_zero] using hcar4 0 (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩ :=
    Restated.gateOffOpeningWindow_of_windowOn facts S Hs Xb hf hHs hHsXb (base := base + 1) (q := q4)
      hpostBase1 m10 (hhorAt m5) hprop4 c4 hc4 hP4
      (fun read hlo' hhi w hw => hwindowAt (q4 + 1) s2 read hlo' hhi w hw) hloBase1
  have hwindow4 : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q4 P4 :=
    ⟨⟨c4, hc4, hP4⟩, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
  have hproposalHor4 : M.proposal_time S.E
      ((M.opening_slot S.hc q4)) ≤ rho.horizon := by
    refine (facts.sch.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [← Restated.a_eq_confirmation_opening_l58 facts S q4]
    exact hhorAt m6
  have hloQ4 : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q4)) :=
    hloBase.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hbq4))
  have hrelayQ4 : M.proposal_time S.E ((M.opening_slot S.hc q4)) + S.E.Δ <
      (Restated.Vocabulary.Execution.Setup.a M S endpoint) :=
    lt_of_lt_of_le (Restated.proposal_add_delta_lt_action_l67 facts S q4) (Restated.Vocabulary.Proofs.Assembly.a_mono facts S m6)
  have hparentQ4 : P4.parent? = some P4.parent := proposal_parent?₆₇b facts S _ _ _ hP4
  have hparentCap4' : (M.derive_named S.E S.cfg P4.parent).h ≤ Mh := by
    have hopenPos4 : 0 < (M.opening_slot S.hc q4) := by
      exact facts.gr.opening_slot_pos_of_round_pos S.hc hwindow4.roundPositive
    have hrunP4 : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
        (S.E.proposer (M.opening_slot S.hc q4)) (M.proposal_time S.E (M.opening_slot S.hc q4))) →
        M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q4))
          (W j (S.E.proposer (M.opening_slot S.hc q4))) (M.round_of S.hc (M.opening_slot S.hc q4)) := by
      have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q4)) .g1 - S.E.Δ := by
        rw [facts.gr.round_of_opening_slot_eq S.hc q4]
        have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hbq4
        have h2 := facts.gr.q10_early_g2_le_early_g1 S q4
        have h3 : lo ≤ M.a S.hc S.E.Δ base := hloBase
        linarith
      intro j hj
      exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
        (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop4) hwin
    have hupper := Restated.honestProposedBlock_height_le_honestHMaxAtOn facts
      S Hs Xb hf hHs hopenPos4 hprop4 hproposalHor4 c4 hc4 hP4 hloQ4
      (fun j hj => hf.tick_outcome j _ _ hj) hrunP4
    refine le_trans (facts.cs.derive_height_mono S.E S.cfg (parent_preceq_self₆₇b P4)) ?_
    refine hupper.trans ?_
    exact (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloQ4 hrelayQ4 hhorEnd
      hne).trans hcap
  have hbasePred : base + 1 ≤ q - 1 := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.add_assoc] using m1
  have hqPred : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hwindowQ.roundPositive)
  have hprevQ : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) u).st.h_max = Mh := by
    intro u hu
    exact (hwindowAt (q + 1) s3 ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred)
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.sub_le q 1).trans (Nat.le_succ q))) u hu).2
  have hbaseQ : base + 1 ≤ q := hbasePred.trans (Nat.sub_le q 1)
  have hloPrevQ : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hloBase1.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred)
  have hcutFrameQ : ∀ w ∈ Hs (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1)),
      (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))) w).st.h_max = Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))) w).st.h_j + 2 ≤ Mh := by
    intro w hw
    have hframeQ := hwindowAt (q + 1) s3
      (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1))
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseQ).trans
        ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (facts.gr.action_add_delta_le_next_Γ_neg1 S q)))
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q)) w hw
    exact ⟨hframeQ.2, hframeQ.1⟩
  have hnextQ := Restated.seedOpeningProposal_nextActiveDomainOn facts S Hs Xb hf hHs hHsXb hcarrier hwindowQ
    hcutFrameQ hloPrevQ
  have hdomLoQ : ∀ p : Phase, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤
      M.domain S.E S.hc q p := by
    intro p
    have h := Restated.action_add_delta_le_domain_g2_succ_l54 facts S (q - 1)
    rw [hqPred] at h
    exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred).trans
      (((le_add_of_nonneg_right S.E.Δ_pos.le).trans h).trans (facts.gr.domain_g2_le_domain_l67 S q p))
  have hdomHiQ : ∀ p : Phase,
      M.domain S.E S.hc q p ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    fun p => (facts.gr.domain_le_a S q p).trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q))
  have hdomFrameQ : ∀ p : Phase,
      ∀ w ∈ Hs (M.domain S.E S.hc q p),
        (W (strictEventIndex rho (M.domain S.E S.hc q p)) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho (M.domain S.E S.hc q p)) w).st.h_max = Mh :=
    fun p w hw => hwindowAt (q + 1) s3 _ (hdomLoQ p) (hdomHiQ p) w hw
  have hloFrozenQ : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1) :=
    hloBase.trans (Restated.action_le_proposal_openingPred_l67 facts S hbq1)
  have hpacketQ := Restated.seedLifecyclePacket_of_roundCeilingOn facts
    S Hs Xb hf hHs hHsXb hcom hfb hcarrier hceiling hwindowQ hprevQ hnextQ
    (fun w hw => (hdomFrameQ .g1 w hw).2) (fun w hw => (hdomFrameQ .g1 w hw).1)
    (fun w hw => (hdomFrameQ .g0 w hw).2) (fun w hw => (hdomFrameQ .g0 w hw).1)
    hloPrevQ hloFrozenQ hA
    (hA (q - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase hbasePred))
  have hM1 : 1 ≤ Mh := (by decide : (1 : Nat) ≤ 2).trans hM
  have hframePromotion : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q4 - 1)) → ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh := by
    intro read hlo' hhi w hw
    exact hwindowAt (q4 - 1) s4 read
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S m13).trans hlo') hhi w hw
  have hpostQ1 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (m16.trans (Nat.le_succ q)))
  have hloQ1 : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (m16.trans (Nat.le_succ q)))
  have hgradeNextQ : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) Phase.g2),
      Pq.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) Phase.g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) Phase.g2)) v).st (q + 1) Phase.g2
            Pq.erase ⇢ b → b = true := by
    simpa only [hqPred] using hpacketQ.lifecycle.gradeNext
  have hrunQ : Restated.RunBlockOn M S rho W Xb Pq := hpacketQ.lifecycle.runBlock
  have hopening := Restated.seedOpeningProposal_preceq_nextOpeningParent_of_gradeOn facts
    (Mh := Mh) (q := q) (q' := q4) (C' := B4) (B := Pq) (B' := P4)
    S Hs Xb hf hHs hHsXb hcom hfb hwindow4 hcar4 hceil4 hgradeNextQ
      hrunQ hpred hM1 hqPlusTwo hpostQ1
      (hhorAt m9) hframePromotion hloQ1 (hloOpenAt (q + 1) hr0q1) (hloVoteAt q4 hbq4) hA
  have hformsAtPromotion := Restated.namedGradeFormsAt_persists_through_gateOffActionWindowOn facts
    S Hs Xb hf hHs hHsXb hfb (r0 := q + 1) (q := q4 - 1) (Nat.succ_pos q) hgradeNextQ
    hrunQ (by rw [hpred])
    hM1 hpostQ1 (hhorAt m9)
    (fun read hlo' hhi w hw =>
      let h := hframePromotion read hlo' hhi w hw
      ⟨h.2, h.1⟩)
    hloQ1 (hloOpenAt (q + 1) hr0q1) (fun k hk _ _ => hA k hk)
  have hformsPromotion := (hformsAtPromotion (q4 - 1) m12 (le_refl _)).1
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hwindowPromotion : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q4 - 1))),
      Pq.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q4 - 1))) w).st.core).toFG := by
    intro w hw
    have hprocessed : Pq.erase ∈
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q4 - 1))) w).st.T :=
      (p54% formsW_processedAtRead₅₄s) facts S Hs Xb hf hformsPromotion
        (hHs _ _ (facts.gr.domain_le_a S (q4 - 1) .g2) hw) (le_refl _)
    have hframeAtQ4 := hframePromotion ((Restated.Vocabulary.Execution.Setup.a M S (q4 - 1)))
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S m12) le_rfl w hw
    exact Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw)
      (hhorAt m9) hprocessed rfl hrunQ
      (by rw [hpred]) hM1 hframeAtQ4.2 hframeAtQ4.1
  have hbaseSourceFrame : base + 1 ≤ q4 - 2 :=
    (shp% seedSourceFrameRounds_nat) hbaseq m2
  have hpromotionAt := hpromotion Mh q q4 Cq B4 Pq P4 hM hgradedQ hcarrier
    hceiling hwindowQ hpred m14 hr0q4 hcar4 hceil4 hwindow4
    (hpostBase1.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseSourceFrame)) (hhorAt m6)
    (fun read hlo' hhi w hw => hwindowAt q4 s5 read
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseSourceFrame).trans hlo') hhi w hw)
    hrunQ hformsPromotion hwindowPromotion
  have hq4PredPos : 0 < q4 - 1 := (Nat.succ_pos q).trans_le m12
  have hbaseQ4Pred : base + 1 ≤ q4 - 1 := m13.trans m12
  have hq4PredSucc : q4 - 1 + 1 = q4 :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hwindow4.roundPositive)
  have hloQ4Pred : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q4 - 1)) :=
    hloBase1.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseQ4Pred)
  have hgateQ4Pred : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q4 - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q4 - 1))) w).st.h_j + 2 ≤ Mh := by
    intro w hw
    exact (hwindowAt (q4 - 1) s4 ((Restated.Vocabulary.Execution.Setup.a M S (q4 - 1)))
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseQ4Pred) le_rfl w hw).1
  have hbelowPq : NamedBlock.Preceq Pq P4.parent :=
    hopening P4.parent hparentQ4
  obtain ⟨cq, hcq, hPqOut⟩ := proposal_along₆₇b facts S hf (M.opening_slot S.hc q) hwindowQ.proposal
  have hmatureOfParentPred :
      (M.derive_named S.E S.cfg P4.parent).h = Mh - 1 →
        ∀ P' : NamedBlock V, NamedBlock.parent? P4 = some P' →
          (M.derive_named S.E S.cfg P').T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q4 := by
    intro hparentPred
    have hsame : (M.derive_named S.E S.cfg Pq).h =
        (M.derive_named S.E S.cfg P4.parent).h := by
      rw [hpred, hparentPred]
    exact Restated.laterOpening_timeoutMature_of_sameHeightOn facts S Hs Xb hf hdelayBound
      hwindowQ.roundPositive m14
      (some_mem_proposedBlockAt₆₇b facts S hf (M.opening_slot S.hc q) cq hcq hPqOut)
      (mem_stateBeforeTime_along₆₇b hf.sorted hf.onePath _) c4 hc4 hP4
      hparentQ4 hbelowPq hsame.symm
  have hfbProp : Execution.BelowOneThird S
      (Hs (M.proposal_time S.E ((M.opening_slot S.hc (q4 - 1 + 1))))) :=
    hfb _ (by rw [hq4PredSucc]; exact hproposalHor4)
  rcases Restated.seedFreshOpening_promotion_atAction_l67 facts S Hs Xb hf hHs hHsXb
      (r := q4 - 1) (C := Pq) (B := P4) hfbProp hM hq4PredPos
      hloQ4Pred hrunQ hpred hformsPromotion
      hwindowPromotion hpromotionAt.sourceHeightLeNextOpeningParent hgateQ4Pred c4
      (by rw [hq4PredSucc]; exact hc4) (by rw [hq4PredSucc]; exact hP4) hbelowPq hparentCap4'
      (by rw [hq4PredSucc]; exact hprop4)
      (by rw [hq4PredSucc]; exact hproposalHor4)
      (by rw [hq4PredSucc]; exact hmatureOfParentPred) hA
      (hloOpenAt (q4 - 1) hr0q4p) with
    hexact4 | hrise4
  ·
    have hcutFrame4 : ∀ w ∈ Hs (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q4 + 1)),
        (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q4 + 1))) w).st.h_max = Mh ∧
          (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q4 + 1))) w).st.h_j + 2 ≤ Mh := by
      intro w hw
      have h := hwindowAt (q4 + 1) s2 (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q4 + 1))
        ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S m11).trans
          (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
            (facts.gr.action_add_delta_le_next_Γ_neg1 S q4)))
        (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q4)) w hw
      exact ⟨h.2, h.1⟩
    have hprevFrontier4 : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q4 - 1))),
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q4 - 1))) u).st.h_max = Mh := by
      intro u hu
      exact (hwindowAt (q4 - 1) s4 ((Restated.Vocabulary.Execution.Setup.a M S (q4 - 1)))
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((shp% seedPrevRound_nat) m10)) le_rfl u hu).2
    have hdomG0Lo : (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤
        M.domain S.E S.hc q4 .g0 := by
      have h := Restated.action_add_delta_le_domain_g2_succ_l54 facts S (q4 - 1)
      rw [hq4PredSucc] at h
      exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbaseQ4Pred).trans
        (((le_add_of_nonneg_right S.E.Δ_pos.le).trans h).trans
          (facts.gr.domain_g2_le_domain_l67 S q4 .g0))
    have hdomG0Hi : M.domain S.E S.hc q4 .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q4 + 1)) :=
      (facts.gr.domain_le_a S q4 .g0).trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q4))
    have hloFrozen4 : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q4) - 1) :=
      hloBase.trans (Restated.action_le_proposal_openingPred_l67 facts S hbq41)
    have hadopt4 := Restated.seedOpeningLifecycle_of_inputsOn facts S Hs Xb hf hHs hHsXb hcom hfb hcar4
      hceil4 hwindow4 hprevFrontier4 hcutFrame4
      (fun w hw => (hwindowAt (q4 + 1) s2 _ hdomG0Lo hdomG0Hi w hw).2)
      (fun w hw => (hwindowAt (q4 + 1) s2 _ hdomG0Lo hdomG0Hi w hw).1)
      hloQ4Pred hloFrozen4 hA
      (hA (q4 - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase hbaseQ4Pred))
    exact Restated.seedExactOpening_outcomeOn facts S Hs Xb hf hHs hHsXb hcom hfb hM m11 m15 m8 hpostBase
      hhorEnd hcap (hwindowAt (q5 - 1) s7) hcar4 hcar5 hceil5 c4 hc4 hP4 c5 hc5 hP5
      hadopt4.gradeNext hexact4 hloBase (hloOpenAt (q4 + 1) hr0q4s) hA
  ·
    rw [hq4PredSucc] at hrise4
    exact Or.inl (lt_of_lt_of_le hrise4
      (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloQ4 hrelayQ4 hhorEnd hne))

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
local macro "shp% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.SeedHeightProgress)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committees condition and the weight bound, if `2 ≤ q`,
    `S.E.t_GST ≤ S.a (q − 2)`, `S.a (q + 1)` is in the horizon, every member of the set for each
    read from `S.a (q − 2)` to `S.a (q + 1)` has `h_j + 2 ≤ Mh` and `h_max = Mh` before that read,
    the band carriers cover rounds `q − 2` and `q − 1`, the bounds on `lo` hold and the awake
    conditions hold, then every member of the sets for `S.a (q − 1)` and `S.a q` selects a grade-2
    candidate at every node state of its action read. -/
theorem seedGradedAndClear_of_coversOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (_hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round}
    (hq2 : 2 ≤ q)
    (hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hframe : Restated.SeedGateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (q - 2) (q + 1))
    (hcoverPrev : Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh (q - 2)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 2)))))
    (hcoverCur : Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh (q - 1)
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAprev2 : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 2)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 2))) → M.awake_for_grade2 S u (W j u) (q - 2)) :
    Restated.SeedRoundGradedAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs q := by
  obtain ⟨hstep2, hstep1, hle21, hle1, hle2⟩ := (shp% seedCoverRounds_nat) hq2
  have hhorQ : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans hhor
  have hhorPred : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hle1).trans hhorQ
  have hframeAt : ∀ {k : Round}, q - 2 ≤ k → k ≤ q + 1 →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.h_max = Mh := by
    intro k hlo' hhi w hw
    exact hframe ((Restated.Vocabulary.Execution.Setup.a M S k)) (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hlo') (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi) w hw
  have hrelay : ∀ {k : Round}, q - 2 ≤ k → k + 1 ≤ q + 1 →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ),
        (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ)) w).st.h_max = Mh ∧
          (W (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ)) w).st.h_j + 2 ≤ Mh := by
    intro k hlo' hhi w hw
    have hstep : (Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (k + 1)) :=
      le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S k)
        (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S k))
    have hthis := hframe ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ)
      (le_trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hlo')
        (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)))
      (hstep.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi)) w hw
    exact ⟨hthis.2, hthis.1⟩
  have hdomain : ∀ {k : Round}, q - 2 ≤ k → k + 1 ≤ q + 1 →
      ∀ w ∈ Hs (M.domain S.E S.hc (k + 1) .g2),
        (W (strictEventIndex rho (M.domain S.E S.hc (k + 1) .g2)) w).st.h_max = Mh ∧
          (W (strictEventIndex rho (M.domain S.E S.hc (k + 1) .g2)) w).st.h_j + 2 ≤ Mh := by
    intro k hlo' hhi w hw
    have hlow : (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) ≤ M.domain S.E S.hc (k + 1) .g2 :=
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hlo').trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (Restated.action_add_delta_le_domain_g2_succ_l54 facts S k))
    have hhigh : M.domain S.E S.hc (k + 1) .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
      (facts.gr.domain_le_a S (k + 1) .g2).trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi)
    have hthis := hframe _ hlow hhigh w hw
    exact ⟨hthis.2, hthis.1⟩
  have hloPrev1 : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hle21)
  have hloOpenCur : lo ≤ M.opening S.E S.hc (q - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hle1 _))
  have hframeHeal : ∀ {k : Round}, q - 2 ≤ k → k ≤ q + 1 →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.core).toFG.h_max = Mh ∧
          (M.toHealing
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.core).toFG.h_j + 2 ≤ Mh := by
    intro k hlo' hhi w hw
    have hread := hframeAt hlo' hhi w hw
    refine ⟨?_, ?_⟩
    · rw [facts.sto.Sts_toHealing_h_max]
      exact hread.2
    · rw [facts.sto.toHealing_h_j]
      exact hread.1
  have hgradePrev : Restated.SeedRoundBandGradeAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb Mh (q - 1) := by
    have h := Restated.seedBandGrade_of_bandCarrierCoverOn facts S Hs Xb hf hHs hHsXb hfb
      (Mh := Mh) (q := q - 2) hpostPrev
      (by rw [hstep2]; exact hhorPred)
      (hrelay (le_refl _) (by rw [hstep2]; exact hle1.trans (Nat.le_succ q)))
      (fun w hw => by
        rw [hstep2] at hw ⊢
        exact hframeHeal hle21 (hle1.trans (Nat.le_succ q)) w hw)
      hcoverPrev
      (hdomain (le_refl _) (by rw [hstep2]; exact hle1.trans (Nat.le_succ q)))
      hlo (by rw [hstep2]; exact hloOpen) hAprev2
    rwa [hstep2] at h
  have hgradeCur : Restated.SeedRoundBandGradeAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs Xb Mh q := by
    have h := Restated.seedBandGrade_of_bandCarrierCoverOn facts S Hs Xb hf hHs hHsXb hfb
      (Mh := Mh) (q := q - 1)
      (hpostPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hle21))
      (by rw [hstep1]; exact hhorQ)
      (hrelay hle21 (by rw [hstep1]; exact Nat.le_succ q))
      (fun w hw => by
        rw [hstep1] at hw ⊢
        exact hframeHeal hle2 (Nat.le_succ q) w hw)
      hcoverCur
      (hdomain hle21 (by rw [hstep1]; exact Nat.le_succ q))
      hloPrev1 (by rw [hstep1]; exact hloOpenCur)
      (hA (q - 1) (Restated.lo_le_early_g2_sub_delta_of_opening facts S (Nat.sub_pos_of_lt hq2)
        hloOpen le_rfl))
    rwa [hstep1] at h
  have hframeStore : ∀ {k : Round}, q - 2 ≤ k → k ≤ q + 1 →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        (Restated.Vocabulary.Execution.Setup.a M S k) ≤ rho.horizon ∧
          (M.toHealing
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.core).toFG.h_max = Mh ∧
            (M.toHealing
              (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w).st.core).toFG.h_j + 2 ≤ Mh := by
    intro k hlo' hhi w hw
    exact ⟨(Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi).trans hhor,
      hframeHeal hlo' hhi w hw⟩
  exact Restated.seedRoundGraded_of_bandGradeOn facts S Hs Xb hf
    (hframeStore hle21 (hle1.trans (Nat.le_succ q)))
    (hframeStore hle2 (Nat.le_succ q)) hgradePrev hgradeCur

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
local macro "shp% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.SeedHeightProgress)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Along `W`, under the committees condition and the weight bound,
    `Restated.HeightProgressSeedFromOn` holds from `r0`, given proposer carriers recurring within
    `gap` from `t₀` (`hrec`), the boundary condition and band-carrier cover at every carrier round
    `q ≥ base + 4` of a window in which every member has `h_j + 2 ≤ Mh` and `h_max = Mh` (`hadopt`),
    the `Mh − 1` closer (`hclose`), `lo ≤ S.a r0`, `lo ≤ opening (r0 + 1 − η_SG)`, `t₀ ≤ S.a r0` and
    the grade-2 awake condition `hA`. -/
theorem heightProgressSeedFrom_of_carrierAdoptionOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs) (hfb : BelowOneThirdOn S rho Hs)
    {r0 gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (_hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hadopt : ∀ (Mh : Height) (base q : Round), r0 ≤ base → base + 4 ≤ q →
      S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S base) → (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) ≤ rho.horizon →
      Restated.SeedGateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh (base + 1) (q + 2) →
      Restated.ProposerCarrierAtOn M S Hs q →
      Restated.SeedBoundaryAdoptionAtOn M S rho W Hs Xb Mh q
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))) ∧
        Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh q
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))))
    (hclose : Restated.SeedPredCloserFromOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb r0 gap delayExtra)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.HeightProgressSeedFromOn M S rho W (fun t => W (strictEventIndex rho t))
      (fun t => W (inclusiveEventIndex rho t)) Hs Xb r0 gap delayExtra := by
  intro base hr0 hpostBase Mh hM _hfrontierBase hgateBase hhorEnd
  set endpoint : Round := base + seedLag gap delayExtra with hendpoint
  by_cases hrise : Mh < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpoint)).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpoint)) v).st.core.h_max)
  · exact Or.inl hrise
  have hcap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpoint)).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpoint)) v).st.core.h_max) ≤ Mh :=
    Nat.le_of_not_gt hrise
  obtain ⟨x0, hx0⟩ := Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs ((Restated.Vocabulary.Execution.Setup.a M S base))
  have h2 : 2 ≤ Mh :=
    (Nat.le_add_left 2 _).trans (hgateBase x0 hx0)
  have hloBase : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base) := hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)
  rcases Restated.seedBaseFixedRoot_or_gateOffWindowOn facts S Hs Xb hf hHs hHsXb hcom hfb (Mh := Mh)
      (base := base) (endpoint := endpoint) hM hpostBase h2 hcap hhorEnd hloBase with
    hfix | hgateWindow
  · obtain ⟨u, read, hu, hread1, hread2, hlo1, hfixRead⟩ := hfix
    exact Or.inr (Or.inl ⟨u, read, hu, hread1, hread2,
      Or.inl ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ base)).trans hlo1), hfixRead⟩)
  have hloOpenAt : ∀ k : Round, r0 + 1 ≤ k → lo ≤ M.opening S.E S.hc (k - S.hc.η_SG) :=
    fun k hk => hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hk _))
  have hloVoteAt : ∀ k : Round, base < k →
      lo ≤ M.vote_time S.E ((M.opening_slot S.hc k) - 1) :=
    fun k hk => hloBase.trans (Restated.action_le_vote_openingPred_l67 facts S hk)
  have hselect (k : Round) (hbk : base < k) (hk : k + gap ≤ endpoint) :
      ∃ c : Round, k ≤ c ∧ c ≤ k + gap ∧ Restated.ProposerCarrierAtOn M S Hs c :=
    hrec k
      ((ht₀.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0)).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hbk)))
      ((Restated.Vocabulary.Proofs.HealingLemmas.openingProposal_window_le_action facts S k gap).trans
        ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk).trans hhorEnd))
  have hfirst : base < base + 4 ∧ base + 4 + gap ≤ endpoint := by
    simpa only [hendpoint, seedLag] using
      ((shp% seedAdoptionSelectRound1_nat) (base := base) (gap := gap)
        (delayExtra := delayExtra))
  obtain ⟨q1, hq1lo, hq1hi, hcar1⟩ := hselect (base + 4)
    hfirst.1 hfirst.2
  have hsecond : base < q1 + 2 ∧ q1 + 2 + gap ≤ endpoint := by
    simpa only [hendpoint, seedLag] using
      ((shp% seedAdoptionSelectRound2_nat) (delayExtra := delayExtra) hq1lo hq1hi)
  obtain ⟨q2, hq2lo, hq2hi, hcar2⟩ := hselect (q1 + 2)
    hsecond.1 hsecond.2
  have hthird : base < q2 + 2 + delayExtra ∧
      q2 + 2 + delayExtra + gap ≤ endpoint := by
    simpa only [hendpoint, seedLag] using
      ((shp% seedAdoptionSelectRound3_nat) hq1lo hq1hi hq2lo hq2hi)
  obtain ⟨q3, hq3lo, hq3hi, hcar3⟩ := hselect (q2 + 2 + delayExtra)
    hthird.1 hthird.2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
    n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29,
    n30, n31⟩ :=
    (shp% seedAdoptionRounds_nat) (delayExtra := delayExtra) hq1lo hq1hi hq2lo hq2hi hq3lo
      hq3hi
  obtain ⟨hbq1s, hr0q1s, hr0q1, hbq2, hbq2s, hr0q2p, hr0q2s⟩ :=
    seedAdoptionLaterRounds_nat_l67 hr0 hq1lo hq2lo
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ :=
    seedAdoptionReadsStrict_nat_l67 hq1lo hq1hi hq2lo hq2hi hq3lo hq3hi
  obtain ⟨c2, hc2⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q2)))
      (S.E.proposer (M.opening_slot S.hc q2))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc q2))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q2)))
      (S.E.proposer (M.opening_slot S.hc q2))).cache
  obtain ⟨P2, hP2⟩ := proposal_some_along₆₇b facts S hf (M.opening_slot S.hc q2) c2 hc2
  obtain ⟨c3, hc3⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q3)))
      (S.E.proposer (M.opening_slot S.hc q3))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc q3))
    (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q3)))
      (S.E.proposer (M.opening_slot S.hc q3))).cache
  obtain ⟨P3, hP3⟩ := proposal_some_along₆₇b facts S hf (M.opening_slot S.hc q3) c3 hc3
  have hq1end2 : q1 + 2 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n1
  have hq2end1 : q2 + 1 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n25
  have hq2end2 : q2 + 2 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n2
  have hq3end2 : q3 + 2 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n3
  have hq3end : q3 ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n4
  have hq2budget : q2 + 2 * gap + 6 + 2 * delayExtra ≤ endpoint := by
    simpa only [hendpoint, seedLag] using n23
  have hpostBase1 : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ base))
  have hpostBase1L : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) :=
    gstLagged_le_a_succ₆₇b facts S hpostBase
  have hloBase1 : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) :=
    hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ base))
  have hhorAt : ∀ {k : Round}, k ≤ endpoint → (Restated.Vocabulary.Execution.Setup.a M S k) ≤ rho.horizon := by
    intro k hk
    exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk).trans hhorEnd
  have hwindow : ∀ (k : Round), k < endpoint →
      ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh := by
    intro k hk read hlo' hhi w hw
    exact hgateWindow read hlo' (hhi.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hk.le)) w hw
      (Or.inl (lt_of_le_of_lt (Int.add_le_add_right hhi _)
        (Restated.action_add_delta_lt_action_of_lt_l67 facts S hk)))
  have hframeAt : ∀ {lo' hi : Round}, base + 1 ≤ lo' → hi < endpoint →
      Restated.SeedGateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh lo' hi := by
    intro lo' hi hlo' hhi read hread1 hread2 w hw
    exact hwindow hi hhi read ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hlo').trans hread1) hread2 w hw
  have hbq1 : base < q1 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 4)) hq1lo
  have hAbase1 := hA (base + 1)
    (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase (Nat.lt_succ_self base))
  obtain ⟨hadoption, hcover1⟩ := hadopt Mh base q1 hr0 hq1lo hpostBase
    (hhorAt hq1end2) (hframeAt (le_refl (base + 1)) t1)
    hcar1
  obtain ⟨B1, hceil1⟩ := Restated.exists_roundCeiling_of_window_of_adoptionOn facts S Hs Xb hf hHs hHsXb hcom
    hfb (base := base + 1) (q := q1) hpostBase1L n7 (hhorAt hq1end2)
    (fun read hlo' hhi w hw => hwindow (q1 + 2) t1 read hlo' hhi w hw)
    hadoption.headThin hadoption.entry hloBase1 hA hAbase1
  obtain ⟨B2, hceil2, -⟩ := Restated.roundCeiling_through_of_windowOn facts S Hs Xb hf hHs hHsXb hcom hfb
    (base := base + 1) (first := q1 + 1) (last := q2) (C := B1)
    hpostBase1L n8 (hhorAt hq2end2)
    (fun read hlo' hhi w hw => hwindow (q2 + 1) t4 read hlo' hhi w hw)
    hceil1 hloBase1 (hloVoteAt (q1 + 1) hbq1s) (hloOpenAt (q1 + 1) hr0q1s) hA hAbase1 q2 n9
    (le_refl _)
  obtain ⟨B3, hceil3, -⟩ := Restated.roundCeiling_through_of_windowOn facts S Hs Xb hf hHs hHsXb hcom hfb
    (base := base + 1) (first := q1 + 1) (last := q3) (C := B1)
    hpostBase1L n8 (hhorAt hq3end2)
    (fun read hlo' hhi w hw => hwindow (q3 + 1) (Nat.lt_of_succ_lt t3) read hlo' hhi w hw)
    hceil1 hloBase1 (hloVoteAt (q1 + 1) hbq1s) (hloOpenAt (q1 + 1) hr0q1s) hA hAbase1 q3 n10
    (le_refl _)
  have hprop2 : S.E.proposer ((M.opening_slot S.hc q2)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q2))) := by
    simpa only [Nat.add_zero] using hcar2 0 (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩ :=
    Restated.gateOffOpeningWindow_of_windowOn facts S Hs Xb hf hHs hHsXb (base := base + 1) (q := q2)
      hpostBase1 n11 (hhorAt hq2end1) hprop2 c2 hc2 hP2
      (fun read hlo' hhi w hw => hwindow (q2 + 1) t4 read hlo' hhi w hw) hloBase1
  have hwindow2 : Restated.NamedGateOffOpeningWindowAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q2 P2 :=
    ⟨⟨c2, hc2, hP2⟩, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
  have hcovers := Restated.seedBandCarrierCover_throughOn facts S Hs Xb hf hHs hHsXb hfb (Mh := Mh)
    (lo := q1) (hi := q2 + 1) (hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S n17))
    (hhorAt hq2end1) (hframeAt ((Nat.le_succ (base + 1)).trans n7) t4)
    hcover1 (hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S n17)) (hloOpenAt (q1 + 1) hr0q1s) hA
    (hA q1 (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase hbq1))
  have hgraded2 := Restated.seedGradedAndClear_of_coversOn facts S Hs Xb hf hHs hHsXb hcom hfb (q := q2)
    n28 (hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.le_succ base).trans n27)))
    (hhorAt hq2end1) (hframeAt n27 t4)
    (hcovers (q2 - 2) n29 n31.1) (hcovers (q2 - 1) n30 n31.2)
    (hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.le_succ base).trans n27)))
    (hloOpenAt (q2 - 1) hr0q2p) hA
    (hA (q2 - 2) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase
      (Nat.lt_of_lt_of_le hbq1 (Nat.le_sub_of_add_le hq2lo))))
  have hloQ2 : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q2)) :=
    hloBase.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hbq2))
  have hrunP2 : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick
      (S.E.proposer (M.opening_slot S.hc q2)) (M.proposal_time S.E (M.opening_slot S.hc q2))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q2))
        (W j (S.E.proposer (M.opening_slot S.hc q2))) (M.round_of S.hc (M.opening_slot S.hc q2)) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q2)) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc q2]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hbq2
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q2
      have h3 : lo ≤ M.a S.hc S.E.Δ base := hloBase
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop2) hwin
  rcases Restated.namedGateOffOpening_pred_or_exact_or_hMaxRiseOn facts S Hs Xb hf hHs hcar2
      hwindow2 hloQ2 hrunP2 with hpred | hexact | hriseProposal
  ·
    exact hclose base q2 B2 P2 hr0 n13 hq2budget hpostBase hhorEnd Mh hM hcap h2
      hgateWindow hgraded2 hcar2 hceil2 hwindow2 hpred
  ·
    have hcutFrame2 : ∀ w ∈ Hs (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q2 + 1)),
        (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q2 + 1))) w).st.h_max = Mh ∧
          (W (strictEventIndex rho (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q2 + 1))) w).st.h_j + 2 ≤ Mh := by
      intro w hw
      have h := hwindow (q2 + 1) t4 (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q2 + 1))
        ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S n12).trans
          (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
            (facts.gr.action_add_delta_le_next_Γ_neg1 S q2)))
        (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S q2)) w hw
      exact ⟨h.2, h.1⟩
    have hbasePred2 : base + 1 ≤ q2 - 1 := (shp% seedPrevRound_nat) n11
    have hprevFrontier2 : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q2 - 1))),
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q2 - 1))) u).st.h_max = Mh := by
      intro u hu
      exact (hwindow (q2 - 1) t5 ((Restated.Vocabulary.Execution.Setup.a M S (q2 - 1)))
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred2) le_rfl u hu).2
    have hq2Pred : q2 - 1 + 1 = q2 :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hwindow2.roundPositive)
    have hdomG0Lo : (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤
        M.domain S.E S.hc q2 .g0 := by
      have h := Restated.action_add_delta_le_domain_g2_succ_l54 facts S (q2 - 1)
      rw [hq2Pred] at h
      exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred2).trans
        (((le_add_of_nonneg_right S.E.Δ_pos.le).trans h).trans
          (facts.gr.domain_g2_le_domain_l67 S q2 .g0))
    have hdomG0Hi : M.domain S.E S.hc q2 .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q2 + 1)) :=
      (facts.gr.domain_le_a S q2 .g0).trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q2))
    have hloPrev2 : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q2 - 1)) := hloBase1.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred2)
    have hloFrozen2 : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q2) - 1) :=
      hloBase.trans (Restated.action_le_proposal_openingPred_l67 facts S hbq2s)
    have hadopt2 := Restated.seedOpeningLifecycle_of_inputsOn facts S Hs Xb hf hHs hHsXb hcom hfb hcar2
      hceil2 hwindow2 hprevFrontier2 hcutFrame2
      (fun w hw => (hwindow (q2 + 1) t4 _ hdomG0Lo hdomG0Hi w hw).2)
      (fun w hw => (hwindow (q2 + 1) t4 _ hdomG0Lo hdomG0Hi w hw).1)
      hloPrev2 hloFrozen2 hA
      (hA (q2 - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase hbasePred2))
    exact Restated.seedExactOpening_outcomeOn facts S Hs Xb hf hHs hHsXb hcom hfb h2 n12 n14 hq3end
      hpostBase hhorEnd hcap (hwindow (q3 - 1) t6) hcar2 hcar3 hceil3 c2 hc2 hP2 c3 hc3 hP3
      hadopt2.gradeNext hexact hloBase (hloOpenAt (q2 + 1) hr0q2s) hA
  ·
    have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S endpoint))).Nonempty :=
      Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _
    refine Or.inl (lt_of_lt_of_le hriseProposal ?_)
    exact Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloQ2
      (lt_of_lt_of_le (Restated.proposal_add_delta_lt_action_l67 facts S q2)
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.le_succ q2).trans hq2end1))) hhorEnd hne

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

local macro "p66b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_66b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p54% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_54)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p65b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_65b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
