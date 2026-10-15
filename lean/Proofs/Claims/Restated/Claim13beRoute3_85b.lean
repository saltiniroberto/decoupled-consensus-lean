import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_67b
import Proofs.Claims.Restated.Claim13beRoute3_70b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Proofs.Claims.Restated.Claim13beRoute3_86g
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradePersistence
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4FKGrade
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The opening proposal after the progress deadline

At a round after the progress deadline whose opening proposer is honest and proposed `P`, every
honest round SG block and FG source is `P`, the previous opening proposal is an ancestor of `P`'s
parent and is graded 2 at the round, and the FG root at a read in the round is an ancestor of `P`.
Stated over a model `M : Record.Model V` along a path `W` of the run, then along the path an
execution follows.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_64b.lean`, by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_58.lean`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_60.lean`, by name. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_63.lean`, by name. -/
local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_71.lean`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86b.lean`, by name. -/
local macro "p86b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86c.lean`, by name. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86f.lean`, by name. -/
local macro "p86f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86g.lean`, by name. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open scoped DC

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₈₅b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₈₅b {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- If `m` is at least two rounds after the progress deadline and `lo ≤ opening (rGST + 2 − η_SG)`,
    then `lo ≤ opening (m − η_SG)`. -/
theorem lo_le_opening_afterDeadline_l85b (facts : Record.Facts M) {delayExtra : Nat} (S : Setup V) {rho : Record.Run V}
    {rGST gap : Round} {m : Round} {lo : Int}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG)) :
    lo ≤ M.opening S.E S.hc (m - S.hc.η_SG) := by
  refine hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S ?_)
  have h2 : rGST + 2 ≤ m := by
    have hbase : rGST + 1 ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
      unfold fgSafetyProgressDeadline
      exact Nat.le_add_right _ _
    exact (Nat.succ_le_succ hbase).trans ((Nat.le_succ _).trans hm)
  exact Nat.sub_le_sub_right h2 _

/-- The SG root read under the grade contract of a cache `c'` from the healing view of a store with
    a cache `c` written in is the one read from the store's own healing view. -/
private theorem sgRoot_store_with_cache₈₅b (facts : Record.Facts M) {E : Env V}
    {hc : Protocol.HealConfig} {st : M.NS} {c c' : M.Cache} {r : Round} {x : Block V} :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

/-- For every world that can hold before round `m`'s action instant and every node state `n` of
    `v`'s round-`m` action read from it, `n`'s round-`m` anchor can return a block `X` exactly when
    the confirmation anchor can return `X` at the node state built from `v`'s store in that world,
    with its clock set to the confirmation instant of `m`'s opening slot and the cache of `n`. -/
theorem nodeAnchor_action_eq_confirmationAnchor_l85b (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (m : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S m),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) m,
    ∀ X : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n m ⇢ X ↔
      Restated.Vocabulary.Internal.namedConfirmationAnchor M S
        (M.mkNode (M.ns_setClock S.E (w v).st (M.confirmation_time S.E (M.opening_slot S.hc m)))
          (w v).record n.cache) ⇢ X := by
  intro w hw n hn X
  unfold Restated.Vocabulary.Internal.namedConfirmationAnchor
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st, sgRoot_store_with_cache₈₅b facts]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [← (p86f% tickStore_eq₈₆f) facts S]
  exact (Restated.Vocabulary.Proofs.w4_confAnchorWith_eq_nodeAnchor facts S rho v m w hw n hn X).symm

/-- Under the premises of `openingAdoption_afterDeadlineOn` along `W`, every node state of the
    round-`m` action read on `W` of a member of the set for `S.a m` has live confirmation `P`, and
    every outcome of its round-`m` grade read has an anchor that is an ancestor of `P` and a clear
    test that passes `P`. -/
private theorem actionRead_openingProposal₈₅b (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) u) m,
      nu.st.core.live_confirmed = P.erase ∧
      ∀ Gr : GradeRead V, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S nu m ⇢ Gr →
        Block.Preceq Gr.anchor P.erase ∧ Gr.clear P.erase = true := by
  obtain ⟨-, hlive, hclear⟩ := Restated.openingAdoption_afterDeadlineOn facts S Hs Xb hf hHs
    hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll
  have hread := Restated.openingProposal_confirmationRead_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc m)) =
      (Restated.Vocabulary.Execution.Setup.a M S m) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E m).symm
  intro u hu nu hnu
  have hmem := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S m)
  have hdom0 : M.domain S.E S.hc m .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S m) :=
    facts.gr.domain_le_a S m .g0
  refine ⟨hlive u hu nu hnu, fun Gr hGr => ⟨?_, ?_⟩⟩
  · have h1 : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S nu m ⇢ Gr.anchor :=
      returns_map_intro₈₅b (fun g : GradeRead V => g.anchor) _ Gr hGr
    have h2 := (Restated.nodeAnchor_action_eq_confirmationAnchor_l85b facts S rho u m _ hmem nu hnu
      Gr.anchor).1 h1
    rw [hconfA] at h2 hread
    obtain ⟨c', hc', st, hst, rfl⟩ := hnu
    rw [facts.nd.mkNode_cache] at h2
    exact (hread u hu c' hc').2.1 Gr.anchor h2
  · exact hclear u (hHs _ _ hdom0 hu) nu hnu (Gr.clear P.erase)
      (returns_map_intro₈₅b (fun g : GradeRead V => g.clear P.erase) _ Gr hGr)

/-- Under the premises of `openingAdoption_afterDeadlineOn` along `W`, every round-`m` SG block of a
    member of the set for `S.a m` is the opening proposal `P`: for every node state of its round-`m`
    action read on `W` and every grade-2 candidate that node state can give, every block the SG vote
    selector can return is `P`. -/
theorem sgBlock_eq_openingProposal_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) u) m,
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) A2 ⇢ G →
        G = P.erase := by
  intro u hu nu hnu A2 hA2 G hG
  obtain ⟨hlive, hreads⟩ := actionRead_openingProposal₈₅b facts S Hs Xb hf hHs hHsXb hcom
    hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll u hu nu hnu
  have hmem := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S m)
  have hnuAt : nu ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho u m :=
    ⟨_, hmem, hnu⟩
  obtain ⟨Gr, hGr⟩ := facts.gr.read_nonempty (M.gradeContract nu.cache) S.E S.hc
    (M.toHealing nu.st.core) m
  exact Restated.Vocabulary.Proofs.w4_actionSGBlockAt_eq_liveConfirmed facts S
    (Can := P.erase) (D := P.erase) (A := Gr.anchor)
    (Proofs.ModelProperties.Preceq_self P.erase) (hreads Gr hGr).1 nu hnuAt hlive Gr hGr rfl
    (hreads Gr hGr).2 A2 hA2 G hG

/-- Under the premises of `openingAdoption_afterDeadlineOn` along `W`, if the FG source at a node
    state of the round-`m` action read on `W` of a member of the set for `S.a m` can return
    `some X`, then `X` is the opening proposal `P`. -/
theorem fgSource_eq_openingProposal_of_some_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) u) m,
      ∀ X : Block V,
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nu ⇢ some X → X = P.erase := by
  intro u hu nu hnu X hsource
  obtain ⟨hlive, hreads⟩ := actionRead_openingProposal₈₅b facts S Hs Xb hf hHs hHsXb hcom
    hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll u hu nu hnu
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.succ_pos 1) ((Nat.le_add_left 2 _).trans hm)
  have hdom1 : M.domain S.E S.hc m .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S m) :=
    facts.gr.domain_le_a S m .g1
  have hloc := Restated.lo_le_opening_afterDeadline_l85b facts S hm hloOpen
  have hmem := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S m)
  have hnuAt : nu ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho u m :=
    ⟨_, hmem, hnu⟩
  have hround : M.round_of S.hc (M.toHealing nu.st.core).s = m := by
    show M.round_of S.hc (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore.s = m
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho u m nu hnuAt
  have hsource' : (do
      let g ← M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
        (M.round_of S.hc (M.toHealing nu.st.core).s)
      M.fg_source_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
        (M.round_of S.hc (M.toHealing nu.st.core).s) g) ⇢ some X := hsource
  rw [hround] at hsource'
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₈₅b _ _ _).1 hsource'
  obtain ⟨q, hA2q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2q
  obtain ⟨Gr, hGr⟩ := facts.gr.read_nonempty (M.gradeContract nu.cache) S.E S.hc
    (M.toHealing nu.st.core) m
  have hGQ : Gr.Q2 = some q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ Gr hGr _ hA2).symm
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nu m ⇢ some q := by
    have h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nu m ⇢ Gr.Q2 :=
      returns_map_intro₈₅b (fun g : GradeRead V => g.Q2) _ Gr hGr
    rwa [hGQ] at h
  have hqA : Block.Preceq q Gr.anchor :=
    Restated.actionQ2_preceq_actionAnchorOn facts S Hs Xb hf hHs hHsXb hmpos hhor
      (hHs _ _ hdom1 hu) hloc nu hnu hq Gr.anchor
      (returns_map_intro₈₅b (fun g : GradeRead V => g.anchor) _ Gr hGr)
  have hqP : Block.Preceq q P.erase :=
    Proofs.ModelProperties.Preceq_trans hqA (hreads Gr hGr).1
  have hwalk : M.deepest_clear (some q)
      (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore.live_confirmed Gr.clear =
        some P.erase := by
    rw [facts.sto.toHealing_live_confirmed, hlive]
    exact facts.gr.deepest_clear_eq_tip (preceq_eq_true_iff_Preceq.2 hqP) (hreads Gr hGr).2
  exact (Option.some.inj
    (facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ Gr hGr hwalk _ hsrc))

/-- Under the premises of `openingAdoption_afterDeadlineOn` along `W`, if moreover `m` is at least
    three rounds after the deadline and the opening proposer of round `m − 1` is in the set for its
    opening slot's confirmation instant and proposed `P'` on `W`, then `P'` is an ancestor of the
    parent of every proposal input of the round-`m` opening proposer's read on `W`. -/
theorem prevOpeningProposal_preceq_proposedParent_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hm3 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ m)
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (m - 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (m - 1)))))
    {P' : NamedBlock V}
    (cp' : M.Cache)
    (hcp' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (m - 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).cache ⇢ cp')
    (hP' : M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (m - 1))))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).record cp').st ⇢ some P') :
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc m)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
            (S.E.proposer (M.opening_slot S.hc m))).st
          (M.proposal_time S.E (M.opening_slot S.hc m)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
            (S.E.proposer (M.opening_slot S.hc m))).record cp).st.core) ⇢ I →
      Block.Preceq P'.erase I.parent := by
  intro I hI
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc m)) =
      (Restated.Vocabulary.Execution.Setup.a M S m) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E m).symm
  have hvoteHor : M.vote_time S.E ((M.opening_slot S.hc m)) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans (by rw [hconfA]; exact hhor)
  have hsgParent := (p86g% actionSGBlock_preceq_proposedParent_afterDeadlineOn₈₆g) facts S Hs Xb
    hf hHs hHsXb hcom hbelow hrec hdelay hpost hm hvoteHor hopening cp hcp hP hloPost hloOpen
    ht₀ hAll
  have hmPrev : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m - 1 :=
    Nat.le_sub_of_add_le hm3
  have hmlt : m - 1 ≤ m := Nat.sub_le m 1
  have hhorPrev : (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) ≤ rho.horizon :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hmlt).trans hhor
  have hsg := Restated.sgBlock_eq_openingProposal_afterDeadlineOn facts S Hs Xb hf hHs hHsXb
    hcom hbelow hrec hdelay hpost hmPrev hhorPrev hopeningPrev cp' hcp' hP' hloPost hloOpen ht₀ hAll
  have hprop : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs ((Restated.Vocabulary.Execution.Setup.a M S (m - 1))) := by
    refine hHs _ _
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hmlt) ?_
    rw [← hconfA]
    exact hopening
  obtain ⟨nv, hnv, g, hg, B, hB⟩ := (p64b% exists_actionSG₆₄b) facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (m - 1)))
      (S.E.proposer (M.opening_slot S.hc m))) (m - 1)
  have hBP := hsg _ hprop nv hnv g hg B hB
  rw [← hBP]
  exact hsgParent _ hprop nv hnv g hg B hB I hI

/-- Under the bundle with path `W` and a run-scoped named height-regime base along `W`, if every
    head a member of the set for `vote_time o_p` can vote at `o_p` on `W` is `P`, and every FG
    source `some Y` of a round-`p` action read on `W` of a member of the set for `S.a p` has
    `Y = P`, then for a read between `S.a p` and `S.a (p + 1)` within the horizon and `u` in the set
    for the read, the FG root of `u`'s store in the world of `W` strictly before the read is an
    ancestor of `P`. -/
theorem NamedHeightRegimeBaseRunOn.fgRoot_preceq_openingProposal_at_read_l85b
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤
      inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline))
    {p : Round} (hp : deadline + 2 ≤ p) {P : NamedBlock V}
    (hheads : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc p))), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc p))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).st
          (M.vote_time S.E (M.opening_slot S.hc p)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        H = P.erase)
    (hsource : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S p)),
      ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S p)) w) p,
      ∀ Y : Block V,
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nw ⇢ some Y → Y = P.erase)
    {read : Time} (hreadLow : (Restated.Vocabulary.Execution.Setup.a M S p) ≤ read)
    (hreadHigh : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (p + 1)))
    (hhor : read ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) P.erase := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hbelow
  have hpD : deadline < p :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) hp
  have hread : (Restated.Vocabulary.Execution.Setup.a M S deadline) ≤ read :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hpD.le).trans
      hreadLow
  have hconfP : M.confirmation_time S.E ((M.opening_slot S.hc p)) =
      (Restated.Vocabulary.Execution.Setup.a M S p) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E p).symm
  obtain ⟨hi1, -, -, -, -, hi6⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc p)
  have hΔ := S.E.Δ_pos
  have hshor : M.vote_time S.E ((M.opening_slot S.hc p)) + S.E.Δ ≤ rho.horizon := by
    have h1 := hreadLow.trans hhor
    rw [← hconfP] at h1
    linarith
  have hs : M.opening_slot S.hc deadline + 1 ≤ M.opening_slot S.hc p :=
    (p71% firstInterior_le_of_action_lt_confirmation₇₁w) facts S (by
      rw [hconfP]
      exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S hpD)
  have huVote : u ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc p))) := by
    refine hHs _ _ ?_ hu
    refine le_trans ?_ hreadLow
    rw [← hconfP]
    linarith
  obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ := (p86g% exists_headOutcome₈₆g) facts S
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) u)
    (M.vote_time S.E (M.opening_slot S.hc p))
  have hHP : H = P.erase := hheads u huVote cw hcw Tr hTr L hL L' hL' H hH
  rcases Restated.fgRoot_confirmationWitness_at_readOn facts S Hs Xb hf hHs hHsXb hmajority
      (hHsXb _ hu) read hhor with
    hgen | ⟨C, hC, hJ, b, tb, hb, hemit, hbt, hpair, hW⟩
  · rw [hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · by_cases hsmall : (M.derive_named S.E S.cfg C).h_j ≤ blocked
    · obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
        Restated.NamedHeightRegimeBaseRunOn.exists_regime_before_deadline facts hf hHs
          hHsXb hX hXXb hbelow hgst h hgstLo hloOpen hdeadline
      have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
      have hRT := Restated.NamedHeightRegimeRunOn.fgRoot_compatible_after_source_run_l86b
        facts hf hHs hHsXb hX hXXb hcom hbelow hreg
        (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone ha).trans
          hread) hhor hu hlo hA
      have hRTpre : Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG)
          T.erase := by
        by_cases hz : (M.derive_named S.E S.cfg C).h_j = 0
        · have hgenJ := facts.cs.justified_zero_is_genesis S.E S.cfg C hz
          rw [← hJ, hgenJ]
          exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
        · obtain ⟨J, hJC, hJerase, hJheight⟩ :=
            (facts.cs.justified_ancestor_height S.E S.cfg C).resolve_left hz
          have hCrun : Restated.RunBlockOn M S rho W Xb C :=
            Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hu) hC
          have hJrun : Restated.RunBlockOn M S rho W Xb J :=
            Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hJC
          obtain ⟨hTrun, hTheight⟩ :=
            Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb hreg
          rcases (show Block.Preceq
                (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG)
                T.erase ∨
              Block.Preceq T.erase
                (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) from
            compatible_cases hRT) with
            hRT' | hTR
          · exact hRT'
          · have hTJ : NamedBlock.Preceq T J :=
              Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTrun hJrun
                (by rw [hJerase, hJ]; exact hTR)
            have hmono := facts.cs.derive_height_mono S.E S.cfg hTJ
            rw [hTheight, hJheight] at hmono
            exact False.elim (Nat.not_succ_le_self blocked (hmono.trans hsmall))
      rw [← hHP]
      exact preceq_trans_Preceq hRTpre
        (Restated.NamedHeightRegimeRunOn.heads_from_firstInterior facts hf hHs hHsXb hX
          hXXb hcom hbelow hreg
          ((Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc ha) 1).trans hs)
          hshor hlo hA u huVote cw hcw Tr hTr L hL L' hL' H hH)
    · have hrowHeight : b.height_pair.erase.height? =
          some (M.derive_named S.E S.cfg C).h_j := by
        rw [hpair]
        rfl
      have hact : Restated.Vocabulary.Execution.Setup.a M S b.round < read := by
        rw [← (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath
          hemit).2]
        exact hbt
      have hbp : b.round ≤ p :=
        Nat.le_of_lt_succ
          ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).lt_iff_lt.mp
            (hact.trans_le hreadHigh))
      have hbT : b.val_index ∈ Hs tb := hHs _ _ hbt.le hb
      obtain ⟨nb, hnb⟩ : ∃ nb, nb ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
          b.round := by
        obtain ⟨nb, hnb, -⟩ := (p64b% exists_actionSG₆₄b) facts S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
          b.round
        exact ⟨nb, hnb⟩
      obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S nb
      rcases lt_or_eq_of_le hbp with hlt | hlast
      · let m := (M.derive_named S.E S.cfg C).h_j - (blocked + 1)
        have heq : blocked + m + 1 = (M.derive_named S.E S.cfg C).h_j := by
          calc
            _ = m + (blocked + 1) := by ac_rfl
            _ = (M.derive_named S.E S.cfg C).h_j :=
              Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
        have hrow : b.height_pair.erase.height? = some (blocked + m + 1) := by
          rw [hrowHeight]
          exact congrArg some heq.symm
        obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
          Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named facts hf hHs hHsXb
            hX hXXb hcom hbelow hgst h m hbT hemit hrow hgstLo hloOpen hA
        have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
        have hTR : T.erase =
            M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG :=
          (Option.some.inj
            (Restated.NamedHeightRegimeRunOn.witness_eq facts hf hHs hHsXb hX hXXb hcom
              hbelow hreg hbT hemit hrow hlo hA nb hnb _ (hW nb hnb o ho))).symm
        have hab : a.round ≤ b.round := hreg.minimal b tb hbT hemit hrow
        have hopen : M.opening_slot S.hc a.round + 1 ≤ M.opening_slot S.hc p :=
          (p71% firstInterior_le_of_action_lt_confirmation₇₁w) facts S (by
            rw [hconfP]
            exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S
              (lt_of_le_of_lt hab hlt))
        rw [← hTR, ← hHP]
        exact Restated.NamedHeightRegimeRunOn.heads_from_firstInterior facts hf hHs hHsXb hX
          hXXb hcom hbelow hreg hopen hshor hlo hA u huVote cw hcw Tr hTr L hL L' hL' H hH
      · have htb : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
          (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
        have hbP : b.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S p)) := by
          rw [htb, hlast] at hbT
          exact hbT
        obtain ⟨o1, ho1, ho1R⟩ := (p60% returns_map_elim₆₀) _ _ _ (hW nb hnb o ho)
        obtain ⟨Y1, rfl⟩ : ∃ Y1, o1 = some Y1 := by
          cases o1 with
          | none => simp at ho1R
          | some Y1 => exact ⟨Y1, rfl⟩
        have hY1 : Y1 = P.erase := hsource b.val_index hbP nb (by rw [← hlast]; exact hnb) Y1 ho1
        have hR : M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG =
            (nb.st.core.σ P.erase).T_h := by
          rw [← hY1]
          exact (Option.some.inj ho1R).symm
        obtain ⟨D, K, hfg, -, hsrc, -, -, -, -, hKD, -⟩ :=
          Restated.honestHeightRow_confirmationWitnessOn facts S Hs Xb hf (hHsXb _ hb) hemit
            hrowHeight nb hnb _ ho1
        have hDP : D.erase = P.erase := by
          rw [← hY1]
          exact (Option.some.inj hsrc).symm
        obtain ⟨o2, ho2, ho2K⟩ := (p60% returns_map_elim₆₀) _ _ _ hfg
        obtain ⟨Y2, rfl⟩ : ∃ Y2, o2 = some Y2 := by
          cases o2 with
          | none => simp at ho2K
          | some Y2 => exact ⟨Y2, rfl⟩
        have hY2 : Y2 = P.erase := hsource b.val_index hbP nb (by rw [← hlast]; exact hnb) Y2 ho2
        have hK : (nb.st.core.σ P.erase).T_h = (M.derive_named S.E S.cfg K).T_h := by
          rw [← hY2]
          exact Option.some.inj ho2K
        rw [hR, hK, ← hDP]
        exact preceq_trans_Preceq (facts.csAdded.derive_named_T_h_preceq S.E S.cfg K) hKD

/-- Under the premises of `fgRoot_preceq_previousHead_through_confirmation_after_GSTOn` along `W`,
    if `p` is at least two rounds after the deadline, every head a member of the set for
    `vote_time o_p` can vote at `o_p` on `W` is `P`, and every FG source `some Y` of a round-`p`
    action read on `W` of a member of the set for `S.a p` has `Y = P`, then for a read between
    `S.a p` and `S.a (p + 1)` within the horizon and `u` in the set for the read, the FG root of
    `u`'s store in the world of `W` strictly before the read is an ancestor of `P`. -/
theorem fgRoot_preceq_openingProposal_at_read_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {p : Round} (hp : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ p)
    {P : NamedBlock V}
    (hheads : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc p))), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc p))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).st
          (M.vote_time S.E (M.opening_slot S.hc p)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc p))) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        H = P.erase)
    (hsource : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S p)),
      ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S p)) w) p,
      ∀ Y : Block V,
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nw ⇢ some Y → Y = P.erase)
    {read : Time} (hreadLow : (Restated.Vocabulary.Execution.Setup.a M S p) ≤ read)
    (hreadHigh : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (p + 1)))
    (hhor : read ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) P.erase := by
  have hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ Xb := fun t _ => hHsXb t
  have hXXb : Xb ⊆ Xb := Finset.Subset.refl _
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)) :=
    hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right rGST 2))
  have hpD : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ p :=
    (Nat.le_add_right _ 2).trans hp
  have hreadD : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hpD).trans
      hreadLow
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
      S Hs Xb Xb hf hHs hHsXb hX hXXb hcom hbelow hrec hdelay hpost (hreadD.trans hhor)
      hlo hloOpen ht₀ hA
  exact Restated.NamedHeightRegimeBaseRunOn.fgRoot_preceq_openingProposal_at_read_l85b
    facts hf hHs hHsXb hX hXXb hcom hbelow
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
    hbase hfirst hp hheads hsource hreadLow hreadHigh hhor hu
    (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

/-- In a parent-closed store with `F ⪯ J`, a block `B` that is a descendant of the FG root and an
    ancestor of a member `C` of the filtered tree is in the filtered tree. -/
theorem mem_filtered_of_preceq_mem_filtered_l85b (facts : Record.Facts M) {st : M.S} (hpc : Restated.Vocabulary.Internal.ParentClosed M st)
    (hFJ : Block.Preceq st.F st.J) {B C : Block V}
    (hC : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG)
    (hBC : Block.Preceq B C)
    (hroot : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) B) :
    B ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
  obtain ⟨W, hWT, hCW, hband⟩ := (facts.fc.parts_of_mem_get_filtered_block_tree hC).1.2
  rw [facts.sto.toHealing_T] at hWT
  rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ] at hband
  exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq facts hpc hFJ hroot hWT
    hband (Proofs.ModelProperties.Preceq_self B) (Proofs.ModelProperties.Preceq_trans hBC hCW)

/-- Under the premises of `prevOpeningProposal_preceq_proposedParent_afterDeadlineOn` along `W`, the
    previous opening proposal `P'` is in the filtered tree of the store, in the world of `W`
    strictly before `S.a m`, of every member of the set for `S.a m`. -/
theorem prevOpeningProposal_activeAtAction_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hm3 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ m)
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (m - 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (m - 1)))))
    {P' : NamedBlock V}
    (cp' : M.Cache)
    (hcp' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (m - 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).cache ⇢ cp')
    (hP' : M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (m - 1))))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).record cp').st ⇢ some P') :
    ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)),
      P'.erase ∈ M.get_filtered_block_tree
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) w).st.core).toFG := by
  classical
  have hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
        rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
        M.awake_for_grade2 S u (W j u) k :=
    fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu)
  obtain ⟨-, -, -, -, -, -, hqEq, -, -⟩ := facts.gr.openingSlots_l86f S hm
  have hmPrev : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m - 1 :=
    Nat.le_sub_of_add_le hm3
  have hmlt : m - 1 ≤ m := Nat.sub_le m 1
  have hhorPrev : (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) ≤ rho.horizon :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hmlt).trans hhor
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc m)) =
      (Restated.Vocabulary.Execution.Setup.a M S m) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E m).symm
  have hread := Restated.openingProposal_confirmationRead_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll
  have hadoptPrev := Restated.openingAdoption_afterDeadlineOn facts S Hs Xb hf hHs hHsXb
    hcom hbelow hrec hdelay hpost hmPrev hhorPrev hopeningPrev cp' hcp' hP' hloPost hloOpen ht₀
    hAll
  have hsourcePrev := Restated.fgSource_eq_openingProposal_of_some_afterDeadlineOn facts S Hs Xb
    hf hHs hHsXb hcom hbelow hrec hdelay hpost hmPrev hhorPrev hopeningPrev cp' hcp' hP'
    hloPost hloOpen ht₀ hAll
  have hP'parent := Restated.prevOpeningProposal_preceq_proposedParent_afterDeadlineOn facts S Hs
    Xb hf hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen
    ht₀ hAll hm3 hopeningPrev cp' hcp' hP'
  set start := (M.opening_slot S.hc m) with hstartdef
  set wp := W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start) with hwpdef
  set pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) wp.record cp
    with hpndef
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho start :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hPn : M.proposal_with (M.gradeContract pn.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer start)) pn.st ⇢ some P := by
    rw [hpncache]
    exact hP
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    (S.node (S.E.proposer start)) (M.toHealing pn.st.core)
  have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn.cache) S.E S.hc
      (S.node (S.E.proposer start)) (M.toHealing pn.st.core) ⇢ I := by
    rw [hpncache]
    exact hI
  obtain ⟨-, hIP⟩ := (p58% parent_preceq_of_proposal₅₈s) facts S rho start pn hpread hPn I hI'
  have hP'P : Block.Preceq P'.erase P.erase := preceq_trans_Preceq (hP'parent I hI) hIP
  intro w hw
  have hroot : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) w).st.core).toFG)
      P'.erase :=
    Restated.fgRoot_preceq_openingProposal_at_read_afterDeadlineOn facts S Hs Xb hf hHs
      hHsXb hcom hbelow hrec hdelay hpost hmPrev hadoptPrev.1 hsourcePrev
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hmlt)
      (by rw [hqEq]) hhor hw hloPost hloOpen ht₀ hA
  have hcand : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) w).st.core).toFG := by
    obtain ⟨cc, hcc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E start)) w).st.core.toHealing
      (M.confirmation_time S.E start)
      (W (strictEventIndex rho (M.confirmation_time S.E start)) w).cache
    have h := (hread w hw cc hcc).2.2
    change P.erase ∈ M.get_filtered_block_tree (M.toHealing _).toFG at h
    rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h; rw [(p60% setClock_filtered₆₀) facts S, hconfA] at h
    exact h
  have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S m)
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
    (Restated.Vocabulary.Execution.Setup.a M S m) w _ hmemA
  have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    facts S rho (Restated.Vocabulary.Execution.Setup.a M S m) w _ hmemA
  exact Restated.mem_filtered_of_preceq_mem_filtered_l85b facts hpc hFJ hcand hP'P hroot

/-- Under the premises of `prevOpeningProposal_preceq_proposedParent_afterDeadlineOn` along `W`, the
    previous opening proposal `P'` is in the filtered tree of the node state, in the world of `W`
    strictly before the round-`m` grade-2 domain instant, of every member of the set for that
    instant. -/
theorem prevOpeningProposal_activeAtDomain_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hm3 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ m)
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (m - 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (m - 1)))))
    {P' : NamedBlock V}
    (cp' : M.Cache)
    (hcp' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (m - 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).cache ⇢ cp')
    (hP' : M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (m - 1))))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).record cp').st ⇢ some P') :
    ∀ w ∈ Hs (M.domain S.E S.hc m .g2),
      P'.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc m .g2)) w) := by
  classical
  have hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
        rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
        M.awake_for_grade2 S u (W j u) k :=
    fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu)
  obtain ⟨hdeadlineSlot, -, -, -, hdSucc, -, hqEq, hcDeadline, -⟩ :=
    facts.gr.openingSlots_l86f S hm
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc m)) =
      (Restated.Vocabulary.Execution.Setup.a M S m) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E m).symm
  have htdEq : M.domain S.E S.hc m .g2 =
      M.proposal_time S.E (M.opening_slot S.hc m) - S.E.Δ := by
    have h := facts.gr.gammaNeg1_eq_domain_g2_succ S (m - 1)
    rw [hqEq, facts.sch.Γ_0_eq_proposal_time S.hc S.E m] at h
    exact h.symm
  set D := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDdef
  set start := (M.opening_slot S.hc m) with hstartdef
  set d := start - 1 with hddef
  set td := M.domain S.E S.hc m .g2 with htddef
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.succ_pos 1) ((Nat.le_add_left 2 _).trans hm)
  have hmPrev : D + 2 ≤ m - 1 := Nat.le_sub_of_add_le hm3
  have hmlt : m - 1 ≤ m := Nat.sub_le m 1
  have hhorPrev : (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) ≤ rho.horizon :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hmlt).trans hhor
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6⟩ := facts.sch.slot_instants_l55 S.E d
  obtain ⟨hj1, -, -, -, -, hj6⟩ := facts.sch.slot_instants_l55 S.E start
  rw [hdSucc] at hi4 hi5
  have hΔ := S.E.Δ_pos
  have htdA : td ≤ (Restated.Vocabulary.Execution.Setup.a M S m) := by
    rw [← hconfA]; linarith
  have htdHor : td ≤ rho.horizon := htdA.trans hhor
  have hvoteTd : M.vote_time S.E d ≤ td := by linarith
  have htdConf : td ≤ M.confirmation_time S.E d := by linarith
  have hshor : M.vote_time S.E d + S.E.Δ ≤ rho.horizon := by
    have h1 := hhor
    rw [← hconfA] at h1
    linarith
  have hprevTd : (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) ≤ td :=
    Restated.Vocabulary.Proofs.HealingSurface.action_pred_le_domain_g2 facts S hmpos
  have hDtd : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ td :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hcDeadline.trans (Nat.sub_le (m - 1) 1))).trans hprevTd
  have hvoteHor : M.vote_time S.E start ≤ rho.horizon := by
    have h1 := hhor
    rw [← hconfA] at h1
    linarith
  have hex := fun w : V => (p86g% exists_headOutcome₈₆g) facts S
    (W (strictEventIndex rho (M.vote_time S.E d)) w) (M.vote_time S.E d)
  choose head hheadAll using hex
  obtain ⟨E, hErun, hEheads, hEmax, hupper, -, -, -⟩ :=
    Restated.openingPivot_afterDeadlineOn facts S Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay
      hpost hm hvoteHor hopening cp hcp hP hloPost hloOpen ht₀ hAll head (fun w _ => hheadAll w)
  have hsg := Restated.sgBlock_eq_openingProposal_afterDeadlineOn facts S Hs Xb hf hHs hHsXb
    hcom hbelow hrec hdelay hpost hmPrev hhorPrev hopeningPrev cp' hcp' hP' hloPost hloOpen ht₀ hAll
  have hprop : S.E.proposer start ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (m - 1))) := by
    refine hHs _ _
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hmlt) ?_
    rw [← hconfA]
    exact hopening
  have hP'E : Block.Preceq P'.erase E.erase := by
    obtain ⟨nv, hnv, g, hg, B, hB⟩ := (p64b% exists_actionSG₆₄b) facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (m - 1)))
        (S.E.proposer start)) (m - 1)
    have hBP := hsg _ hprop nv hnv g hg B hB
    rw [← hBP]
    exact hupper _ hprop nv hnv g hg B hB
  have hadoptPrev := Restated.openingAdoption_afterDeadlineOn facts S Hs Xb hf hHs hHsXb
    hcom hbelow hrec hdelay hpost hmPrev hhorPrev hopeningPrev cp' hcp' hP' hloPost hloOpen ht₀
    hAll
  have hsourcePrev := Restated.fgSource_eq_openingProposal_of_some_afterDeadlineOn facts S Hs Xb
    hf hHs hHsXb hcom hbelow hrec hdelay hpost hmPrev hhorPrev hopeningPrev cp' hcp' hP'
    hloPost hloOpen ht₀ hAll
  intro w hw
  have hwVote : w ∈ Hs (M.vote_time S.E d) := hHs _ _ hvoteTd hw
  have hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho td) w).st.core).toFG) P'.erase :=
    Restated.fgRoot_preceq_openingProposal_at_read_afterDeadlineOn facts S Hs Xb hf hHs
      hHsXb hcom hbelow hrec hdelay hpost hmPrev hadoptPrev.1 hsourcePrev hprevTd
      (by rw [hqEq]; exact htdA) htdHor hw hloPost hloOpen ht₀ hA
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    (p86f% exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f) facts S Hs Xb
      hf hHs hHsXb hcom hbelow hrec hdelay hpost hDtd htdHor hdeadlineSlot htdConf hshor hw
      hloPost hloOpen ht₀ hA
  have hTE : Block.Preceq T.erase E.erase := by
    apply hEmax
    intro w' hw'
    obtain ⟨c, hc, T', hT', L, hL, L', hL', hH⟩ := hheadAll w'
    exact hTheads w' hw' c hc T' hT' L hL L' hL' (head w') hH
  have hTENamed : NamedBlock.Preceq T E :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTrun hErun hTE
  have hheadVote : head w ∈ (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.T := by
    obtain ⟨c, hc, T', hT', L, hL, L', hL', hH⟩ := hheadAll w
    have h := Restated.voteDutyHead_mem_voteDutyStoreOn facts S Hs Xb hf w d c hc T' hT' L hL L'
      hL' (head w) hH
    rw [(p60% voteStore_eq₆₀s) facts, facts.hd.Sts_setClock_core_T] at h
    exact h
  have hheadTd : head w ∈ (W (strictEventIndex rho td) w).st.core.T :=
    Restated.seedStore_T_subsetOn facts S Hs Xb hf w hvoteTd hheadVote
  have hmemTd := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath td
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
    td w _ hmemTd
  have hEmem : E.erase ∈ (W (strictEventIndex rho td) w).st.core.T := by
    have hpc' := hpc
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc'
    rw [facts.sto.toHealing_gs_T] at hpc'
    exact Proofs.Records.mem_of_preceq hpc'.2 E.erase (head w) hheadTd
      (preceq_eq_true_iff_Preceq.2 (hEheads w hwVote))
  have hEbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts S Hs Xb hf (hHsXb _ hw)
    hEmem hErun
  have hEview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    td w _ hmemTd E hEbody
  have hEband : (W (strictEventIndex rho td) w).st.core.h_max - 1 ≤
      ((W (strictEventIndex rho td) w).st.core.σ E.erase).h := by
    rw [hEview]
    exact hTband.trans (facts.cs.derive_height_mono S.E S.cfg hTENamed)
  have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    facts S rho td w _ hmemTd
  exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq
    facts hpc hFJ hroot hEmem hEband (Proofs.ModelProperties.Preceq_self P'.erase) hP'E

/-- Under the premises of `prevOpeningProposal_preceq_proposedParent_afterDeadlineOn` along `W`,
    every member of the set for the round-`m` grade-2 domain instant has `P'` in the filtered tree
    of its node state in the world of `W` strictly before that instant, and every outcome of its
    round-`m` grade-2 store grade for `P'` there is `true`. -/
theorem namedGradeFormsAt_prevOpeningProposal_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hm3 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ m)
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (m - 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (m - 1)))))
    {P' : NamedBlock V}
    (cp' : M.Cache)
    (hcp' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (m - 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).cache ⇢ cp')
    (hP' : M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (m - 1))))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).record cp').st ⇢ some P') :
    Restated.NamedGradeFormsAtOn M S rho Hs m P'.erase
      (W (strictEventIndex rho (M.domain S.E S.hc m Phase.g2))) := by
  obtain ⟨-, -, -, -, -, -, hqEq, hcDeadline, -⟩ := facts.gr.openingSlots_l86f S hm
  have hmPrev : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m - 1 :=
    Nat.le_sub_of_add_le hm3
  have hmlt : m - 1 ≤ m := Nat.sub_le m 1
  have hhorPrev : (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) ≤ rho.horizon :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hmlt).trans hhor
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc m)) =
      (Restated.Vocabulary.Execution.Setup.a M S m) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E m).symm
  have hsg := Restated.sgBlock_eq_openingProposal_afterDeadlineOn facts S Hs Xb hf hHs hHsXb
    hcom hbelow hrec hdelay hpost hmPrev hhorPrev hopeningPrev cp' hcp' hP' hloPost hloOpen ht₀ hAll
  have hcover : Restated.ActionCarriersCoverOn M S rho Hs (m - 1) P'.erase
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (m - 1)))) := by
    intro v hv n hn g hg A hA'
    rw [hsg v hv n hn g hg A hA']
    exact Proofs.ModelProperties.Preceq_self P'.erase
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hrGSTm : rGST ≤ m - 1 := hGSTdead.trans (hcDeadline.trans (Nat.sub_le (m - 1) 1))
  have hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) :=
    hpost.trans
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hrGSTm)
  have hloPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) :=
    hloPost.trans
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hrGSTm)
  have hkPrev : lo ≤ M.early S.E S.hc (m - 1) .g2 - S.E.Δ := by
    have hdead : rGST + 1 ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
      unfold fgSafetyProgressDeadline
      exact Nat.le_add_right _ _
    exact Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (Nat.lt_of_lt_of_le (Nat.lt_of_succ_le hdead) ((Nat.le_add_right _ 2).trans hmPrev))
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (m - 1 + 1) ≤
      rho.horizon := by
    rw [hqEq]
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E m]
    obtain ⟨-, -, -, -, -, hj6⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc m)
    have hΔ := S.E.Δ_pos
    have h1 := hhor
    rw [← hconfA] at h1
    linarith
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (m - 1 + 1)))).Nonempty := by
    rw [hqEq, ← hconfA]
    exact ⟨_, hopening⟩
  have hactive := Restated.prevOpeningProposal_activeAtAction_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀
    hAll hm3 hopeningPrev cp' hcp' hP'
  have hactiveDomain := Restated.prevOpeningProposal_activeAtDomain_afterDeadlineOn facts S Hs Xb
    hf hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen
    ht₀ hAll hm3 hopeningPrev cp' hcp' hP'
  have hforms := Restated.namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn facts S
    Hs Xb hf hHs hHsXb (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hcover hpostPrev
    hcut (by rw [hqEq]; exact hactive) (by rw [hqEq]; exact hactiveDomain)
    (fun u hu => hAll (m - 1) u hkPrev (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu))
    hloPrev hne
  rw [hqEq] at hforms
  exact hforms

/-- Under the premises of `prevOpeningProposal_preceq_proposedParent_afterDeadlineOn` along `W`,
    every outcome of the FG source at every node state of the round-`m` action read on `W` of a
    member of the set for `S.a m` is `some P`. -/
theorem fgSource_eq_openingProposal_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hm3 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ m)
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (m - 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (m - 1)))))
    {P' : NamedBlock V}
    (cp' : M.Cache)
    (hcp' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (m - 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (S.E.proposer (M.opening_slot S.hc (m - 1)))).cache ⇢ cp')
    (hP' : M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (m - 1))))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (m - 1))))
          (S.E.proposer (M.opening_slot S.hc (m - 1)))).record cp').st ⇢ some P') :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) u) m,
      ∀ o : Option (Block V),
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nu ⇢ o → o = some P.erase := by
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.succ_pos 1) ((Nat.le_add_left 2 _).trans hm)
  have hloc := Restated.lo_le_opening_afterDeadline_l85b facts S hm hloOpen
  have hforms := Restated.namedGradeFormsAt_prevOpeningProposal_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀
    hAll hm3 hopeningPrev cp' hcp' hP'
  have hactive := Restated.prevOpeningProposal_activeAtAction_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀
    hAll hm3 hopeningPrev cp' hcp' hP'
  have hsome := Restated.fgSource_eq_openingProposal_of_some_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀
    hAll
  intro u hu nu hnu o ho
  have hdom0 : M.domain S.E S.hc m .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S m) :=
    facts.gr.domain_le_a S m .g0
  have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S m)
  have hnuAt : nu ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho u m :=
    ⟨_, hmemA, hnu⟩
  have hactiveN : P'.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nu :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S _ hmemA
      (hactive u hu) nu hnu
  obtain ⟨Gr, hGr⟩ := facts.gr.read_nonempty (M.gradeContract nu.cache) S.E S.hc
    (M.toHealing nu.st.core) m
  have hq0 : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nu m ⇢ Gr.Q2 :=
    returns_map_intro₈₅b (fun g : GradeRead V => g.Q2) _ Gr hGr
  obtain ⟨Q, hQ, -⟩ := Restated.namedGradeFormsAt_preceq_actionQ2On facts S Hs Xb hf hHs
    hmpos hhor hforms (hHs _ _ hdom0 hu) nu hnu hactiveN hloc Gr.Q2 hq0
  rw [hQ] at hq0
  have hround : M.round_of S.hc (M.toHealing nu.st.core).s = m := by
    show M.round_of S.hc (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore.s = m
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho u m nu hnuAt
  have ho' : (do
      let g ← M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
        (M.round_of S.hc (M.toHealing nu.st.core).s)
      M.fg_source_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
        (M.round_of S.hc (M.toHealing nu.st.core).s) g) ⇢ o := ho
  rw [hround] at ho'
  obtain ⟨X, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.exists_actionFGSource_of_actionQ2
    facts S rho u m _ hmemA nu hnu hq0 o ho'
  exact congrArg some (hsome u hu nu hnu X ho)

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- In the run `R` of the execution `x` up to step `n`, along its path `W`, for a round `c` with
    `deadlineRoundW S tGAT gap + 2 ≤ c` within the horizon whose opening proposer is not held at the
    opening slot's confirmation instant and proposed `P` on `W`: every block the SG vote selector
    can return at a round-`c` action read on `W` of a validator not held at `S.a c`, with any
    grade-2 candidate, is `P`. -/
theorem sgBlock_eq_openingProposal_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) A2 ⇢ G →
        G = P.erase := by
  intro R W wp cp hcp pn hP
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.sgBlock_eq_openingProposal_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)

/-- In the run `R` of the execution `x` up to step `n`, along its path `W`, for a round `c` with
    `deadlineRoundW S tGAT gap + 2 ≤ c` within the horizon whose opening proposer is not held at the
    opening slot's confirmation instant and proposed `P` on `W`: if the FG source at a round-`c`
    action read on `W` of a validator not held at `S.a c` can return `some X`, then `X` is `P`. -/
theorem fgSource_eq_openingProposal_of_some_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ X : Block V,
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nu ⇢ some X →
        X = P.erase := by
  intro R W wp cp hcp pn hP
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.fgSource_eq_openingProposal_of_some_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)

/-- In the run `R` of the execution `x` up to step `n`, along its path `W`, for a round `c` with
    `deadlineRoundW S tGAT gap + 3 ≤ c` within the horizon whose opening proposers of `c` and
    `c − 1` are not held at their opening slots' confirmation instants and proposed `P` and `P'` on
    `W`: `P'` is an ancestor of the parent of every proposal input of the round-`c` opening
    proposer's read on `W`. -/
theorem prevOpeningProposal_preceq_proposedParent_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c)))
        (M.toHealing pn.st.core) ⇢ I →
      Block.Preceq P'.erase I.parent := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.prevOpeningProposal_preceq_proposedParent_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
        exact (Nat.le_succ _).trans hc3)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc3)
    hopeningPrev cp' hcp' hP'

/-- In the run `R` of the execution `x` up to step `n`, along its path `W`, for a round `c` with
    `deadlineRoundW S tGAT gap + 3 ≤ c` within the horizon whose opening proposers of `c` and
    `c − 1` are not held at their opening slots' confirmation instants and proposed `P` and `P'` on
    `W`: every validator not held at the round-`c` grade-2 domain instant has `P'` in the filtered
    tree of its node state in the world of `W` strictly before that instant, and every outcome of
    its round-`c` grade-2 store grade for `P'` there is `true`. -/
theorem namedGradeFormsAt_prevOpeningProposal_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    Restated.NamedGradeFormsAtOn M (Setup.alwaysAwake S) R (notHeldAt Sched) c P'.erase
      (W (strictEventIndex R (M.domain S.E S.hc c Phase.g2))) := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.namedGradeFormsAt_prevOpeningProposal_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
        exact (Nat.le_succ _).trans hc3)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc3)
    hopeningPrev cp' hcp' hP'

/-- In the run `R` of the execution `x` up to step `n`, along its path `W`, for a round `c` with
    `deadlineRoundW S tGAT gap + 3 ≤ c` within the horizon whose opening proposers of `c` and
    `c − 1` are not held at their opening slots' confirmation instants and proposed `P` and `P'` on
    `W`: every outcome of the FG source at every round-`c` action read on `W` of a validator not
    held at `S.a c` is `some P`. -/
theorem fgSource_eq_openingProposal_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ o : Option (Block V),
        Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nu ⇢ o →
        o = some P.erase := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.fgSource_eq_openingProposal_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
        exact (Nat.le_succ _).trans hc3)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc3)
    hopeningPrev cp' hcp' hP'

end

end DecoupledConsensusModel.Sts.Restated
