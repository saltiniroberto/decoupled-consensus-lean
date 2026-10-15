import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_86b
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingContinuation
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
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
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86f

/-!
# The pivot of an opening after the progress deadline

Theorems over a model `M : Record.Model V`, read along one path `W` of the run: the proposal and the
pivot path are candidates at an interior vote read, the pivot is an ancestor of the proposal-free
walk's head, and after the progress deadline an opening has a pivot block that every previous head
descends from and that is an ancestor of the proposed parent.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_64b` by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_60` by name. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_58` by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_71` by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_86c` by name. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, is the core store of
    `n`'s store with its clock set to `t`. -/
private theorem tickStore_eq₈₆f (facts : Record.Facts M) (S : Setup V) (n : M.N) (t : Time) :
    Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t =
      (M.ns_setClock S.E n.st t).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

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

/-- Along the path `W`, if `0 < s`, `P1` is a proposal of slot `s` with parent `Parent`, `v`
    admitted `P1` before `vote_time s`, `P1`'s stored height in `v`'s vote-duty store is at least
    `h_max − 1`, and the FG root there is an ancestor of a block `pivot ≠ P1` that is an ancestor of
    `Parent`, then at every vote-duty read of `v`, for every outcome `A0` of the anchor and `T` of
    the filtered block tree: `P1` is in `T`, `pivot` is in `T` without `P1`, and so is every block
    strictly descending from `A0` that is an ancestor of `pivot`. -/
theorem interiorProposal_candidateAndPivotPathOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hs : 0 < s) {v : V}
    (hv : v ∈ Hs (M.view_freeze S.E (s - 1)))
    (hgat : lo ≤ M.view_freeze S.E (s - 1))
    {P1 Parent : NamedBlock V} {pivot : Block V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ cp)
    (hP1 : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P1)
    (hparent : NamedBlock.parent? P1 = some Parent)
    (hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v P1.erase (M.vote_time S.E s))
    (hband : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).h_max - 1 ≤
      ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).σ P1.erase).h)
    (hrootPivot : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG) pivot)
    (hpivotParent : Block.Preceq pivot Parent.erase)
    (hpivotNe : pivot ≠ P1.erase) :
    ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv →
      let m := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv
      ∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ A0 →
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
        P1.erase ∈ T ∧
        pivot ∈ T.erase P1.erase ∧
        ∀ D : Block V, Block.Preceq A0 D → D ≠ A0 → Block.Preceq D pivot →
          D ∈ T.erase P1.erase := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, (Nat.sub_add_cancel hs).symm⟩
  rw [Nat.add_sub_cancel] at hv hgat
  intro cv hcv m A0 hA0 T hT
  have hnst : m.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (k + 1))) v).st (M.vote_time S.E (k + 1))) _ := facts.nd.mkNode_st _ _ _
  have hms : m.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  have hpread : M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (k + 1))) (S.E.proposer (k + 1))).st
      (M.proposal_time S.E (k + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (k + 1))) (S.E.proposer (k + 1))).record cp ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (k + 1) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hP1slot : P1.erase.slot = k + 1 := by
    rw [Proofs.NamedWire.erase_slot]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho (k + 1) (some P1)
      ⟨_, hpread, by rw [facts.nd.mkNode_cache]; exact hP1⟩ rfl
  have hP1T : P1.erase ∈ (W (strictEventIndex rho (M.vote_time S.E (k + 1))) v).st.core.T :=
    (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit (le_refl _)).1
  have hvoteT : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (k + 1))) v).st.core (k + 1)).T =
      (W (strictEventIndex rho (M.vote_time S.E (k + 1))) v).st.core.T :=
    (p58% tickStore_T₅₈s) facts _ _
  obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (k + 1))) v).st.core (k + 1))).toFG.toSG.toGoldfishStore
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (k + 1))) v).st.core (k + 1))).s
  have hP1Q : P1.erase ∈ Q := by
    refine facts.fc.mem_voter_processed_block_tree_of_slot S.E _ _ ?_ ?_ Q hQ
    · rw [facts.sto.toHealing_gs_T, hvoteT]
      exact hP1T
    · rw [(p60% voteStore_hs_s₆₀s) facts]
      exact hP1slot
  have hparentPre : Block.Preceq Parent.erase P1.erase := by
    cases P1 with
    | genesis => cases hparent
    | node p sl rt vs sp rows proposer =>
        simp only [NamedBlock.parent?] at hparent
        have hp : p = Parent := Option.some.inj hparent
        subst Parent
        have h := (preceq_eq_true_iff_Preceq.1
          (preceq_parent (NamedBlock.node p sl rt vs sp rows proposer).erase))
        rwa [Proofs.NamedWire.erase_parent, namedBlock_parent_node] at h
  have hpivotP1 : Block.Preceq pivot P1.erase := preceq_trans_Preceq hpivotParent hparentPre
  have hbandm : m.st.core.h_max - 1 ≤ (m.st.core.σ P1.erase).h := by
    rw [hms]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [← (p60% voteStore_eq₆₀s) facts]
    exact hband
  have hrootm : Block.Preceq (M.get_fg_root (M.toHealing m.st.core).toFG) pivot := by
    rw [hms]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [← (p60% voteStore_eq₆₀s) facts]
    exact hrootPivot
  have hrootP1 : Block.Preceq (M.get_fg_root (M.toHealing m.st.core).toFG) P1.erase :=
    preceq_trans_Preceq hrootm hpivotP1
  have hP := Restated.namedCandidatePath_of_processedBandDescendantOn facts S Hs Xb hf hv
    (Proofs.ModelProperties.Preceq_self P1.erase) Q hQ hP1Q cv hcv hbandm hrootP1 hgat T hT
  have hPiv := Restated.namedCandidatePath_of_processedBandDescendantOn facts S Hs Xb hf hv
    hpivotP1 Q hQ hP1Q cv hcv hbandm hrootm hgat T hT
  refine ⟨hP.1, Finset.mem_erase.mpr ⟨hpivotNe, hPiv.1⟩, ?_⟩
  intro D hAD hDne hDP
  have hDT : D ∈ T := by
    by_cases hEq : D = pivot
    · rw [hEq]
      exact hPiv.1
    · exact hPiv.2 A0 hA0 D hAD hDne hDP hEq
  exact Finset.mem_erase.mpr
    ⟨fun h => hpivotNe (Proofs.ModelProperties.Preceq_antisymm hpivotP1 (by rw [← h]; exact hDP)),
      hDT⟩

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

/-- Along the path `W`, if every committee member of slot `d` in the set votes a run block
    descending from `A`, an anchor `A0` of `v`'s vote-duty read at `d + 1` is an ancestor of `A`,
    `A` is a body of that read with height at least its `h_max − 1`, and `A` is an ancestor of the
    proposed parent of slot `d + 1`, then `A` is an ancestor of every head the walk from `A0` can
    return on the read's filtered tree without the proposal `B`. -/
theorem pivot_preceq_proposalFreeHead_bandOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {d : Slot} (hd : 0 < d)
    (hpost : lo ≤ M.vote_time S.E d)
    (hhor : M.support_cutoff S.E d ≤ rho.horizon)
    {v : V} (hv : v ∈ Hs (M.vote_time S.E (d + 1))) {A B : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).st.core.toHealing
      (M.proposal_time S.E (d + 1))
      (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).cache ⇢ cp)
    (hB : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (d + 1)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).st
        (M.proposal_time S.E (d + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).record
        cp).st ⇢ some B)
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb d (fun X => Block.Preceq A.erase X))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st.core.toHealing
      (M.vote_time S.E (d + 1))
      (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).cache ⇢ cv)
    {A0 : Block V}
    (hA0 :
      let m := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st
          (M.vote_time S.E (d + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).record cv
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ A0)
    (htargetAnchor : Block.Preceq A0 A.erase)
    (htargetBody : A ∈ (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st
          (M.vote_time S.E (d + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).record cv).st.bodies)
    (htargetBand : (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st
          (M.vote_time S.E (d + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).record cv).st.core.h_max - 1 ≤
      (M.derive_named S.E S.cfg A).h)
    {I : Protocol.ProposalInput V}
    (hI : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
      (S.node (S.E.proposer (d + 1)))
      (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).st
        (M.proposal_time S.E (d + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).record
        cp).st.core) ⇢ I)
    (hpivotParent : Block.Preceq A.erase I.parent) :
    let m := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st
        (M.vote_time S.E (d + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).record cv
    ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T₀ →
    ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
    ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
    ∀ sc : Block V → ℕ,
      (∀ X : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) X ⇢ sc X) →
    ∀ el : Block V → Bool,
      (∀ X : Block V, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) X ⇢ el X) →
    ∀ G : Block V, M.ghost A0 (T₀.erase B.erase) sc el ⇢ G → Block.Preceq A.erase G := by
  intro m T₀ hT₀ vv hvv vsv hvsv sc hsc el hel G hG
  have hnst : m.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st (M.vote_time S.E (d + 1))) _ := facts.nd.mkNode_st _ _ _
  have hslot : m.st.core.s = d + 1 := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hcutVote : M.support_cutoff S.E d ≤ M.vote_time S.E (d + 1) :=
    facts.sch.support_cutoff_le_vote_time_succ S.E d
  have hvSC : v ∈ Hs (M.support_cutoff S.E d) := hHs _ _ hcutVote hv
  have hvFreeze : v ∈ Hs (M.view_freeze S.E d) :=
    hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E d).le hv
  have hgatFreeze : lo ≤ M.view_freeze S.E d := by
    obtain ⟨h1, -, h3, -⟩ := facts.sch.slot_instants_l55 S.E d
    linarith [S.E.Δ_pos]
  have hrootA0 : Block.Preceq (M.get_fg_root (M.toHealing m.st.core).toFG) A0 :=
    Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S m _ A0 hA0
  have hroot : Block.Preceq (M.get_fg_root (M.toHealing m.st.core).toFG) A.erase :=
    preceq_trans_Preceq hrootA0 htargetAnchor
  have havailable := Restated.honestHeadsAvailableBefore_of_namedPostHealingConeOn facts
    S Hs Xb hf hHs hHsXb hvSC hpost hhor (by have h := hroot; rw [hnst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); exact h) hcone
  have hresolve := Restated.headsResolveIn_storeBeforeTime_of_availableBefore_atOn facts
    S Hs Xb hf (hHsXb _ hvSC) d hcutVote havailable
  have hGammaConf : M.vote_time S.E (d + 1) ≤ M.confirmation_time S.E d := by
    have h := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E d
    linarith [S.E.Δ_pos]
  have hTgs : (M.toHealing m.st.core).toFG.toSG.toGoldfishStore.T =
      (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st.core.T := by
    rw [facts.sto.toHealing_gs_T, hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hbase := Restated.canonicalSuffixConeSupportVoterViewOn facts
    S Hs Xb hf hHs hHsXb hcom hd hpost hhor hcone hvSC hcutVote hGammaConf
    (gst := (M.toHealing m.st.core).toFG.toSG.toGoldfishStore)
    (by
      funext k
      rw [facts.sto.toHealing_gs_gf_votes, hnst, facts.nd.store_with_cache_core_gf_votes, facts.hd.setClock_core_gf_votes])
    (by
      rw [facts.sto.toHealing_gs_timestamp_vote, hnst, facts.nd.store_with_cache_core_timestamp_vote, facts.hd.setClock_core_timestamp_vote])
    hTgs
    (by
      rw [hTgs, facts.sto.toHealing_gs_timestamp_block, hnst, facts.nd.store_with_cache_core_timestamp_block,
        facts.hd.setClock_core_timestamp_block]
      exact hresolve)
  have hconeV : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E m.st.core.T vv vsv vv
      (m.st.core.s - 1) (Hs (M.confirmation_time S.E d)) (fun X => Block.Preceq A.erase X) := by
    have h := hbase vv (by rw [← hslot]; exact hvv) vsv (by rw [← hslot]; exact hvsv)
    rw [facts.sto.toHealing_gs_T] at h
    rw [hslot, Nat.add_sub_cancel]
    exact h
  have hvalid : Protocol.VoteSetValid S.E (m.st.core.s - 1) vv := by
    have h := Restated.fixedRoot_preparedVoteViewValidOn facts S Hs Xb hf v (d + 1) vv
      (by have h := hvv; rw [hnst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); exact h)
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact h
  have hmaj := (p60% supporterMajority_of_cone₆₀s) facts S.E hconeV hvalid
  have hpos : 0 < ((S.E.committee d) ∩ Hs (M.confirmation_time S.E d)).card := by
    have hcommittee := hcom d
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxConf := (Finset.mem_inter.mp hx).2
  have hxCommittee := (Finset.mem_inter.mp hx).1
  have hxVote : x ∈ Hs (M.vote_time S.E d) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E d) hxConf
  obtain ⟨H, hAH, hHrun, hemit⟩ := hcone x hxVote hxCommittee
  have hHhead : Restated.HonestHeadOn M S rho W Hs Xb d H.erase :=
    ⟨x, hxConf, hxCommittee, ⟨H, rfl, hHrun⟩, hemit⟩
  have hAproc := Restated.voterProcessed_of_availableBefore_of_honestHeadOn facts S Hs Xb hf
    havailable hHhead hAH cv hcv
  have hms : m.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st.core (d + 1))).toFG.toSG.toGoldfishStore
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (d + 1))) v).st.core (d + 1))).s
  have hAQ : A.erase ∈ Q := by
    refine hAproc Q ?_
    have h := hQ
    have hs : ∀ x : M.S, (M.toHealing x).s = x.s := fun x => facts.sto.toHealing_gs_s x
    rw [(p60% voteStore_eq₆₀s) facts] at h
    rw [hms]
    simp only [hs, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_processed_block_tree,
      facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time] at h ⊢
    exact h
  have hview : m.st.core.σ A.erase = M.derive_named S.E S.cfg A := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_σ]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho _ v _
      ((p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath (M.vote_time S.E (d + 1))) A
      (by
        have h := htargetBody
        rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies, facts.hd.Sts_setClock_bodies] at h
        exact h)
  have hband : m.st.core.h_max - 1 ≤ (m.st.core.σ A.erase).h := by
    rw [hview]
    exact htargetBand
  have hcand := Restated.namedCandidatePath_of_processedBandDescendantOn facts S Hs Xb hf
    hvFreeze (Proofs.ModelProperties.Preceq_self A.erase) Q hQ hAQ cv hcv hband hroot hgatFreeze
    T₀ hT₀
  have hpread : M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).st
      (M.proposal_time S.E (d + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (d + 1))) (S.E.proposer (d + 1))).record cp ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (d + 1) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  obtain ⟨hparent, -⟩ := (p58% parent_preceq_of_proposal₅₈s) facts S rho _ _ hpread
    (by rw [facts.nd.mkNode_cache]; exact hB) I (by rw [facts.nd.mkNode_cache]; exact hI)
  have hpath : Block.Preceq A0 A.erase →
      ∀ C : Block V, Block.Preceq A0 C → C ≠ A0 → Block.Preceq C A.erase →
        C ∈ T₀.erase B.erase := by
    intro _ C hAC hCne hCA
    have hCmem : C ∈ T₀ := by
      by_cases hEq : C = A.erase
      · rw [hEq]
        exact hcand.1
      · exact hcand.2 A0 hA0 C hAC hCne hCA hEq
    refine Finset.mem_erase.mpr ⟨?_, hCmem⟩
    intro hEq
    have hCP := preceq_trans_Preceq hCA hpivotParent
    rw [hEq] at hCP
    have hdepth := Block.preceq_depth_le (preceq_eq_true_iff_Preceq.2 hCP)
    have hstrict := Protocol.depth_of_parent? hparent
    omega
  have hcompat := compatible_of_preceq_common_Preceq htargetAnchor
    (Proofs.ModelProperties.Preceq_self A.erase)
  obtain ⟨sup, hsup⟩ := facts.fc.raw_supporters_nonempty m.st.core.T vv vsv (m.st.core.s - 1)
    A.erase
  have hfc := (facts.fc.goldfish_fork_choice_eq_ghost S.E m.st.core.σ m.st.core.h_max m.st.core.T
    m.st.core.s A0 (T₀.erase B.erase) vv vsv (m.st.core.s - 1) sc hsc el hel G).mpr hG
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority _ _ _ _ _ _ _ _ _ hconeV.sub
    sup hsup (hmaj sup hsup) hcompat hpath G hfc

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

/-- Under the bundle along `W`, if `v ∈ Xb`, `P`'s erasure is in the tree of `v`'s store in
    `W (strictEventIndex rho t)` and `P` is a run block read through `Xb` along `W`, then `P` is a
    body of that store. -/
theorem namedBody_of_mem_storeBeforeTime_l86f (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {t : Time} {P : NamedBlock V}
    (hmem : P.erase ∈ (W (strictEventIndex rho t) v).st.core.T)
    (hPrun : Restated.RunBlockOn M S rho W Xb P) :
    P ∈ (W (strictEventIndex rho t) v).st.bodies := by
  obtain ⟨D, hD, hDErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho t v _
      ((p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath t) hmem
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hD
  have hroot : D.root = P.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root P, hDErase]
  have hDP : D = P :=
    hf.rootCollisionFree.root_injective D P hDrun hPrun D P
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self P)) hroot
  rw [← hDP]
  exact hD

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

/-- After the progress deadline, some run block `T` read through `Xb` along `W` has height at least
    the reader `u`'s `h_max` minus one at `read`, and is an ancestor of every head that every member
    of the set for `vote_time s` can vote at a later slot `s`. -/
private theorem exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f
    (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {read : Time}
    (hread : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot}
    (hs : (M.opening_slot S.hc)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hnext : read ≤ M.confirmation_time S.E s)
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ T : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb T ∧
      (W (strictEventIndex rho read) u).st.h_max - 1 ≤ (M.derive_named S.E S.cfg T).h ∧
      ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
        let n := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
            (M.vote_time S.E s))
          (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
        ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
          Block.Preceq T.erase H := by
  have hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ Xb := fun t _ => hHsXb t
  have hXXb : Xb ⊆ Xb := Finset.Subset.refl _
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)) :=
    hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right rGST 2))
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
      S Hs Xb Xb hf hHs hHsXb hX hXXb hcom hbelow hrec hdelay hpost (hread.trans hhor)
      hlo hloOpen ht₀ hA
  exact Restated.NamedHeightRegimeBaseRunOn.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_deadline
    facts hf hHs hHsXb hX hXXb hcom hbelow
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
    hbase hfirst hhor hs hnext hshor hu
    (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

/-- For a round `m` with `D + 2 ≤ m`, `D` the progress deadline, whose opening proposer is in the
    set and proposes `P` along `W`: some run block `E` is the greatest common ancestor of the heads
    at the previous slot `d` of the members of the set for `vote_time d`; every round-`(m − 1)` SG
    block of a member of the set is an ancestor of `E`; `E` is an ancestor of the parent of every
    proposal input; the proposer's anchor is an ancestor of `E`; and `E`'s stored height at the
    proposer's duty store is at least that store's `h_max − 1`. -/
theorem openingPivot_afterDeadlineOn (facts : Record.Facts M)
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
    (hhor : M.vote_time S.E ((M.opening_slot S.hc m)) ≤ rho.horizon)
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
    (head : V → Block V)
    (hhead : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc m) - 1)), ∃ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc m) - 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc m) - 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc m) - 1))) w).cache ⇢ c ∧
      let n := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc m) - 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc m) - 1)))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc m) - 1))) w).record c
      ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ head w) :
    ∃ E : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb E ∧
      (∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc m) - 1)),
        Block.Preceq E.erase (head w)) ∧
      (∀ B : Block V,
        (∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc m) - 1)), Block.Preceq B (head w)) →
        Block.Preceq B E.erase) ∧
      (∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (m - 1))),
        ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (m - 1))) u) (m - 1),
        ∀ A2 : Option (Block V),
          M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
        ∀ G : Block V,
          M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
          Block.Preceq G E.erase) ∧
      (∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc m)))
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).st
            (M.proposal_time S.E (M.opening_slot S.hc m)))
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).record cp).st.core) ⇢ I →
        Block.Preceq E.erase I.parent) ∧
      (∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).st
            (M.proposal_time S.E (M.opening_slot S.hc m)))
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).record cp)
          (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).st
            (M.proposal_time S.E (M.opening_slot S.hc m)))
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).record cp).st.core.s) ⇢ A0 →
        Block.Preceq A0 E.erase) ∧
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
            (S.E.proposer (M.opening_slot S.hc m))).st.core
          (M.proposal_time S.E (M.opening_slot S.hc m))).h_max - 1 ≤
        ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
            (S.E.proposer (M.opening_slot S.hc m))).st.core
          (M.proposal_time S.E (M.opening_slot S.hc m))).σ E.erase).h := by
  classical
  have hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 S u (W j u) k :=
    fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu)
  obtain ⟨hdeadlineSlot, hdeadlineTwo, hinterior, hdPos, hdSucc, hcEq, hqEq, hcDeadline, -⟩ :=
    facts.gr.openingSlots_l86f S hm
  set D := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDdef
  set start := (M.opening_slot S.hc m) with hstartdef
  set d := start - 1 with hddef
  set wp := W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start) with hwpdef
  set pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) wp.record cp
    with hpndef
  have hpnst : pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) _ := facts.nd.mkNode_st _ _ _
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpncore : pn.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  have hGSTdead : rGST ≤ D := by
    rw [hDdef]
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6⟩ := facts.sch.slot_instants_l55 S.E d
  have hpS : M.proposal_time S.E start = M.proposal_time S.E d + 4 * S.E.Δ := by
    rw [← hdSucc]
    exact hi4
  have hvS : M.vote_time S.E start = M.proposal_time S.E d + 5 * S.E.Δ := by
    rw [← hdSucc]
    exact hi5
  have hΔ := S.E.Δ_pos
  have hproposalHor : M.proposal_time S.E start ≤ rho.horizon :=
    (facts.sch.proposal_time_lt_vote_time S.E start).le.trans hhor
  have hprevVoteHor : M.vote_time S.E d ≤ rho.horizon :=
    (facts.sch.vote_time_mono_slots S.E (Nat.sub_le start 1)).trans hhor
  have hprevDelta : M.vote_time S.E d + S.E.Δ ≤ rho.horizon := by linarith
  have hsupportHor : M.support_cutoff S.E d ≤ rho.horizon := by linarith
  have hdeadlineProposal : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ M.proposal_time S.E start :=
    (Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S D).le.trans
      (facts.sch.proposal_time_mono S.E hdeadlineTwo)
  have hdeadlineVote : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ M.vote_time S.E start :=
    hdeadlineProposal.trans (facts.sch.proposal_time_lt_vote_time S.E start).le
  have hloD : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S D) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hGSTdead)
  have hloVoteD : lo ≤ M.vote_time S.E d :=
    Restated.lo_le_vote_after_deadline_l86e facts S hloPost hdeadlineSlot
  have hkM1 : lo ≤ M.early S.E S.hc (m - 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (by rw [← hcEq]; exact Nat.lt_succ_of_le (hGSTdead.trans hcDeadline))
  have hwinD : lo ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
    have hD1 : rGST + 1 ≤ D := by
      rw [hDdef]
      unfold fgSafetyProgressDeadline
      exact Nat.le_add_right _ _
    have hDd : D ≤ M.round_of S.hc d := by
      have h := facts.gr.round_of_mono S.hc ((Nat.le_succ _).trans hdeadlineSlot)
      rwa [facts.gr.round_of_opening_slot_eq] at h
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
      (lt_of_lt_of_le (Nat.lt_of_succ_le hD1) hDd)
    have h2 := facts.gr.q10_early_g2_le_early_g1 S (M.round_of S.hc d)
    have h3 : lo ≤ M.a S.hc S.E.Δ rGST := hloPost
    linarith
  have hpropConf : S.E.proposer start ∈ Hs (M.confirmation_time S.E start) := hopening
  have hpropVote : S.E.proposer start ∈ Hs (M.vote_time S.E start) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E start) hpropConf
  have hpropProposal : S.E.proposer start ∈ Hs (M.proposal_time S.E start) :=
    hHs _ _ (facts.sch.proposal_time_lt_vote_time S.E start).le hpropVote
  have hpropSC : S.E.proposer (d + 1) ∈ Hs (M.support_cutoff S.E d) := by
    rw [hdSucc]
    refine hHs _ _ ?_ hpropProposal
    linarith
  have houts := hhead
  obtain ⟨E, hErun, hEheads, hEmax⟩ :=
    Restated.exists_namedGreatestPreviousHeadOn facts S Hs Xb hf hHs hHsXb hcom hdPos
      hprevVoteHor hloVoteD head hhead
      (fun w _ hw j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwinD)
  have hupper : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (m - 1))),
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (m - 1))) u) (m - 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
        Block.Preceq G E.erase := by
    intro u hu nv hnv A2 hA2 G hG
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts w hw
    exact Restated.actionSGBlock_preceq_voterHeadAt_after_GSTOn facts S Hs Xb hf hHs hHsXb
      hcom hbelow hrec hdelay hpost (c := m - 2) hcDeadline (by rw [hcEq]; exact hinterior)
      hprevDelta (by rw [hcEq]; exact hu)
      (hAll _ _ (by rw [hcEq]; exact hkM1) (by rw [hcEq]; exact hu)) hw hloPost hloOpen ht₀ hA
      c hc T hT L hL L' hL' (head w) hH nv (by rw [hcEq]; exact hnv) A2 hA2 G hG
  have hreadBound : ∀ {read : Time}, (Restated.Vocabulary.Execution.Setup.a M S D) ≤ read →
      read ≤ rho.horizon → read ≤ M.confirmation_time S.E d → ∀ {u : V}, u ∈ Hs read →
      Block.Preceq
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) E.erase := by
    intro read hread hreadHor hnext u hu
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts w hw
    exact Restated.fgRoot_preceq_previousHead_through_confirmation_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hread hreadHor hdeadlineSlot hnext hprevDelta
      hu hloPost hloOpen ht₀ hA w hw c hc T hT L hL L' hL' (head w) hH
  have hproposalNext : M.proposal_time S.E start ≤ M.confirmation_time S.E d := by linarith
  have hvoteNext : M.vote_time S.E start ≤ M.confirmation_time S.E d := by linarith
  have hsourceRoot : Block.Preceq (M.get_fg_root (M.toHealing pn.st.core).toFG) E.erase := by
    rw [hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [(p60% setClock_fgRoot₆₀) facts S]
    exact hreadBound hdeadlineProposal hproposalHor hproposalNext hpropProposal
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ m ≤ rho.horizon := by
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E m]
    linarith
  have hpostPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) :=
    hloD.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hcDeadline.trans (Nat.sub_le (m - 1) 1)))
  have hround : M.round_of S.hc pn.st.core.s = m := by
    rw [hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_opening_slot_eq_schedule S.hc m
  have hsourceAnchor : ∀ A0 : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S pn
        (M.round_of S.hc pn.st.core.s) ⇢ A0 → Block.Preceq A0 E.erase := by
    intro A0 hA0
    rw [hround] at hA0
    have h := Restated.fixedRoot_preparedProposalAnchor_preceq_of_previousCarriersOn facts S Hs Xb
      hf hHs hHsXb hbelow (q := m - 1) hpostPrev (by rw [hqEq]; exact hcut)
      (by rw [hqEq]; exact hproposalHor) hupper (by rw [hqEq]; exact hpropProposal)
      cp (by rw [hqEq]; exact hcp) (by rw [hqEq]; exact hsourceRoot) (hA (m - 1) hkM1)
    rw [hqEq] at h
    exact h A0 hA0
  obtain ⟨Ts, hTsrun, hTsband, hTsheads⟩ :=
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f facts S Hs Xb
      hf hHs hHsXb hcom hbelow hrec hdelay hpost hdeadlineProposal hproposalHor hdeadlineSlot
      hproposalNext hprevDelta hpropProposal hloPost hloOpen ht₀ hA
  have hTsE : Block.Preceq Ts.erase E.erase := by
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts w hw
    exact hTsheads w hw c hc T hT L hL L' hL' (head w) hH
  have hTsENamed : NamedBlock.Preceq Ts E :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTsrun hErun hTsE
  have hsourceBand : wp.st.core.h_max - 1 ≤ (M.derive_named S.E S.cfg E).h :=
    hTsband.trans (facts.cs.derive_height_mono S.E S.cfg hTsENamed)
  have hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
      (fun X => Block.Preceq E.erase X) := by
    intro x hx hcommittee
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts x hx
    obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
      Restated.named_voter_head_emitsOn facts S Hs Xb hf hHsXb hx hdPos hcommittee
        hprevVoteHor hloVoteD c hc
        (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx hwinD) T hT L hL L' hL' (head x) hH
    exact ⟨X, by rw [hXhead]; exact hEheads x hx, hXrun, hXemit⟩
  have hrootCompat : Block.compatible (M.get_fg_root (M.toHealing pn.st.core).toFG) E.erase = true :=
    compatible_of_preceq_common_Preceq hsourceRoot (Proofs.ModelProperties.Preceq_self E.erase)
  have hsupport := Restated.fixedRoot_preparedProposalConeSupport_of_namedConeOn facts S Hs Xb hf
    hHs hHsXb hcom hdPos hloVoteD hsupportHor hpropSC cp (by rw [hdSucc]; exact hcp)
    (by rw [hdSucc]; exact hsourceRoot) hcone
  rw [hdSucc] at hsupport
  have hvalid := Restated.proposerDutyStore_proposer_view_valid_coreOn facts S Hs Xb hf start
  have hproposerVoteRoot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (d + 1))) (S.E.proposer (d + 1))).st
        (M.vote_time S.E (d + 1))).core).toFG) E.erase := by
    rw [(p60% setClock_fgRoot₆₀) facts S, hdSucc]
    exact hreadBound hdeadlineVote hhor hvoteNext hpropVote
  have hmemP := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (M.proposal_time S.E start)
  have hmemW : E.erase ∈ wp.st.core.T := by
    have havailable := Restated.honestHeadsAvailableBefore_of_namedPostHealingConeOn facts S Hs Xb
      hf hHs hHsXb hpropSC hloVoteD hsupportHor hproposerVoteRoot hcone
    have hxcPos : 0 < ((S.E.committee d) ∩ Hs (M.confirmation_time S.E d)).card := by
      have hc := hcom d
      omega
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hxcPos
    have hx0c := (Finset.mem_inter.mp hx0).1
    have hx0conf := (Finset.mem_inter.mp hx0).2
    have hx0vote : x0 ∈ Hs (M.vote_time S.E d) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E d) hx0conf
    obtain ⟨X, hXE, hXrun, hXemit⟩ := hcone x0 hx0vote hx0c
    have hXhead : Restated.HonestHeadOn M S rho W Hs Xb d X.erase :=
      ⟨x0, hx0conf, hx0c, ⟨X, rfl, hXrun⟩, hXemit⟩
    rcases havailable X.erase hXhead with hgen | hadmit
    · have hEgen : E.erase = Block.genesis :=
        eq_genesis_of_Preceq_genesis (hgen ▸ hXE)
      rw [hEgen]
      exact (Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf (S.E.proposer start)
          (M.proposal_time S.E start) (M.proposal_time S.E start)).1
    · have hXT := (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit
        (facts.sch.support_cutoff_le_proposal_time_succ S.E d)).1
      rw [hdSucc] at hXT
      have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
        (M.proposal_time S.E start) (S.E.proposer start) _ hmemP
      unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
      rw [facts.sto.toHealing_gs_T] at hpc
      exact Proofs.Records.mem_of_preceq hpc.2 E.erase X.erase hXT
        (preceq_eq_true_iff_Preceq.2 hXE)
  have hEbody : E ∈ wp.st.bodies :=
    Restated.namedBody_of_mem_storeBeforeTime_l86f facts S Hs Xb hf (hHsXb _ hpropProposal)
      hmemW hErun
  have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (M.proposal_time S.E start) (S.E.proposer start) _ hmemP E hEbody
  have hσ : (pn.st.core.σ E.erase).h = (M.derive_named S.E S.cfg E).h := by
    rw [hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_σ]
    exact congrArg (fun z => z.h) hview
  have hbandpn : pn.st.core.h_max - 1 ≤ (pn.st.core.σ E.erase).h := by
    rw [hσ, hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_h_max]
    exact hsourceBand
  have hmem : E.erase ∈ pn.st.core.T := by
    rw [hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
    exact hmemW
  have hwitness : Restated.Vocabulary.Proofs.HealingSurface.CanonicalConeWitness M pn.st.core E.erase :=
    ⟨E.erase, hmem, Proofs.ModelProperties.Preceq_self _, hbandpn⟩
  have hEparent := Restated.fixedRoot_preparedProposalHead_preceq_of_coneOn facts S Hs Xb
    (Hs (M.confirmation_time S.E d)) hf cp hcp hrootCompat hwitness
    (fun R hR => hsourceAnchor R ((p60% nodeAnchor_of_sgRoot₆₀s) facts S pn _
      (by rw [hpncache]; exact hR)))
    hsupport (by rw [hpncore]; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]); rw [← tickStore_eq₈₆f facts]
                 exact hvalid)
  refine ⟨E, hErun, hEheads, hEmax, hupper, hEparent, hsourceAnchor, ?_⟩
  have h := hbandpn
  rw [hpncore] at h
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
  rw [← tickStore_eq₈₆f facts] at h
  exact h

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

/-- `openingPivot_afterDeadlineOn` in the run `R` of the first `n` steps of the execution `x`, along
    the path `W = Restated.runAllPath M S Sched x v₀ n`, for a round `c` with
    `Restated.deadlineRoundW M S tGAT gap + 2 ≤ c` and an opening proposer not held at its
    confirmation instant: some run block `E` is the greatest common ancestor of the heads of the
    validators not held at the previous slot, every round-`(c − 1)` SG block of a validator not held
    is an ancestor of `E`, `E` is an ancestor of the parent of every proposal input, the proposer's
    anchor is an ancestor of `E`, and `E`'s stored height is at least the proposer's `h_max − 1`. -/
theorem openingPivot_runAll_notHeld (facts : Record.Facts M)
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
    (hhor : M.vote_time S.E ((M.opening_slot S.hc c)) ≤
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
    ∀ head : V → Block V,
      (∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) - 1)), ∃ cw : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).st.core.toHealing
          (M.vote_time S.E ((M.opening_slot S.hc c) - 1))
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).cache ⇢ cw ∧
        let nw := M.mkNode
          (M.ns_setClock S.E
            (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).st
            (M.vote_time S.E ((M.opening_slot S.hc c) - 1)))
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) - 1))) w).record cw
        ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E nw.st.core nw.st.core.s ⇢ T ∧
        ∃ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s ⇢ L ∧
        ∃ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore
            nw.st.core.s ⇢ L' ∧
        M.get_head_in_tree_with_layer (M.gradeContract nw.cache) S.E S.hc
          (M.toHealing nw.st.core) T L L' (nw.st.core.s - 1) ⇢ head w) →
    ∃ E : NamedBlock V,
      Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ E ∧
      (∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) - 1)),
        Block.Preceq E.erase (head w)) ∧
      (∀ B : Block V,
        (∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) - 1)),
          Block.Preceq B (head w)) →
        Block.Preceq B E.erase) ∧
      (∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1))),
        ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
            (W (strictEventIndex R
              (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1))) u) (c - 1),
        ∀ A2 : Option (Block V),
          M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
        ∀ G : Block V,
          M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
          Block.Preceq G E.erase) ∧
      (∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c)))
          (M.toHealing pn.st.core) ⇢ I →
        Block.Preceq E.erase I.parent) ∧
      (∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) pn
          (M.round_of S.hc pn.st.core.s) ⇢ A0 →
        Block.Preceq A0 E.erase) ∧
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S) wp.st.core
          (M.proposal_time S.E (M.opening_slot S.hc c))).h_max - 1 ≤
        ((Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S) wp.st.core
          (M.proposal_time S.E (M.opening_slot S.hc c))).σ E.erase).h := by
  intro R W wp cp hcp pn hP head hhead
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.openingPivot_afterDeadlineOn facts
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
      k hk u j hj) head hhead

end

end DecoupledConsensusModel.Sts.Restated
