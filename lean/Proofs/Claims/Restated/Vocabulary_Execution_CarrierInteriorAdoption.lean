import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SGOpeningFrozenSuffix
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Equal Goldfish scores under the candidate score bridge

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: when the
candidate score bridge holds between a proposer's node state at the proposal time and a voter's node
state at the vote time, a block in both trees gets the same Goldfish score from the voter's views as
from the proposer's.
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
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time and every node
    state `m` that `v` can hold at slot `s`'s vote time, if the proposal duty run on `n` can return
    `P` and the candidate score bridge holds for `n`, `n`'s core store and `m`'s core store, then
    every block `C` in the filtered block tree of `n`'s store and in an outcome of `m`'s voter
    filtered block tree without `P` gets, for every outcome of the views, a Goldfish score from
    `m`'s voter views equal to its score from `n`'s proposer views. -/
theorem Vocabulary.Proofs.HealingSurface.carrierInterior_scoreEq_of_scoreBridge (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {s : Slot} {v : V} {P : NamedBlock V} :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    ∀ m ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s,
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some P →
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge M S rho s v P
      n n.st.core m.st.core →
    ∀ C,
    C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
    C ∈ T.erase P.erase →
    ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
    ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
    ∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
    ∀ x : Nat, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) C ⇢ x →
    ∀ y : Nat, M.goldfish_score S.E n.st.core.T
        (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
        psv.toFinset (n.st.core.s - 1) C ⇢ y →
    x = y := by
  intro n hn m hm hP hbridge C hCsource T hT hCtarget vv hvv vsv hvsv psv hpsv x hx y hy
  have hCcandidate : C ∈ T := Finset.mem_of_mem_erase hCtarget
  have hCfiltered : C ∈ M.get_filtered_block_tree (M.toHealing m.st.core).toFG := by
    obtain ⟨Pp, hPp⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
      (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s
    obtain ⟨hproc, hF, ⟨Y, hY, hCY, hh⟩, hroot⟩ :=
      facts.hd.voter_filtered_block_tree_cases S.E m.st.core m.st.core.s T hT hCcandidate Pp hPp
    apply facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing m.st.core) (W := Y)
    · exact facts.fc.mem_T_of_mem_voter_processed_block_tree S.E _ _ Pp hPp hproc
    · rw [facts.sto.ModelProperties_toHealing_F]; exact hF
    · exact facts.fc.mem_T_of_mem_voter_processed_block_tree S.E _ _ Pp hPp hY
    · exact hCY
    · rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
      exact hh
    · exact hroot
  have hsourceSlot : n.st.core.s = s := by
    obtain ⟨w, -, c, -, rfl⟩ := hn
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s, facts.sto.store_with_t_s_s,
      facts.sch.slotOf_proposal_time]
  have htargetSlot : m.st.core.s = s := by
    obtain ⟨w, -, c, -, rfl⟩ := hm
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s, facts.sto.store_with_t_s_s,
      facts.sch.slotOf_vote_time]
  have hscore : ∀ (sourceTree targetTree : Finset (Block V))
      (sourceRaw sourceSupport targetRaw targetSupport : Finset (GoldfishVote V)) (k : Slot),
      Restated.Vocabulary.Protocol.CandidateScorePreservingViewExtension M sourceTree targetTree
        sourceRaw sourceSupport targetRaw targetSupport C →
      ∀ g : Nat, M.goldfish_score S.E sourceTree sourceRaw sourceSupport k C ⇢ g →
      ∀ g' : Nat, M.goldfish_score S.E targetTree targetRaw targetSupport k C ⇢ g' →
      g = g' := by
    intro sourceTree targetTree sourceRaw sourceSupport targetRaw targetSupport k h g hg g' hg'
    have heq : ∀ w : V, M.equivocates sourceRaw w = M.equivocates targetRaw w := by
      intro w
      cases hs : M.equivocates sourceRaw w with
      | true => exact (facts.sch.equivocates_mono_of_subset h.raw_subset hs).symm
      | false =>
          cases ht : M.equivocates targetRaw w with
          | false => rfl
          | true =>
              exfalso
              obtain ⟨u, hu, u', hu', hne, huw, hu'w⟩ :=
                (facts.sch.equivocates_eq_true_iff targetRaw w).mp ht
              by_cases hus : u ∈ sourceRaw
              · by_cases hu's : u' ∈ sourceRaw
                · have : M.equivocates sourceRaw w = true :=
                    (facts.sch.equivocates_eq_true_iff sourceRaw w).mpr
                      ⟨u, hus, u', hu's, hne, huw, hu'w⟩
                  rw [hs] at this; exact Bool.false_ne_true this
                · have := h.raw_extra_equiv u' hu' hu's
                  rw [hu'w, hs] at this; exact Bool.false_ne_true this
              · have := h.raw_extra_equiv u hu hus
                rw [huw, hs] at this; exact Bool.false_ne_true this
    choose t ht using fun u => facts.fc.targets_under_nonempty sourceTree C u
    choose t' ht' using fun u => facts.fc.targets_under_nonempty targetTree C u
    refine facts.fc.goldfish_score_eq_of_iff S.E k C heq t ht t' ht' ?_ g hg g' hg'
    intro w hclean
    have hcleanT : M.equivocates targetRaw w = false := by rw [← heq w]; exact hclean
    constructor
    · rintro ⟨u, hu, huw, hus, htu⟩
      rcases h.forward u hu (t u) (ht u) htu with ⟨hreach, hall⟩ | hequiv
      · exact ⟨u, hreach, huw, hus, hall _ (ht' u)⟩
      · rw [huw, hcleanT] at hequiv; exact absurd hequiv Bool.false_ne_true
    · rintro ⟨u, hu, huw, hus, htu⟩
      rcases h.backward u hu (t' u) (ht' u) htu with ⟨hreach, hall⟩ | hequiv
      · exact ⟨u, hreach, huw, hus, hall _ (ht u)⟩
      · rw [huw, hclean] at hequiv; exact absurd hequiv Bool.false_ne_true
  -- The bridge at `C`, with the voter's views read at slot `s`.
  have hvv' := hvv
  have hvsv' := hvsv
  rw [htargetSlot] at hvv' hvsv'
  have hext := hbridge C hCsource hCfiltered vv hvv' vsv hvsv'
  -- The proposal's votes are the proposer's views.
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing n.st.core)
  have hpsv' : M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s ⇢ psv := by
    rw [facts.sto.toHealing_s]; exact hpsv
  have hv1 : P.erase.gf_votes =
      M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s := by
    rw [Proofs.NamedWire.erase_goldfish_votes,
      Restated.Vocabulary.Protocol.proposedBlock_gf_votes facts S rho s n hn hP input hinput,
      facts.dt.with_proposal_input_id_gf_votes _ _ _ _ _ input hinput, facts.sto.toHealing_s]
  have hv2 : P.erase.gf_support_votes = psv := by
    rw [Proofs.NamedWire.erase_goldfish_support,
      Restated.Vocabulary.Protocol.proposedBlock_gf_support_votes facts S rho s n hn hP input hinput,
      facts.dt.with_proposal_input_id_gf_support_votes _ _ _ _ _ input hinput psv hpsv']
  have hy2 : M.goldfish_score S.E n.st.core.T P.erase.gf_votes.toFinset
      P.erase.gf_support_votes.toFinset (s - 1) C ⇢ y := by
    rw [hv1, hv2]
    rw [hsourceSlot] at hy ⊢
    exact hy
  have hx2 : M.goldfish_score S.E m.st.core.T vv vsv (s - 1) C ⇢ x := by
    rw [htargetSlot] at hx; exact hx
  exact (hscore _ _ _ _ _ _ (s - 1) hext y hy2 x hx2).symm

end

end DecoupledConsensusModel.Sts.Restated
