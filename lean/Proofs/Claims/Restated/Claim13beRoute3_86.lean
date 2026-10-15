import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_52
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SGOpeningFrozenSuffix
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The proposal suffix transfer from the pivot's band

The proposal suffix transfers from the pivot to a voter when the pivot's chain-state height is at
least `h_max − 1` in both duty stores, stated over a model `M : Record.Model V` along a path `W` of
the run.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle with path `W`, in a run in which every tick has an outcome: if `0 < s`,
    `lo ≤ proposal_time (s − 1)`, the proposer of `s` and `v` are in the set for `vote_time s`,
    `vote_time s` is in the horizon, the proposal computed on the proposer's read can be `P`, the
    five core inputs hold at the proposer's and `v`'s reads, and the pivot's chain-state height is
    at least `h_max − 1` in both staged stores, then the proposal suffix transfers from the pivot to
    `v` in both directions between the two reads. -/
theorem namedProposalPivotSuffixTransfer_of_pivotBandOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    {pivot : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv)
    (h : Restated.Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixCoreInputs M S rho s pivot v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv))
    (hsourceBand :
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).h_max - 1 ≤
        ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).σ pivot).h)
    (htargetBand :
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).h_max - 1 ≤
        ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).σ pivot).h) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho s pivot v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv) := by
  obtain ⟨T0, hT0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
    (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core
    (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core.s
  have hPT := h.proposalCandidate T0 hT0
  have hT0' : M.voter_filtered_block_tree S.E (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).s ⇢ T0 := by
    have h1 := hT0
    rw [facts.nd.mkNode_st] at h1
    simp only [facts.nd.store_with_cache_voter_filtered_block_tree,
      facts.nd.store_with_cache_core_s] at h1
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      ← facts.hd.setClock_core_eq_store_with_t_s]
    exact h1
  exact Restated.namedProposalPivotSuffixTransfer_of_core_of_scoreBridgeOn facts
    S Hs Xb hf hHs hHsXb hs hpost hprop hv hvoteHor cp hcp hP cv hcv h
      (Restated.namedProposalCandidateScoreBridge_afterGSTOn facts S Hs Xb hf hHs hHsXb hs
        hpost hprop hv hvoteHor cp hcp hP
        (facts.fc.voter_filtered_block_tree_subset_filtered S.E _ T0 hT0' hPT))
      (Or.inr ⟨hsourceBand, htargetBand⟩)

end

end DecoupledConsensusModel.Sts.Restated
