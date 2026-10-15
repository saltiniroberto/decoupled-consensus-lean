module
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
public import Proofs.Vocabulary.ModelProperties.Store_pool
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.ForkChoice
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks
public import Proofs.Vocabulary.Objects.AdmissibleCore
import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Proposal snapshot identities -/


/-- The Goldfish votes included in a processed block `B` of slot `s`, all of slot `s - 1`, are in
    the voter view of slot `s`. -/
theorem carried_raw_subset_voter_view
    (E : Env V) (st : Protocol.GoldfishStore V) {s : Slot} {B : Block V}
    (hB : B ∈ st.T) (hBslot : B.slot = s)
    (hslots : ∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) :
    B.gf_votes.toFinset ⊆ Protocol.voter_view E st s := by
  intro u hu
  rw [Protocol.voter_view, Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  refine ⟨B, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨hB, hBslot⟩
  · rw [Finset.mem_filter]
    refine ⟨hu, ?_⟩
    have hslot := hslots u (List.mem_toFinset.mp hu)
    rw [hBslot] at hslot
    exact Nat.eq_sub_of_add_eq hslot

namespace CandidateScorePreservingViewExtension

variable {sourceTree targetTree : Finset (Block V)}
  {sourceRaw sourceSupport targetRaw targetSupport :
    Finset (GoldfishVote V)} {C : Block V}

end CandidateScorePreservingViewExtension

/-! ## Slot timing -/


/-- One slot's view freeze plus one network delay is the next proposal time. -/
theorem view_freeze_add_delta_eq_proposal_time_succ
    (E : Env V) (s : Slot) :
    Protocol.view_freeze E s + E.Δ = Protocol.proposal_time E (s + 1) := by
  unfold Protocol.view_freeze Protocol.proposal_time Env.t slotStart
  push_cast
  ring


#print axioms carried_raw_subset_voter_view
#print axioms view_freeze_add_delta_eq_proposal_time_succ

end Protocol
end DecoupledConsensusModel

end
