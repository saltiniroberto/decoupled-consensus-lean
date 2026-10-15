import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Votes carried by a proposal

The Goldfish votes and support votes a proposed block carries, and when a support vote carried by a
block enters the receiver's support view, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, if the
    proposal run on `n` can return the named block `B`, then `B`'s Goldfish votes are those of every
    proposal input computed from `n`. -/
theorem Vocabulary.Protocol.proposedBlock_gf_votes (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some B →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    B.gf_votes = input.gf_votes := by
  intro n hnmem hB input hinput
  have _hr : M.reachedNode n := by
    obtain ⟨w, hw, c, hc, rfl⟩ := hnmem
    exact facts.nd.reachedNode_confirmationRead S.E S.hc (w _) _ c hc
      (Record.reachedNode_stateBeforeTime facts S rho _ w hw _)
  have _hrs : M.reachedStore n.st := facts.nd.reachedStore_of_node n _hr
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc n.st
  exact (Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts
    (M.gradeContract n.cache) .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) n.st B hB
    input hinput L hL).2.2.2.2.1

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, if the
    proposal run on `n` can return the named block `B`, then `B`'s support votes are those of every
    proposal input computed from `n`. -/
theorem Vocabulary.Protocol.proposedBlock_gf_support_votes (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some B →
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    B.gf_support_votes = input.gf_support_votes := by
  intro n hnmem hB input hinput
  have _hr : M.reachedNode n := by
    obtain ⟨w, hw, c, hc, rfl⟩ := hnmem
    exact facts.nd.reachedNode_confirmationRead S.E S.hc (w _) _ c hc
      (Record.reachedNode_stateBeforeTime facts S rho _ w hw _)
  have _hrs : M.reachedStore n.st := facts.nd.reachedStore_of_node n _hr
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc n.st
  exact (Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts
    (M.gradeContract n.cache) .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) n.st B hB
    input hinput L hL).2.2.2.2.2.1

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, if the
    proposal run on `n` can return the named block `B`, then the set of `B`'s Goldfish votes is the
    vote pool of `n`'s core store at the slot before that store's slot. -/
theorem Vocabulary.Protocol.proposedBlock_raw_eq_proposer_pool (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (s : Slot) {B : NamedBlock V} :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some B →
    B.gf_votes.toFinset =
      (M.store_pool n.st.core)
        (n.st.core.s - 1) := by
  intro n _ hB
  have hgf := facts.dt.proposal_with_gf_votes
    (M.gradeContract n.cache) .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) n.st (B := B)
    (some B) hB rfl
  rw [hgf]
  ext u
  rw [List.mem_toFinset, facts.sto.mem_pool_iff]

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution

/-- If the block `B` of slot `s` is in `st`'s tree, `u` is one of `B`'s support votes of the slot
    before `B`'s, and the resolution test of `u` in `st`'s tree can return `true`, then `u` is in
    every outcome of the voter's support view of `st` at slot `s`. -/
theorem Vocabulary.Protocol.mem_voter_support_view_of_carried (facts : Record.Facts M)
    (E : Env V) (st : M.GS) {s : Slot} {B : Block V}
    {u : GoldfishVote V}
    (hB : B ∈ st.T) (hBslot : B.slot = s)
    (hu : u ∈ B.gf_support_votes)
    (hresolved : M.resolved st.T u ⇢ true)
    (huslot : u.slot + 1 = B.slot) :
    ∀ Y : Finset (GoldfishVote V), M.voter_support_view E st s ⇢ Y → u ∈ Y :=
  facts.fc.mem_voter_support_view_of_carried E st s hB hBslot hu true hresolved rfl
    (Nat.eq_sub_of_add_eq (hBslot ▸ huslot))

end

end DecoupledConsensusModel.Sts.Restated
