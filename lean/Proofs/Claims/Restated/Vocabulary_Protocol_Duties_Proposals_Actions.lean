import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Record.Wiring

/-!
# The payload of a proposal

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a block the
proposal duty returns has a retained parent, takes its slot, root, Goldfish votes, support votes and
proposer from the proposal input, and takes its attestations from the selected rows.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedActions
open Protocol.NamedActions

/-- If the proposal duty under `contract`, with the row source `source`, can return the block `B` at
    `st`, then for every outcome `input` of the proposal input built at `st`'s healing view and
    every outcome `L` of the rows `M.select source hc st`, `B`'s parent is a body retained by `st`
    that erases to the parent of `input`; `B`'s slot, root, Goldfish votes, Goldfish support votes
    and proposer are `input`'s; and `B`'s attestations are the proposal rows of `B`'s parent over
    `L`. -/
theorem Vocabulary.Proofs.NamedActions.proposal_payload (facts : Record.Facts M) (contract : M.Contract)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.NS) (B : NamedBlock V)
    (hout : M.proposal_with contract source E hc nd st ⇢ some B) :
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M contract E hc nd (M.toHealing st.core) ⇢ input →
    ∀ L : List (NamedAttestation V), M.select source hc st ⇢ L →
    ∀ (hn : M.reachedStore st := by trivial),
    B.parent ∈ st.bodies ∧ B.parent.erase = input.parent ∧
    B.slot = input.slot ∧ B.root = input.root ∧
    B.gf_votes = input.gf_votes ∧ B.gf_support_votes = input.gf_support_votes ∧
    B.attestations = M.proposalRows B.parent L ∧ B.proposer? = some input.proposer :=
  fun input hc1 L hc2 _hn => facts.dt.proposal_payload contract source E hc nd st B (some B) hout rfl input hc1 L hc2

end

end DecoupledConsensusModel.Sts.Restated
