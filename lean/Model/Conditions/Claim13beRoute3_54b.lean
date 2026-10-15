import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# The opening proposer's height

The condition `ProposerProposalStoreBelowFrontierOn` bounding the `h_max` of a round's opening
proposer by the largest `h_max` over the set at an endpoint, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- The `h_max` of the store, in the world `w₁`, of round `q`'s opening proposer is at most the
    largest `h_max` of the stores, in the world `w₂`, of the members of `Hs endpoint` (zero when
    that set is empty). -/
def ProposerProposalStoreBelowFrontierOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (q : Round) (endpoint : Time) (w₁ w₂ : V → M.N) : Prop :=
  (w₁ (S.E.proposer (M.opening_slot S.hc q))).st.h_max ≤
    (Hs endpoint).sup fun v => (w₂ v).st.core.h_max

end

end DecoupledConsensusModel.Sts.Restated
