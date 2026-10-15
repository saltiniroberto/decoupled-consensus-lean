import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.Store
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Processed attestations

The processed attestations of a store, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.Store
open Protocol (ChainState)
open Protocol (SGVote)

/-- The attestations of `st`'s SG votes of every round from 0 to the round of `st`'s slot, in
    ascending round order. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.S.processed_attestations {M : Record.Model V} (hc : Protocol.HealConfig) (st : M.S) :
    List (CombinedAttestation V) :=
  (List.range ((M.round_of hc st.s) + 1)).flatMap st.sg_votes

end

end DecoupledConsensusModel.Sts.Restated
