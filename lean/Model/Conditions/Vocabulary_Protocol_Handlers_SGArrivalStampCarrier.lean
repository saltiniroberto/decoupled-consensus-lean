import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Arrival stamps of SG rows

The condition that every SG row a named store holds is in its own round's bucket and carries an SG
vote stamp at most a fixed bound, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage

/-- The store clock of `st` is at most `bound`, and every SG row in bucket `k` has round `k` and an
    SG vote stamp at most `bound`. -/
def Vocabulary.Proofs.NamedOutageHistory.SGArrival.Data (M : Record.Model V) (bound : Time) (st : M.NS) : Prop :=
  st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
    a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
      st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)

end

end DecoupledConsensusModel.Sts.Restated
