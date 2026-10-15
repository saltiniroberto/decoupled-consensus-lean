import Proofs.Vocabulary.Protocol.Handlers.SGArrival
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# A held attestation row keeps its stamp

An attestation row a validator holds stays held, with the same arrival stamp, at every later event,
stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedSGArrival
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage

/-- For `i ≤ j`, every world `w₁` before the `i`-th event of `rho` in which the attestation row `a`
    is in the bucket of its round of `reader`'s rows, and every world `w₂` the events `i` to `j - 1`
    lead to from `w₁`: `a` is still in that bucket in `w₂`, and the arrival stamp of `a`'s SG vote
    in `reader`'s store is the same in `w₂` as in `w₁`. -/
theorem Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (reader : V)
    {i j : Nat} (hij : i ≤ j) {a : NamedAttestation V} :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    a ∈ (w₁ reader).st.sg_rows a.round →
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
    a ∈ (w₂ reader).st.sg_rows a.round ∧
      (w₂ reader).st.core.timestamp_sg_vote (M.sgVote a.erase) =
        (w₁ reader).st.core.timestamp_sg_vote
          (M.sgVote a.erase) :=
  facts.hdRun.stateBefore_sg_row_stamp_mono S rho reader hij

end

end DecoupledConsensusModel.Sts.Restated
