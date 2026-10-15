import Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# A body for the height maximum

In every world of a run, a validator's store holds a body whose derived height is the store's
`h_max`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedMaximumCarrier
open Execution Protocol

/-- In every world before time `t` in `rho`, `v`'s store holds a body whose derived height is the
    `h_max` of `v`'s core store. -/
theorem Vocabulary.Proofs.NamedMaximumCarrier.maximum_carrier_stateBeforeTime (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t, 
    ∃ D : NamedBlock V,
      D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).h =
        (w₁ v).st.core.h_max :=
  facts.hdRun.maximum_carrier_stateBeforeTime S rho t v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedMaximumCarrier
open Execution Protocol

/-- In every world before the `i`-th event of `rho`, `v`'s store holds a body whose derived height
    is the `h_max` of `v`'s core store. -/
theorem Vocabulary.Proofs.NamedMaximumCarrier.maximum_carrier_stateBefore (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, 
    ∃ D : NamedBlock V,
      D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).h =
        (w₁ v).st.core.h_max :=
  facts.hdRun.maximum_carrier_stateBefore S rho i v

end

end DecoupledConsensusModel.Sts.Restated
