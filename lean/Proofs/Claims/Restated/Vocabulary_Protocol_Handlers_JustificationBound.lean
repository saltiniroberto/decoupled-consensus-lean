import Proofs.Vocabulary.Protocol.Handlers.JustificationBound
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_StoreFinality
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Bounds on the store's justification

In every world of a run, a validator's store satisfies `JustificationBelowMax` and
`NamedNoHighJustifications`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedJustificationBound
open Execution Protocol

/-- In every world before the `i`-th event of `rho`, `v`'s core store satisfies
    `JustificationBelowMax`. -/
theorem Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, 
    Restated.Vocabulary.Internal.JustificationBelowMax M ((w₁ v)).st.core :=
  facts.hdRun.justificationBelowMax_stateBefore S rho i v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedJustificationBound
open Execution Protocol

/-- In every world before time `t`, `v`'s core store satisfies `JustificationBelowMax`. -/
theorem Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time)
    (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t,  Restated.Vocabulary.Internal.JustificationBelowMax M ((w₁ v)).st.core :=
  facts.hdRun.justificationBelowMax_stateBeforeTime S rho t v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedJustificationBound
open Execution Protocol

/-- In every world before the `i`-th event of `rho`, `v`'s named store satisfies
    `NamedNoHighJustifications`. -/
theorem Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, 
    Restated.Vocabulary.Internal.NamedNoHighJustifications M S.E S.cfg ((w₁ v)).st :=
  facts.hdRun.noHighJustifications_stateBefore S rho i v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedJustificationBound
open Execution Protocol

/-- In every world before time `t`, `v`'s named store satisfies `NamedNoHighJustifications`. -/
theorem Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t, 
    Restated.Vocabulary.Internal.NamedNoHighJustifications M S.E S.cfg ((w₁ v)).st :=
  facts.hdRun.noHighJustifications_stateBeforeTime S rho t v

end

end DecoupledConsensusModel.Sts.Restated
