import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepSG

/-!
# The stores and frames of the action read

The healing stores `actionHealingStore` and grade frames `actionFrame` a validator's action read can
hold, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The healing stores of the node states of the round-`r₁` action read from `before`. -/
def actionHealingStore (M : Record.Model V) (S : Setup V) (before : M.N) (r₁ : Round) :
    DC.NDR M.HS :=
  (fun n : M.N => M.toHealing n.st.core) ''
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S) before r₁

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The grade frames of round `r₁` read from the cache of each node state of the round-`r₁` action
    read from `before`, clipped to that node state's healing store. -/
def actionFrame (M : Record.Model V) (S : Setup V) (before : M.N) (r₁ : Round) : DC.NDR M.Frame :=
  (fun n : M.N => M.readFrame n.cache (M.toHealing n.st.core) r₁) ''
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S) before r₁

end

end DecoupledConsensusModel.Sts.Restated
