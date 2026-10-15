import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_4

/-!
# The slot bound on a store's tree

The conditions `TreeSlotBounded` and `TreeSlotStep`, stated over a model `M : Record.Model V`.
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

/-- Every block of the store's tree is of a slot at most the store's own slot. -/
def TreeSlotBounded (M : Record.Model V) (st : M.S) : Prop :=
  ∀ B : Block V, B ∈ st.T → B.slot ≤ st.s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `st` satisfies `TreeSlotBounded`, so does `st'`. -/
def TreeSlotStep (M : Record.Model V) (st st' : M.S) : Prop :=
  Restated.TreeSlotBounded M st → Restated.TreeSlotBounded M st'

end

end DecoupledConsensusModel.Sts.Restated
