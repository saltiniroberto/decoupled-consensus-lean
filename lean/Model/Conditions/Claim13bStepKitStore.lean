import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepKitStore

/-!
# Attestation pools indexed by round

The condition `SGVotesRoundIndexed` on a grade view, stated over a model `M : Record.Model V`.
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

/-- Every attestation the grade view `gv` holds at a round `r'` is an attestation of round `r'`. -/
def SGVotesRoundIndexed (M : Record.Model V) (gv : M.GV) : Prop :=
  ∀ (r' : Round), ∀ u ∈ gv.sg_votes r', u.round = r'

end

end DecoupledConsensusModel.Sts.Restated
