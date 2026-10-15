import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bKit
import Model.Conditions.Sts_Constants
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_76

/-!
# A bound on the length of the phase

The length bound with one period added implies the length bound alone, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `tGAT + (healingLengthη S gap + (constants S).period) ≤ tE`, then
    `tGAT + healingLengthη S gap ≤ tE`. -/
theorem healingLength_le_of_kit_l76 (facts : Record.Facts M) (S : Setup V) {tGAT tE : Int} {gap : Nat}
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) :
    tGAT + Restated.healingLengthη M S gap ≤ tE := by
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  linarith

end

end DecoupledConsensusModel.Sts.Restated
