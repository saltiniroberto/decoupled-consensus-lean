import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bHandover
import Model.Conditions.Sts_Constants
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bHandover

/-!
# The healing length is not negative

Over a model `M : Record.Model V`, `Restated.healingLength M S gap` is at least zero.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The healing length is at least zero. -/
theorem healingLength_nonneg (facts : Record.Facts M) (S : Setup V) (gap : Nat) : 0 ≤ Restated.healingLength M S gap := by
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hstartup : (0 : Int) ≤ (Restated.constants M S).finalityStartup gap :=
    ((Restated.constants_holds facts S).delays_nonneg gap).2.2.2.2.1
  have hdeadline : (0 : Int) ≤ (Restated.constants M S).finalityDeadline gap :=
    ((Restated.constants_holds facts S).delays_nonneg gap).2.2.2.2.2
  have hgapmul : (0 : Int) ≤ (gap : Int) * (Restated.constants M S).period :=
    mul_nonneg (Int.natCast_nonneg gap) (le_of_lt hper)
  show (0 : Int) ≤ (Restated.constants M S).finalityStartup gap + (gap : Int) * (Restated.constants M S).period +
    (Restated.constants M S).finalityDeadline gap + (Restated.constants M S).period
  linarith

end

end DecoupledConsensusModel.Sts.Restated
