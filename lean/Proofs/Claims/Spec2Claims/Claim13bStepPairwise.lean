import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote_mk

/-!
# Graded blocks of a grade read

The predicate `SGGraded`: a block is the grade-2 candidate of a grade read or the block the read
anchors the round at.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `B` is the grade-2 candidate `grades.Q2` of the grade read, or the block `grades.anchor` the
    read anchors the round at. -/
def SGGraded (grades : Protocol.GradeRead V) (B : Block V) : Prop :=
  grades.Q2 = some B ∨ B = grades.anchor

end DecoupledConsensusModel.Sts
