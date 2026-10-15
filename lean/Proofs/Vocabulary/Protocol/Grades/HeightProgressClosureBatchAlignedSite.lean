module
public import Proofs.Vocabulary.Generic.FixedHeightRootAdmission
public import Proofs.Vocabulary.ModelProperties.HealingStore_gradeView
public import Proofs.Vocabulary.Protocol.Grades.RelativeCarrierWindowGateOff
public import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedSlotInterval
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import Proofs.Vocabulary.ModelProperties.NamedBlock_parent
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The G0 cutoff

`allPhasesCutoff` is the G0 early cutoff.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedOutageEntry
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- `allPhasesCutoff` of round `q` is the round's G0 early cutoff. -/
theorem allPhasesCutoff_eq_early_g0 (S : Setup V) (q : Round) :
    allPhasesCutoff S.E S.hc q = early S.E S.hc q .g0 := rfl


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
