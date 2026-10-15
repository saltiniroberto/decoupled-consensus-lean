module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedHeadReads
public import Model.Vocabulary.Statements.Instantiation.Certificates
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.Store
public import Mathlib.Algebra.Order.Floor.Div
public import Proofs.Vocabulary.Internal.Legacy.Definitions.Confirmation
public import Proofs.Vocabulary.Internal.Legacy.Interface
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedOutageEntry
import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The admissibility bundle the proofs read

`AdmissibleCore`, the bundle of admissibility facts the proofs read, assembled from execution
validity and partial synchrony.
-/

namespace DecoupledConsensusModel.Proofs

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The bundle of admissibility facts the proofs read, `NamedAdmissibleCore S rho`. -/
abbrev AdmissibleCore (S : Setup V) (rho : Run V) : Prop := NamedAdmissibleCore S rho

namespace AdmissibleCore

abbrev toScheduleWellFormed := @NamedAdmissibleCore.toNamedScheduleWellFormed

/-- Assembles `AdmissibleCore` from execution validity and partial synchrony. -/
def ofParts {S : Setup V} {rho : Run V}
    (execution : ExecutionValid S rho) (synchrony : PartialSynchrony S rho) :
    AdmissibleCore S rho where
  toNamedScheduleWellFormed := execution.toNamedScheduleWellFormed
  toNamedDeliveryWellFormed := execution.toNamedDeliveryWellFormed
  toNamedRootCollisionFree := execution.toNamedRootCollisionFree
  toNamedUnforgeable := execution.toNamedUnforgeable
  toNamedSynchrony := synchrony

end AdmissibleCore
end DecoupledConsensusModel.Proofs

namespace DecoupledConsensusModel

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

namespace Execution.Admissible

/-- The `NamedAdmissibleCore` bundle of an admissible run. -/
def toNamedAdmissibleCore {S : Setup V} {rho : Run V} (h : Admissible S rho) :
    NamedAdmissibleCore S rho :=
  Proofs.AdmissibleCore.ofParts h.toExecutionValid h.toNamedSynchrony

end Execution.Admissible

namespace Statements.WeakGenesis

end Statements.WeakGenesis

namespace Statements.StrongRecoveryPrefix

end Statements.StrongRecoveryPrefix

namespace Statements.WeakContinuation

end Statements.WeakContinuation

namespace Statements.StrongFinalityRun

end Statements.StrongFinalityRun

namespace Internal.NamedOutageEntry.OutageExecution

end Internal.NamedOutageEntry.OutageExecution

end DecoupledConsensusModel

end
