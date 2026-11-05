module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Network
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# NetworkUpTo, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/NetworkUpTo.lean` over a model `M`, for an
execution `x` of `protocolOf M S`: under the environment's promises up to a bound, on a wake-shaped
trace, the delivery comes before the step at which the time reaches the deadline; the same under
the delivery promise up to a bound alone, and under the sync fact up to a bound. It reads no fact
of the model.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithinUpTo)

open GoldilocksCorrectness.Record.Statements.Executions
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)
variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)
variable [RootOrder] {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsUpTo EnvFactsBy EnvFactsDeliveryUpTo
  SyncedWithinUpTo)

end GoldilocksCorrectness.Record.Proofs.Executions
