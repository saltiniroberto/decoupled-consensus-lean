module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Record.Restated.Statements.View.GoldilocksViewDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.ViewDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# UnforgeabilityDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/UnforgeabilityDefs.lean` over a
model `M`, for an execution `x` of `protocolOf M S`: a validator honest through a step, and two
distinct blocks honest validators hold by a time sharing a root, read on the view of `x` through
`nodeView M`. The attribution `author`, the block of an object `blockOf` and the vocabulary
`Vocab.goldilocks` read the objects only, which every model shares; the twins read the landed ones.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (carries)

open GoldilocksCorrectness.Statements.Network

namespace GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

section Executions

variable [RootOrder]

end Executions

section RootCollision

open GoldilocksCorrectness.Record.Statements.View
open GoldilocksCorrectness.Statements.AbstractTrace.View (RootCollisionHeldByV)

variable [RootOrder]

/-- `RootCollisionHeldBy M S Sched x t`: two distinct blocks that honest validators hold at steps at
times at most `t` have the same root. It is the negation of `RootsNameBlocksUntil M S Sched x t`.

Defined as its view form: `RootCollisionHeldByV` with Goldilocks's
vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view of `x`,
`projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's finalized
block, confirmed tip (`confirmedOf`) and held blocks. `rootCollisionHeldBy_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the bound on the time.

Read aloud: by the time `t`, a root collision has hit two blocks honest validators hold. -/
def RootCollisionHeldBy (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (t : ℕ) : Prop :=
  RootCollisionHeldByV GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks A
    ((x.map (nodeView M))) t

end RootCollision

end GoldilocksCorrectness.Record.Statements.Executions

