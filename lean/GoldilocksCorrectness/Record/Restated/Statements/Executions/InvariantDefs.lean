module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# InvariantDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/InvariantDefs.lean` over a model `M`:
the attestations a node's anti-slashing record sent at a height where it holds a lock name the
locked block, read through the record's readers `n.sentLock` and `n.sentAttestations`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (AttestationsValid ChainStatesComputed
  FinalizedAncestorJustified HeightCacheBounds JustificationCacheBounds JustifiedHeight
  JustifiedInTree)

open GoldilocksCorrectness.Statements.Routines (PoolKeyed PoolStamped)

namespace GoldilocksCorrectness.Record.Statements.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn RecordConsistent)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `LockNamesSent M n`: whenever the anti-slashing record of the node state `n` holds the lock
`T` at a height `h` (`n.sentLock h`), every attestation content it sent (`n.sentAttestations`)
at `h` names `T`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: at a height where the record holds a lock, every attestation it sent names the
locked block. -/
def LockNamesSent (n : M.N) : Prop :=
  ∀ (h : Height) (T : BlockId), n.sentLock h = some T → ∀ b ∈ n.sentAttestations, b.h = h → b.T = T

end GoldilocksCorrectness.Record.Statements.Executions

