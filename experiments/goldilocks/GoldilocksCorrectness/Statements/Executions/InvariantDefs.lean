module
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Routines.RecordDefs
public import GoldilocksCorrectness.Statements.Routines.ChainStateDefs
public import GoldilocksCorrectness.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Statements.Routines.ACStoreDefs
public import GoldilocksCorrectness.Statements.Routines.NodeDefs

@[expose] public section

/-!
# The node invariant: its vocabulary

What every validator's node state holds at every step of every execution, as definitions over the
node's own types: the chain state computed from a block alone (`chainStateOf`); the pool filed by
slot and committee (`PoolKeyed`) with every vote stamped (`PoolStamped`); the tree closed under
parents, each non-genesis block passing the checks that read the block alone (`TreeClosed`); every
tree block stamped (`TreeStamped`); every chain state of the tree computed from its block
(`ChainStatesComputed`); every included attestation valid against the parent's chain state
(`AttestationsValid`); every stamp at most the node's clock (`StampsBounded`); every block stamped
no earlier than its parent (`StampOrder`); no two blocks of the tree sharing a root
(`RootsNameBlocksIn`); every attestation of the pool well formed (`PoolAttestationsWellFormed`);
the finalized block the justified block or an ancestor of it (`FinalizedAncestorJustified`); no
block of the tree with a chain-state height greater than the cache `h_max`
(`HeightCacheBounds`); no block on the finalized block's chain with a justification height greater
than the cache `h_j` (`JustificationCacheBounds`); the justified block at its justification height
(`JustifiedHeight`) and accepted (`JustifiedInTree`); every lock of the record at a height at most
the cache `h_j` (`LockBelowJustified`); and their conjunction with `S.F ∈ S.T` and the record's
consistency (`RecordConsistent`), `NodeInv`. Every attestation the record sent at a height where it
holds a lock names the locked block (`LockNamesSent`), a consequence of the record's consistency.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (AttestationsValid ChainStatesComputed
  FinalizedAncestorJustified HeightCacheBounds JustificationCacheBounds JustifiedHeight
  JustifiedInTree)

open GoldilocksCorrectness.Statements.Routines (PoolKeyed PoolStamped)

namespace GoldilocksCorrectness.Statements.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn RecordConsistent)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `LockNamesSent Λ`: whenever the anti-slashing record `Λ` holds the lock `T` at a height `h`,
every attestation content of `Λ.sent` at `h` names `T`.

The variables:
- `Λ`: the anti-slashing record.

Read aloud: at a height where the record holds a lock, every attestation it sent names the locked
block.

 -/
def LockNamesSent (Λ : SigningHistory) : Prop :=
  ∀ (h : Height) (T : BlockId), Λ.lock h = some T → ∀ b ∈ Λ.sent, b.h = h → b.T = T

end GoldilocksCorrectness.Statements.Executions
