module
public import GoldilocksCorrectness.Statements.Routines.ACStoreDefs
public import GoldilocksCorrectness.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Statements.Routines.RecordDefs
public import GoldilocksCorrectness.Statements.Routines.WalkDefs

@[expose] public section

/-!
# Conditions on a node state: the node invariant and its parts

`TreeClosed`, `TreeStamped`, `StampsBounded`, `StampOrder`, `PoolAttestationsWellFormed`,
`LockBelowJustified`: conditions on the block tree, the stamps, the attestation pool and the lock of
a node state; `NodeInv`: the node invariant, their conjunction with the conditions on the FG state;
`confirmedOf`: the block a node state's AC state names as confirmed. Nothing is proved here.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `confirmedOf n`: the confirmed tip of the node state `n`, `ac_confirmed n.A (fg_to_ac n.S)`:
the record `n.A.latest_confirmed` when it is a block of `n`'s tree with `n`'s finalized block
`n.S.F` as an ancestor or itself, and `n.S.F` otherwise.

The variables:
- `n`: the node state.

Read aloud: the block the node's available chain reports as confirmed. -/
def confirmedOf (n : NodeState V) : Block V := ac_confirmed n.A (fg_to_ac n.S)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `TreeClosed P X S`: the genesis block is in the tree `S.T`, and every other block of the tree
has its parent in the tree, is well formed, has the proposer of its slot, and has a parent of an
earlier slot.

The variables:
- `P`: the values given to the node; `X`: the digest; `S`: the FG state.

Read aloud: the tree is closed under parents, and each of its blocks passed the checks that read
the block alone. -/
def TreeClosed (P : Provisional V) (X : External V) (S : FGState V) : Prop :=
  Block.genesis ∈ S.T ∧
    ∀ B ∈ S.T, B ≠ Block.genesis →
      B.parent ∈ S.T ∧ block_well_formed P X B = true ∧
        B.proposer? = some (P.proposer B.slot) ∧ B.parent.slot < B.slot

/-- `TreeStamped n`: every block of the tree `n.S.T` has a stamp in `n.A`.

The variables:
- `n`: the node state.

Read aloud: every block of the tree is stamped. -/
def TreeStamped (n : NodeState V) : Prop :=
  ∀ B ∈ n.S.T, n.A.timestamp_block B ≠ none

/-- `StampsBounded n`: the stamp of every block of the tree, and of every vote of the pool, is at
most the node's clock `n.t`.

The variables:
- `n`: the node state.

Read aloud: nothing the node holds is stamped later than its clock. -/
def StampsBounded (n : NodeState V) : Prop :=
  (∀ B ∈ n.S.T, ∀ τ : Stamp, n.A.timestamp_block B = some τ → τ ≤ (n.t : Stamp)) ∧
    ∀ s : Slot, ∀ vote ∈ n.A.gf_votes s, ∀ τ : Stamp,
      n.A.timestamp_vote vote = some τ → τ ≤ (n.t : Stamp)

/-- `StampOrder n`: every non-genesis block of the tree and its parent are stamped, the parent no
later than the block.

The variables:
- `n`: the node state.

Read aloud: a block of the tree is stamped no earlier than its parent. -/
def StampOrder (n : NodeState V) : Prop :=
  ∀ B ∈ n.S.T, B ≠ Block.genesis →
    ∃ τ τ' : Stamp, n.A.timestamp_block B.parent = some τ ∧
      n.A.timestamp_block B = some τ' ∧ τ ≤ τ'

/-- `PoolAttestationsWellFormed S`: every attestation of the pool `S.attestations` of the FG state
`S` is well formed (`attestation_well_formed`).

The variables:
- `S`: the FG state.

Read aloud: the node holds in its pool of attestations only attestations of the form of an
attestation. -/
def PoolAttestationsWellFormed (S : FGState V) : Prop :=
  ∀ a ∈ S.attestations, attestation_well_formed a = true

/-- `LockBelowJustified n`: whenever the anti-slashing record `n.Λ` of the node state `n` holds a
lock at a height `h`, `h` is at most the cache `n.S.h_j`.

The variables:
- `n`: the node state.

Read aloud: a lock of the record at a height means the cache `h_j` is at least that height.

 -/
def LockBelowJustified (n : NodeState V) : Prop :=
  ∀ (h : Height) (T : BlockId), n.Λ.lock h = some T → h ≤ n.S.h_j

/-- `NodeInv C P X n`: the node state `n` holds `PoolKeyed`, `PoolStamped`, `TreeClosed`, its
finalized block in its tree, `TreeStamped`, `ChainStatesComputed`, `AttestationsValid`,
`StampsBounded`, `StampOrder`, no two blocks of its tree share a root
(`RootsNameBlocksIn n.S.T`) together with `FinalizedAncestorJustified n.S` and
`HeightCacheBounds n.S`, and with `JustificationCacheBounds n.S`, `JustifiedHeight n.S`,
`JustifiedInTree n.S`, `LockBelowJustified n` and the consistency of its anti-slashing record
(`RecordConsistent n.Λ`), and every attestation of its pool is well formed
(`PoolAttestationsWellFormed n.S`).

The variables:
- `C`: the parameters; `P`: the values given to the node; `X`: the digest; `n`: the node state.

Read aloud: every Goldfish vote filed under a slot has that slot and a validator of that slot's
committee, and is stamped. The genesis block is in the tree; every other block of the tree has its
parent in the tree, is well formed, has its slot's proposer, and a parent of an earlier slot. The
finalized block is in the tree. Every block of the tree is stamped, with a stamp at most the
node's clock, no earlier than its parent's stamp; every pool vote's stamp is at most the clock.
The chain state the node holds for a block of the tree is the one computed from the block alone,
and every attestation a non-genesis block of the tree includes is valid against the chain state
the node holds for the block's parent. No two blocks of the tree have the same root; the finalized
block is the justified block or an ancestor of it; no block of the tree has a chain-state height
greater than the cache `h_max`. No block of the tree on the finalized block's chain has a
justification height greater than the cache `h_j`; the justified block is the genesis block or has
the chain-state height `h_j`, and is in the tree; every lock of the anti-slashing record is at a
height at most `h_j`; and the record is consistent. Every attestation of the pool of attestations
is well formed.

  they sit in parentheses with
`RootsNameBlocksIn n.S.T` so that every other clause keeps the position at which proofs elsewhere
read it.  -/
def NodeInv (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) : Prop :=
  PoolKeyed P n.A ∧ PoolStamped n.A ∧ TreeClosed P X n.S ∧ n.S.F ∈ n.S.T ∧ TreeStamped n ∧
    ChainStatesComputed C n.S ∧ AttestationsValid n.S ∧ StampsBounded n ∧ StampOrder n ∧
      (RootsNameBlocksIn n.S.T ∧ (FinalizedAncestorJustified n.S ∧ HeightCacheBounds n.S) ∧
        (JustificationCacheBounds n.S ∧ JustifiedHeight n.S ∧ JustifiedInTree n.S ∧
          LockBelowJustified n ∧ RecordConsistent n.Λ)) ∧
        PoolAttestationsWellFormed n.S

end

end GoldilocksCorrectness.Statements.Routines
