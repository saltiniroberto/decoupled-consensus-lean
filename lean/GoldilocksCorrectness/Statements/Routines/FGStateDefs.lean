module
public import Goldilocks.FG.State
public import GoldilocksCorrectness.Statements.Routines.ChainStateDefs

@[expose] public section

/-!
# Conditions on an FG state

`FinalizedFromChain C S`, `ChainStatesComputed C S`, `AttestationsValid S`,
`FinalizedAncestorJustified S`, `HeightCacheBounds S`, `JustificationCacheBounds S`,
`JustifiedHeight S` and `JustifiedInTree S`: conditions on one FG state `S` (its caches, its tree
and the chain states it holds), each stated in its own docstring. Nothing is proved here.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `FinalizedFromChain C S`: the finalized block `S.F` of the FG state `S` is the finalized block
of the chain state `chainStateOf C B` of a block `B` of the tree `S.T`.

The variables:
- `C`: the parameters; `S`: the FG state.

Read aloud: the finalized block of the FG state is the finalized block of the chain state of a
block of its tree. -/
def FinalizedFromChain (C : Config) (S : FGState V) : Prop :=
  ∃ B ∈ S.T, S.F = (chainStateOf C B).F

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `ChainStatesComputed C S`: the chain state `S` holds for each block of its tree is the one
computed from the block alone, `chainStateOf C B`.

The variables:
- `C`: the parameters; `S`: the FG state.

Read aloud: the node's chain states of its tree are the blocks' own. -/
def ChainStatesComputed (C : Config) (S : FGState V) : Prop :=
  ∀ B ∈ S.T, S.σ B = chainStateOf C B

/-- `AttestationsValid S`: every attestation a non-genesis block of the tree `S.T` includes is
valid against the chain state `S` holds for the block's parent.

The variables:
- `S`: the FG state.

Read aloud: every included attestation is valid against the parent's chain state. -/
def AttestationsValid (S : FGState V) : Prop :=
  ∀ B ∈ S.T, B ≠ Block.genesis →
    ∀ a ∈ B.attestations, valid_attestation (S.σ B.parent) a = true

/-- `FinalizedAncestorJustified S`: the finalized block `S.F` of the FG state `S` is the justified
block `S.J` or an ancestor of it.

The variables:
- `S`: the FG state.

Read aloud: the finalized block is on the justified block's chain.

 -/
def FinalizedAncestorJustified (S : FGState V) : Prop := S.F.AncestorEq S.J

/-- `HeightCacheBounds S`: no block of the tree `S.T` of the FG state `S` has a chain-state height
`(S.σ B).h` greater than the cache `S.h_max`.

The variables:
- `S`: the FG state.

Read aloud: the cache `h_max` is at least the chain-state height of every accepted block.

 -/
def HeightCacheBounds (S : FGState V) : Prop := ∀ B ∈ S.T, (S.σ B).h ≤ S.h_max

/-- `JustificationCacheBounds S`: no block `B` of the tree `S.T` of the FG state `S` that is the
finalized block `S.F` or a descendant of it has a justification height `(S.σ B).h_j` greater than
the cache `S.h_j`.

The variables:
- `S`: the FG state.

Read aloud: no accepted block on the finalized block's chain has a justification height greater
than the cache `h_j`.

 -/
def JustificationCacheBounds (S : FGState V) : Prop :=
  ∀ B ∈ S.T, S.F.AncestorEq B → (S.σ B).h_j ≤ S.h_j

/-- `JustifiedHeight S`: the justified block `S.J` of the FG state `S` is the genesis block, or its
chain-state height `(S.σ S.J).h` is the justification height `S.h_j`.

The variables:
- `S`: the FG state.

Read aloud: the justified block's own chain-state height is the justification height, the genesis
block excepted (it has height `1` and is justified at `0` by convention).

 -/
def JustifiedHeight (S : FGState V) : Prop :=
  S.J = Block.genesis ∨ (S.σ S.J).h = S.h_j

/-- `JustifiedInTree S`: the justified block `S.J` of the FG state `S` is in its tree `S.T`.

The variables:
- `S`: the FG state.

Read aloud: the justified block is accepted.

 -/
def JustifiedInTree (S : FGState V) : Prop := S.J ∈ S.T

end

end GoldilocksCorrectness.Statements.Routines
