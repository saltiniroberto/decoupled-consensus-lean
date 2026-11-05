module
public import Goldilocks.FG.ChainState
public import Goldilocks.FG.ValidatorClient
public import Spec2.Defs.Notation

@[expose] public section

/-!
# The FG state, the frame and the handlers of the finality gadget

The FG state `S` is what the finality gadget keeps: the tree `S.T` of the blocks it has accepted;
the chain state `S.σ[B]` of each accepted block `B`; the finalized block `S.F`; the justified
block `S.J` with its height `S.h_j`; the greatest chain-state height `S.h_max` of an accepted
block; and the pool `S.attestations` of the attestations it has received, one copy of each, in
the order of first acceptance. `S.F`, `S.J`, `S.h_j` and `S.h_max` are the finality caches: they
are computed from the chain states of the accepted blocks, block by block, as each is accepted.

The frame `Φ` (`Frame V`) is what the finality gadget gives the available chain. It is computed
from `S` each time it is read (`fg_to_ac`).

This file declares, in the namespace `Goldilocks`:

- `FGState V`, the FG state, and its initial value `FGState.initial`;
- the readers of the finality caches: `fg_contest`, whether the FG state is contested;
  `head_height_floor`, the least chain-state height of a viable block; `get_fc_root`, the root of
  the fork choice; `is_viable` and `has_viable_descendant`; and `fg_to_ac`, the frame;
- `update_finality`, the finality caches updated from one chain state;
- the handlers: `fg_on_attestation`, an attestation received; `fg_on_block`, the writes of an
  accepted block; and `fg_attest`, the attestation of the validator from a source and a head;
- `attestations_on_chain` and `on_chain`, the attestations a chain includes; and
  `proposal_attestations`, the attestations of the pool a block on a given parent includes.

The tests that refuse a block are not in this file: the node runs them, all together, before it
calls `fg_on_block`.

This file holds definitions only.
-/

open scoped DC

namespace Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The FG state -/

/-- What the finality gadget keeps. -/
structure FGState (V : Type) where
  /-- The tree of accepted blocks. A block enters it only when the finalized block `F` is an
  ancestor of it or the block itself, and no block leaves it. -/
  T : Finset (Block V)
  /-- `σ B`: the chain state of the accepted block `B`, computed once, when `B` was accepted. A
  block not accepted reads the chain state of the genesis block, `ChainState.initial`. -/
  σ : (B : Block V) → ChainState V
  /-- The finalized block. -/
  F : Block V
  /-- The justified block: the justification, of all those of the chain states of accepted
  blocks of which `F` is an ancestor or which is `F`, that is greatest by its height and then by
  its root. -/
  J : Block V
  /-- The height at which `J` was justified. -/
  h_j : Height
  /-- The greatest chain-state height `σ[B].h` of an accepted block `B`. -/
  h_max : Height
  /-- The pool: every attestation received, one copy of each, in the order of first acceptance.
  It is read only to choose the attestations a proposed block includes. -/
  attestations : List (Attestation V)

/-- The initial FG state: the tree holds the genesis block alone; every block reads the chain
state of the genesis block, `ChainState.initial`; the finalized and the justified blocks are the
genesis block; the justification height is `0`; the greatest chain-state height is `1`; the pool
is empty. -/
@[no_expose] def FGState.initial : FGState V where
  T := {Block.genesis}
  σ := fun _ => ChainState.initial
  F := Block.genesis
  J := Block.genesis
  h_j := 0
  h_max := 1
  attestations := []

/-! ## The readers of the finality caches -/

/-- `fg_contest S`: whether the FG state `S` is contested.

1. If `S.h_max` is not `S.h_j + 1`, it is not.
2. Otherwise it is when some accepted block `B` of `S.T`, of which `S.F` is an ancestor or which
   is `S.F`, has the chain-state height `S.σ[B].h = S.h_max`, and `S.J` is neither an ancestor
   of `B` nor `B`.

The test reads the whole tree `S.T`, and no tree of a voter. -/
@[no_expose] def fg_contest (S : FGState V) : Bool := Id.run do
  if S.h_max ≠ S.h_j + 1 then
    return false
  return (∃ B ∈ S.T, S.F.ancestorEq B ∧ S.σ[B].h = S.h_max ∧ ¬ S.J.ancestorEq B : Bool)

/-- `head_height_floor S`: the least chain-state height of a viable block: `S.h_max` when the FG
state is contested (`fg_contest`), and `S.h_max − 1` otherwise. -/
@[no_expose] def head_height_floor (S : FGState V) : Height := Id.run do
  if fg_contest S then
    return S.h_max
  return S.h_max - 1

/-- `get_fc_root S`: the root of the fork choice: the justified block `S.J` when `S.h_max` is
`S.h_j + 1` and the FG state is not contested (`fg_contest`), and the finalized block `S.F`
otherwise. -/
@[no_expose] def get_fc_root (S : FGState V) : Block V := Id.run do
  if S.h_max = S.h_j + 1 && !fg_contest S then
    return S.J
  return S.F

/-- `is_viable S B`: whether the block `B` is viable: its chain-state height `S.σ[B].h` is at
least the floor `head_height_floor S`. -/
@[no_expose] def is_viable (S : FGState V) (B : Block V) : Bool :=
  head_height_floor S ≤ S.σ[B].h

/-- `has_viable_descendant S B`: whether some accepted block `B'` of `S.T`, of which `B` is an
ancestor or which is `B`, is viable (`is_viable`). -/
@[no_expose] def has_viable_descendant (S : FGState V) (B : Block V) : Bool :=
  ∃ B' ∈ S.T, B.ancestorEq B' ∧ is_viable S B'

/-- `fg_to_ac S`: the frame the finality gadget gives the available chain:

1. `tree`: the accepted blocks of `S.T` of which `S.F` is an ancestor or which are `S.F`;
2. `fc_root`: the root of the fork choice, `get_fc_root S`;
3. `viable_heads`: the blocks of `tree` of which `fc_root` is an ancestor or which are `fc_root`,
   and which are viable (`is_viable`);
4. `F`: the finalized block `S.F`, the root of `tree`. -/
@[no_expose] def fg_to_ac (S : FGState V) : Frame V := Id.run do
  let tree := {B ∈ S.T | S.F.ancestorEq B}
  let fc_root := get_fc_root S
  let viable_heads := {B ∈ tree | fc_root.ancestorEq B && is_viable S B}
  return Frame.mk (tree := tree) (fc_root := fc_root) (viable_heads := viable_heads) (F := S.F)

/-! ## The finality update -/

section Finality

variable [RootOrder]

/-- The FG state `S` with its finality caches updated from the chain state `σ`. Three steps, in
order, each reading `S` as the step before it left it:

1. the greatest chain-state height `S.h_max` becomes the greater of itself and `σ.h`;
2. if the finalized block `S.F` is an ancestor of `σ.J` or `σ.J` itself, and the justification
   of `σ` is greater than that of `S` — `S.h_j < σ.h_j`, or `S.h_j = σ.h_j` and the root of `S.J`
   comes before the root of `σ.J` in the root order (`RootOrder.before`) — then the justified
   block and its height become `σ.J` and `σ.h_j`;
3. if `S.F` is an ancestor of `σ.F` and is not `σ.F`, `σ.F` is an ancestor of the justified block
   `S.J` (as step 2 left it) or `S.J` itself, and `σ.F` has a viable descendant
   (`has_viable_descendant`, read with the `S.h_max` of step 1), the finalized block becomes
   `σ.F`. -/
@[no_expose] def update_finality (S : FGState V) (σ : ChainState V) : FGState V := Id.run do
  let mut S := S
  S.h_max ← max S.h_max σ.h
  if S.F.ancestorEq σ.J &&
      (S.h_j < σ.h_j || (S.h_j = σ.h_j && RootOrder.before S.J.root σ.J.root)) then
    S.J ← σ.J
    S.h_j ← σ.h_j
  if S.F.ancestorStrict σ.F && σ.F.ancestorEq S.J && has_viable_descendant S σ.F then
    S.F ← σ.F
  return S

/-! ## The handlers -/

/-- The FG state `S` with the attestation `a` received: `a` is appended to the pool
`S.attestations` when the pool does not hold it already. -/
@[no_expose] def fg_on_attestation (S : FGState V) (a : Attestation V) : FGState V := Id.run do
  let mut S := S
  if a ∉ S.attestations then
    S.attestations ← S.attestations ++ [a]
  return S

/-- The FG state `S` with the block `B` accepted. Its caller has tested every refusal of `B`
first (`block_admissible`, the node's test of a block); this routine only writes. In order:

1. the chain state of `B`, `S.σ[B]`, is computed by `state_transition` from the chain state
   `S.σ[B.parent]` of its parent and from `B`;
2. `B` enters the tree `S.T`;
3. the finality caches are updated from the chain state of `B` (`update_finality`);
4. each attestation of `B.attestations` is received into the pool, in list order
   (`fg_on_attestation`). -/
@[no_expose] def fg_on_block (C : Config) (S : FGState V) (B : Block V) : FGState V := Id.run do
  let mut S := S
  S.σ[B] ← state_transition C S.σ[B.parent] B
  S.T ← S.T ∪ {B}
  S ← update_finality S S.σ[B]
  for a in B.attestations do
    S ← fg_on_attestation S a
  return S

end Finality

/-- The attestation the validator `v` sends from the source block `source` and the head block
`head`, built from its anti-slashing record `Λ`, together with the record after it; `none` in
place of the attestation when it sends none. The source gives the height `h_c` of its chain state
and the root `T_c` of the block that took that chain state into the height; the head gives the
justification height `h_j`, the root `J` of the justified block and the finalization height `h_F`
of its chain state. `create_attestation` decides the attestation from these and `Λ`. -/
@[no_expose] def fg_attest (S : FGState V) (Λ : SigningHistory) (v : V) (source head : Block V) :
    SigningHistory × Option (Attestation V) := Id.run do
  let (h_c, T_c) := (S.σ[source].h, S.σ[source].T_h.root)
  let (h_j, J, h_F) := (S.σ[head].h_j, S.σ[head].J.root, S.σ[head].h_F)
  return create_attestation Λ v h_c T_c h_j J h_F

/-! ## The attestations of a proposal -/

/-- The attestations included in the block `B` and in each of its ancestors: those of `B` first,
then those of its parent's chain; none for the genesis block. -/
@[no_expose] def attestations_on_chain : Block V → List (Attestation V)
  | .genesis => []
  | .node parent _ _ _ _ atts _ => atts ++ attestations_on_chain parent

/-- `on_chain a H`: whether the attestation `a` is included in the block `H` or in one of its
ancestors (`attestations_on_chain H`). -/
@[no_expose] def on_chain (a : Attestation V) (H : Block V) : Bool :=
  a ∈ attestations_on_chain H

/-- `proposal_attestations S H`: the attestations of the pool `S.attestations` that a block whose
parent is `H` includes, in the pool's order: those valid against the chain state `S.σ[H]` of `H`
(`valid_attestation`) and not already included in `H` or in one of its ancestors
(`on_chain`). -/
@[no_expose] def proposal_attestations (S : FGState V) (H : Block V) : List (Attestation V) :=
  S.attestations.filter (fun a => valid_attestation S.σ[H] a && !on_chain a H)

end Goldilocks
