module
public import Goldilocks.Config
public import Goldilocks.Objects
public import Spec2.Defs.Notation

@[expose] public section

/-!
# The chain state and its transition

A chain state `σ` is what a block's chain says about the finality gadget: the latest block `σ.L`
and its slot `σ.s`; the current height `σ.h` and the block `σ.T_h` that took the chain into it;
the validators counted at the current height, `σ.target_participation` and `σ.progress`; the
justifications waiting to be finalized, `σ.pending_finality`, with the validators counted for each
of them, `σ.finality_participation[j]`; the latest justification `σ.J` with its height `σ.h_j`;
and the latest finalization `σ.F` with its height `σ.h_F`. The chain state of a block is computed
from the chain state of its parent.

This file declares, in the namespace `Goldilocks`:

- `PendingPair V`, a justification waiting to be finalized, and `ChainState V`;
- `ChainState.initial`, the chain state of the genesis block;
- `is_pending`, whether a finality pair names a pending justification, and `valid_attestation`,
  whether an attestation may be included in a block whose parent has the chain state `σ`;
- `process_attestation`, what one attestation adds to a chain state;
- `advance_height`, `newest` and `process_height_events`: moving to the next height, the newest
  pending justifications, and the height events;
- `process_attestations` and `state_transition`: the chain state of a block, computed from its
  parent's.

A set of validators is a quorum when its size is at least `quorum V`.

This file holds definitions only.
-/

open scoped DC

namespace Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The chain state -/

/-- A justification waiting to be finalized. -/
structure PendingPair (V : Type) where
  /-- The height at which the chain justified the block `T`. -/
  j : Height
  /-- The justified block. -/
  T : Block V
deriving DecidableEq

/-- What a block's chain says about the finality gadget. -/
structure ChainState (V : Type) where
  /-- The latest block. -/
  L : Block V
  /-- The slot of the latest block. -/
  s : Slot
  /-- The current height. -/
  h : Height
  /-- The block that took the chain into the height `h`. -/
  T_h : Block V
  /-- The validators whose target vote at the height `h` for the block `T_h` has been counted. -/
  target_participation : Finset V
  /-- The validators whose target vote or timeout at the height `h` for the block `T_h` has been
  counted. -/
  progress : Finset V
  /-- The justifications not yet finalized: at most `K_W` pairs, in increasing order of their
  heights `j`, each with `h_F < j ≤ h_j`. -/
  pending_finality : List (PendingPair V)
  /-- `finality_participation j`: the validators whose finality pair names the pending
  justification of height `j` and has been counted. -/
  finality_participation : (j : Height) → Finset V
  /-- The latest justified block. -/
  J : Block V
  /-- The height at which `J` was justified. -/
  h_j : Height
  /-- The latest finalized block. -/
  F : Block V
  /-- The height at which `F` was justified. -/
  h_F : Height

/-- The chain state of the genesis block: the blocks `L`, `T_h`, `J` and `F` are the genesis
block; the slot `s` is `0`; the height `h` is `1`; the heights `h_j` and `h_F` are `0`; no
validator is counted, and no justification is pending. -/
@[no_expose] def ChainState.initial : ChainState V where
  L := .genesis
  s := 0
  h := 1
  T_h := .genesis
  target_participation := ∅
  progress := ∅
  pending_finality := []
  finality_participation := fun _ => ∅
  J := .genesis
  h_j := 0
  F := .genesis
  h_F := 0

/-! ## The attestations a block may include -/

/-- `is_pending σ p`: whether the finality pair `p` names a pending justification of `σ`: some
pair of `σ.pending_finality` has the height `p.hf` and a block whose root is `p.Tf`. -/
@[no_expose] def is_pending (σ : ChainState V) (p : FinalityPair) : Bool :=
  ∃ e ∈ σ.pending_finality, e.j = p.hf ∧ e.T.root = p.Tf

/-- `valid_attestation σ a`: whether the attestation `a` may be included in a block whose parent
has the chain state `σ`:

1. `true` when `a` votes at the height `σ.h` for the block `σ.T_h`;
2. otherwise, `true` when `a` has a finality pair `p`, `p` names a pending justification of `σ`
   (`is_pending`), and `p.hf < a.h < σ.h`;
3. otherwise `false`. -/
@[no_expose] def valid_attestation (σ : ChainState V) (a : Attestation V) : Bool := Id.run do
  if a.h = σ.h && a.T = σ.T_h.root then
    return true
  if a.finality_pair ≠ none then
    let p := a.finality_pair.value
    return is_pending σ p && p.hf < a.h && a.h < σ.h
  return false

/-! ## One attestation -/

/-- The chain state `σ` with the attestation `a` counted. Write `v` for `a`'s validator. The two
tests are independent.

1. If `a` has a finality pair `p` that names a pending justification of `σ` (`is_pending`), `v`
   is added to `σ.finality_participation[p.hf]`.
2. If `a` votes at the height `σ.h` for the block `σ.T_h`, `v` is added to `σ.progress`, and, when
   the vote is a target vote (`a.τ` is `false`), to `σ.target_participation` too.

Blocks are compared by their roots: an attestation names a block by its root. -/
@[no_expose] def process_attestation (σ : ChainState V) (a : Attestation V) : ChainState V := Id.run do
  let mut σ := σ
  let v := a.val_index
  if a.finality_pair ≠ none then
    let p := a.finality_pair.value
    if is_pending σ p then
      σ.finality_participation[p.hf] ← σ.finality_participation[p.hf] ∪ {v}
  if a.h = σ.h && a.T = σ.T_h.root then
    σ.progress ← σ.progress ∪ {v}
    if !a.τ then
      σ.target_participation ← σ.target_participation ∪ {v}
  return σ

/-! ## The height events -/

/-- The chain state `σ` moved to the next height: the height `σ.h` is increased by one, the block
`σ.T_h` that took the chain into it becomes the latest block `σ.L`, and the sets
`σ.target_participation` and `σ.progress` are emptied. -/
@[no_expose] def advance_height (σ : ChainState V) : ChainState V := Id.run do
  let mut σ := σ
  σ.h ← σ.h + 1
  σ.T_h ← σ.L
  σ.target_participation, σ.progress ← ∅
  return σ

/-- `newest K_W l`: the last `K_W` elements of the list `l`, or the whole of `l` when it has at
most `K_W` elements. -/
@[no_expose] def newest (K_W : Nat) (l : List (PendingPair V)) : List (PendingPair V) :=
  l.drop (l.length - K_W)

/-- The height events of the chain state `σ`, in this order. Write `q` for `quorum V`.

1. Finalization: for each pending justification `e` of `σ.pending_finality` whose validators
   `σ.finality_participation[e.j]` are a quorum, the finalized block and its height `(σ.F, σ.h_F)`
   become `(e.T, e.j)`. The list is in increasing order of the heights, so the pair that remains
   written is the quorate one of greatest height.
2. The pending justifications of height at most `σ.h_F` are dropped.
3. Justification: if the validators of `σ.target_participation` are a quorum, the justified block
   and its height `(σ.J, σ.h_j)` become `(σ.T_h, σ.h)`; the pair `(σ.h, σ.T_h)` is appended to
   `σ.pending_finality` with no validator counted for it; only the newest `C.K_W` pairs are kept
   (`newest`); and the result is that state moved to the next height (`advance_height`).
4. Timeout: otherwise, if the validators of `σ.progress` are a quorum and the slot `σ.s` is at
   least `C.δt` slots after the slot of `σ.T_h`, the result is the state moved to the next height.

Otherwise the result is `σ` as steps 1 and 2 left it. -/
@[no_expose] def process_height_events (C : Config) (σ : ChainState V) : ChainState V := Id.run do
  let mut σ := σ
  let q := quorum V
  for e in σ.pending_finality do
    if q ≤ |σ.finality_participation[e.j]| then
      σ.F ← e.T
      σ.h_F ← e.j
  σ.pending_finality ← σ.pending_finality.filter (fun e => σ.h_F < e.j)
  if q ≤ |σ.target_participation| then
    σ.J ← σ.T_h
    σ.h_j ← σ.h
    σ.pending_finality ← σ.pending_finality ++ [PendingPair.mk (j := σ.h) (T := σ.T_h)]
    σ.finality_participation[σ.h] ← ∅
    σ.pending_finality ← newest C.K_W σ.pending_finality
    return advance_height σ
  if q ≤ |σ.progress| && σ.T_h.slot + C.δt ≤ σ.s then
    return advance_height σ
  return σ

/-! ## The chain state of a block -/

/-- The chain state `σ` after the attestations `atts` of the block `B` are counted, before the
height events. The slot `σ.s` becomes `B`'s slot. Each element of `atts` is counted in list order
with `process_attestation`. The latest block `σ.L` becomes `B`. -/
@[no_expose] def process_attestations (σ : ChainState V) (B : Block V) (atts : List (Attestation V)) :
    ChainState V := Id.run do
  let mut σ := σ
  σ.s ← B.slot
  for a in atts do
    σ ← process_attestation σ a
  σ.L ← B
  return σ

/-- The chain state of the block `B`, computed from the chain state `σ` of its parent, in two
steps:

1. the attestations `B` includes are counted (`process_attestations`), with `B` as the latest
   block;
2. the height events of the chain state so updated are applied (`process_height_events`).

It cannot fail. What a block must satisfy against `σ` (its proposer, a parent of an earlier slot,
every attestation it includes valid by `valid_attestation`) is tested before it is called, by the
node's test of a block, `block_admissible`. -/
@[no_expose] def state_transition (C : Config) (σ : ChainState V) (B : Block V) : ChainState V := Id.run do
  let mut σ := σ
  σ ← process_attestations σ B B.attestations
  σ ← process_height_events C σ
  return σ

end Goldilocks
