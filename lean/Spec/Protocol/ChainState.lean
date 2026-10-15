import Spec.Config
import Spec.Objects
import Spec.Defs.Notation

/-!
# The chain-state transition

A chain state `σ` is what a block's chain says about the finality gadget: the latest block `σ.L`
and its slot `σ.s`; the current height `σ.h` and the block `σ.T_h` that entered it; the flag
`σ.nj`, whether the current height is nonjustifiable; the three sets of validators
`σ.target_participation`, `σ.progress` and `σ.finalize` counted at the current height; the
justified block `σ.J` and its height `σ.h_j`; and the finalized block `σ.F` and its height
`σ.h_F`. The store holds one chain state per block, computed from the chain state of the block's
parent when the block is admitted.

This file declares, in the namespace `Spec.Protocol`:

- `ChainState.initial`: the chain state of the genesis block;
- `ChainState.targetQuorum`, `ChainState.progQuorum`, `ChainState.finalityQuorum`: whether each
  of the three sets of a chain state weighs a quorum;
- `nonjustifiable`: whether a height is nonjustifiable;
- `process_attestation`: what one attestation adds to a chain state;
- `finalityReady`, `targetReady`, `progReady`: the conditions of the three height events;
- `advance_height`, `process_height_events`: moving to the next height, and the three height
  events in order;
- `process_attestations`, `state_transition`: the chain state of a block, computed from its
  parent's.

The type `ChainState` is declared in `lean/Spec/Objects.lean`. A function on a chain state
is called as a function, `ChainState.targetQuorum P σ`, not with field notation.

This file holds definitions only.
-/

open scoped DC

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The initial chain state and the quorums -/

namespace ChainState

/-- The initial chain state, the chain state of the genesis block: the latest block `L`, the block
`T_h` that entered the current height, the justified block `J` and the finalized block `F` are
the genesis block; the slot `s` is `0`; the height `h` is `1`; the justified height `h_j` and the
finalized height `h_F` are `0`; the flag `nj` is false; and the three sets
`target_participation`, `progress` and `finalize` are empty. -/
def initial : ChainState V where
  L := .genesis
  s := 0
  h := 1
  T_h := .genesis
  nj := false
  target_participation := ∅
  progress := ∅
  finalize := ∅
  J := .genesis
  h_j := 0
  F := .genesis
  h_F := 0

/-- `targetQuorum P σ`: whether the validators whose target vote `σ` has counted at its current
height, `σ.target_participation`, weigh a quorum (`P.quorumCheck`). -/
def targetQuorum (P : Provisional V) (σ : ChainState V) : Bool :=
  P.quorumCheck σ.target_participation

/-- `progQuorum P σ`: whether the validators whose target vote or timeout vote `σ` has counted at
its current height, `σ.progress`, weigh a quorum (`P.quorumCheck`). -/
def progQuorum (P : Provisional V) (σ : ChainState V) : Bool :=
  P.quorumCheck σ.progress

/-- `finalityQuorum P σ`: whether the validators whose finality pair for the justified block `σ.J`
the chain state `σ` has counted, `σ.finalize`, weigh a quorum (`P.quorumCheck`). -/
def finalityQuorum (P : Provisional V) (σ : ChainState V) : Bool :=
  P.quorumCheck σ.finalize

end ChainState

/-! ## One attestation -/

/-- `nonjustifiable C h h_F`: whether the height `h` is nonjustifiable in a chain state whose
finalized height is `h_F`: `C.K` divides `h`, and `h − h_F` is greater than `C.D`. -/
def nonjustifiable (C : Config) (h h_F : Height) : Bool :=
  (C.K ∣ h) && (C.D < h - h_F)

/-- The chain state `σ` with the attestation `a` counted. Write `v` for `a`'s validator. The two
tests are independent, so one attestation can add `v` to the finality set and to the height sets.

1. If `σ`'s justified height is greater than its finalized height (`σ.h_F < σ.h_j`) and `a`'s
   finality pair is the pair `(σ.h_j, σ.J)`, `v` is added to `σ.finalize`.
2. If `a`'s height pair is the target vote at the height `σ.h` for the block `σ.T_h`, `v` is added
   to `σ.target_participation` and to `σ.progress`; otherwise, if it is the timeout vote at `σ.h`
   for `σ.T_h`, `v` is added to `σ.progress` only. Any other height pair (another height, another
   block, or the empty pair) adds nothing.

Blocks are compared by their roots: an attestation names a block by its root. -/
def process_attestation (σ : ChainState V) (a : Attestation V) : ChainState V := Id.run do
  let mut σ := σ
  let v := a.val_index
  if σ.h_F < σ.h_j &&
      a.finality_pair = FinalityPair.mk (height := σ.h_j) (target := σ.J.root) then
    σ.finalize ← σ.finalize ∪ {v}
  if a.height_pair = .vote σ.h σ.T_h.root false then
    σ.target_participation ← σ.target_participation ∪ {v}
    σ.progress ← σ.progress ∪ {v}
  else if a.height_pair = .vote σ.h σ.T_h.root true then
    σ.progress ← σ.progress ∪ {v}
  return σ

/-! ## The height events -/

/-- `finalityReady P σ`: the condition of the finality event: `σ`'s justified height is greater
than its finalized height, and the validators of `σ.finalize` weigh a quorum. -/
def finalityReady (P : Provisional V) (σ : ChainState V) : Bool :=
  (σ.h_F < σ.h_j) && ChainState.finalityQuorum P σ

/-- `targetReady P σ`: the condition of the justification event: `σ`'s current height is not
nonjustifiable (`σ.nj` is false), and the validators of `σ.target_participation` weigh a
quorum. -/
def targetReady (P : Provisional V) (σ : ChainState V) : Bool :=
  !σ.nj && ChainState.targetQuorum P σ

/-- `progReady C P σ`: the condition of the progress event: the validators of
`σ.target_participation` weigh a quorum; or the slot `σ.s` is at least `C.timeoutDelay` slots
after the slot of `σ.T_h`, and the validators of `σ.progress` weigh a quorum. -/
def progReady (C : Config) (P : Provisional V) (σ : ChainState V) : Bool :=
  ChainState.targetQuorum P σ ||
    ((σ.T_h.slot + C.timeoutDelay ≤ σ.s) && ChainState.progQuorum P σ)

/-- The chain state `σ` moved to the next height. The height `σ.h` is increased by one. The latest
block `σ.L` becomes `σ.T_h`, the block that entered the new height. The flag `σ.nj` is computed
for the new height and `σ.h_F` (`nonjustifiable`). The sets `σ.target_participation` and
`σ.progress` are emptied.

`σ.finalize` is not emptied: only the justification event empties it. -/
def advance_height (C : Config) (σ : ChainState V) : ChainState V := Id.run do
  let mut σ := σ
  σ.h ← σ.h + 1
  σ.T_h ← σ.L
  σ.nj ← nonjustifiable C σ.h σ.h_F
  σ.target_participation, σ.progress ← ∅
  return σ

/-- The three height events of the chain state `σ`, tested once each, in this order.

1. Finality: if `finalityReady P σ`, the finalized block and its height `(σ.F, σ.h_F)` become
   `(σ.J, σ.h_j)`; the next test reads the state so updated.
2. Justification: if `targetReady P σ`, the justified block and its height `(σ.J, σ.h_j)` become
   `(σ.T_h, σ.h)`, `σ.finalize` is emptied, and the result is that state moved to the next height
   (`advance_height`).
3. Progress: otherwise, if `progReady C P σ`, the result is the state moved to the next height.

Otherwise the result is `σ` as the finality event left it. -/
def process_height_events (C : Config) (P : Provisional V) (σ : ChainState V) :
    ChainState V := Id.run do
  let mut σ := σ
  if finalityReady P σ then
    σ.F ← σ.J
    σ.h_F ← σ.h_j
  if targetReady P σ then
    σ.J ← σ.T_h
    σ.h_j ← σ.h
    σ.finalize ← ∅
    return advance_height C σ
  if progReady C P σ then
    return advance_height C σ
  return σ

/-! ## The chain state of a block -/

/-- The chain state `σ` after the attestations `atts` of the block `B` are counted, before the
height events. The slot `σ.s` becomes `B`'s slot. Each element of `atts` is counted in list order
with `process_attestation`. The latest block `σ.L` becomes `B`. -/
def process_attestations (σ : ChainState V) (B : Block V) (atts : List (Attestation V)) :
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
2. the height events of the chain state so updated are tested once (`process_height_events`). -/
def state_transition (C : Config) (P : Provisional V) (σ : ChainState V) (B : Block V) :
    ChainState V := Id.run do
  let mut σ := σ
  σ ← process_attestations σ B B.attestations
  σ ← process_height_events C P σ
  return σ

end Spec.Protocol
