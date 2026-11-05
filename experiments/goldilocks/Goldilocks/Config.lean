module
public import Goldilocks.Objects

@[expose] public section

/-!
# The node's parameters

The routines of Goldilocks read three records.

- `Config`: every parameter a node knows, fixed for the whole protocol: the schedule unit `Δ`, the
  delay `Δ_F` of attestations, the round length `R`, the bound `K_W` on the justifications a chain
  state keeps waiting for finalization, the timeout delay `δt` and the slow window `k`, with their
  conditions.
- `Provisional V`: values given to the node for now: the proposer and the committee of each slot.
- `External V`: the values another piece of software supplies to the node: the digest that gives
  a block its root.

A routine takes `(C : Config)`, also `(P : Provisional V)` when it reads one of the values of
`Provisional V`, and also `(X : External V)` when it reads the digest, directly or through a
routine it calls.

This file declares, in the namespace `Goldilocks`, the three structures and the readers of the
schedule, written on `C`: `C.t_`, `C.slot`, `C.round`, `C.T_` and `C.a_`. The five times of a
slot's duties after its start are written where they are read, as `C.t_ s + C.Δ`.

This file holds definitions only.
-/

namespace Goldilocks

/-- Every parameter a node knows. They are fixed for the whole protocol. -/
structure Config where
  /-- `Δ`: the schedule unit. Slot `s` starts at `4 * Δ * s`, and the duties of a slot fall at
  whole multiples of `Δ` after its start. The protocol is designed for blocks and Goldfish votes
  delivered within `Δ`. -/
  Δ : Time
  /-- `Δ` is positive, so the start `4 * Δ * s` of slot `s` is strictly increasing in `s`. -/
  Δ_pos : 0 < Δ
  /-- `Δ_F`: the delay the protocol is designed for in the delivery of attestations. -/
  Δ_F : Time
  /-- `Δ ≤ Δ_F`. -/
  Δ_F_ge : Δ ≤ Δ_F
  /-- `R`: the number of slots in a round. Round `r` is the slots `r * R` to `r * R + R − 1`. -/
  R : Nat
  /-- `R ≥ 2`. -/
  R_ge_two : 2 ≤ R
  /-- `R ≥ ⌈(6 * Δ + Δ_F) / (4 * Δ)⌉`, written without the ceiling: a round, `4 * Δ * R` long,
  lasts at least `6 * Δ + Δ_F`. So `Δ_F` after round `r`'s action time `6 * Δ` after its opening
  is no later than the opening of round `r + 1`. -/
  R_covers : 6 * Δ + Δ_F ≤ 4 * Δ * (R : Time)
  /-- `K_W`: the number of justifications a chain state keeps waiting for finalization; it keeps
  the `K_W` of greatest height. -/
  K_W : Nat
  /-- `K_W ≥ 2`. -/
  K_W_ge_two : 2 ≤ K_W
  /-- `δt`: the timeout delay, in slots. A chain state moves to its next height without a
  justification only at a block whose slot is at least `δt` after the slot of the block that took
  the chain state into its current height. -/
  δt : Nat
  /-- `k`: the length of the slow window, in slots. A lock written by the confirmation update of
  slot `s` expires at `4 * Δ * (s + k) + 5 * Δ`. -/
  k : Nat
  /-- `k ≥ 2`. -/
  k_ge_two : 2 ≤ k

/-- Values given to the node for now, which the protocol could later compute from the chain. -/
structure Provisional (V : Type) where
  /-- `proposer s`: the validator whose block of slot `s` the node admits. -/
  proposer : (s : Slot) → V
  /-- `committee s`: the committee of slot `s`, the validators whose Goldfish votes for slot `s`
  the node admits, and who cast one in slot `s`. The whole set of validators at every slot is one
  value of this field. -/
  committee : (s : Slot) → Finset V

/-- The values another piece of software supplies to the node. -/
structure External (V : Type) where
  /-- `digest parent_root s attestations votes support_votes`: the root of a block with that
  content: the root of its parent, its slot, its attestations, its Goldfish votes and its
  support votes. No property of the function is assumed. -/
  digest : (parent_root : BlockId) → (s : Slot) → (attestations : List (Attestation V)) →
    (votes : List (GoldfishVote V)) → (support_votes : List (GoldfishVote V)) → BlockId

namespace Config

variable (C : Config)

/-! ## The schedule -/

/-- `t_s`: the time slot `s` starts, `4 * Δ * s`. -/
@[no_expose] def t_ (s : Slot) : Time := 4 * C.Δ * (s : Time)

/-- `slot(t)`: the slot that contains the time `t`, `⌊t / (4 * Δ)⌋`; a time before `0` is in
slot `0`. -/
@[no_expose] def slot (t : Time) : Slot := (Int.fdiv t (4 * C.Δ)).toNat

/-! ## The rounds -/

/-- `round(s)`: the round of slot `s`, `⌊s / R⌋`. -/
def round (s : Slot) : Round := s / C.R

/-- `T_r`: the opening time of round `r`, the start of its first slot `r * R`. -/
def T_ (r : Round) : Time := C.t_ (r * C.R)

/-- `a_r`: the action time of round `r`, `6 * Δ` after its opening time `T_r`. -/
def a_ (r : Round) : Time := C.T_ r + 6 * C.Δ

end Config

end Goldilocks
