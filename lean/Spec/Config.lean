import Spec.Objects

/-!
# The node's parameters

The routines of `Spec` read two records.

- `Config`: every parameter a node knows, fixed for the whole protocol: the schedule unit `Δ`, the
  round length `R`, the lookback `η_SG` of the strong gadget, and the finality gadget's constants
  `K`, `D` and `timeoutDelay`, with the conditions on `Δ`, `R`, `η_SG`, `K` and `D`.
- `Provisional V`: values given to the node for now, which the protocol will eventually compute
  from the chain: the proposer of each slot, the committee of each slot, and the weights of the
  validators.
- `External V`: the values another piece of software supplies to the node: the root of the block
  each validator proposes in each slot.

A routine takes `(C : Config)`, also `(P : Provisional V)` when it reads one of the values of
`Provisional V`, and also `(X : External V)` when it reads the root of a new block, directly or
through a routine it calls.

No record holds the instant after which delivery is bounded by `Δ`: that instant is a property of
an execution, not something a node knows.

This file declares, in the namespace `Spec`:

- the three structures `Config`, `Provisional V` and `External V`;
- the readers of the schedule that `Spec`'s routines call, written on `C`: `C.slotOf`,
  `C.round_of`, `C.round_attestation_time`, `C.proposal_time`, `C.vote_time`,
  `C.gf_confirmation_time`, `C.view_freeze`, `C.confirmation_time`, `C.opening`, `C.early`, and
  `Protocol.Phase.earlyOffset`, the offset of a grade result's first cutoff that `C.early` reads;
- the readers on `P`: the committee reader `P.committee`, and the weights `P.weightOf`,
  `P.totalWeight`, `P.finalityThreshold` and the quorum test `P.quorumCheck`.

Each reader is written from the fields of `C` or `P`.

This file holds definitions only.
-/

open Spec.Protocol (Phase)

namespace Spec

/-- Every parameter a node knows. They are fixed for the whole protocol. -/
structure Config where
  /-- `Δ`: the schedule unit. Slot `s` starts at `4 * Δ * s`, and the duties of a slot fall at
  whole multiples of `Δ` after its start. -/
  Δ : Time
  /-- `Δ` is positive, so the start `4 * Δ * s` of slot `s` is strictly increasing in `s`. -/
  Δ_pos : 0 < Δ
  /-- `R`: the number of slots in a round. Round `r` is the slots `r * R` to `r * R + R − 1`. -/
  R : Nat
  /-- `R ≥ 3`. Round `r`'s attestation instant is `6 * Δ` after the start of its first slot; with
  `R ≥ 3` it falls in the round's second slot, still inside round `r`. The grade-2 window of
  round `r + 1` opens `5 * Δ` before that round; an attestation of round `r` delivered within `Δ`
  lands inside it only when rounds are at least `12 * Δ` long. -/
  R_ge_three : 3 ≤ R
  /-- `η_SG`: the lookback of the strong gadget, in rounds. A store admits an attestation of a
  round only when the round is at most `η_SG` rounds before the store's own, and a grade reads the
  attestations of the latest `η_SG` rounds before the graded round. -/
  η_SG : Round
  /-- `η_SG ≥ 1`. -/
  η_SG_ge_one : 1 ≤ η_SG
  /-- `K`: the period of the nonjustifiable heights. A chain state that enters the height `h` marks
  it nonjustifiable when `K` divides `h` and `h` is more than `D` above the chain state's
  finalized height. -/
  K : Nat
  /-- `D`: the bound on the gap between a chain state's height and its finalized height, beyond
  which a height that `K` divides is nonjustifiable. -/
  D : Nat
  /-- `timeoutDelay`: the delay, in slots, before a chain state counts a progress quorum that is
  not a target quorum (`ChainState.progQuorum` and `ChainState.targetQuorum`): it counts one only
  at a block whose slot is at least `timeoutDelay` after the slot of the block that took the chain
  state into its current height. -/
  timeoutDelay : Nat
  /-- `K ≥ 4`. At `K = 2` the heights skipped as nonjustifiable fall again on multiples of `K`, so
  the skipping repeats by itself; at `K = 3` there is no gap `g` with `g ≥ 2` and `g + 2 ≤ K`,
  which the finality statements about this protocol need. -/
  K_ge_four : 4 ≤ K
  /-- `D ≥ 2`. In steady operation a chain state enters a new height with its height `2` above
  its finalized height, so a smaller `D` would mark the heights that `K` divides nonjustifiable in
  steady operation. -/
  D_ge_two : 2 ≤ D

/-- Values given to the node for now, which the protocol will eventually compute from the
chain. -/
structure Provisional (V : Type) [Fintype V] where
  /-- The proposer of each slot: `proposer s` is the validator whose block of slot `s` the node
  admits. -/
  proposer : (s : Slot) → V
  /-- The committees: the validators whose Goldfish votes for slot `s` the node admits are
  `committees.members s`. -/
  committees : Committees V
  /-- The electorate: a fixed positive weight for each validator. A grade compares the weight of
  the validators that support a block with the weight of those that oppose it, and the finality
  gadget's quorums are counted in weight. -/
  electorate : Electorate V

/-- The values another piece of software supplies to the node: for a block, the execution
client's payload root. -/
structure External (V : Type) where
  /-- The root of the block validator `v` proposes in slot `s`. -/
  new_root : (v : V) → (s : Slot) → BlockId

variable {V : Type} [DecidableEq V] [Fintype V]

namespace Protocol

/-- `Phase.earlyOffset p`: the first cutoff of a grade result of phase `p`, counted in delays
`Δ` from the instant its round opens: `−3` for the grade-0 result, `−4` for the grade-1 result,
`−5` for the grade-2 result. -/
def Phase.earlyOffset (p : Phase) : Int :=
  if p = .g0 then -3 else if p = .g1 then -4 else -5

end Protocol

namespace Config

variable (C : Config)

/-! ## The schedule -/

/-- `C.slotOf t`: the slot that contains the instant `t`, `⌊t / (4 * Δ)⌋`; an instant before `0` is
in slot `0`. -/
def slotOf (t : Time) : Slot := (Int.fdiv t (4 * C.Δ)).toNat

/-- `C.proposal_time s`: the instant slot `s` starts, `4 * Δ * s`, at which its block is
proposed. -/
def proposal_time (s : Slot) : Time := 4 * C.Δ * (s : Time)

/-- `C.vote_time s`: the instant of slot `s`'s Goldfish vote, `Δ` after the slot starts. -/
def vote_time (s : Slot) : Time := C.proposal_time s + C.Δ

/-- `C.gf_confirmation_time s`: the Goldfish confirmation time of slot `s`, `2 * Δ` after the
slot starts: the instant the tick runs the confirmation for slot `s − 1`
(`update_confirmation`), which counts the slot's votes resolved before it. -/
def gf_confirmation_time (s : Slot) : Time := C.proposal_time s + 2 * C.Δ

/-- `C.view_freeze s`: the view freeze of slot `s`, `3 * Δ` after the slot starts. -/
def view_freeze (s : Slot) : Time := C.proposal_time s + 3 * C.Δ

/-- `C.confirmation_time s`: the confirmation instant of slot `s`, `6 * Δ` after the slot
starts. -/
def confirmation_time (s : Slot) : Time := C.proposal_time s + 6 * C.Δ

/-! ## The rounds -/

/-- `C.round_of s`: the round of slot `s`, `⌊s / R⌋`. -/
def round_of (s : Slot) : Round := s / C.R

/-- `C.opening r`: the instant round `r` opens, the start of its first slot `r * R`. -/
def opening (r : Round) : Time := C.proposal_time (r * C.R)

/-- `C.round_attestation_time r`: round `r`'s attestation instant, `6 * Δ` after the start of the
round's first slot `r * R`. -/
def round_attestation_time (r : Round) : Time := C.opening r + 6 * C.Δ

/-- `C.early r p`: the first cutoff of round `r`'s grade result of phase `p`: `C.opening r` less
`3 * Δ` for the grade-0 result, `4 * Δ` for the grade-1 result, `5 * Δ` for the grade-2
result. -/
def early (r : Round) (p : Phase) : Time := C.opening r + Protocol.Phase.earlyOffset p * C.Δ

end Config

namespace Provisional

variable (P : Provisional V)

/-- `P.committee s`: the committee of slot `s`. -/
def committee (s : Slot) : Finset V := P.committees.members s

/-! ## The weights -/

/-- `P.weightOf S`: the total weight of the validators of the set `S`, each counted once, read
from the electorate `P.electorate`. -/
def weightOf (S : Finset V) : Nat := ∑ v ∈ S, P.electorate.weight v

/-- `P.totalWeight`: the total weight of all validators, `W`. -/
def totalWeight : Nat := ∑ v, P.electorate.weight v

/-- `P.finalityThreshold`: two thirds of the total weight, rounded up, `⌈2 * W / 3⌉`, written
`(2 * W + 2) / 3` in natural numbers. -/
def finalityThreshold : Nat := (2 * P.totalWeight + 2) / 3

/-- `P.quorumCheck S`: whether the validators of the set `S` weigh at least
`P.finalityThreshold`. -/
def quorumCheck (S : Finset V) : Bool := P.finalityThreshold ≤ P.weightOf S

end Provisional

end Spec
