import Spec.Consensus.Model

/-!
# Figure 3 — the round schedule

Figure 3 is a diagram, not pseudocode: one round of the schedule drawn for `R = 2`, the
grade instants and the action time above the axis, the phases of each slot below. What it
draws is Definition 9 and the timing prose that opens the draft's Section 4, and this file
renders that: the instants every later figure reads. There is no routine here.

Taking the start of slot 0 as time 0, slot `s` starts at `4Δs`, and a slot starting at `t`
runs four phases: `t` proposal, `t + Δ` vote, `t + 2Δ` support freeze, `t + 3Δ` slot-view
freeze. For round `r`, `t_r` is the proposal time of its opening slot, the round's *action
time* is `a_r = t_r + 6Δ` — the evaluation time of its opening slot, where the validator
performs the round's SG and FG action — and the round's four *grade instants*, at which it
grades the received round-`(r−1)` attestations, are

    Γ⁻¹ = t_r − Δ,   Γ⁰ = t_r,   Γ¹ = t_r + Δ,   Γ² = t_r + 2Δ.

## Instants are `Int`; slots, rounds and durations are `Nat`

Round 0's first grade instant is `t_0 − Δ = −Δ`, a genuinely negative instant, and the
timed store's clock needs an initial value below time 0 for the tick at `t = 0` to pass its
own precondition. `Nat` would truncate the first and cannot express the second, so every
*instant* is an `Int`, while a slot or round number and the duration `Δ` stay `Nat`.

## The schedule requires `R ≥ 2`

The action lies in the round's second slot, and the heads signed at `a_r` must arrive
before round `r+1`'s first grade instant — `a_r + Δ ≤ t_{r+1} − Δ`, which reduces to
`R ≥ 2`. `Params` carries only the model-level `R ≥ 1`; the stronger bound joins as an
explicit assumption where a proof needs it, the same treatment the hash's injectivity
gets.

## Absent, with no consumer yet

The support-freeze and slot-view-freeze phase times, and the slot's available-confirmation
time (`2Δ` into the following slot): all read by the draft's Section 5, which is not
drafted. Each arrives with its first consumer.
-/

set_option autoImplicit false

namespace Consensus

section Schedule
variable [Params]

open Params

/-- Round `r`'s *opening slot*, `rR` — the first of its `R` consecutive slots. -/
def openingSlot (r : Nat) : Nat := r * R

/-- The instant slot `s` starts: `4Δs`, taking the start of slot 0 as time 0. Also the
    slot's proposal phase. -/
def slotStart (s : Nat) : Int := (4 * Δ * s : Nat)

/-- The vote phase of slot `s`: `Δ` into the slot. Definition 14 reads the opening slot's
    vote time — `voteTime (openingSlot r)` — as the moment a validator derives its round's
    SG root. -/
def voteTime (s : Nat) : Int := slotStart s + Δ

/-- `t_r`, the proposal time of round `r`'s opening slot: `4ΔrR`. -/
def roundStart (r : Nat) : Int := slotStart (openingSlot r)

/-- `a_r = t_r + 6Δ`, the round's *action time*: the evaluation time of its opening slot,
    `2Δ` into the round's second slot, where the validator performs the round's SG and FG
    action. -/
def actionTime (r : Nat) : Int := roundStart r + 6 * Δ

/-- `Γ^j` of round `r`: `t_r + jΔ`, for `j ∈ {−1, 0, 1, 2}` — the four instants at which
    round `r` grades the received round-`(r−1)` attestations. The draft names no others,
    but nothing here constrains `j`; Definitions 11 and 12 pass the four literals. -/
def gradeInstant (r : Nat) (j : Int) : Int := roundStart r + j * Δ

end Schedule

end Consensus
