module
public import Goldilocks

@[expose] public section

/-!
# The slot layout

`SlotLayout V` holds what a model of Goldilocks says about time and about the validators of a
block: when each slot's duty times and wake windows fall, which slot a time is in, the validator
set of a block and the count that advances the chain state on it. Every time is a natural number,
as the statements about executions read it, and every time member takes the node's parameters
`C : Config`. `SlotLayout.goldilocks` is the layout of the spec. This file holds definitions only.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Block quorum)

/-- When the slots' duties and wake windows fall, and the validators of each block. -/
structure SlotLayout (V : Type) [DecidableEq V] [Fintype V] where
  /-- `slotStart C s`: the time slot `s` starts.
      Read aloud: the start of slot `s`. -/
  slotStart : (C : Config) → (s : ℕ) → ℕ
  /-- `voteTime C s`: the time of slot `s`'s Goldfish vote.
      Read aloud: the vote time of slot `s`. -/
  voteTime : (C : Config) → (s : ℕ) → ℕ
  /-- `supportCutoff C s`: the cutoff of slot `s`'s early votes, the time of the confirmation
      update of slot `s`.
      Read aloud: the support cutoff of slot `s`. -/
  supportCutoff : (C : Config) → (s : ℕ) → ℕ
  /-- `viewFreeze C s`: the time up to which a block counts in the next slot's voter tree.
      Read aloud: the view freeze of slot `s`. -/
  viewFreeze : (C : Config) → (s : ℕ) → ℕ
  /-- `lateVoteCutoff C s`: the cutoff of slot `s`'s late votes.
      Read aloud: the late-vote cutoff of slot `s`. -/
  lateVoteCutoff : (C : Config) → (s : ℕ) → ℕ
  /-- `dutyWindowStart C s`: the time from which a validator must have been awake to run slot
      `s`'s revocation of the locks, Goldfish vote, confirmation update and attestation.
      Read aloud: the start of slot `s`'s duty window. -/
  dutyWindowStart : (C : Config) → (s : ℕ) → ℕ
  /-- `proposalWindowStart C s`: the time from which a validator must have been awake to propose
      slot `s`'s block.
      Read aloud: the start of slot `s`'s proposal window. -/
  proposalWindowStart : (C : Config) → (s : ℕ) → ℕ
  /-- `slot C t`: the slot the time `t` is in.
      Read aloud: the slot of `t`. -/
  slot : (C : Config) → (t : ℕ) → ℕ
  /-- `validators B`: the validator set associated with the block `B`.
      Read aloud: the validators of `B`. -/
  validators : (B : Block V) → Finset V
  /-- `quorumAt B`: the number of validators whose votes advance a chain state on the block `B`.
      Read aloud: the quorum at `B`. -/
  quorumAt : (B : Block V) → ℕ

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's slot layout: slot `s` starts at `C.t_ s`, its four duty times fall `C.Δ`,
`2 * C.Δ`, `3 * C.Δ` and `6 * C.Δ` after its start, its wake windows start at
`duty_window_start C s` and `proposal_window_start C s` (read as `0` when negative), the slot of
`t` is `C.slot t`, every block's validator set is every validator, and its quorum is `quorum V`.

Read aloud: the slot layout of Goldilocks. -/
def SlotLayout.goldilocks : SlotLayout V where
  slotStart C s := (C.t_ s).toNat
  voteTime C s := (C.t_ s + C.Δ).toNat
  supportCutoff C s := (C.t_ s + 2 * C.Δ).toNat
  viewFreeze C s := (C.t_ s + 3 * C.Δ).toNat
  lateVoteCutoff C s := (C.t_ s + 6 * C.Δ).toNat
  dutyWindowStart C s := (Goldilocks.duty_window_start C s).toNat
  proposalWindowStart C s := (Goldilocks.proposal_window_start C s).toNat
  slot C t := C.slot (t : Int)
  validators _ := Finset.univ
  quorumAt _ := quorum V

end GoldilocksCorrectness.Record
