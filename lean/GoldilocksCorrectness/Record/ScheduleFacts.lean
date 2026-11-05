module
public import GoldilocksCorrectness.Record.SlotLayout
public import GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The schedule's facts, and the two classes of slot layouts

Three structures of statements about a slot layout `L : SlotLayout V`:

- `ScheduleFacts L`: the facts every model's slot layout owes, the field `sched` of `Facts M`. The
  four duty times of a slot are at least one delay apart and the next slot starts at least one
  delay after the view freeze; slot `0` starts at time `0`; the slot of a time is read off the
  slot starts; the wake windows open in slot order and early enough; a round leaves room for an
  attestation; the late-vote cutoff of a slot is no earlier than the next slot's support cutoff;
  and the quorum at a block is two thirds of its validator set, rounded up.
- `UniformSchedule L`: the class of slot layouts spaced as Goldilocks spaces its slots. It is a
  hypothesis `(U : UniformSchedule L)` on the theorems that need the exact spacing, never a field
  of `Facts M`.
- `FixedValidators L`: the class of slot layouts whose every block has every validator. It is a
  hypothesis `(Fx : FixedValidators L)`, never a field of `Facts M`.

Every time is a natural number read at the parameters `S.C` of a setup `S`; `Δ S` and `Δ_F S` are
the two delays as natural numbers (`Statements/Routines/ScheduleDefs.lean`). This file holds the
three structures only.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Block)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of the slot layout `L`: the order of each slot's duty times, the slot of a time, the
wake windows, the room a round leaves for an attestation, the late-vote cutoff, and the quorum at
a block.

Read aloud: the slot layout `L` orders each slot's times at least one delay apart, starts time at
slot `0`, places every time in the slot whose start it has reached, opens the wake windows early
enough and in slot order, leaves a round room for an attestation, puts the late-vote cutoff of a
slot no earlier than the next slot's support cutoff, and gives each block two thirds of its
validators as its quorum. -/
structure ScheduleFacts (L : SlotLayout V) : Prop where
  /-- The vote time of a slot is at least one delay after its start.

      Read aloud: slot `s`'s Goldfish vote is at least `Δ S` after slot `s` starts. -/
  slotStart_add_Δ_le_voteTime :
    ∀ (S : Setup V) (s : ℕ), L.slotStart S.C s + Δ S ≤ L.voteTime S.C s
  /-- The support cutoff of a slot is at least one delay after its vote time.

      Read aloud: slot `s`'s support cutoff is at least `Δ S` after its vote time. -/
  voteTime_add_Δ_le_supportCutoff :
    ∀ (S : Setup V) (s : ℕ), L.voteTime S.C s + Δ S ≤ L.supportCutoff S.C s
  /-- The view freeze of a slot is at least one delay after its support cutoff.

      Read aloud: slot `s`'s view freeze is at least `Δ S` after its support cutoff. -/
  supportCutoff_add_Δ_le_viewFreeze :
    ∀ (S : Setup V) (s : ℕ), L.supportCutoff S.C s + Δ S ≤ L.viewFreeze S.C s
  /-- The next slot starts at least one delay after a slot's view freeze.

      Read aloud: slot `s + 1` starts at least `Δ S` after slot `s`'s view freeze. -/
  viewFreeze_add_Δ_le_slotStart_succ :
    ∀ (S : Setup V) (s : ℕ), L.viewFreeze S.C s + Δ S ≤ L.slotStart S.C (s + 1)
  /-- Slot `0` starts at time `0`.

      Read aloud: time starts with slot `0`. -/
  slotStart_zero : ∀ (S : Setup V), L.slotStart S.C 0 = 0
  /-- A time is at least the start of slot `s` exactly when its slot is at least `s`.

      Read aloud: slot `s` has started at the time `t` exactly when the slot of `t` is `s` or
      later. -/
  slotStart_le_iff :
    ∀ (S : Setup V) (s t : ℕ), L.slotStart S.C s ≤ t ↔ s ≤ L.slot S.C t
  /-- The duty window of slot `s + 1` starts no later than the start of slot `s`.

      Read aloud: a validator awake from the start of slot `s + 1`'s duty window is awake from the
      start of slot `s`. -/
  dutyWindowStart_succ_le_slotStart :
    ∀ (S : Setup V) (s : ℕ), L.dutyWindowStart S.C (s + 1) ≤ L.slotStart S.C s
  /-- The duty windows start in slot order.

      Read aloud: a later slot's duty window starts no earlier. -/
  dutyWindowStart_mono :
    ∀ (S : Setup V) (s s' : ℕ), s ≤ s' → L.dutyWindowStart S.C s ≤ L.dutyWindowStart S.C s'
  /-- The duty window of slot `s + 1` starts no later than the proposal window of slot `s + 2`.

      Read aloud: a validator awake from the start of slot `s + 2`'s proposal window is awake from
      the start of slot `s + 1`'s duty window. -/
  dutyWindowStart_succ_le_proposalWindowStart :
    ∀ (S : Setup V) (s : ℕ),
      L.dutyWindowStart S.C (s + 1) ≤ L.proposalWindowStart S.C (s + 2)
  /-- An attestation sent at the support cutoff of slot `s + 1` arrives, within `Δ_F S`, by the
      start of slot `s + R`.

      Read aloud: the support cutoff of slot `s + 1`, plus `Δ_F S`, is at most the start of slot
      `s + S.C.R`. -/
  supportCutoff_succ_add_Δ_F_le_slotStart :
    ∀ (S : Setup V) (s : ℕ), L.supportCutoff S.C (s + 1) + Δ_F S ≤ L.slotStart S.C (s + S.C.R)
  /-- The late-vote cutoff of a slot is no earlier than the support cutoff of the next slot.

      Read aloud: slot `s`'s late votes are cut off no earlier than slot `s + 1`'s early votes. -/
  supportCutoff_succ_le_lateVoteCutoff :
    ∀ (S : Setup V) (s : ℕ), L.supportCutoff S.C (s + 1) ≤ L.lateVoteCutoff S.C s
  /-- The quorum at a block is two thirds of the block's validator set, rounded up.

      Read aloud: the number of validators whose votes advance a chain state on `B` is
      `(2 * n + 2) / 3`, `n` the number of `B`'s validators. -/
  quorumAt_eq : ∀ (B : Block V), L.quorumAt B = (2 * (L.validators B).card + 2) / 3

/-- The class of slot layouts spaced as Goldilocks spaces its slots: slots last `4 * Δ S`, the
four duty times fall `Δ S`, `2 * Δ S`, `3 * Δ S` and `6 * Δ S` into the slot, the duty window of a
slot opens `S.C.k` slots and the proposal window `S.C.k + 1` slots before its vote time (at `0`
when that is negative), and the slot of a time is its quotient by `4 * Δ S`.

Read aloud: `L` is spaced exactly as Goldilocks is. -/
structure UniformSchedule (L : SlotLayout V) : Prop where
  /-- Slot `s` starts at `4 * Δ S * s`.

      Read aloud: slots last four delays, from time `0`. -/
  slotStart_eq : ∀ (S : Setup V) (s : ℕ), L.slotStart S.C s = 4 * Δ S * s
  /-- The vote time of a slot is one delay after its start.

      Read aloud: slot `s`'s Goldfish vote is `Δ S` into the slot. -/
  voteTime_eq : ∀ (S : Setup V) (s : ℕ), L.voteTime S.C s = L.slotStart S.C s + Δ S
  /-- The support cutoff of a slot is two delays after its start.

      Read aloud: slot `s`'s support cutoff is `2 * Δ S` into the slot. -/
  supportCutoff_eq : ∀ (S : Setup V) (s : ℕ), L.supportCutoff S.C s = L.slotStart S.C s + 2 * Δ S
  /-- The view freeze of a slot is three delays after its start.

      Read aloud: slot `s`'s view freeze is `3 * Δ S` into the slot. -/
  viewFreeze_eq : ∀ (S : Setup V) (s : ℕ), L.viewFreeze S.C s = L.slotStart S.C s + 3 * Δ S
  /-- The late-vote cutoff of a slot is six delays after its start.

      Read aloud: slot `s`'s late-vote cutoff is `6 * Δ S` after slot `s` starts. -/
  lateVoteCutoff_eq :
    ∀ (S : Setup V) (s : ℕ), L.lateVoteCutoff S.C s = L.slotStart S.C s + 6 * Δ S
  /-- The duty window of a slot opens `S.C.k` slots before its vote time, or at `0`.

      Read aloud: slot `s`'s duty window starts at `slotStart s + Δ S − 4 * Δ S * S.C.k`, cut at
      `0`. -/
  dutyWindowStart_eq :
    ∀ (S : Setup V) (s : ℕ),
      L.dutyWindowStart S.C s = L.slotStart S.C s + Δ S - 4 * Δ S * S.C.k
  /-- The proposal window of a slot opens `S.C.k + 1` slots before its vote time, or at `0`.

      Read aloud: slot `s`'s proposal window starts at
      `slotStart s + Δ S − 4 * Δ S * (S.C.k + 1)`, cut at `0`. -/
  proposalWindowStart_eq :
    ∀ (S : Setup V) (s : ℕ),
      L.proposalWindowStart S.C s = L.slotStart S.C s + Δ S - 4 * Δ S * (S.C.k + 1)
  /-- The slot of a time is its quotient by the slot length.

      Read aloud: the time `t` is in slot `t / (4 * Δ S)`. -/
  slot_eq : ∀ (S : Setup V) (t : ℕ), L.slot S.C t = t / (4 * Δ S)

/-- The class of slot layouts whose every block has every validator.

Read aloud: in `L`, every block's validator set is the whole type of validators. -/
structure FixedValidators (L : SlotLayout V) : Prop where
  /-- Every block's validator set is every validator.

      Read aloud: the validators of `B` are all of `V`. -/
  validators_eq_univ : ∀ (B : Block V), L.validators B = Finset.univ

end GoldilocksCorrectness.Record
