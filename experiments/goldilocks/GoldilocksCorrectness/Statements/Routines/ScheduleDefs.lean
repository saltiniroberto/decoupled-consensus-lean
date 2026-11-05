module
public import GoldilocksSts

@[expose] public section

/-!
# The schedule's times

The times the statements read, as natural numbers, from the parameters `S.C` of a setup `S`:

- `Δ`, `Δ_F`: the two delays;
- `slotStart`, `voteTime`, `supportCutoff`, `viewFreeze`, `lateVoteCutoff`: the start of a slot
  and its times `Δ`, `2Δ`, `3Δ` and `6Δ` after it;
- `dutyWindowStart`, `proposalWindowStart`: the two times the wake rule compares with;
- `anchorCW S tGAT`: the time `k + 2` slots after `tGAT`, from which the one committee premise of
  Lemma 89's phase holds.

They read the schedule alone: no node state, no execution. Moved here unchanged from
`Statements/Executions/ExecutionDefs.lean` and `Statements/Executions/Lemma89Defs.lean`. Nothing is proved here.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `Δ S`: the delay `S.C.Δ` as a natural number, the value itself since it is positive.

Read aloud: the schedule unit, the delay blocks and Goldfish votes are designed to arrive within. -/
@[no_expose] def Δ (S : Setup V) : ℕ := S.C.Δ.toNat

/-- `Δ_F S`: the delay `S.C.Δ_F` as a natural number, the value itself since it is at least `Δ`.

Read aloud: the delay attestations are designed to arrive within. -/
@[no_expose] def Δ_F (S : Setup V) : ℕ := S.C.Δ_F.toNat

/-- `slotStart S s`: the start `S.C.t_ s` of the slot `s` as a natural number, the value itself
since it is nonnegative.

Read aloud: the time slot `s` starts. -/
@[no_expose] def slotStart (S : Setup V) (s : ℕ) : ℕ := (S.C.t_ s).toNat

/-- `voteTime S s`: the time `S.C.t_ s + S.C.Δ` as a natural number, the value itself since it is
nonnegative.

Read aloud: the time of slot `s`'s Goldfish vote, one delay after the slot's start. -/
@[no_expose] def voteTime (S : Setup V) (s : ℕ) : ℕ := (S.C.t_ s + S.C.Δ).toNat

/-- `supportCutoff S s`: the time `S.C.t_ s + 2 * S.C.Δ` as a natural number, the value itself
since it is nonnegative.

Read aloud: two delays after the start of slot `s`, the cutoff of slot `s`'s early votes. -/
@[no_expose] def supportCutoff (S : Setup V) (s : ℕ) : ℕ := (S.C.t_ s + 2 * S.C.Δ).toNat

/-- `viewFreeze S s`: the time `S.C.t_ s + 3 * S.C.Δ` as a natural number, the value itself since
it is nonnegative.

Read aloud: three delays after the start of slot `s`. -/
@[no_expose] def viewFreeze (S : Setup V) (s : ℕ) : ℕ := (S.C.t_ s + 3 * S.C.Δ).toNat

/-- `lateVoteCutoff S s`: the time `S.C.t_ s + 6 * S.C.Δ` as a natural number, the value itself
since it is nonnegative.

Read aloud: six delays after the start of slot `s`, the cutoff of slot `s`'s late votes. -/
@[no_expose] def lateVoteCutoff (S : Setup V) (s : ℕ) : ℕ := (S.C.t_ s + 6 * S.C.Δ).toNat

/-- `dutyWindowStart S s`: the time `duty_window_start S.C s` as a natural number; `0` when the
spec's value is negative, which happens for a small `s`.

Read aloud: the time from which a validator must have been awake to run slot `s`'s revocation,
Goldfish vote, confirmation update and attestation. -/
@[no_expose] def dutyWindowStart (S : Setup V) (s : ℕ) : ℕ := (duty_window_start S.C s).toNat

/-- `proposalWindowStart S s`: the time `proposal_window_start S.C s` as a natural number; `0`
when the spec's value is negative, which happens for a small `s`.

Read aloud: the time from which a validator must have been awake to propose slot `s`'s block. -/
@[no_expose] def proposalWindowStart (S : Setup V) (s : ℕ) : ℕ := (proposal_window_start S.C s).toNat

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `anchorCW S tGAT`: the time `k + 2` slots after `tGAT`, from which the one committee premise
of the phase holds.

The variables:
- `S`: the setup; `tGAT`: the time from which every honest validator is awake.

Read aloud: `tGAT + 4Δ(k + 2)`. -/
@[no_expose] def anchorCW (S : Setup V) (tGAT : ℕ) : ℕ := tGAT + 4 * Δ S * (S.C.k + 2)

end GoldilocksCorrectness.Statements.Routines
