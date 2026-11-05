module
public import GoldilocksCorrectness.Statements.Executions.SleepyDefs

@[expose] public section

/-!
# The honest round opening slots and the finality window

The conditions on the schedule that the finality-liveness statements and Lemma 90's inclusion read:

- `HonestOpenerAt S Sched s`, the proposer of slot `s` is awake and outside the adversary set from
  the start of the proposal window of slot `s` to the support cutoff of slot `s + 1`;
- `QuorumActiveAt S Sched s`, at least `quorum V` validators are in `honestActiveAt S Sched s`;
- `FinalityWindowAt S Sched r`, the four consecutive rounds `r` to `r + 3` have honest round
  opening slots, and the first three a quorum of honest active validators;
- `AwakeForDelayWithin S Sched Δw v t t'`, between `t` and `t'` the validator `v` is awake for one
  whole delay or one whole catch-up delay `Δw`, whichever is longer.


-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff proposalWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `HonestOpenerAt S Sched s`: the proposer of slot `s` is awake and outside the adversary set at
every time from `proposalWindowStart S s` to `supportCutoff S (s + 1)`. It is the per-slot premise
`ConfirmedIncludedAfterHealing` spells out, given a name; when `s` is the first slot of a round,
`s` is an honest round opening slot.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: the proposer of `s` is awake and honest from its proposal window to the slot's
update. -/
def HonestOpenerAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Prop :=
  ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
    S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int)

/-- `QuorumActiveAt S Sched s`: at least `quorum V` validators are in `honestActiveAt S Sched s`
(awake from `dutyWindowStart S s` through `supportCutoff S (s + 1)`, outside the adversary set at
that cutoff).

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: a quorum of validators runs slot `s`'s duties honestly, the attestation of the round
whose first slot is `s` included. -/
def QuorumActiveAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Prop :=
  quorum V ≤ |honestActiveAt S Sched s|

/-- `FinalityWindowAt S Sched r`: for the four consecutive rounds `r`, `r + 1`, `r + 2`, `r + 3`,
each first slot `(r + i) * R` has `HonestOpenerAt`, and the first three have `QuorumActiveAt`.

The variables:
- `S`: the setup; `Sched`: the schedule; `r`: the first round of the window.

Read aloud: four consecutive honest round opening slots, the proposer of each awake and honest from
its proposal window to its slot's update, with a quorum of honest active validators at the first
three. -/
def FinalityWindowAt (S : Setup V) (Sched : Schedule V) (r : ℕ) : Prop :=
  (∀ i : ℕ, i < 4 → HonestOpenerAt S Sched ((r + i) * S.C.R)) ∧
  (∀ i : ℕ, i < 3 → QuorumActiveAt S Sched ((r + i) * S.C.R))

omit [Fintype V] in
/-- `AwakeForDelayWithin S Sched Δw v t t'`: `v` is awake at every time of some interval of length
`max (Δ S) Δw` that starts at or after `t` and ends at or before `t'`.

The variables:
- `S`: the setup; `Sched`: the schedule; `Δw`: the catch-up delay; `v`: the validator; `t`, `t'`:
  the two ends.



Read aloud: between `t` and `t'`, `v` is awake for one whole delay or one whole catch-up delay,
whichever is longer. -/
def AwakeForDelayWithin (S : Setup V) (Sched : Schedule V) (Δw : ℕ) (v : V) (t t' : ℕ) : Prop :=
  ∃ τ : ℕ, t ≤ τ ∧ τ + max (Δ S) Δw ≤ t' ∧
    v ∈ Sched.awakeThroughout (τ : Int) ((τ + max (Δ S) Δw : ℕ) : Int)

end GoldilocksCorrectness.Statements.Executions
