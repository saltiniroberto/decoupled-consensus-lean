module
public import Model.Sts.Spec2Claims.Claim13bd

@[expose] public section

/-!
# Synchrony from the wake, awake windows and sleepiness

The premises on honest sends and their delivery (`HonestSendAt`, `SynchronyFromWake`), on when
validators wake and fall asleep, the awake windows `wVote` and `wAttest` with the validator sets
they define, the sleepiness premises over those sets, and the common-view premises.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Step `k` is an honest send of `sm`: step `k` added a copy of `sm` to the sent log, and `sm`'s
    signer is not held by the adversary at `x[k].time`, the instant step `k` starts from. -/
def HonestSendAt (S : Setup V) {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (k : Nat) (sm : SignedMsg V (NamedObject V)) : Prop :=
  sm ∈ x[k + 1].sent - x[k].sent ∧ sm.sender ∉ Sched.adv (x[k].time : Int)

/-- Synchrony from the wake: a message an honest validator sends at step `k` is delivered to every
    validator awake throughout from `x[k + 1].time` to the deadline
    `max x[k].time S.E.t_GST + S.E.Δ`, at a step after `k` whose time is at least `x[k].time` and
    strictly before that deadline. -/
def SynchronyFromWake (S : Setup V) {Sched : Schedule V} (x : AtomicExec (protocol S) Sched) :
    Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    HonestSendAt S x k sm →
    w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ

/-- Validators wake only at multiples of `Δ`: a validator awake at `t` and asleep at `t − 1` has `t`
    a multiple of `S.E.Δ`. -/
def AwakeAtMultiples (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ (t : Int) (v : V), v ∈ Sched.awake t → v ∉ Sched.awake (t - 1) → t % S.E.Δ = 0

/-- Validators wake only at action instants: a validator awake at `t` and asleep at `t − 1` has `t`
    a round's action instant. -/
def WakesAtActionInstants (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ (t : Int) (v : V), v ∈ Sched.awake t → v ∉ Sched.awake (t - 1) →
    ∃ r : Round, t = S.hc.a S.E.Δ r

/-- Validators fall asleep only right after an action instant: a validator awake at `t − 1` and
    asleep at `t` has `t` one after a round's action instant. -/
def SleepsAfterActionInstants (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ (t : Int) (v : V), v ∈ Sched.awake (t - 1) → v ∉ Sched.awake t →
    ∃ r : Round, t = S.hc.a S.E.Δ r + 1

/-- The awake window `(4R + 2)Δ` a voter needs before slot `s`'s vote instant: for every slot of a
    round it reaches back to five delays before the round's opening, so the voter has read the
    cutoff view from which the round's g1 anchor is computed. -/
def wVote (S : Setup V) : Int := (4 * (S.hc.R : Int) + 2) * S.E.Δ

/-- The awake window `4RΔ` an attester needs before round `r`'s action instant to take part in the
    round's grade formation: one whole period, so that round `r + 1`'s window starts at round `r`'s
    action instant. -/
def wAttest (S : Setup V) : Int := 4 * (S.hc.R : Int) * S.E.Δ

/-- The validators awake throughout `wVote` before slot `s`'s vote instant. -/
def activeAtW (S : Setup V) (Sched : Schedule V) (s : Slot) : Finset V :=
  Sched.awakeThroughout (slotStart S.E.Δ s + S.E.Δ - wVote S) (slotStart S.E.Δ s + S.E.Δ)

/-- The validators awake throughout `wAttest` before round `r`'s action instant. -/
def activeRoundW (S : Setup V) (Sched : Schedule V) (r : Nat) : Finset V :=
  Sched.awakeThroughout (S.hc.a S.E.Δ r - wAttest S) (S.hc.a S.E.Δ r)

/-- The validators the vote duty makes vote at slot `s`: those awake at its vote instant. -/
def votersAt (S : Setup V) (Sched : Schedule V) (s : Slot) : Finset V :=
  Sched.awake (slotStart S.E.Δ s + S.E.Δ)

/-- The validators the attestation duty makes attest at round `r`: those awake at its action
    instant. -/
def attestersAt (S : Setup V) (Sched : Schedule V) (r : Nat) : Finset V :=
  Sched.awake (S.hc.a S.E.Δ r)

/-- The validators that attest at some round of `[lo, hi]`. -/
def attestersIn (S : Setup V) (Sched : Schedule V) (lo hi : Nat) : Finset V :=
  (Finset.Icc lo hi).biUnion (attestersAt S Sched)

/-- Slot-level sleepiness from `anchor` on: at every slot `s`, the validators in `activeAtW (s − 1)`
    not held by the adversary at slot `s`'s vote instant outnumber the adversary at that instant
    together with every other voter of slot `s − 1`. -/
def sleepinessW (S : Setup V) (Sched : Schedule V) (anchor : Int) : Prop :=
  ∀ s : Slot, 1 ≤ s → anchor ≤ slotStart S.E.Δ s →
    (Sched.adv (slotStart S.E.Δ s + S.E.Δ) ∪
        (votersAt S Sched (s - 1) \
          (activeAtW S Sched (s - 1) \ Sched.adv (slotStart S.E.Δ s + S.E.Δ)))).card
      < (activeAtW S Sched (s - 1) \ Sched.adv (slotStart S.E.Δ s + S.E.Δ)).card

/-- Round-level sleepiness from `anchor` on: at every round `r₀`, the validators in
    `activeRoundW (r₀ − 1)` not held by the adversary at round `r₀ + 1`'s opening outweigh the
    adversary at that opening together with every other attester of rounds `r₀ − η_SG` to `r₀ − 1`. -/
def roundSleepinessW (S : Setup V) (Sched : Schedule V) (anchor : Int) : Prop :=
  ∀ r₀ : Nat, 1 ≤ r₀ → anchor ≤ Protocol.opening S.E S.hc r₀ →
    S.E.electorate.weightOf
        (Sched.adv (Protocol.opening S.E S.hc (r₀ + 1)) ∪
          (attestersIn S Sched (r₀ - S.hc.η_SG) (r₀ - 1) \
            (activeRoundW S Sched (r₀ - 1) \ Sched.adv (Protocol.opening S.E S.hc (r₀ + 1)))))
      < S.E.electorate.weightOf
          (activeRoundW S Sched (r₀ - 1) \ Sched.adv (Protocol.opening S.E S.hc (r₀ + 1)))

/-- Committee sleepiness from `anchor` on: in the committee of every slot `s − 1`, the members in
    `activeAtW (s − 1)` not held by the adversary at that slot's confirmation instant outnumber the
    other members. -/
def committeeSleepinessW (S : Setup V) (Sched : Schedule V) (anchor : Int) : Prop :=
  ∀ s : Slot, 1 ≤ s → anchor ≤ slotStart S.E.Δ s →
    ((S.E.committee (s - 1)) \
        (activeAtW S Sched (s - 1) \ Sched.adv (Protocol.confirmation_time S.E (s - 1)))).card
      < ((activeAtW S Sched (s - 1) ∩ S.E.committee (s - 1)) \
          Sched.adv (Protocol.confirmation_time S.E (s - 1))).card

/-- The common view at `tGAT`: every named block that a validator honest through `tGAT` holds at a
    step at or before `tGAT` is held by every honest awake validator at every step from `tGAT + Δ`
    on. -/
def CommonViewAtGAT (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (tGAT : Int) : Prop :=
  ∀ (i j : Nat) (v w : V) (B : NamedBlock V),
    (x[i].time : Int) ≤ tGAT → HonestThroughTime Sched tGAT v →
    B ∈ Read.blocks x[i][v].st →
    tGAT + S.E.Δ ≤ (x[j].time : Int) → HonestThrough Sched x j w → AtomicAwake x j w →
    B ∈ Read.blocks x[j][w].st

/-- The common view at `t₀`, for the readers whose finalized block is an ancestor of the block:
    every named block `B` that a validator honest through `t₀` holds at a step at or before `t₀` is
    held, at every step from `t₀ + Δ` on, by every honest awake validator whose finalized block is
    an ancestor of `B` or `B` itself. -/
def CommonViewOfFinalizedDescendantsAt (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ : Int) : Prop :=
  ∀ (i j : Nat) (v w : V) (B : NamedBlock V),
    (x[i].time : Int) ≤ t₀ → HonestThroughTime Sched t₀ v →
    B ∈ Read.blocks x[i][v].st →
    t₀ + S.E.Δ ≤ (x[j].time : Int) → HonestThrough Sched x j w → AtomicAwake x j w →
    Block.Preceq (Read.finalized x[j][w].st) B.erase →
    B ∈ Read.blocks x[j][w].st

end DecoupledConsensusModel.Sts
