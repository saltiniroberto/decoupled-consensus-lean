module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ReceiveDefs
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs

@[expose] public section

/-!
# AsyncResilienceDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/AsyncResilienceDefs.lean` over a
model `M`, for an execution `x` of `protocolOf M S`: the delivery premises up to a bound, the lock
holders and their majority where the previous votes are owed inside the period, read at the model's
times; the persistence of the confirmed tips and the finalized blocks' compatibility, each its view
form on the view of `x`, `projectTrace (nodeView M) x.toTrace`; the caches, certificates and
attestations relative to a block; the lock holder's state, whose lock entry on the protected block
is read through the readers `M.le_B` and `M.le_d`; the votes on the protected chain; and the facts
at the hand-over.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry CachesCompatibleWith)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)
open GoldilocksCorrectness.Record.Statements.View


variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

export GoldilocksCorrectness.Record.Statements.AbstractTrace (holdersAt)

section Delivery

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b`: `SynchronyFromWake` restricted to
the sends whose ordinary deadline `max x[i + 1].time GST + Δ`, counted from the time the message is
on the wire, is at most `b`.

The variables:
- `M`: the model;
- `A`, `x`: the activity, the execution; `Δ`: the delay; `ΔRedeliver`: the re-delivery delay;
  `GST`: the time from which the network is synchronous; `release`: the release reading of a
  message's object; `ok`: the object class; `b`: the bound on the deadlines.

Read aloud: whatever an honest validator puts on the wire early enough to be due by `b` is
delivered, before every tick of the receiver at a time at least its ordinary deadline, to every
validator awake and honest from the send through that tick. -/
def SynchronyFromWakeUpTo (Δ ΔRedeliver GST : ℕ) (release : NamedObject V → Option ℕ)
    (ok : NamedObject V → Prop) (b : ℕ) : Prop :=
  ∀ (i k : ℕ) (v : V) (sm : SignedMsg V (NamedObject V)) (t : ℕ),
    x.HonestSendAt A i sm → ok sm.msg →
    max (x.time (i + 1)) GST + Δ ≤ b →
    x.lbl k = Event.tick v t → i < k →
    -- `v` is awake and honest after every step from the send on to its tick `k`
    (∀ j : ℕ, i + 1 ≤ j → j ≤ k → v ∈ A.active j) →
    max (x.time (i + 1)) GST + Δ ≤ x.time k →
    -- after a delivery `j₀` that found `v` not yet reacted to `r`, the re-delivery deadline
    -- (`ΔRedeliver` after `v`'s first tick `k₁` at a reading at least `r`) is at most the time of `k`
    (∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      i < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k) →
    ∃ j : ℕ, i < j ∧ j < k ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ t → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k → x.lbl l ≠ Event.restart v t' false

/-- `CatchUpOnWakeUpTo M A x Δ Δw ΔRedeliver GST release ok b`: a validator `v` restarted at a step `k`
after the step `i` at which an honest validator put a message `sm` of the class `ok` on the wire, that
ticks at a step `k' > k` to a clock value `c'` at least the catch-up deadline (the later of the
message's ordinary deadline `max x[i + 1].time GST + Δ` and the restart's `max x[k].time GST + Δw`),
active after every step `j` with `k < j ≤ k'`: when the object of `sm` has a release clock value `r`
and a delivery of `sm` to `v` after the restart found `v` not yet reacted to `r`, provided that the
re-delivery deadline (`ΔRedeliver` after the time of `v`'s first tick after that delivery at a clock
value at least `r`) is at most the time of `k'`, `v` is delivered `sm` at a step `j` with
`k < j < k'`; when `r` is at most `c'`, that delivery found `v` already reacted to `r`; and no step
between `j` and `k'` is a restart of `v` that loses its memory. Restricted to the restarts for which
both deadlines are at most `b`.

This is the shape of the delivery promise `delivered`, as `CatchUpOnWakeBy` has it.

The variables:
- `M`: the model;
- `A`, `x`: the activity, the execution; `Δ`: the delay; `Δw`: the catch-up delay; `ΔRedeliver`: the
  re-delivery delay; `GST`: the time from which the network is synchronous; `release`: the release
  clock value of a message's object; `ok`: the object class; `b`: the bound on the deadlines.

Read aloud: a validator that restarts, early enough for both deadlines to fall by `b`, and stays
active up to any of its ticks at a clock value at least the catch-up deadline, receives before that
tick every message of the class `ok` an honest validator put on the wire before its restart, with no
memory-losing restart in between; and, when the object's release clock value is at most that tick's,
the delivery found its clock already there, provided a re-delivery after its clock reached that value
would come before the tick. -/
def CatchUpOnWakeUpTo (Δ Δw ΔRedeliver GST : ℕ) (release : NamedObject V → Option ℕ)
    (ok : NamedObject V → Prop) (b : ℕ) : Prop :=
  ∀ (i k : ℕ) (v : V) (sm : SignedMsg V (NamedObject V)) (t : ℕ) (keep : Bool) (k' c' : ℕ),
    x.HonestSendAt A i sm → ok sm.msg → x.lbl k = Event.restart v t keep →
    -- the message is put on the wire at a step before the restart
    i < k →
    -- both deadlines are at most `b`
    max (x.time (i + 1)) GST + Δ ≤ b → max (x.time k) GST + Δw ≤ b →
    -- `v` ticks after the restart to a clock value at least the catch-up deadline
    k < k' → x.lbl k' = Event.tick v c' →
    max (max (x.time (i + 1)) GST + Δ) (max (x.time k) GST + Δw) ≤ (c' : ℝ) →
    -- `v` is active after every step after the restart up to that tick
    (∀ j : ℕ, k < j → j ≤ k' → v ∈ A.active j) →
    -- after a delivery `j₀` after the restart that found `v` not yet reacted to `r`, the re-delivery
    -- deadline (`ΔRedeliver` after `v`'s first tick `k₁` at a clock value at least `r`) is at most the
    -- time of `k'`
    (∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      k < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k' → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k') →
    ∃ j : ℕ, k < j ∧ j < k' ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ c' → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k' → x.lbl l ≠ Event.restart v t' false

end Delivery

section Kit

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `HoldersOutweighWhereOwed M S Sched s Δs b₀ b₁`: at every slot `s' ≥ s + 2` with
`b₀ < M.supportCutoff S.C (s' − 1)` and `M.supportCutoff S.C (s' − 1) + Δ S < b₁ + max (Δ S) Δs`
(`VotesOwedInPeriod`), the members of slot `s'`'s committee that are not in
`holdersAt M S Sched s s'` are fewer than those that are.

The variables:
- `M`: the model;
- `S`, `Sched`: the setup, the schedule; `s`: the hand-over slot; `Δs`: the sync delay; `b₀`, `b₁`:
  the start and the end of the period.

The recovery after the period is `max (Δ S) Δs`;

Read aloud: wherever the previous slot's votes are owed inside the period, the lock holders
outweigh the rest of the committee. -/
def HoldersOutweighWhereOwed (s Δs b₀ b₁ : ℕ) : Prop :=
  ∀ s' : ℕ, s + 2 ≤ s' → b₀ < M.supportCutoff S.C (s' - 1) →
    M.supportCutoff S.C (s' - 1) + Δ S < b₁ + max (Δ S) Δs →
    |S.P.committee s' \ holdersAt M S A x s s'| < |holdersAt M S A x s s' ∩ S.P.committee s'|

/-- `VotesOwedInPeriod M S Δs b₀ b₁ s'`: the votes of slot `s' − 1` have their ordinary delivery
deadline `M.supportCutoff S.C (s' − 1)` after the period's start, and less than the recovery's
excess over one delay after the period's end: `b₀ < M.supportCutoff S.C (s' − 1)` and
`M.supportCutoff S.C (s' − 1) + Δ S < b₁ + max (Δ S) Δs`. A slot of which this does not hold is one
whose previous slot's honest votes reach every honest active voter before its view freeze.

The variables:
- `M`: the model;
- `S`: the setup; `Δs`: the sync delay; `b₀`, `b₁`: the start and the end of the period; `s'`: the
  slot.

The recovery after the period is `max (Δ S) Δs`;

Read aloud: at slot `s'`, a voter's view of the previous slot's votes is the adversary's choice. -/
def VotesOwedInPeriod (Δs b₀ b₁ s' : ℕ) : Prop :=
  b₀ < M.supportCutoff S.C (s' - 1) ∧ M.supportCutoff S.C (s' - 1) + Δ S < b₁ + max (Δ S) Δs

/--
For every slot `s'` at least two after the hand-over slot `s` whose previous slot's votes are not
owed inside the period (`VotesOwedInPeriod`), with roots naming blocks among what honest validators
hold up to the vote time of `s'`, every validator `u ∈ honestActiveAt M S A x s'`, and every block `T`
certified at height `h` on the chain of a block `Y` in the state `u`'s tick to the vote time of `s'`
starts from (`T` an ancestor of `Y`, or `Y`), of chain-state height greater than `B`'s and compatible
with the finalized block in the state `u`'s tick to the view freeze of slot `s' − 1` starts from, that
some validator, outside the adversary set at a step whose time is at most the start of `u`'s duty
window `M.dutyWindowStart S.C s'`, or at a step at or before a tick of `u` to a clock value at most the
spec's start of that window `Goldilocks.duty_window_start S.C s'`, holds at that step: `T` is in the tree
of the state `u`'s tick to that view freeze starts from.

The three reads of `u`'s state are at `u`'s own ticks.

The antecedent is read at a step: a holder at any step whose time is
at most the duty window's start, the holder's relay then at a time at most that start. Its second case
covers a holder that relays `T` before `u`'s tick to a clock value at most the window's start, the tick
at which `u`'s window may begin (the second case of `activeThroughoutToTick`): such a tick is at a real
time up to `ΔClockBehind` after that start, and `u` may be down when the relay is on the wire.

The two antecedents `RootsNameBlocksUntil …` and `¬ VotesOwedInPeriod …` are the hypotheses `hRoots`
and `hgood` of `cert_entry_held_before_freeze`, which reads the line. Derived from the restated
catch-up premise at a catch-up delay at most `max (Δ S) Δs` by `delT_of_catchUp`
(`Proofs/Executions/PeriodEntryDeliveryLine.lean`).

The variables:
- `M`: the model;
- `S`, `A`, `x`: the setup, the activity, the execution; `s`: the hand-over slot; `B`: its proposal;
  `b₀`, `b₁`: the start and the end of the period; `Δs`: the sync delay.

Read aloud: a certified entry that an honest validator held at a step whose time is at most the
start of the voter's duty window, or at a step at or before a tick of the voter to a clock value at most
that start, is in the state the voter's tick to its view freeze starts from. -/
def DelTLine (s : ℕ) (B : Block V) (b₀ b₁ Δs : ℕ) : Prop :=
  ∀ (s' : ℕ) (u : V) (Y T : Block V) (h : Height),
    RootsNameBlocksUntil M A x (M.voteTime S.C s') →
    s + 2 ≤ s' → ¬ VotesOwedInPeriod M S Δs b₀ b₁ s' →
    u ∈ honestActiveAt M S A x s' →
    Y ∈ (x.tickInput u (M.voteTime S.C s')).tree → T.AncestorEq Y →
    GoldilocksCorrectness.Record.Statements.Routines.ProgressCertOn M Y h T →
    (M.chainStateOf S.C B).h < (M.chainStateOf S.C T).h →
    (x.tickInput u (M.viewFreeze S.C (s' - 1))).finalized.compatible T = true →
    (∃ (j : ℕ) (v : V), (x.time j ≤ M.dutyWindowStart S.C s' ∨
        ∃ (k c₀ : ℕ), j ≤ k ∧ x.lbl k = Event.tick u c₀ ∧ (c₀ : ℤ) ≤ Goldilocks.duty_window_start S.C s') ∧
      v ∉ A.corrupted j ∧ T ∈ (x.st j v).tree) →
    T ∈ (x.tickInput u (M.viewFreeze S.C (s' - 1))).tree

/-- `ConfirmedPersistsFrom M S Sched x s tAwakeEnd b₀`: every block `P` that is, at a step `T` of
time at least `tAwakeEnd` and at most `M.supportCutoff S.C (s + 1)`, the confirmed tip of a
validator `v` outside the adversary set at every time up to the time of `T`, or an ancestor of it, is, at every step `j` of time at least `b₀`,
the confirmed tip or an ancestor of the confirmed tip of every validator `w ∈ updaterAt M S Sched s`
honest through `j`.



The confirmed tip of `v` at `T` is read only when no step from `T` on is `v`'s tick to the time of
`T`: on the unfolding of an own execution, a validator
whose tick to a time comes at or after the step still shows its node state from before that time.

Defined as its view form: `ConfirmedPersistsFromV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `confirmedPersistsFrom_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

Each updater's confirmed tip is read only after its own tick to the hand-over cutoff.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: every block that is `v`'s confirmed tip at a step from `tAwakeEnd` to the hand-over
update, or an ancestor of it, is, at every step from `b₀` on, the confirmed tip or an ancestor of
the confirmed tip of every validator honest through that step that ran the hand-over update. -/
def ConfirmedPersistsFrom (s tAwakeEnd b₀ : ℕ) : Prop :=
  ConfirmedPersistsFromV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) s tAwakeEnd b₀

/-- `FinalizedCompatibleFrom M S Sched x s tAwakeEnd b₀`: every block `P` that is, at a step `T` of
time at least `tAwakeEnd` and at most `M.supportCutoff S.C (s + 1)`, the confirmed tip of a
validator outside the adversary set at every time up to the time of `T`, or an ancestor of it, is compatible with the finalized block of every
validator honest through any step of time at least `b₀`.



The confirmed tip of `v` at `T` is read only when no step from `T` on is `v`'s tick to the time of
`T`: on the unfolding of an own execution, a validator
whose tick to a time comes at or after the step still shows its node state from before that time.

Defined as its view form: `FinalizedCompatibleFromV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `finalizedCompatibleFrom_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: from `b₀` on, no honest validator finalizes a block conflicting with what was
confirmed from `tAwakeEnd` to the hand-over update. -/
def FinalizedCompatibleFrom (s tAwakeEnd b₀ : ℕ) : Prop :=
  FinalizedCompatibleFromV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) s tAwakeEnd b₀

/-- `ConfirmedPersistsBetween M S Sched x s tAwakeEnd b₀ t`: `ConfirmedPersistsFrom S Sched x s
tAwakeEnd b₀` read up to the time `t`. Every block `P` that is, at a step `T` of time
at least `tAwakeEnd` and at most `M.supportCutoff S.C (s + 1)`, the confirmed tip of a validator `v`
outside the adversary set at every time up to the time of `T`, or an ancestor of it, is, at every step `j` of time at least `b₀` and at most
`t`, the confirmed tip or an ancestor of the confirmed tip of every validator
`w ∈ updaterAt M S Sched s` honest through `j`. `ConfirmedPersistsFrom M S Sched x s tAwakeEnd b₀`
is this for every time `t` (`confirmedPersistsFrom_iff`).



The confirmed tip of `v` at `T` is read only when no step from `T` on is `v`'s tick to the time of
`T`: on the unfolding of an own execution, a validator
whose tick to a time comes at or after the step still shows its node state from before that time.

Defined as its view form: `ConfirmedPersistsBetweenV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `confirmedPersistsBetween_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

Each updater's confirmed tip is read only after its own tick to the hand-over cutoff.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period; `t`: the time up to which the later steps are read.

Read aloud: every block that is `v`'s confirmed tip at a step from `tAwakeEnd` to the hand-over
update, or an ancestor of it, is, at every step from `b₀` up to `t`, the confirmed tip or an
ancestor of the confirmed tip of every validator honest through that step that ran the hand-over
update.

 -/
def ConfirmedPersistsBetween (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ConfirmedPersistsBetweenV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) s tAwakeEnd b₀ t

/-- `FinalizedCompatibleBetween M S Sched x s tAwakeEnd b₀ t`: `FinalizedCompatibleFrom S Sched x s
tAwakeEnd b₀` read up to the time `t`. Every block `P` that is, at a step `T` of
time at least `tAwakeEnd` and at most `M.supportCutoff S.C (s + 1)`, the confirmed tip of a
validator outside the adversary set at every time up to the time of `T`, or an ancestor of it, is compatible with the finalized block of every
validator honest through any step of time at least `b₀` and at most `t`.
`FinalizedCompatibleFrom M S Sched x s tAwakeEnd b₀` is this for every time `t`
(`finalizedCompatibleFrom_iff`).



The confirmed tip of `v` at `T` is read only when no step from `T` on is `v`'s tick to the time of
`T`: on the unfolding of an own execution, a validator
whose tick to a time comes at or after the step still shows its node state from before that time.

Defined as its view form: `FinalizedCompatibleBetweenV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `finalizedCompatibleBetween_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period; `t`: the time up to which the later steps are read.

Read aloud: from `b₀` up to `t`, no honest validator finalizes a block conflicting with what was
confirmed from `tAwakeEnd` to the hand-over update.

 -/
def FinalizedCompatibleBetween (s tAwakeEnd b₀ t : ℕ) : Prop :=
  FinalizedCompatibleBetweenV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) s tAwakeEnd b₀ t

/-- `ConfirmedPersistsFrom M S Sched x s tAwakeEnd b₀` holds exactly when `ConfirmedPersistsBetween
S Sched x s tAwakeEnd b₀ t` holds for every time `t`.

Why: one way, the upper end is dropped. The other way, the later step `j` is read at the time
`t := x[j].time`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: persistence from `b₀` on is persistence read up to every time, of the confirmed tips
read from `tAwakeEnd` on.

 before, it read the lower end `0`. -/
theorem confirmedPersistsFrom_iff (s tAwakeEnd b₀ : ℕ) :
    ConfirmedPersistsFrom M S A x s tAwakeEnd b₀ ↔
      ∀ t : ℕ, ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t := by
  constructor
  · intro h t v T P hv hTe hT hk hP w j hw hupd htk hb _
    exact h v T P hv hTe hT hk hP w j hw hupd htk hb
  · intro h v T P hv hTe hT hk hP w j hw hupd htk hb
    obtain ⟨t, ht⟩ := exists_nat_ge (x.time j)
    exact h t v T P hv hTe hT hk hP w j hw hupd htk hb ht

/-- `FinalizedCompatibleFrom M S Sched x s tAwakeEnd b₀` holds exactly when
`FinalizedCompatibleBetween M S Sched x s tAwakeEnd b₀ t` holds for every time `t`.

Why: one way, the upper end is dropped. The other way, the later step `j` is read at the time
`t := x[j].time`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: finalized compatibility from `b₀` on is finalized compatibility read up to every
time, of the confirmed tips read from `tAwakeEnd` on.

 before, it read the lower end `0`. -/
theorem finalizedCompatibleFrom_iff (s tAwakeEnd b₀ : ℕ) :
    FinalizedCompatibleFrom M S A x s tAwakeEnd b₀ ↔
      ∀ t : ℕ, FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t := by
  constructor
  · intro h t v T P hv hTe hT hk hP w j hw hb _
    exact h v T P hv hTe hT hk hP w j hw hb
  · intro h v T P hv hTe hT hk hP w j hw hb
    obtain ⟨t, ht⟩ := exists_nat_ge (x.time j)
    exact h t v T P hv hTe hT hk hP w j hw hb ht

/-- `CertificatesCompatibleWithAt M S Sched x H B j`: every progress certificate at a height greater
than `H` on the chain of a block a validator honest at step `j` holds then names by root a block
compatible with `B` at that height.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step.

Read aloud: at step `j`, no certificate at a height greater than `H` names a block conflicting
with `B`. -/
def CertificatesCompatibleWithAt (H : ℕ) (B : Block V) (j : ℕ) : Prop :=
  ∀ (w : V) (D T : Block V) (h : Height),
    w ∉ A.corrupted j → D ∈ (x.st j w).tree →
    ProgressCertOn D h T → H < h →
    ∃ E : Block V, (M.chainStateOf S.C E).h = h ∧ T.root = E.root ∧
      (E.AncestorEq B ∨ B.AncestorEq E)

/-- `BlocksTwoPastDescend M S Sched x B`: at every step, every block a validator honest then holds
whose chain-state height is at least `B`'s plus two is `B` or a descendant of `B`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block.

Read aloud: a chain conflicting with `B` gains at most one height past `B`'s. -/
def BlocksTwoPastDescend (B : Block V) : Prop :=
  ∀ (j : ℕ) (w : V) (D : Block V),
    w ∉ A.corrupted j → D ∈ (x.st j w).tree →
    (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h →
    B.AncestorEq D

/-- `AttestationsCompatibleWithBefore M S Sched x B H t₀ j`: every attestation a validator's
tick put on the wire at a step before `j` has height at most `H` when the tick is
before `t₀` and the sender is still outside the adversary set at `t₀`, and names by root an entry
block compatible with `B` at its height when the tick is at or after `t₀` and the sender is still
outside the adversary set once the steps of the tick's time are over.



No `v ∈ A.awakeAtTime x t` is asked beside the tick: a tick is by
a validator awake at its own step (the environment's `tick_active`).
For a tick at or after `t₀`, the sender is asked outside the adversary set after every step whose
time is the tick's; for a tick before `t₀`, at `t₀`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `j`: the step.

Read aloud: up to step `j`, the attestations ticks put on the wire before `t₀` by a validator still
honest at `t₀` have height at most `H`, and those sent from `t₀` on by a validator still honest once
the steps at the real time of its tick are over name an entry of a chain compatible with `B`. -/
def AttestationsCompatibleWithBefore (B : Block V) (H t₀ j : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V), i < j →
    x.lbl i = Event.tick v t →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i →
    (t < t₀ → v ∉ A.corruptedAtTime x t₀ → a.h ≤ H) ∧
    (t₀ ≤ t → v ∉ A.corruptedAtTime x (x.time i) → ∃ E : Block V, (E.AncestorEq B ∨ B.AncestorEq E) ∧
      IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = a.h ∧ a.T = E.root)

end Kit

section Period

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `HolderInvAt M S Sched x s B j w`: the lock holder `w`'s state at step `j`: (1) some lock
entry of `w` has the block `B` and the deadline `S.C.t_ (s + S.C.k) + 5 * S.C.Δ` of a slot-`s`
lock, or `B` is a strict ancestor of `w`'s finalized block; (2) `w`'s latest confirmed block is
`B` or a descendant of `B`, and `w` holds it; (3) every fast block is compatible with `B`;
(4) every lock entry live at some clock value no earlier than `w`'s own clock value
`x.clockValue j w` is on a block compatible with `B`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s`: the hand-over slot; `B`: the protected block; `j`: the step; `w`: the lock holder.

Read aloud: `w` still holds the hand-over lock or has finalized a strict descendant of `B`, its
latest confirmed block has not left `B`'s chain, and nothing it has fast-confirmed or locked
conflicts with `B`. -/
def HolderInvAt (s : ℕ) (B : Block V) (j : ℕ) (w : V) : Prop :=
  ((∃ e ∈ (x.st j w).lockEntries, M.le_B e = B ∧ M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) ∨
    B.ancestorStrict (x.st j w).finalized = true) ∧
  B.AncestorEq (x.st j w).latestConfirmed ∧
  (x.st j w).latestConfirmed ∈ (x.st j w).tree ∧
  (∀ D ∈ (x.st j w).fastBlocks, D.compatible B = true) ∧
  (∀ e ∈ (x.st j w).lockEntries, ∀ (t : ℕ), x.clockValue j w ≤ t →
    M.is_live (x.st j w) (t : Int) e = true → e.B.compatible B = true)

/-- `VotesExtendAt M S Sched x s B Δs b₀ b₁ s'`: every slot-`s'` Goldfish vote that a validator `u`
put on the wire at its tick at the vote time of `s'` is `u`'s vote for a block it holds that is
`B` or a descendant of `B`, for every `u ∈ holdersAt M S Sched s s'`, and, when the votes of slot
`s' − 1` were not owed inside the period (`VotesOwedInPeriod`), for every
`u ∈ honestActiveAt M S Sched s'`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `Δs`: the sync delay; `b₀`, `b₁`: the start and the end of the period; `s'`: the
  slot of the votes.

Read aloud: the holders always vote on `B`'s chain; everybody honest does at a slot whose
previous votes arrived in time. -/
def VotesExtendAt (s : ℕ) (B : Block V) (Δs b₀ b₁ s' : ℕ) : Prop :=
  (∀ u ∈ holdersAt M S A x s s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
  (¬ VotesOwedInPeriod M S Δs b₀ b₁ s' → ∀ u ∈ honestActiveAt M S A x s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u)

/-- `HandoverFacts M S Sched x tW s B H t₀ tAwakeEnd`: the facts right after the hand-over update at
the cutoff `c = M.supportCutoff S.C (s + 1)`: `H` is less than `B`'s chain-state height; every lock
holder, in the state its own tick to `c` leaves (`x.tickOutput w c`, the configuration
`x.tickStep w c + 1`), saved `B` for slot `s`, records `B`, and satisfies `HolderInvAt`; at every
configuration whose time is from `c` to the window's end `tW`, every validator outside the adversary set there has its caches
compatible with `B`, every certificate at a height greater than `H` on a held block names a block
compatible with `B`, and every honest attestation sent before that configuration is old (height at
most `H`, when sent before `t₀`) or names an entry compatible with `B`; every honest active voter of
slot `s + 1` voted on `B`'s chain; and every confirmed tip read at a step from `tAwakeEnd` to the
cutoff is `B` or an ancestor of `B`.

 the third, fourth and fifth clauses
are about the configuration as a whole and read every configuration whose time is from `c` to `tW`
(the whole window the clock bounds allow at `tW := c + ΔClockBehind`). Under the
shared clock of the condition on executions `EnvFactsBy` some configuration has the time `c`
(`time_hits`).





The variables:
- `M`: the model;
- `tW`: the end of the window in which the third to fifth clauses are read;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `H`: the height threshold; `t₀`: the time from which the attestations are new;
  `tAwakeEnd`: the time from which the confirmed tips are read.

Read aloud: right after its own hand-over update every honest validator that ran it holds a live
fast lock on `B` and records `B`; from the cutoff's time to `tW` nobody's caches, certificates or attestations
conflict with `B`; and what anyone had confirmed from `tAwakeEnd` on, read once it had processed the
step's time, is an ancestor of `B`. -/
def HandoverFacts (tW : ℝ) (s : ℕ) (B : Block V) (H t₀ tAwakeEnd : ℕ) : Prop :=
  H < (M.chainStateOf S.C B).h ∧
  (∀ w ∈ updaterAt M S A x s,
    (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
    (x.tickOutput w (M.supportCutoff S.C (s + 1))).latestConfirmed = B ∧
    HolderInvAt M S x s B (x.tickStep w (M.supportCutoff S.C (s + 1)) + 1) w) ∧
  (∀ (j : ℕ) (u : V), (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → u ∉ A.corrupted j →
    CachesCompatibleWith M S B H (x.st j u)) ∧
  (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → CertificatesCompatibleWithAt M S A x H B j) ∧
  (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → AttestationsCompatibleWithBefore M S A x B H t₀ j) ∧
  (∀ Δs b₀ b₁ : ℕ, VotesExtendAt M S A x s B Δs b₀ b₁ (s + 1)) ∧
  (∀ (v : V) (T : ℕ) (P : Block V), A.HonestThroughTime x (x.time T) v → tAwakeEnd ≤ x.time T →
    x.time T ≤ M.supportCutoff S.C (s + 1) →
    (∀ (t : ℕ), (t : ℝ) ≤ x.time T → ∀ T' : ℕ, T ≤ T' → x.lbl T' ≠ Event.tick v t) →
    P.AncestorEq (M.ac_confirmed (x.st T v)) → P.AncestorEq B)

end Period

section After

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

end After

end GoldilocksCorrectness.Record.Statements.Executions

