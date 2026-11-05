module
public import GoldilocksCorrectness.Statements.Network.ViewVocabDefs

@[expose] public section

/-!
# The network premises, for any protocol under the sts framework

The premises the top statements take on the network and on the adversary, stated for any protocol
under the sts framework's atomic semantics: they read a run's configurations and labels, the
schedule's awake and adversary sets, and the message type, and nothing of the protocol's own
structure. A protocol supplies what they leave as arguments: the delay, the class of messages a
delay is promised for, the operations of `ViewVocab`, a threshold.

They are stated over a `Trace`, a sequence of configurations and labels with no step proofs, so
that the same premise reads an execution (`x.toTrace`) or a trace whose node states have been
mapped to a view. Nothing is proved here except the two equalities that read an execution's trace
as the execution.

## The trace

- `Trace`: the configurations and the labels; `x[i]`, the configuration after `i` steps;
- `AtomicExec.toTrace`: an execution with its proofs forgotten.

## The premises

- `HonestThroughTime`: a validator outside the adversary set at every time up to a time;
- `TimeDiverges`: every time is reached;
- `HonestSendAt`: a step put a message on the wire, its signer honest;
- `SynchronyFromWake`, `CatchUpOnWake`: synchrony from the start of the receiver's awake window,
  and catch-up on wake, for the messages of one class with one delay;
- `SynchronyFromWakeBy`, `CatchUpOnWakeBy`: the same with the deadline a function of the time;
- `deadlineOutside`, `SynchronyFromWakeOutside`, `CatchUpOnWakeOutside`: the two suspended on one
  asynchronous period;
- `Unforgeability`: a message whose object, or an object it includes, is attributed to an honest
  validator is on the wire under that validator's own signature;
- `AdversaryFewerThanThirdUntil`, `AdversaryFewerThanQuorumUntil`: fewer than a third of a number,
  or fewer than a quorum, of the validators have been in the adversary set up to a time.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Statements.Network

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg Config)

/-! ## The trace -/

/-- `Trace Node Msg St Ev`: a run's configurations and labels, with no step proofs. -/
structure Trace (Node Msg St Ev : Type) where
  /-- `cfg i`: the configuration after `i` steps. -/
  cfg : (i : ℕ) → Config Node Msg St
  /-- `lbl i`: the label of the step `i`. -/
  lbl : (i : ℕ) → AtomicAction Node Msg Ev

/-- `x[i]` is the configuration after `i` steps, as for an execution. -/
instance {Node Msg St Ev : Type} :
    GetElem (Trace Node Msg St Ev) ℕ (Config Node Msg St) (fun _ _ => True) where
  getElem x i _ := x.cfg i

end GoldilocksCorrectness.Statements.Network

namespace Framework.StsMultisetLog.AtomicExec

open GoldilocksCorrectness.Statements.Network (Trace)

variable {Node Msg St Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg St Ev} {Sched : Schedule Node}

/-- `x.toTrace`: the execution `x` with its initial-state and step proofs forgotten.

Read aloud: the configurations and labels of `x`. -/
def toTrace (x : AtomicExec Pr Sched) : Trace Node Msg St Ev := ⟨x.cfg, x.lbl⟩

/-- The configuration after `i` steps of `x.toTrace` is the one of `x`. -/
@[simp] theorem toTrace_getElem (x : AtomicExec Pr Sched) (i : ℕ) : x.toTrace[i] = x[i] := rfl

/-- The labels of `x.toTrace` are the ones of `x`. -/
@[simp] theorem toTrace_lbl (x : AtomicExec Pr Sched) : x.toTrace.lbl = x.lbl := rfl

end Framework.StsMultisetLog.AtomicExec

namespace GoldilocksCorrectness.Statements.Network

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg Config)

/-! ## The premises -/

/-- `HonestThroughTime Sched t v`: `v` is outside the adversary set at every time at most `t`.

The variables:
- `Sched`: the schedule; `t`: the time; `v`: the validator.

Read aloud: `v` has not been in the adversary set at any time up to `t`. -/
def HonestThroughTime {Node : Type} (Sched : Schedule Node) (t : Int) (v : Node) : Prop :=
  ∀ t' ≤ t, v ∉ Sched.adv t'

/-- `TimeDiverges x`: every time is reached by some configuration of `x`.

The variables:
- `x`: the trace.

Read aloud: for every time `t`, some step of the run is at the time `t` or later. -/
def TimeDiverges {Node Msg St Ev : Type} (x : Trace Node Msg St Ev) : Prop :=
  ∀ t : ℕ, ∃ i : ℕ, t ≤ x[i].time

section Delivery

variable {Node Msg St Ev : Type} [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
  (Sched : Schedule Node) (x : Trace Node Msg St Ev)

omit [Fintype Node] in
/-- `HonestSendAt Sched x i sm`: the step `i` of `x` added a copy of the signed message `sm` to
the sent log, and the signer of `sm` is outside the adversary set at the time the step starts
from. A node's own send and a re-send of what it received each count.

The variables:
- `Sched`: the schedule; `x`: the trace; `i`: the step; `sm`: the signed message.

Read aloud: at the step `i`, an honest validator put `sm` on the wire, as its own send or as a
re-send of what it received. -/
def HonestSendAt (i : ℕ) (sm : SignedMsg Node Msg) : Prop :=
  sm ∈ x[i + 1].sent - x[i].sent ∧ sm.sender ∉ Sched.adv (x[i].time : Int)

/-- Synchrony, as a delivery step, for the messages in the class `ok`: such a message an honest
validator put on the wire at the step `i` is delivered to every validator that is awake and
honest at every time from the time the message is on the wire, `x[i + 1].time`, through the
deadline `max x[i + 1].time GST + Δ`, counted from the time the message is on the wire, at a step
after `i` at a time from `x[i].time` on and strictly before the deadline. A node's own send at a
tick and a re-send of what it received are treated alike: each is on the wire at the time of the
configuration its step produces. The class `ok` is a parameter because a protocol may be designed for several
delays, each promised only for its own class of messages. The promise is made only to a receiver
outside the adversary set throughout the window, since the framework delivers only to such a
validator.

The variables:
- `Sched`: the schedule; `x`: the trace; `Δ`: the delay bound; `GST`: the time from which the
  network is synchronous; `ok`: the class of messages the promise is about;
- `i`: the step of the send; `v`: the receiver; `sm`: the signed message;
- `j`: the step of the delivery.

Read aloud: whatever an honest validator puts on the wire that is in the class `ok` is delivered,
strictly before the later of the time it is on the wire and `GST` plus `Δ`, to every validator
awake and honest from the time it is on the wire through that deadline. -/
def SynchronyFromWake (Δ GST : ℕ) (ok : Msg → Prop) : Prop :=
  ∀ (i : ℕ) (v : Node) (sm : SignedMsg Node Msg),
    HonestSendAt Sched x i sm → ok sm.msg →
    v ∈ Sched.awakeThroughout (x[i + 1].time : Int) ((max x[i + 1].time GST + Δ : ℕ) : Int) →
    -- `v` is outside the adversary set at every time of the window
    (∀ t : ℕ, x[i + 1].time ≤ t → t ≤ max x[i + 1].time GST + Δ → v ∉ Sched.adv (t : Int)) →
    ∃ j : ℕ, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧
      x[i].time ≤ x[j].time ∧ x[j].time < max x[i + 1].time GST + Δ

/-- Catch-up on wake, for the messages in the class `ok`: such a message an honest validator put on
the wire at the step `i`, on the wire before the time `t` at which the validator `v` wakes
(`x[i + 1].time < t`, the time of the configuration the step produces), is delivered to `v`
at a step after `i`, at a time from `t` on and strictly before `max t GST + Δ`, provided `v` stays
awake and honest throughout `[t, max t GST + Δ]`. Sends at or after the wake are covered by
`SynchronyFromWake`. The class `ok` is a parameter for the reason `SynchronyFromWake` gives.

The variables:
- `Sched`: the schedule; `x`: the trace; `Δ`: the delay bound; `GST`: the time from which the
  network is synchronous; `ok`: the class of messages the promise is about;
- `i`: the step of the send; `v`: the validator that wakes; `sm`: the signed message; `t`: the
  time `v` wakes at;
- `j`: the step of the delivery.

Read aloud: a validator that wakes at `t`, and stays awake and honest for a delay after the later
of `t` and `GST`, receives in that time every message of the class `ok` an honest validator put on
the wire before `t`. -/
def CatchUpOnWake (Δ GST : ℕ) (ok : Msg → Prop) : Prop :=
  ∀ (i : ℕ) (v : Node) (sm : SignedMsg Node Msg) (t : ℕ),
    HonestSendAt Sched x i sm → ok sm.msg →
    -- the message was on the wire before `t`
    x[i + 1].time < t →
    -- `v` wakes at `t`: awake at `t`, asleep at `t − 1`
    v ∈ Sched.awake (t : Int) → v ∉ Sched.awake ((t : Int) - 1) →
    v ∈ Sched.awakeThroughout (t : Int) ((max t GST + Δ : ℕ) : Int) →
    -- `v` is outside the adversary set at every time of the window
    (∀ t' : ℕ, t ≤ t' → t' ≤ max t GST + Δ → v ∉ Sched.adv (t' : Int)) →
    ∃ j : ℕ, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧
      t ≤ x[j].time ∧ x[j].time < max t GST + Δ

/-- `deadlineOutside Δ GST b₀ b₁ t`: the delivery deadline of a send at time `t` around one
asynchronous period `[b₀, b₁)`.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the time of the send.

Read aloud: a send at time `t` whose ordinary deadline `max t GST + Δ` is at or before `b₀` keeps
that deadline; any other send is delivered within `Δ` of the latest of its own time, `b₁` and
`GST`. -/
def deadlineOutside (Δ GST b₀ b₁ t : ℕ) : ℕ :=
  if max t GST + Δ ≤ b₀ then max t GST + Δ else max t (max b₁ GST) + Δ

/-- `SynchronyFromWakeBy Sched x deadline ok`: `SynchronyFromWake` with the deadline a function
of the send's time, the time the message is on the wire: every message of the class `ok` an honest
validator puts on the wire at step `i` is delivered, at a later step of time in
`[x[i].time, deadline x[i + 1].time)`, to every validator awake and outside the adversary set from
the time it is on the wire, `x[i + 1].time`, through that deadline.

The variables:
- `Sched`: the schedule; `x`: the trace; `deadline t`: the delivery deadline of a message on the
  wire at time `t`; `ok`: the class of messages.

Read aloud: what an honest validator puts on the wire reaches, before its deadline, every
validator that stays awake and honest until then. -/
def SynchronyFromWakeBy (deadline : ℕ → ℕ) (ok : Msg → Prop) : Prop :=
  ∀ (i : ℕ) (v : Node) (sm : SignedMsg Node Msg),
    HonestSendAt Sched x i sm → ok sm.msg →
    v ∈ Sched.awakeThroughout (x[i + 1].time : Int) ((deadline x[i + 1].time : ℕ) : Int) →
    (∀ t : ℕ, x[i + 1].time ≤ t → t ≤ deadline x[i + 1].time → v ∉ Sched.adv (t : Int)) →
    ∃ j : ℕ, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧
      x[i].time ≤ x[j].time ∧ x[j].time < deadline x[i + 1].time

/-- `CatchUpOnWakeBy Sched x deadline ok`: `CatchUpOnWake` with the deadline a function of the
wake's time: a validator awake at `t` and not at `t − 1`, awake and outside the adversary set from
`t` through `deadline t`, receives, at a later step of time in `[t, deadline t)`, every message of
the class `ok` an honest validator put on the wire before `t` (`x[i + 1].time < t`).

The variables:
- `Sched`: the schedule; `x`: the trace; `deadline t`: the delivery deadline of a wake at time
  `t`; `ok`: the class of messages.

Read aloud: a validator that wakes and stays awake and honest until the deadline catches up on
every earlier honest message. -/
def CatchUpOnWakeBy (deadline : ℕ → ℕ) (ok : Msg → Prop) : Prop :=
  ∀ (i : ℕ) (v : Node) (sm : SignedMsg Node Msg) (t : ℕ),
    HonestSendAt Sched x i sm → ok sm.msg →
    x[i + 1].time < t →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.awake ((t : Int) - 1) →
    v ∈ Sched.awakeThroughout (t : Int) ((deadline t : ℕ) : Int) →
    (∀ t' : ℕ, t ≤ t' → t' ≤ deadline t → v ∉ Sched.adv (t' : Int)) →
    ∃ j : ℕ, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧
      t ≤ x[j].time ∧ x[j].time < deadline t

/-- `SynchronyFromWakeOutside Sched x Δ GST ok b₀ b₁`: synchrony suspended on the asynchronous
period `[b₀, b₁)`, that is `SynchronyFromWakeBy` at the deadline `deadlineOutside Δ GST b₀ b₁`.

The variables:
- `Sched`: the schedule; `x`: the trace; `Δ`: the delay; `GST`: the time from which the network
  is synchronous before `b₀`; `ok`: the class of messages; `b₀`, `b₁`: the start and the end of
  the period.

Read aloud: a send due by `b₀` is delivered as in the synchronous network; any other send is
delivered within `Δ` of the latest of the time it is on the wire, `b₁` and `GST`. -/
def SynchronyFromWakeOutside (Δ GST : ℕ) (ok : Msg → Prop) (b₀ b₁ : ℕ) : Prop :=
  SynchronyFromWakeBy Sched x (deadlineOutside Δ GST b₀ b₁) ok

/-- `CatchUpOnWakeOutside Sched x Δ GST ok b₀ b₁`: catch-up on wake suspended on the asynchronous
period `[b₀, b₁)`, that is `CatchUpOnWakeBy` at the deadline `deadlineOutside Δ GST b₀ b₁`.

The variables:
- `Sched`: the schedule; `x`: the trace; `Δ`: the delay; `GST`: the time from which the network
  is synchronous before `b₀`; `ok`: the class of messages; `b₀`, `b₁`: the start and the end of
  the period.

Read aloud: a wake whose ordinary deadline is at or before `b₀` catches up as in the synchronous
network; any other catches up within `Δ` of the latest of its own time, `b₁` and `GST`. -/
def CatchUpOnWakeOutside (Δ GST : ℕ) (ok : Msg → Prop) (b₀ b₁ : ℕ) : Prop :=
  CatchUpOnWakeBy Sched x (deadlineOutside Δ GST b₀ b₁) ok

end Delivery

/-- `Unforgeability W Sched x`: a message on the wire whose object, or an object it includes, is
attributed to a validator outside the adversary set at every time up to the step is also on the
wire under that validator's own signature. Who an object is attributed to and what it includes are
read off the vocabulary `W`. -/
structure Unforgeability {Node B Msg St Ev : Type} (W : ViewVocab Node B Msg)
    (Sched : Schedule Node) (x : Trace Node Msg St Ev) : Prop where
  /-- Whenever the sent log after `i` steps holds a message `sm` whose object is attributed to the
  validator `u`, and `u` is outside the adversary set at every time up to the time after `i`
  steps, the sent log after `i` steps holds `u`'s own signed message with that object. -/
  unforgeable : ∀ (i : ℕ) (sm : SignedMsg Node Msg) (u : Node),
    sm ∈ x[i].sent → W.author sm.msg = some u → HonestThroughTime Sched (x[i].time : Int) u →
    (⟨u, sm.msg⟩ : SignedMsg Node Msg) ∈ x[i].sent
  /-- The same for every object `o'` that the object of `sm` includes. -/
  carried : ∀ (i : ℕ) (sm : SignedMsg Node Msg) (o' : Msg) (u : Node),
    sm ∈ x[i].sent → W.carries sm.msg o' → W.author o' = some u →
    HonestThroughTime Sched (x[i].time : Int) u →
    (⟨u, o'⟩ : SignedMsg Node Msg) ∈ x[i].sent

/-- `AdversaryFewerThanThirdUntil Sched n t`: every set of validators each of which is in the
adversary set at some time at most `t` has fewer than a third of `n` members.

The variables:
- `Sched`: the schedule; `n`: the number of validators; `t`: the time up to which the adversary
  set is counted.

Read aloud: fewer than a third of the `n` validators have been in the adversary set at some time
up to `t`. -/
def AdversaryFewerThanThirdUntil {Node : Type} (Sched : Schedule Node) (n : ℕ) (t : Int) : Prop :=
  ∀ A : Finset Node, (∀ v ∈ A, ∃ t' : Int, t' ≤ t ∧ v ∈ Sched.adv t') → 3 * A.card < n

/-- `AdversaryFewerThanQuorumUntil Sched q t`: every set of validators each of which is in the
adversary set at some time at most `t` has fewer than `q` members. The shape of
`AdversaryFewerThanThirdUntil`, with the quorum `q` in place of a third of the validators.

The variables:
- `Sched`: the schedule; `q`: the quorum; `t`: the time up to which the adversary set is counted.

Read aloud: fewer than a quorum `q` of validators have been in the adversary set at some time up
to `t`. -/
def AdversaryFewerThanQuorumUntil {Node : Type} (Sched : Schedule Node) (q : ℕ) (t : Int) :
    Prop :=
  ∀ A : Finset Node, (∀ v ∈ A, ∃ t' : Int, t' ≤ t ∧ v ∈ Sched.adv t') → A.card < q

/-- `AdversaryFewerThanTwoThirdsUntil Sched n t`: every set of validators each of which is in the
adversary set at some time at most `t` has fewer than two thirds of `n` members. The shape of
`AdversaryFewerThanThirdUntil`, with two thirds in place of a third of the validators.

The variables:
- `Sched`: the schedule; `n`: the number of validators; `t`: the time up to which the adversary
  set is counted.

Read aloud: fewer than two thirds of the `n` validators have been in the adversary set at some
time up to `t`. -/
def AdversaryFewerThanTwoThirdsUntil {Node : Type} (Sched : Schedule Node) (n : ℕ) (t : Int) :
    Prop :=
  ∀ A : Finset Node, (∀ v ∈ A, ∃ t' : Int, t' ≤ t ∧ v ∈ Sched.adv t') → 3 * A.card < 2 * n

end GoldilocksCorrectness.Statements.Network
