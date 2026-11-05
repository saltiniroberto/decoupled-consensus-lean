module
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Statements.Routines.CertificateDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Statements.Routines.ReceiveDefs

@[expose] public section

/-!
# The asynchrony claim: the definitions

The delivery premises restricted to the sends due by a bound (the delivery premises suspended on
one asynchronous period `[b₀, b₁)`, `SynchronyFromWakeOutside` and `CatchUpOnWakeOutside`, are
stated for any protocol in `Statements/Network/NetworkDefs.lean`); the lock holders' majority at the slots whose previous votes are owed
inside the period; the persistence of the confirmed tip and the finalized blocks' compatibility
with it, each also read up to a time `t`; the finality gadget's caches,
certificates and attestations relative to a block `B`; the lock holders' state; the facts at the
hand-over; and the invariant the period carries.


 the unbounded forms
`ConfirmedPersistsFrom`, `FinalizedCompatibleFrom` gained the lower end `tAwakeEnd` the same day
.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)
open GoldilocksCorrectness.Statements.View

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Delivery

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `SynchronyFromWakeUpTo S Sched x Δ GST ok b`: `SynchronyFromWake` restricted to the sends
whose ordinary deadline `max x[i + 1].time GST + Δ`, counted from the time the message is on the
wire, is at most `b`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class; `b`: the bound on the deadlines.

Read aloud: whatever an honest validator puts on the wire early enough to be due by `b` is
delivered, strictly before its ordinary deadline, to every validator awake and honest from the
time it is on the wire through that deadline. -/
def SynchronyFromWakeUpTo (Δ GST : ℕ) (ok : NamedObject V → Prop) (b : ℕ) : Prop :=
  ∀ (i : ℕ) (v : V) (sm : SignedMsg V (NamedObject V)),
    HonestSendAt Sched x.toTrace i sm → ok sm.msg →
    max x[i + 1].time GST + Δ ≤ b →
    v ∈ Sched.awakeThroughout (x[i + 1].time : Int) ((max x[i + 1].time GST + Δ : ℕ) : Int) →
    (∀ t : ℕ, x[i + 1].time ≤ t → t ≤ max x[i + 1].time GST + Δ → v ∉ Sched.adv (t : Int)) →
    ∃ j : ℕ, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧
      x[i].time ≤ x[j].time ∧ x[j].time < max x[i + 1].time GST + Δ

/-- `CatchUpOnWakeUpTo S Sched x Δ GST ok b`: `CatchUpOnWake` restricted to the wakes whose
deadline `max t GST + Δ` is at most `b`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class; `b`: the bound on the deadlines.

Read aloud: a validator that wakes at `t`, early enough for `max t GST + Δ ≤ b`, and stays awake
and honest through that deadline, receives in that time every message of the class `ok` an honest
validator put on the wire before `t` (`x[i + 1].time < t`). -/
def CatchUpOnWakeUpTo (Δ GST : ℕ) (ok : NamedObject V → Prop) (b : ℕ) : Prop :=
  ∀ (i : ℕ) (v : V) (sm : SignedMsg V (NamedObject V)) (t : ℕ),
    HonestSendAt Sched x.toTrace i sm → ok sm.msg →
    x[i + 1].time < t → max t GST + Δ ≤ b →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.awake ((t : Int) - 1) →
    v ∈ Sched.awakeThroughout (t : Int) ((max t GST + Δ : ℕ) : Int) →
    (∀ t' : ℕ, t ≤ t' → t' ≤ max t GST + Δ → v ∉ Sched.adv (t' : Int)) →
    ∃ j : ℕ, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧
      t ≤ x[j].time ∧ x[j].time < max t GST + Δ

end Delivery

section Kit

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `holdersAt S Sched s s'`: the lock holders of slot `s` that act at slot `s'`, that is the
validators of `updaterAt S Sched s` (awake through the update of slot `s`, honest at its cutoff)
that are in `honestActiveAt S Sched s'`.

The variables:
- `S`, `Sched`: the setup, the schedule; `s`: the hand-over slot; `s'`: the slot they act at.

Read aloud: the validators that ran slot `s`'s update and are honest and active at slot `s'`. -/
def holdersAt (s s' : ℕ) : Finset V :=
  updaterAt S Sched s ∩ honestActiveAt S Sched s'

/-- `HoldersOutweighWhereOwed S Sched s b₀ b₁`: at every slot `s' ≥ s + 2` with
`b₀ < supportCutoff S (s' − 1) < b₁`, the members of slot `s'`'s committee that are not in
`holdersAt S Sched s s'` are fewer than those that are.

The variables:
- `S`, `Sched`: the setup, the schedule; `s`: the hand-over slot; `b₀`, `b₁`: the start and the
  end of the period.

Read aloud: wherever the previous slot's votes are owed inside the period, the lock holders
outweigh the rest of the committee. -/
def HoldersOutweighWhereOwed (s b₀ b₁ : ℕ) : Prop :=
  ∀ s' : ℕ, s + 2 ≤ s' → b₀ < supportCutoff S (s' - 1) → supportCutoff S (s' - 1) < b₁ →
    |S.P.committee s' \ holdersAt S Sched s s'| < |holdersAt S Sched s s' ∩ S.P.committee s'|

/-- `VotesOwedInPeriod S b₀ b₁ s'`: the votes of slot `s' − 1` have their ordinary delivery
deadline `supportCutoff S (s' − 1)` strictly inside the period. A slot of which this does not
hold is one whose previous slot's honest votes reach every honest active voter before its view
freeze.

The variables:
- `S`: the setup; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot.

Read aloud: at slot `s'`, a voter's view of the previous slot's votes is the adversary's choice. -/
def VotesOwedInPeriod (b₀ b₁ s' : ℕ) : Prop :=
  b₀ < supportCutoff S (s' - 1) ∧ supportCutoff S (s' - 1) < b₁

/-- `ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀`: every block `P` that is, at a step `T` of
time at least `tAwakeEnd` and at most `supportCutoff S (s + 1)`, the confirmed tip of a validator
`v` honest through `T`, or an ancestor of it, is, at every step `j` of time at least `b₀`, the
confirmed tip or an ancestor of the confirmed tip of every validator `w ∈ updaterAt S Sched s`
honest through `j`.



Defined as its view form: `ConfirmedPersistsFromV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedPersistsFrom_unfold` (`Proofs/View/Bridges.lean`) reads it on the execution's
node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: every block that is `v`'s confirmed tip at a step from `tAwakeEnd` to the hand-over
update, or an ancestor of it, is, at every step from `b₀` on, the confirmed tip or an ancestor of
the confirmed tip of every validator honest through that step that ran the hand-over update. -/
def ConfirmedPersistsFrom (s tAwakeEnd b₀ : ℕ) : Prop :=
  ConfirmedPersistsFromV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s tAwakeEnd b₀

/-- `FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀`: every block `P` that is, at a step `T` of
time at least `tAwakeEnd` and at most `supportCutoff S (s + 1)`, the confirmed tip of a validator
honest through `T`, or an ancestor of it, is compatible with the finalized block of every
validator honest through any step of time at least `b₀`.



Defined as its view form: `FinalizedCompatibleFromV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `finalizedCompatibleFrom_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: from `b₀` on, no honest validator finalizes a block conflicting with what was
confirmed from `tAwakeEnd` to the hand-over update. -/
def FinalizedCompatibleFrom (s tAwakeEnd b₀ : ℕ) : Prop :=
  FinalizedCompatibleFromV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s tAwakeEnd b₀

/-- `ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t`: `ConfirmedPersistsFrom S Sched x s
tAwakeEnd b₀` read up to the time `t`. Every block `P` that is, at a step `T` of time
at least `tAwakeEnd` and at most `supportCutoff S (s + 1)`, the confirmed tip of a validator `v`
honest through `T`, or an ancestor of it, is, at every step `j` of time at least `b₀` and at most
`t`, the confirmed tip or an ancestor of the confirmed tip of every validator
`w ∈ updaterAt S Sched s` honest through `j`. `ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀` is
this for every time `t` (`confirmedPersistsFrom_iff`).



Defined as its view form: `ConfirmedPersistsBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedPersistsBetween_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period; `t`: the time up to which the later steps are read.

Read aloud: every block that is `v`'s confirmed tip at a step from `tAwakeEnd` to the hand-over
update, or an ancestor of it, is, at every step from `b₀` up to `t`, the confirmed tip or an
ancestor of the confirmed tip of every validator honest through that step that ran the hand-over
update.

 -/
def ConfirmedPersistsBetween (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ConfirmedPersistsBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s tAwakeEnd b₀ t

/-- `FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t`: `FinalizedCompatibleFrom S Sched x s
tAwakeEnd b₀` read up to the time `t`. Every block `P` that is, at a step `T` of
time at least `tAwakeEnd` and at most `supportCutoff S (s + 1)`, the confirmed tip of a validator
honest through `T`, or an ancestor of it, is compatible with the finalized block of every
validator honest through any step of time at least `b₀` and at most `t`.
`FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀` is this for every time `t`
(`finalizedCompatibleFrom_iff`).



Defined as its view form: `FinalizedCompatibleBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `finalizedCompatibleBetween_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period; `t`: the time up to which the later steps are read.

Read aloud: from `b₀` up to `t`, no honest validator finalizes a block conflicting with what was
confirmed from `tAwakeEnd` to the hand-over update.

 -/
def FinalizedCompatibleBetween (s tAwakeEnd b₀ t : ℕ) : Prop :=
  FinalizedCompatibleBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s tAwakeEnd b₀ t

/-- `ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀` holds exactly when `ConfirmedPersistsBetween
S Sched x s tAwakeEnd b₀ t` holds for every time `t`.

Why: one way, the upper end is dropped. The other way, the later step `j` is read at the time
`t := x[j].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: persistence from `b₀` on is persistence read up to every time, of the confirmed tips
read from `tAwakeEnd` on.

 before, it read the lower end `0`. -/
theorem confirmedPersistsFrom_iff (s tAwakeEnd b₀ : ℕ) :
    ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀ ↔
      ∀ t : ℕ, ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t := by
  constructor
  · intro h t v T P hv hTe hT hP w j hw hupd hb _
    exact h v T P hv hTe hT hP w j hw hupd hb
  · intro h v T P hv hTe hT hP w j hw hupd hb
    exact h x[j].time v T P hv hTe hT hP w j hw hupd hb le_rfl

/-- `FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀` holds exactly when
`FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t` holds for every time `t`.

Why: one way, the upper end is dropped. The other way, the later step `j` is read at the time
`t := x[j].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot;
  `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the start of the
  period.

Read aloud: finalized compatibility from `b₀` on is finalized compatibility read up to every
time, of the confirmed tips read from `tAwakeEnd` on.

 before, it read the lower end `0`. -/
theorem finalizedCompatibleFrom_iff (s tAwakeEnd b₀ : ℕ) :
    FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀ ↔
      ∀ t : ℕ, FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t := by
  constructor
  · intro h t v T P hv hTe hT hP w j hw hb _
    exact h v T P hv hTe hT hP w j hw hb
  · intro h v T P hv hTe hT hP w j hw hb
    exact h x[j].time v T P hv hTe hT hP w j hw hb le_rfl

/-- `CertificatesCompatibleWithAt S Sched x H B j`: every progress certificate at a height greater
than `H` on the chain of a block a validator honest at step `j` holds then names by root a block
compatible with `B` at that height.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step.

Read aloud: at step `j`, no certificate at a height greater than `H` names a block conflicting
with `B`. -/
def CertificatesCompatibleWithAt (H : ℕ) (B : Block V) (j : ℕ) : Prop :=
  ∀ (w : V) (D T : Block V) (h : Height),
    w ∉ Sched.adv (x[j].time : Int) → D ∈ (x[j][w].st).S.T →
    ProgressCertOn D h T → H < h →
    ∃ E : Block V, (chainStateOf S.C E).h = h ∧ T.root = E.root ∧
      (E.AncestorEq B ∨ B.AncestorEq E)

/-- `BlocksTwoPastDescend S Sched x B`: at every step, every block a validator honest then holds
whose chain-state height is at least `B`'s plus two is `B` or a descendant of `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block.

Read aloud: a chain conflicting with `B` gains at most one height past `B`'s. -/
def BlocksTwoPastDescend (B : Block V) : Prop :=
  ∀ (j : ℕ) (w : V) (D : Block V),
    w ∉ Sched.adv (x[j].time : Int) → D ∈ (x[j][w].st).S.T →
    (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h →
    B.AncestorEq D

/-- `AttestationsCompatibleWithBefore S Sched x B H t₀ j`: every attestation an honest awake
validator put on the wire at a tick at a step before `j` has height at most `H` when the tick is
before `t₀`, and names by root an entry block compatible with `B` at its height when the tick is
at or after `t₀`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `j`: the step.

Read aloud: up to step `j`, the honest attestations are old (height at most `H`) or name an
entry of a chain compatible with `B`. -/
def AttestationsCompatibleWithBefore (B : Block V) (H t₀ j : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V), i < j →
    x.lbl i = AtomicAction.tickAllAwake t →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.adv (t : Int) →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent →
    (t < t₀ → a.h ≤ H) ∧
    (t₀ ≤ t → ∃ E : Block V, (E.AncestorEq B ∨ B.AncestorEq E) ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = a.h ∧ a.T = E.root)

end Kit

section Period

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `HolderInvAt S Sched x s B j w`: the lock holder `w`'s state at step `j`: (1) the lock entry
on `B` with the deadline of a slot-`s` lock, `LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)`,
is among `w`'s lock entries, or `B` is a strict ancestor of `w`'s finalized block
(`B.ancestorStrict (x[j][w].st).S.F`); (2) the record of the confirmed tip is `B` or a descendant
of `B`, and `w` holds it; (3) every fast block is compatible with `B`; (4) every lock entry live at
the step's time is on a block compatible with `B`.

The second case of (1) is the one in which `w` no longer needs the lock: once its finalized block
is a strict descendant of `B`, `B` is outside the tree of `w`'s frame, the revocation deletes the
entry on `B`, and every block the walk, the update and the fast test reach is a descendant of the
finalized block, so of `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `j`: the step; `w`: the lock holder.

Read aloud: `w` still holds the hand-over lock or has finalized a strict descendant of `B`, its
record has not left `B`'s chain, and nothing it has fast-confirmed or locked conflicts with
`B`. -/
def HolderInvAt (s : ℕ) (B : Block V) (j : ℕ) (w : V) : Prop :=
  (LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈ (x[j][w].st).A.lock_entries ∨
    B.ancestorStrict (x[j][w].st).S.F = true) ∧
  B.AncestorEq (x[j][w].st).A.latest_confirmed ∧
  (x[j][w].st).A.latest_confirmed ∈ (x[j][w].st).S.T ∧
  (∀ D ∈ (x[j][w].st).A.fast_blocks, D.compatible B = true) ∧
  (∀ e ∈ (x[j][w].st).A.lock_entries,
    is_live (fg_to_ac (x[j][w].st).S) (x[j].time : Int) e = true → e.B.compatible B = true)

/-- `VotesExtendAt S Sched x s B b₀ b₁ s'`: every slot-`s'` Goldfish vote that a validator `u`
put on the wire at its tick at the vote time of `s'` is `u`'s vote for a block it holds that is
`B` or a descendant of `B`, for every `u ∈ holdersAt S Sched s s'`, and, when the votes of slot
`s' − 1` were not owed inside the period (`VotesOwedInPeriod`), for every
`u ∈ honestActiveAt S Sched s'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes.

Read aloud: the holders always vote on `B`'s chain; everybody honest does at a slot whose
previous votes arrived in time. -/
def VotesExtendAt (s : ℕ) (B : Block V) (b₀ b₁ s' : ℕ) : Prop :=
  (∀ u ∈ holdersAt S Sched s s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
  (¬ VotesOwedInPeriod S b₀ b₁ s' → ∀ u ∈ honestActiveAt S Sched s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u)

/-- `HandoverFacts S Sched x s B H t₀ tAwakeEnd`: the facts at the step `stepBefore x
(supportCutoff S (s + 1) + 1)`, whose configuration is the one right after the hand-over update:
`H` is less than `B`'s chain-state height; every lock holder saved `B` for slot `s`, records `B`,
and satisfies `HolderInvAt`; every validator honest at the cutoff has its caches compatible with
`B`; every certificate at a height greater than `H` on a held block names a block compatible with
`B`; every honest attestation sent before then is old (height at most `H`, when sent before `t₀`)
or names an entry compatible with `B`; every honest active voter of slot `s + 1` voted on `B`'s
chain; and every confirmed tip read at a step from `tAwakeEnd` to the cutoff is `B` or an ancestor
of `B`.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `H`: the height threshold; `t₀`: the time from which the attestations are new;
  `tAwakeEnd`: the time from which the confirmed tips are read.

Read aloud: right after the hand-over update every honest validator that ran it holds a live fast
lock on `B` and records `B`; nobody's caches, certificates or attestations conflict with `B`; and
what anyone had confirmed from `tAwakeEnd` on is an ancestor of `B`. -/
def HandoverFacts (s : ℕ) (B : Block V) (H t₀ tAwakeEnd : ℕ) : Prop :=
  H < (chainStateOf S.C B).h ∧
  (∀ w ∈ updaterAt S Sched s,
    (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s = some B ∧
    (stateBefore x (supportCutoff S (s + 1) + 1) w).A.latest_confirmed = B ∧
    HolderInvAt S Sched x s B (stepBefore x (supportCutoff S (s + 1) + 1)) w) ∧
  (∀ u : V, u ∉ Sched.adv ((supportCutoff S (s + 1) : ℕ) : Int) →
    CachesCompatibleWith S B H (stateBefore x (supportCutoff S (s + 1) + 1) u)) ∧
  CertificatesCompatibleWithAt S Sched x H B (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
  AttestationsCompatibleWithBefore S Sched x B H t₀ (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
  (∀ b₀ b₁ : ℕ, VotesExtendAt S Sched x s B b₀ b₁ (s + 1)) ∧
  (∀ (v : V) (T : ℕ) (P : Block V), HonestThrough x T v → tAwakeEnd ≤ x[T].time →
    x[T].time ≤ supportCutoff S (s + 1) →
    P.AncestorEq (confirmedOf (x[T][v].st)) → P.AncestorEq B)

end Period

section After

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end After

end GoldilocksCorrectness.Statements.Executions
