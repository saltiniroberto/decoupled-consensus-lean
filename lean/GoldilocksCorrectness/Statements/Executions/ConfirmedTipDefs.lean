module
public import GoldilocksCorrectness.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Statements.Routines.NodeDefs
public import GoldilocksCorrectness.Statements.View.SlotConclusionDefs
public import GoldilocksCorrectness.Statements.View.GoldilocksViewDefs

@[expose] public section

/-!
# The confirmed tip after the healed slot: the definitions

The definitions the statements of `ConfirmedTipStatements.lean` read:

- `confirmedOf n`, the confirmed tip of the node state `n`: the available chain's
  `ac_confirmed` over the frame of `n`'s FG state;
- `IsHonestConfirmation S Sched x s₀ L`, `L` is a confirmation that an updater of a slot at or
  after `s₀` holds right after its update;
- `ConfirmedAgreeAfterHealing S Sched x tE` and `ConfirmedMonotoneAfterHealing S Sched x tE`, the
  agreement and the growth of the confirmed tips of honest validators from the time `tE` on
  (Lemma 90's two parts), and `ConfirmedAgreeBetween S Sched x tE t`,
  `ConfirmedMonotoneBetween S Sched x tE t`, the two read up to the time `t`, with
  `confirmedAgreeAfterHealing_iff`, `confirmedMonotoneAfterHealing_iff`: each is the one read up to
  every time;
- `RootCollisionAtProposal`, `ConfirmedIncludedAfterHealing S Sched x tE`, the inclusion of the
  honest proposal (Lemma 90's third part), and `ConfirmedIncludedBetween S Sched x tE t`, the
  inclusion read up to the time `t`, with `confirmedIncludedAfterHealing_iff`: the
  inclusion is the inclusion read up to every time;
- `ConfirmedExtendedByHonestProposals S Sched x tE` and
  `ConfirmedExtendedByHonestProposalsBetween S Sched x tE t`, every honest proposal a strict
  descendant of the confirmed tips honest validators had from `tE` until its slot started, with no upper end and read up to the time `t`.



Every conclusion definition of this page is defined as its view form: the definition of the same name with a `V` suffix on `Statements/View/`, with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of the execution `x`,
`projectTrace nodeView x.toTrace`. The lemmas `…_unfold` of `Proofs/View/Bridges.lean` read each on
the execution's node states.
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (slotStart supportCutoff proposalWindowStart)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.View

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `IsHonestConfirmation S Sched x s₀ L`: for some slot `s` at or after `s₀`, some validator of
`updaterAt S Sched s` holds `L` as its confirmation of slot `s` on its node state before the time
after the support cutoff of slot `s + 1`, right after its update.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot;
- `L`: the block.

Read aloud: `L` is the confirmation of some slot at or after `s₀` that some updater of that slot
holds right after its update. -/
def IsHonestConfirmation (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₀ : ℕ) (L : Block V) : Prop :=
  ∃ s : ℕ, s₀ ≤ s ∧ ∃ v ∈ updaterAt S Sched s,
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some L

/-- `ConfirmedAgreeAfterHealing S Sched x tE`: for every two validators `v₁`, `v₂` and steps `i`,
`j` at times at least `tE`, with `v₁` outside the adversary set at every time up to the time of
step `i` and `v₂` at every time up to the time of step `j`, the confirmed tips of `v₁`'s node
state after `i` steps and of `v₂`'s after `j` steps are compatible.

Defined as its view form: `ConfirmedAgreeAfterHealingV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedAgreeAfterHealing_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  agreement holds.

Read aloud: from `tE` on, the confirmed tips of two honest validators are on one chain. -/
def ConfirmedAgreeAfterHealing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) : Prop :=
  ConfirmedAgreeAfterHealingV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE

/-- `ConfirmedMonotoneAfterHealing S Sched x tE`: for every validator `v` and steps `i ≤ j` with
the time of step `i` at least `tE` and `v` outside the adversary set at every time up to the time
of step `j`, the confirmed tip of `v`'s node state after `i` steps is an ancestor of, or equal to,
the one after `j` steps.

Defined as its view form: `ConfirmedMonotoneAfterHealingV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedMonotoneAfterHealing_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  growth holds.

Read aloud: from `tE` on, an honest validator's confirmed tip only extends. -/
def ConfirmedMonotoneAfterHealing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) : Prop :=
  ConfirmedMonotoneAfterHealingV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE

/-- `ConfirmedAgreeBetween S Sched x tE t`: `ConfirmedAgreeAfterHealing S Sched x tE` read up to
the time `t`. For every two validators `v₁`, `v₂` and steps `i`, `j` at times at least `tE` and at
most `t`, with `v₁` outside the adversary set at every time up to the time of step `i` and `v₂` at
every time up to the time of step `j`, the confirmed tips of `v₁`'s node state after `i` steps and
of `v₂`'s after `j` steps are compatible. `ConfirmedAgreeAfterHealing S Sched x tE` is this for
every time `t` (`confirmedAgreeAfterHealing_iff`).

Defined as its view form: `ConfirmedAgreeBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedAgreeBetween_unfold` (`Proofs/View/Bridges.lean`) reads it on the execution's
node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  agreement holds; `t`: the time up to which the steps are read.

Read aloud: from `tE` up to `t`, the confirmed tips of two honest validators are on one chain.

 -/
def ConfirmedAgreeBetween (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE t : ℕ) : Prop :=
  ConfirmedAgreeBetweenV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE t

/-- `ConfirmedMonotoneBetween S Sched x tE t`: `ConfirmedMonotoneAfterHealing S Sched x tE` read up
to the time `t`. For every validator `v` and steps `i ≤ j` with the time of step `i` at least `tE`,
the time of step `j` at most `t`, and `v` outside the adversary set at every time up to the time
of step `j`, the confirmed tip of `v`'s node state after `i` steps is an ancestor of, or equal to,
the one after `j` steps. `ConfirmedMonotoneAfterHealing S Sched x tE` is this for every time `t`
(`confirmedMonotoneAfterHealing_iff`).

Defined as its view form: `ConfirmedMonotoneBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedMonotoneBetween_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  growth holds; `t`: the time up to which the later step is read.

Read aloud: from `tE` up to `t`, an honest validator's confirmed tip only extends.

 -/
def ConfirmedMonotoneBetween (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE t : ℕ) : Prop :=
  ConfirmedMonotoneBetweenV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE t

/-- `ConfirmedAgreeAfterHealing S Sched x tE` holds exactly when `ConfirmedAgreeBetween S Sched x
tE t` holds for every time `t`.

Why: one way, the two upper ends are dropped. The other way, two steps `i`, `j` are read at the
time `t := max x[i].time x[j].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  agreement holds.

Read aloud: the agreement from `tE` on is the agreement read up to every time. -/
theorem confirmedAgreeAfterHealing_iff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) :
    ConfirmedAgreeAfterHealing S Sched x tE ↔ ∀ t : ℕ, ConfirmedAgreeBetween S Sched x tE t := by
  constructor
  · intro h t v₁ v₂ i j h₁ h₂ hi hj _ _
    exact h v₁ v₂ i j h₁ h₂ hi hj
  · intro h v₁ v₂ i j h₁ h₂ hi hj
    exact h (max x[i].time x[j].time) v₁ v₂ i j h₁ h₂ hi hj (le_max_left _ _) (le_max_right _ _)

/-- `ConfirmedMonotoneAfterHealing S Sched x tE` holds exactly when `ConfirmedMonotoneBetween S
Sched x tE t` holds for every time `t`.

Why: one way, the upper end is dropped. The other way, the later step `j` is read at the time
`t := x[j].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  growth holds.

Read aloud: the growth from `tE` on is the growth read up to every time. -/
theorem confirmedMonotoneAfterHealing_iff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) :
    ConfirmedMonotoneAfterHealing S Sched x tE ↔
      ∀ t : ℕ, ConfirmedMonotoneBetween S Sched x tE t := by
  constructor
  · intro h t v i j hij hj hi _
    exact h v i j hij hj hi
  · intro h v i j hij hj hi
    exact h x[j].time v i j hij hj hi le_rfl


/-! -/

open Framework.StsMultisetLog (AtomicAction SignedMsg)

/-- `RootCollisionAtProposal S Sched x s B`: some block that the proposer of slot `s` holds before
the start of slot `s` has the root of `B`. This is the case in which the proposer's own test of a
block (`block_admissible`, which refuses a block whose root a held block has) refuses its proposal
`B`;

Defined as its view form: `RootCollisionAtProposalV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `rootCollisionAtProposal_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `B`: the proposal.

Read aloud: a block the proposer held before the proposal's slot has the proposal's root.

 -/
def RootCollisionAtProposal (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B : Block V) : Prop :=
  RootCollisionAtProposalV Vocab.goldilocks S (projectTrace nodeView x.toTrace) s B

/-- `ConfirmedIncludedAfterHealing S Sched x tE`: for every slot `s` starting at or after `tE` whose
proposer is awake and outside the adversary set at every time from `proposalWindowStart S s` to
the support cutoff of slot `s + 1`: the proposer's tick at the start of slot `s` puts some block on
the wire; and for every block `B` that tick puts on the wire, either a block the proposer held
before the start of slot `s` has `B`'s root (`RootCollisionAtProposal`), or every honest active
validator of slot `s` holds `B` as its confirmed tip (`confirmedOf`) right after the support cutoff
of slot `s + 1`, and, for every validator `v` honest and active at some slot `s' ≥ s`, at every step
`j` after the support cutoff of slot `s' + 1` at which `v` has been honest throughout, `B` is `v`'s
confirmed tip or an ancestor of it.

 the lemmas the proof calls still conclude the saved confirmation.

Defined as its view form: `ConfirmedIncludedAfterHealingV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedIncludedAfterHealing_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read;
- `s`: the slot of the proposal; `i`: the step of the proposer's tick; `B`: the proposal;
- `v`: a validator; `j`: a step; `s'`: a slot from `s` on.

Read aloud: from `tE`, every honest proposal is confirmed by every honest active validator of its
slot and stays confirmed, unless its proposer already held a block with its root.

 -/
def ConfirmedIncludedAfterHealing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) : Prop :=
  ConfirmedIncludedAfterHealingV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) tE

/-- `ConfirmedIncludedBetween S Sched x tE t`: `ConfirmedIncludedAfterHealing S Sched x tE` read up
to the time `t`. For every slot `s` starting at or after `tE` whose update time, the support cutoff
of slot `s + 1`, is at most `t`, and whose proposer is awake and outside the adversary set at every
time from `proposalWindowStart S s` to that support cutoff: the proposer's tick at the start of slot
`s` puts some block on the wire; and for every block `B` that tick puts on the wire, either a block
the proposer held before the start of slot `s` has `B`'s root (`RootCollisionAtProposal`), or every
honest active validator of slot `s` holds `B` as its confirmed tip (`confirmedOf`) right after the
support cutoff of slot `s + 1`, and, for every validator `v` honest and active at some slot
`s' ≥ s`, at every step `j` at a time at most `t`, after the support cutoff of slot `s' + 1`, at
which `v` has been honest throughout, `B` is `v`'s confirmed tip or an ancestor of it.
`ConfirmedIncludedAfterHealing S Sched x tE` is this for every time `t`
(`confirmedIncludedAfterHealing_iff`).



Defined as its view form: `ConfirmedIncludedBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `confirmedIncludedBetween_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read; `t`: the time up to which the updates and the confirmed tips are read;
- `s`: the slot of the proposal; `i`: the step of the proposer's tick; `B`: the proposal;
- `v`: a validator; `j`: a step; `s'`: a slot from `s` on.

Read aloud: from `tE` and up to `t`, every honest proposal is confirmed by every honest active
validator of its slot and stays confirmed, unless its proposer already held a block with its root.

 -/
def ConfirmedIncludedBetween (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE t : ℕ) : Prop :=
  ConfirmedIncludedBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) tE t

/-- `ConfirmedIncludedAfterHealing S Sched x tE` holds exactly when `ConfirmedIncludedBetween S
Sched x tE t` holds for every time `t`.

Why: one way, the two upper ends are dropped. The other way, at a slot `s`, the proposal and the
confirmations right after the update come from the time `t := supportCutoff S (s + 1)`, and the
confirmed tip at a step `j` from the time `t := max (supportCutoff S (s + 1)) x[j].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read.

Read aloud: the inclusion from `tE` is the inclusion read up to every time. -/
theorem confirmedIncludedAfterHealing_iff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) :
    ConfirmedIncludedAfterHealing S Sched x tE ↔
      ∀ t : ℕ, ConfirmedIncludedBetween S Sched x tE t := by
  constructor
  · intro h t s hs _ hp
    obtain ⟨h1, h2⟩ := h s hs hp
    refine ⟨h1, fun B hB => ?_⟩
    rcases h2 B hB with hc | ⟨h3, h4⟩
    · exact Or.inl hc
    · exact Or.inr ⟨h3, fun v j s' hv hss' hact hlt _ => h4 v j s' hv hss' hact hlt⟩
  · intro h s hs hp
    obtain ⟨h1, -⟩ := h (supportCutoff S (s + 1)) s hs le_rfl hp
    refine ⟨h1, fun B hB => ?_⟩
    by_cases hc : RootCollisionAtProposal S Sched x s B
    · exact Or.inl hc
    · right
      refine ⟨?_, ?_⟩
      · rcases (h (supportCutoff S (s + 1)) s hs le_rfl hp).2 B hB with hc' | ⟨h3, -⟩
        · exact absurd hc' hc
        · exact h3
      · intro v j s' hv hss' hact hlt
        rcases (h (max (supportCutoff S (s + 1)) x[j].time) s hs (le_max_left _ _) hp).2 B
            hB with hc' | ⟨-, h4⟩
        · exact absurd hc' hc
        · exact h4 v j s' hv hss' hact hlt (le_max_right _ _)

/-! ## The honest proposal extends the earlier confirmed tips

Lemma 90's fourth conclusion: every honest proposal of a slot
starting at or after `tE` is a strict descendant of every confirmed tip a validator honest
through its step had from `tE` until the slot started. -/

/-- `ConfirmedExtendedByHonestProposals S Sched x tE`: for every slot `s` starting at or after `tE`
whose proposer is awake and outside the adversary set at every time from `proposalWindowStart S s`
to the support cutoff of slot `s + 1` (`HonestOpenerAt`), and every block `B` the proposer's tick
at the start of slot `s` puts on the wire: either a block the proposer held before the start of
slot `s` has `B`'s root (`RootCollisionAtProposal`), or, for every validator `v` and every step `i`
at a time from `tE` to before the start of slot `s` through which `v` has been honest, `v`'s
confirmed tip (`confirmedOf`) after step `i` is an ancestor of `B` other than `B`.

Defined as its view form: `ConfirmedExtendedByHonestProposalsV` with Goldilocks's
vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`.
`confirmedExtendedByHonestProposals_unfold`
(`Proofs/Executions/HonestProposalExtension.lean`) reads it on the execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read.

Read aloud: from `tE`, every honest proposal strictly extends every confirmed tip an honest
validator had from `tE` until the proposal's slot started, unless its proposer already held a
block with its root. -/
def ConfirmedExtendedByHonestProposals (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) : Prop :=
  ConfirmedExtendedByHonestProposalsV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) tE

/-- `ConfirmedExtendedByHonestProposalsBetween S Sched x tE t`:
`ConfirmedExtendedByHonestProposals S Sched x tE` read up to the time `t`, for the slots `s` whose
update time, the support cutoff of slot `s + 1`, is at most `t`. For every such slot `s` starting
at or after `tE` whose proposer is awake and outside the adversary set at every time from
`proposalWindowStart S s` to that support cutoff (`HonestOpenerAt`), and every block `B` the
proposer's tick at the start of slot `s` puts on the wire: either a block the proposer held before
the start of slot `s` has `B`'s root (`RootCollisionAtProposal`), or, for every validator `v` and
every step `i` at a time from `tE` to before the start of slot `s` through which `v` has been
honest, `v`'s confirmed tip (`confirmedOf`) after step `i` is an ancestor of `B` other than `B`.

Defined as its view form: `ConfirmedExtendedByHonestProposalsBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`.
`confirmedExtendedByHonestProposalsBetween_unfold`
(`Proofs/Executions/HonestProposalExtension.lean`) reads it on the execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read; `t`: the time up to which the updates are read.

Read aloud: from `tE` and up to `t`, every honest proposal strictly extends every confirmed tip an
honest validator had from `tE` until the proposal's slot started, unless its proposer already held
a block with its root. -/
def ConfirmedExtendedByHonestProposalsBetween (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE t : ℕ) : Prop :=
  ConfirmedExtendedByHonestProposalsBetweenV Vocab.goldilocks S Sched
    (projectTrace nodeView x.toTrace) tE t

end GoldilocksCorrectness.Statements.Executions
