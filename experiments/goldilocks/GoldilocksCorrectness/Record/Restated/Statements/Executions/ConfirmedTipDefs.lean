module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Record.Restated.Statements.View.SlotConclusionDefs
public import GoldilocksCorrectness.Record.Restated.Statements.View.GoldilocksViewDefs
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipDefs

@[expose] public section

/-!
# ConfirmedTipDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/ConfirmedTipDefs.lean` over a model
`M`, for an execution `x` of `protocolOf M S`: an honest confirmation, and the conclusions about the
confirmed tips after the healed slot, each its view form on the view of `x`, `projectTrace (nodeView
M) x.toTrace`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (slotStart supportCutoff proposalWindowStart)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.View
open GoldilocksCorrectness.Statements.AbstractTrace.View (ConfirmedAgreeAfterHealingV ConfirmedAgreeBetweenV ConfirmedMonotoneAfterHealingV ConfirmedMonotoneBetweenV)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `IsHonestConfirmation M S Sched x s₀ L`: for some slot `s` at or after `s₀`, some validator of
`updaterAt M S Sched s` holds `L` as its confirmation of slot `s` on its node state before the time
after the support cutoff of slot `s + 1`, right after its update.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot;
- `L`: the block.

Read aloud: `L` is the confirmation of some slot at or after `s₀` that some updater of that slot
holds right after its update. -/
def IsHonestConfirmation (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₀ : ℕ) (L : Block V) : Prop :=
  ∃ s : ℕ, s₀ ≤ s ∧ ∃ v ∈ updaterAt M S A x s,
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some L

/-- `ConfirmedAgreeAfterHealing M S Sched x tE`: for every two validators `v₁`, `v₂` and steps `i`,
`j` at times at least `tE`, with `v₁` outside the adversary set at every time up to the time of
step `i` and `v₂` at every time up to the time of step `j`, the confirmed tips of `v₁`'s node
state after `i + 1` steps and of `v₂`'s after `j + 1`
steps are compatible.

Defined as its view form: `ConfirmedAgreeAfterHealingV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `confirmedAgreeAfterHealing_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  agreement holds.

Read aloud: from `tE` on, the confirmed tips of two honest validators are on one chain. -/
def ConfirmedAgreeAfterHealing (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℕ) : Prop :=
  ConfirmedAgreeAfterHealingV GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks A ((x.map (nodeView M))) tE

/-- `ConfirmedMonotoneAfterHealing M S Sched x tE`: for every validator `v` and steps `i ≤ j` with
the time of step `i` at least `tE` and `v` outside the adversary set at every time up to the time
of step `j`, the confirmed tip of `v`'s node state after `i + 1` steps is an ancestor of, or equal to, the one after `j + 1` steps.

Defined as its view form: `ConfirmedMonotoneAfterHealingV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks.
`confirmedMonotoneAfterHealing_unfold` (`Proofs/View/Bridges.lean`) reads it on the execution's node
states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  growth holds.

Read aloud: from `tE` on, an honest validator's confirmed tip only extends. -/
def ConfirmedMonotoneAfterHealing (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℕ) : Prop :=
  ConfirmedMonotoneAfterHealingV GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks A ((x.map (nodeView M))) tE

/-- `ConfirmedAgreeBetween M S Sched x tE t`: `ConfirmedAgreeAfterHealing M S Sched x tE` read up to
the time `t`. For every two validators `v₁`, `v₂` and steps `i`, `j` at times at least `tE` and at
most `t`, with `v₁` outside the adversary set at every time up to the time of step `i` and `v₂` at
every time up to the time of step `j`, the confirmed tips of `v₁`'s node state after `i + 1` steps
 and of `v₂`'s after `j + 1` steps are compatible. `ConfirmedAgreeAfterHealing M S Sched x tE` is this for
every time `t` (`confirmedAgreeAfterHealing_iff`).

Defined as its view form: `ConfirmedAgreeBetweenV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `confirmedAgreeBetween_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  agreement holds; `t`: the time up to which the steps are read.

Read aloud: from `tE` up to `t`, the confirmed tips of two honest validators are on one chain.

 -/
def ConfirmedAgreeBetween (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℝ) (t : ℕ) : Prop :=
  ConfirmedAgreeBetweenV GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks A ((x.map (nodeView M))) tE t

/-- `ConfirmedMonotoneBetween M S Sched x tE t`: `ConfirmedMonotoneAfterHealing M S Sched x tE` read
up to the time `t`. For every validator `v` and steps `i ≤ j` with the time of step `i` at least
`tE`, the time of step `j` at most `t`, and `v` outside the adversary set at every time up to the
time of step `j`, the confirmed tip of `v`'s node state after `i + 1` steps is an ancestor of, or equal to, the one after `j + 1` steps. `ConfirmedMonotoneAfterHealing M S Sched x tE` is this for every time
`t` (`confirmedMonotoneAfterHealing_iff`).

Defined as its view form: `ConfirmedMonotoneBetweenV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `confirmedMonotoneBetween_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  growth holds; `t`: the time up to which the later step is read.

Read aloud: from `tE` up to `t`, an honest validator's confirmed tip only extends.

 -/
def ConfirmedMonotoneBetween (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℝ) (t : ℕ) : Prop :=
  ConfirmedMonotoneBetweenV GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks A ((x.map (nodeView M))) tE t

/-- `ConfirmedAgreeAfterHealing M S Sched x tE` holds exactly when `ConfirmedAgreeBetween S Sched x
tE t` holds for every time `t`.

Why: one way, the two upper ends are dropped. The other way, two steps `i`, `j` are read at the
time `t := max x[i].time x[j].time`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the
  agreement holds.

Read aloud: the agreement from `tE` on is the agreement read up to every time. -/
theorem confirmedAgreeAfterHealing_iff (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℕ) :
    ConfirmedAgreeAfterHealing M S A x tE ↔ ∀ t : ℕ, ConfirmedAgreeBetween M S A x tE t := by
  constructor
  · intro h t v₁ v₂ i j h₁ h₂ hi hj _ _
    exact h v₁ v₂ i j h₁ h₂ hi hj
  · intro h v₁ v₂ i j h₁ h₂ hi hj
    obtain ⟨t, ht⟩ := exists_nat_ge (max (x.time i) (x.time j))
    exact h t v₁ v₂ i j h₁ h₂ hi hj (le_trans (le_max_left _ _) ht) (le_trans (le_max_right _ _) ht)

/-! -/

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)

/-- `RootCollisionAtProposal M S Sched x s B`: some block that the proposer of slot `s` holds in the
state its tick to the start of slot `s` starts from has the root of `B`. This is the case in which the proposer's own test of a
block (`block_admissible`, which refuses a block whose root a held block has) refuses its proposal
`B`;

Defined as its view form: `RootCollisionAtProposalV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `rootCollisionAtProposal_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `B`: the proposal.

Read aloud: a block the proposer held when its tick to the proposal's slot started has the proposal's
root.

 -/
def RootCollisionAtProposal (S : Setup V) (A : Activity V)
  (x : Trace V (NamedObject V) M.N)
    (s : ℕ) (B : Block V) : Prop :=
  RootCollisionAtProposalV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S ((x.map (nodeView M))) s B

/-- `ConfirmedIncludedAfterHealing M S Sched x tE`: for every slot `s` starting at or after `tE`
whose proposer is awake and outside the adversary set at every time from
`M.proposalWindowStart S.C s` to the support cutoff of slot `s + 1`: the proposer's tick at the
start of slot `s` puts some block on the wire; and for every block `B` that tick puts on the wire,
either a block the proposer held before the start of slot `s` has `B`'s root
(`RootCollisionAtProposal`), or every honest active validator of slot `s` holds `B` as its confirmed
tip (`confirmedOf`) right after the support cutoff of slot `s + 1`, and, for every validator `v`
honest and active at some slot `s' ≥ s`, in the state every step `j` leaves, `j` after the support cutoff of slot `s' + 1`
at which `v` has been honest throughout, `B` is `v`'s confirmed tip or an ancestor of it.

 the lemmas the proof calls still conclude the saved confirmation.

Defined as its view form: `ConfirmedIncludedAfterHealingV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks.
`confirmedIncludedAfterHealing_unfold` (`Proofs/View/Bridges.lean`) reads it on the execution's node
states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read;
- `s`: the slot of the proposal; `i`: the step of the proposer's tick; `B`: the proposal;
- `v`: a validator; `j`: a step; `s'`: a slot from `s` on.

Read aloud: from `tE`, every honest proposal is confirmed by every honest active validator of its
slot and stays confirmed, unless its proposer already held a block with its root.

 -/
def ConfirmedIncludedAfterHealing (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℕ) : Prop :=
  ConfirmedIncludedAfterHealingV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) tE

/-- `ConfirmedIncludedBetween M S Sched x tE t`: `ConfirmedIncludedAfterHealing M S Sched x tE` read
up to the time `t`. For every slot `s` starting at or after `tE` whose update time, the support
cutoff of slot `s + 1`, is at most `t`, and whose proposer is awake and outside the adversary set at
every time from `M.proposalWindowStart S.C s` to that support cutoff: the proposer's tick at the
start of slot `s` puts some block on the wire; and for every block `B` that tick puts on the wire,
either a block the proposer held before the start of slot `s` has `B`'s root
(`RootCollisionAtProposal`), or every honest active validator of slot `s` whose tick to the support
cutoff of slot `s + 1` is at a real time at most `t` holds `B` as its confirmed tip
(`confirmedOf`) right after that tick, and, for every validator `v`
honest and active at some slot `s' ≥ s`, in the state every step `j` leaves, `j` at a time at most `t`, after the support
cutoff of slot `s' + 1`, at which `v` has been honest throughout, `B` is `v`'s confirmed tip or an
ancestor of it. `ConfirmedIncludedAfterHealing M S Sched x tE` is this for every time `t`
(`confirmedIncludedAfterHealing_iff`).



Defined as its view form: `ConfirmedIncludedBetweenV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `confirmedIncludedBetween_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read; `t`: the time up to which the updates and the confirmed tips are read;
- `s`: the slot of the proposal; `i`: the step of the proposer's tick; `B`: the proposal;
- `v`: a validator; `j`: a step; `s'`: a slot from `s` on.

Read aloud: from `tE` and up to `t`, every honest proposal is confirmed by every honest active
validator of its slot and stays confirmed, unless its proposer already held a block with its root.

 -/
def ConfirmedIncludedBetween (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE t : ℕ) : Prop :=
  ConfirmedIncludedBetweenV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) tE t

/-- `ConfirmedIncludedAfterHealing M S Sched x tE` holds exactly when `ConfirmedIncludedBetween S
Sched x tE t` holds for every time `t`.

Why: one way, the two upper ends are dropped. The other way, at a slot `s`, the proposal comes from
the time `t := M.supportCutoff S.C (s + 1)`, the confirmation right after `v`'s update from a natural
number at least the real time of `v`'s tick to that cutoff (with that cutoff), and the confirmed tip at
a step `j` from a natural number at least `x[j].time` (with that cutoff).

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read.

Read aloud: the inclusion from `tE` is the inclusion read up to every time. -/
theorem confirmedIncludedAfterHealing_iff (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℕ) :
    ConfirmedIncludedAfterHealing M S A x tE ↔
      ∀ t : ℕ, ConfirmedIncludedBetween M S A x tE t := by
  constructor
  · intro h t s hs _ hp
    obtain ⟨h1, h2⟩ := h s hs hp
    refine ⟨h1, fun B hB => ?_⟩
    rcases h2 B hB with hc | ⟨h3, h4⟩
    · exact Or.inl hc
    · exact Or.inr ⟨fun v hv _ => h3 v hv, fun v j s' hv hss' hact hlt _ _ => h4 v j s' hv hss' hact hlt⟩
  · intro h s hs hp
    obtain ⟨h1, -⟩ := h (M.supportCutoff S.C (s + 1)) s hs le_rfl hp
    refine ⟨h1, fun B hB => ?_⟩
    by_cases hc : RootCollisionAtProposal M S A x s B
    · exact Or.inl hc
    · right
      refine ⟨?_, ?_⟩
      · intro v hv
        -- a natural number at least the real time of `v`'s tick to the cutoff bounds the read
        obtain ⟨t', ht'⟩ := exists_nat_ge (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))))
        rcases (h (max (M.supportCutoff S.C (s + 1)) t') s hs (le_max_left _ _) hp).2 B
            hB with hc' | ⟨h3, -⟩
        · exact absurd hc' hc
        · have h2 : ((t' : ℕ) : ℝ) ≤ ((max (M.supportCutoff S.C (s + 1)) t' : ℕ) : ℝ) := by
            exact_mod_cast le_max_right _ _
          exact h3 v hv (le_trans ht' h2)
      · intro v j s' hv hss' hact hlt
        obtain ⟨t', ht'⟩ := exists_nat_ge (x.time j)
        rcases (h (max (max (M.supportCutoff S.C (s + 1)) t') (M.supportCutoff S.C (s' + 1))) s hs
            (le_trans (le_max_left _ _) (le_max_left _ _)) hp).2 B hB with hc' | ⟨-, h4⟩
        · exact absurd hc' hc
        · have h2 : ((t' : ℕ) : ℝ) ≤
              ((max (max (M.supportCutoff S.C (s + 1)) t') (M.supportCutoff S.C (s' + 1)) : ℕ) : ℝ) := by
            exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
          exact h4 v j s' hv hss' hact hlt (le_max_right _ _) (le_trans ht' h2)

end GoldilocksCorrectness.Record.Statements.Executions

