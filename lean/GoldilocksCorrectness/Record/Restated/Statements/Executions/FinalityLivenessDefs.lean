module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityWindowDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule

@[expose] public section

/-!
# FinalityLivenessDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/FinalityLivenessDefs.lean` over a
model `M`, for an execution `x` of `protocolOf M S`: Lemma 98's conclusion, read up to a time and
with no upper end, each its view form on the view of `x`, `projectTrace (nodeView M) x.toTrace`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff proposalWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

section Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open GoldilocksCorrectness.Record.Statements.View


variable [RootOrder]

/-- `FinalityIncludedBetween M S Sched x Δs tE t`: for every slot `s` starting at or after `tE` with
`HonestOpenerAt M S Sched s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt M S Sched r`
and the update of the window's last opening slot `(r + 3) * R` at most `t`: the proposer's tick at the start of slot `s` puts some block on the wire; and for every block `B` that tick puts on
the wire, either a block the proposer held before the start of slot `s` has `B`'s root
(`RootCollisionAtProposal`), or one of the four rounds' proposals has the root of a block its
proposer held (`RootCollisionAtOpening` on the rounds `r, r + 1, r + 2, r + 3`), or every
validator `v` honest through a step `j` at or before some support cutoff at most `t` (some slot
`s'` with `x[j].time ≤ M.supportCutoff S.C s' ≤ t`), awake for one whole delay between the start
of slot `(r + 3) * R` and the time of step `j`, has at step `j` a finalized block `S.F`
of which `B` is an ancestor or which is `B`, and which no validator had as its finalized block at a
step at a time before the start of slot `s`.



Defined as its view form: `FinalityIncludedBetweenV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `finalityIncludedBetween_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read; `t`: the time that decides the readers: a reader's step is at or before some support
  cutoff at most `t`;
- `s`: the slot of the proposal; `r`: the window's first round; `i`: the step of the proposer's
  tick; `B`: the proposal; `v`, `j`: a reader and its step; `u`, `i'`: a validator and an earlier
  step.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth opening slot is at most `t`, everyone awake for a
delay after the fourth opening slot has finalized that proposal or a descendant of it, a block no
validator had finalized before the proposal, unless a root collision hit one of the five
proposals. -/
def FinalityIncludedBetween (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Δs tE t : ℕ) : Prop :=
  FinalityIncludedBetweenV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) Δs tE t

/-- `FinalityIncludedAfterHealing M S Sched x Δs tE`: `FinalityIncludedBetween M S Sched x Δs tE t` with
no upper end: for every slot `s` starting at or after `tE` with `HonestOpenerAt M S Sched s`, and
every round `r` with `s ≤ r * R` and `FinalityWindowAt M S Sched r`, the proposer of `s` puts some
block on the wire at its tick at the start of `s`, and every such block `B` has a root collision at
one of the five proposals, or is an ancestor of, or equal to, the finalized block of every validator
honest through a step and awake for one whole delay between the start of slot `(r + 3) * R` and that
step's time, a finalized block no validator had at a step before the start of slot `s`.

Defined as its view form: `FinalityIncludedAfterHealingV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks.
`finalityIncludedAfterHealing_unfold` (`Proofs/View/Bridges.lean`) reads it on the execution's node
states.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read.

Read aloud: from `tE`, whenever four consecutive honest round opening slots with quorums at the
first three follow an honest proposal, everyone awake for a delay after the fourth has finalized a
new block at or after that proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedAfterHealing (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Δs tE : ℕ) : Prop :=
  FinalityIncludedAfterHealingV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A ((x.map (nodeView M))) Δs tE

/-- `FinalityIncludedAfterHealing M S Sched x Δs tE` holds exactly when
`FinalityIncludedBetween M S Sched x Δs tE t` holds for every time `t`.

Why: one way, the upper ends are dropped. The other way, the proposal comes from the time
`t := M.supportCutoff S.C ((r + 3) * R + 1)`, the update of the window's last opening slot, and
the reader's step `j` from the time `t := M.supportCutoff S.C n` with
`n := max x[j].time ((r + 3) * R + 1)`: the support cutoff of slot `n` is at or after the step
(`n ≤ M.slotStart S.C n`, from `SF`) and at or after the update of the window's last opening slot,
so it is the support cutoff after the step that the reader condition of `FinalityIncludedBetween`
asks for, and it meets the window condition.

The variables:
- `M`: the model; `SF`: the facts of its slot layout (the slots' times grow with the slot, so every
  time is at or before some support cutoff);
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δs`: the sync delay; `tE`: the time
  from which the slots are read.

Read aloud: finality from `tE` is finality read up to every time. -/
theorem finalityIncludedAfterHealing_iff (SF : GoldilocksCorrectness.Record.ScheduleFacts M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Δs tE : ℕ) :
    FinalityIncludedAfterHealing M S A x Δs tE ↔
      ∀ t : ℕ, FinalityIncludedBetween M S A x Δs tE t := by
  constructor
  · intro h t s r hs hop hsr hwin _
    obtain ⟨h1, h2⟩ := h s r hs hop hsr hwin
    refine ⟨h1, fun B hB => ?_⟩
    rcases h2 B hB with hc | hc | h3
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (fun v j hv _ hAw => h3 v j hv hAw))
  · intro h s r hs hop hsr hwin
    obtain ⟨h1, -⟩ := h (M.supportCutoff S.C ((r + 3) * S.C.R + 1)) s r hs hop hsr hwin le_rfl
    refine ⟨h1, fun B hB => ?_⟩
    by_cases hc : RootCollisionAtProposal M S A x s B
    · exact Or.inl hc
    by_cases hc' : RootCollisionAtOpening M S A x (fun i => r + i) 3
    · exact Or.inr (Or.inl hc')
    right; right
    intro v j hv hAw
    -- the support cutoff of slot `max x[j].time ((r + 3) * R + 1)`: after the step and the window
    obtain ⟨n, hn⟩ := exists_nat_ge (x.time j)
    have hjn : x.time j ≤ M.supportCutoff S.C (max n ((r + 3) * S.C.R + 1)) := by
      have h1 := GoldilocksCorrectness.Record.Proofs.Routines.le_slotStart M.toSlotLayout SF S
        (max n ((r + 3) * S.C.R + 1))
      have h2 := GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout SF S
        (max n ((r + 3) * S.C.R + 1))
      have h3 := le_max_left n ((r + 3) * S.C.R + 1)
      have h4 : n ≤ M.supportCutoff S.C (max n ((r + 3) * S.C.R + 1)) := by omega
      have h5 : (n : ℝ) ≤ (M.supportCutoff S.C (max n ((r + 3) * S.C.R + 1)) : ℕ) := by
        exact_mod_cast h4
      linarith
    rcases (h (M.supportCutoff S.C (max n ((r + 3) * S.C.R + 1))) s r hs hop hsr hwin
        (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout SF S
          (le_max_right _ _))).2 B hB with h₁ | h₁ | h₁
    · exact absurd h₁ hc
    · exact absurd h₁ hc'
    · exact h₁ v j hv ⟨_, hjn, le_rfl⟩ hAw

end Executions

end GoldilocksCorrectness.Record.Statements.Executions

