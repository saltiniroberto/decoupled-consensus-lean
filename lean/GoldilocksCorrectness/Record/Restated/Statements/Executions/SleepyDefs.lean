module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Statements.Executions.SleepyDefs

@[expose] public section

/-!
# SleepyDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/SleepyDefs.lean` over a model `M`:
the validators awake through a slot's duties at the model's times (`M.dutyWindowStart S.C`,
`M.supportCutoff S.C`), the conditions on the schedule read at those times, and, for an execution
`x` of `protocolOf M S`, the honest chain of the updaters' saved confirmations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

export GoldilocksCorrectness.Record.Statements.AbstractTrace (activeAt honestActiveAt updaterAt
  Sleepiness)

/-- `CommitteeSleepiness M S Sched anchor`: at every slot `s ≥ 1` starting at or after `anchor`,
the members of the committee of slot `s − 1` in `honestActiveAt M S Sched (s - 1)` outnumber the
other members of that committee.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which the condition holds.

Read aloud: from `anchor` on, in the committee of the slot before each slot, the honest active
members are more than the rest. -/
def CommitteeSleepiness (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (anchor : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → anchor ≤ M.slotStart S.C s →
    |S.P.committee (s - 1) \ honestActiveAt M S A x (s - 1)| <
      |honestActiveAt M S A x (s - 1) ∩ S.P.committee (s - 1)|

/-- `CommitteeSleepinessUntil M S A x anchor T`: at every slot `s ≥ 1` starting at or after `anchor`
whose support cutoff is at most `T`, the members of the committee of slot `s − 1` in
`honestActiveAt M S A x (s - 1)` outnumber the other members of that committee.

The condition at slot `s` is a statement about the activity up to `M.supportCutoff S.C s`:
`honestActiveAt M S A x (s - 1)` is the set of validators awake through the duties of slot `s − 1`,
up to that cutoff, and outside the adversary set at it. So the premise reads nothing after `T`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `anchor`: the time from which the condition holds; `T`: the
  time up to which it is read.

Read aloud: from `anchor` on, for every slot whose update is at most `T`, the honest active members
of the previous slot's committee are more than the rest. -/
def CommitteeSleepinessUntil (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (anchor T : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → anchor ≤ M.slotStart S.C s → M.supportCutoff S.C s ≤ T →
    |S.P.committee (s - 1) \ honestActiveAt M S A x (s - 1)| <
      |honestActiveAt M S A x (s - 1) ∩ S.P.committee (s - 1)|

/-- Committee sleepiness from `anchor` gives the bounded form at every `T`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `anchor`: the time from which the condition holds; `T`: the
  time up to which the bounded form is read.

Read aloud: the premise for all time implies the premise read up to `T`. -/
theorem committeeSleepinessUntil_of_committeeSleepiness (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (anchor T : ℕ) (h : CommitteeSleepiness M S A x anchor) :
    CommitteeSleepinessUntil M S A x anchor T :=
  fun s hs hanchor _ => h s hs hanchor

/-- The bounded form read up to `T` holds up to every `T' ≤ T`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `anchor`: the time from which the condition holds; `T`, `T'`:
  the two times up to which it is read.

Read aloud: a premise read up to `T` is read up to any earlier time. -/
theorem CommitteeSleepinessUntil.mono {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {anchor T' T : ℕ}
    (h : CommitteeSleepinessUntil M S A x anchor T) (hle : T' ≤ T) :
    CommitteeSleepinessUntil M S A x anchor T' :=
  fun s hs hanchor hT => h s hs hanchor (le_trans hT hle)

/-- `HonestCommitteesIn M S Sched t₀ t₁ tH`: at every slot `s` that starts at or after `t₀` and
whose next slot starts at or before `t₁`, the members of the committee of slot `s` outside the
adversary set at the time `tH s` are more than half of that committee.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `t₀`, `t₁`: the ends of the phase;
- `tH`: for each slot, the time at which the honesty of its committee is read.

Read aloud: in every committee of the phase, more than half of the members are honest at the
time `tH` names for its slot. -/
def HonestCommitteesIn (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (t₀ t₁ : ℕ) (tH : (s : ℕ) → ℕ) :
    Prop :=
  ∀ s : ℕ, t₀ ≤ M.slotStart S.C s → M.slotStart S.C (s + 1) ≤ t₁ →
    |S.P.committee s| < 2 * |S.P.committee s \ A.corruptedAtTime x (tH s)|

section Executions

variable [RootOrder]

/-- `OnHonestChainAt M S Sched x s₀ s B`: `s` is at or after `s₀`, and `B` is an ancestor of, or
equal to, the confirmation of slot `s` that some validator of `updaterAt M S Sched s` holds right
after its update, on its node state before the time after the support cutoff of slot `s + 1`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₀`: the first slot of the chain; `s`: the slot; `B`: the block.

Read aloud: `B` is on the honest chain at slot `s`. -/
def OnHonestChainAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₀ s : ℕ) (B : Block V) : Prop :=
  s₀ ≤ s ∧ ∃ v ∈ updaterAt M S A x s, ∃ C : Block V,
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C ∧
    B.AncestorEq C

/-- `OnHonestChain M S Sched x s₀ B`: `B` is on the honest chain at some slot.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₀`: the first slot of the chain; `B`: the block.

Read aloud: `B` is on the honest chain from slot `s₀`. -/
def OnHonestChain (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₀ : ℕ) (B : Block V) : Prop :=
  ∃ s : ℕ, OnHonestChainAt M S A x s₀ s B

/-- `OnHonestChainBefore M S Sched x s₀ s B`: `B` is on the honest chain at some slot less than
`s`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₀`: the first slot of the chain; `s`: the bound on the slot; `B`: the block.

Read aloud: `B` is on the honest chain before slot `s`. -/
def OnHonestChainBefore (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₀ s : ℕ) (B : Block V) : Prop :=
  ∃ s' : ℕ, s' < s ∧ OnHonestChainAt M S A x s₀ s' B

/-- `ConfirmationsChain M S Sched x s₀`: from slot `s₀` on, a confirmation that a validator of
`updaterAt` holds right after its update for a slot is an ancestor of, or equal to, one that a
validator of `updaterAt` holds for a later slot, and two such confirmations of one slot are
compatible.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot;
- `s`, `s'`: the two slots; `v`, `v'`: the two updaters; `C`, `C'`: their confirmations.

Read aloud: from slot `s₀` on, the updaters' confirmations form one chain. -/
def ConfirmationsChain (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₀ : ℕ) : Prop :=
  ∀ (s s' : ℕ) (v v' : V) (C C' : Block V), s₀ ≤ s → s ≤ s' →
    v ∈ updaterAt M S A x s → v' ∈ updaterAt M S A x s' →
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C →
    (x.tickOutput v' (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
    (s < s' → C.AncestorEq C') ∧ (s = s' → C.compatible C' = true)

/-- `ConfirmationsChainBefore M S Sched x s₀ s'`: `ConfirmationsChain M S Sched x s₀` for the slots
less than `s'`: from slot `s₀` on and before slot `s'`, a confirmation that a validator of
`updaterAt` holds right after its update for a slot is an ancestor of, or equal to, one that a
validator of `updaterAt` holds for a later slot, and two such confirmations of one slot are
compatible.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot; `s'`: the
  bound on the slots;
- `s`, `s''`: the two slots; `v`, `v'`: the two updaters; `C`, `C'`: their confirmations.

Read aloud: the updaters' confirmations of the slots from `s₀` to before `s'` form one chain. -/
def ConfirmationsChainBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s' : ℕ) : Prop :=
  ∀ (s s'' : ℕ) (v v' : V) (C C' : Block V), s₀ ≤ s → s ≤ s'' → s'' < s' →
    v ∈ updaterAt M S A x s → v' ∈ updaterAt M S A x s'' →
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C →
    (x.tickOutput v' (M.supportCutoff S.C (s'' + 1))).savedConfirmation s'' = some C' →
    (s < s'' → C.AncestorEq C') ∧ (s = s'' → C.compatible C' = true)

/-- The whole chain gives every prefix of it: `ConfirmationsChain M S Sched x s₀` implies
`ConfirmationsChainBefore M S Sched x s₀ s'` for every `s'`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot; `s'`: the
  bound on the slots.

Read aloud: when the updaters' confirmations from slot `s₀` on form one chain, so do those of the
slots from `s₀` to before `s'`. -/
theorem confirmationsChainBefore_of_chain (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s' : ℕ) (h : ConfirmationsChain M S A x s₀) :
    ConfirmationsChainBefore M S A x s₀ s' :=
  fun s s'' v v' C C' h₀ hle _ => h s s'' v v' C C' h₀ hle

end Executions

end GoldilocksCorrectness.Record.Statements.Executions

