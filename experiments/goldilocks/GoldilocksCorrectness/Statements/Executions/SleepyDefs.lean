module
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# The sleepy model over executions, and the vocabulary of the honest chain

The definitions the statements about the sleepy model (`SleepyStatements.lean`) and the honest
chain read:

- `activeAt S Sched s`, `honestActiveAt S Sched s` and `updaterAt S Sched s`, the validators awake
  through the duties of slot `s`, the honest ones among them, and the validators awake and honest
  through the confirmation update that evaluates slot `s`;
- `Sleepiness S Sched anchor` and `CommitteeSleepiness S Sched anchor`, the two sleepiness
  conditions from a time `anchor` on;
- `HonestCommitteesIn S Sched t₀ t₁ tH`, honest committee majorities at the slots of a phase,
  with the time at which honesty is read as a parameter;
- `OnHonestChainAt`, `OnHonestChain`, `OnHonestChainBefore`, `ConfirmationsChain` and
  `ConfirmationsChainBefore`, the honest chain made of the updaters' saved confirmations, and
  `confirmationsChainBefore_of_chain`, that the whole chain gives every prefix of it.

`AdversaryFewerThanQuorumUntil` (read with `quorum V`: fewer than `quorum V` validators are in the
adversary set at some time up to `t`) is stated for any protocol in
`Statements/Network/NetworkDefs.lean`.


-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `activeAt S Sched s`: the validators awake at every time from the duty window's start of slot
`s` to the support cutoff of slot `s + 1`, where their confirmation update that evaluates slot `s`
runs.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s`. -/
def activeAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Finset V :=
  Sched.awakeThroughout ((dutyWindowStart S s : ℕ) : Int) ((supportCutoff S (s + 1) : ℕ) : Int)

omit [Fintype V] in
/-- `honestActiveAt S Sched s`: the validators of `activeAt S Sched s` outside the adversary set
at the support cutoff of slot `s + 1`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s` and honest at its update. -/
def honestActiveAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Finset V :=
  activeAt S Sched s \ Sched.adv ((supportCutoff S (s + 1) : ℕ) : Int)

omit [Fintype V] in
/-- `updaterAt S Sched s`: the validators awake at every time from the duty window's start of
slot `s + 1` to the support cutoff of slot `s + 1`, the window of the confirmation update that
evaluates slot `s`, and outside the adversary set at that cutoff.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot the update evaluates.

Read aloud: the validators awake and honest through the update of slot `s`. -/
def updaterAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Finset V :=
  Sched.awakeThroughout ((dutyWindowStart S (s + 1) : ℕ) : Int)
      ((supportCutoff S (s + 1) : ℕ) : Int) \
    Sched.adv ((supportCutoff S (s + 1) : ℕ) : Int)

/-- `Sleepiness S Sched anchor`: at every slot `s ≥ 1` starting at or after `anchor`, the
validators of `activeAt S Sched (s - 1)` outside the adversary set at the vote time of slot `s`
outnumber the adversary set at that time.

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which the condition holds.

Read aloud: from `anchor` on, the honest validators active at the slot before outnumber the
adversary at every vote time. -/
def Sleepiness (S : Setup V) (Sched : Schedule V) (anchor : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → anchor ≤ slotStart S s →
    |Sched.adv ((voteTime S s : ℕ) : Int)| <
      |activeAt S Sched (s - 1) \ Sched.adv ((voteTime S s : ℕ) : Int)|

/-- `CommitteeSleepiness S Sched anchor`: at every slot `s ≥ 1` starting at or after `anchor`,
the members of the committee of slot `s − 1` in `honestActiveAt S Sched (s - 1)` outnumber the
other members of that committee.

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which the condition holds.

Read aloud: from `anchor` on, in the committee of the slot before each slot, the honest active
members are more than the rest. -/
def CommitteeSleepiness (S : Setup V) (Sched : Schedule V) (anchor : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → anchor ≤ slotStart S s →
    |S.P.committee (s - 1) \ honestActiveAt S Sched (s - 1)| <
      |honestActiveAt S Sched (s - 1) ∩ S.P.committee (s - 1)|

/-- `CommitteeSleepinessUntil S Sched anchor T`: at every slot `s ≥ 1` starting at or after
`anchor` whose support cutoff is at most `T`, the members of the committee of slot `s − 1` in
`honestActiveAt S Sched (s - 1)` outnumber the other members of that committee.

The condition at slot `s` is a statement about the schedule up to `supportCutoff S s`:
`honestActiveAt S Sched (s - 1)` is the set of validators awake through the duties of slot `s − 1`,
up to that cutoff, and outside the adversary set at it. So the premise reads nothing after `T`.

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which the condition holds; `T`:
  the time up to which it is read.

Read aloud: from `anchor` on, for every slot whose update is at most `T`, the honest active members
of the previous slot's committee are more than the rest. -/
def CommitteeSleepinessUntil (S : Setup V) (Sched : Schedule V) (anchor T : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → anchor ≤ slotStart S s → supportCutoff S s ≤ T →
    |S.P.committee (s - 1) \ honestActiveAt S Sched (s - 1)| <
      |honestActiveAt S Sched (s - 1) ∩ S.P.committee (s - 1)|

/-- `HonestCommitteesIn S Sched t₀ t₁ tH`: at every slot `s` that starts at or after `t₀` and
whose next slot starts at or before `t₁`, the members of the committee of slot `s` outside the
adversary set at the time `tH s` are more than half of that committee.

The variables:
- `S`: the setup; `Sched`: the schedule; `t₀`, `t₁`: the ends of the phase;
- `tH`: for each slot, the time at which the honesty of its committee is read.

Read aloud: in every committee of the phase, more than half of the members are honest at the
time `tH` names for its slot. -/
def HonestCommitteesIn (S : Setup V) (Sched : Schedule V) (t₀ t₁ : ℕ) (tH : (s : ℕ) → ℕ) :
    Prop :=
  ∀ s : ℕ, t₀ ≤ slotStart S s → slotStart S (s + 1) ≤ t₁ →
    |S.P.committee s| < 2 * |S.P.committee s \ Sched.adv ((tH s : ℕ) : Int)|

section Executions

variable [RootOrder]

/-- `OnHonestChainAt S Sched x s₀ s B`: `s` is at or after `s₀`, and `B` is an ancestor of, or
equal to, the confirmation of slot `s` that some validator of `updaterAt S Sched s` holds right
after its update, on its node state before the time after the support cutoff of slot `s + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₀`: the first slot of the chain; `s`: the slot; `B`: the block.

Read aloud: `B` is on the honest chain at slot `s`. -/
def OnHonestChainAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₀ s : ℕ) (B : Block V) : Prop :=
  s₀ ≤ s ∧ ∃ v ∈ updaterAt S Sched s, ∃ C : Block V,
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C ∧
    B.AncestorEq C

/-- `OnHonestChain S Sched x s₀ B`: `B` is on the honest chain at some slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₀`: the first slot of the chain; `B`: the block.

Read aloud: `B` is on the honest chain from slot `s₀`. -/
def OnHonestChain (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₀ : ℕ) (B : Block V) : Prop :=
  ∃ s : ℕ, OnHonestChainAt S Sched x s₀ s B

/-- `OnHonestChainBefore S Sched x s₀ s B`: `B` is on the honest chain at some slot less than
`s`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₀`: the first slot of the chain; `s`: the bound on the slot; `B`: the block.

Read aloud: `B` is on the honest chain before slot `s`. -/
def OnHonestChainBefore (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₀ s : ℕ) (B : Block V) : Prop :=
  ∃ s' : ℕ, s' < s ∧ OnHonestChainAt S Sched x s₀ s' B

/-- `ConfirmationsChain S Sched x s₀`: from slot `s₀` on, a confirmation that a validator of
`updaterAt` holds right after its update for a slot is an ancestor of, or equal to, one that a
validator of `updaterAt` holds for a later slot, and two such confirmations of one slot are
compatible.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot;
- `s`, `s'`: the two slots; `v`, `v'`: the two updaters; `C`, `C'`: their confirmations.

Read aloud: from slot `s₀` on, the updaters' confirmations form one chain. -/
def ConfirmationsChain (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₀ : ℕ) : Prop :=
  ∀ (s s' : ℕ) (v v' : V) (C C' : Block V), s₀ ≤ s → s ≤ s' →
    v ∈ updaterAt S Sched s → v' ∈ updaterAt S Sched s' →
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C →
    (stateBefore x (supportCutoff S (s' + 1) + 1) v').A.saved_confirmation s' = some C' →
    (s < s' → C.AncestorEq C') ∧ (s = s' → C.compatible C' = true)

/-- `ConfirmationsChainBefore S Sched x s₀ s'`: `ConfirmationsChain S Sched x s₀` for the slots
less than `s'`: from slot `s₀` on and before slot `s'`, a confirmation that a validator of
`updaterAt` holds right after its update for a slot is an ancestor of, or equal to, one that a
validator of `updaterAt` holds for a later slot, and two such confirmations of one slot are
compatible.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot; `s'`: the
  bound on the slots;
- `s`, `s''`: the two slots; `v`, `v'`: the two updaters; `C`, `C'`: their confirmations.

Read aloud: the updaters' confirmations of the slots from `s₀` to before `s'` form one chain. -/
def ConfirmationsChainBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s' : ℕ) : Prop :=
  ∀ (s s'' : ℕ) (v v' : V) (C C' : Block V), s₀ ≤ s → s ≤ s'' → s'' < s' →
    v ∈ updaterAt S Sched s → v' ∈ updaterAt S Sched s'' →
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C →
    (stateBefore x (supportCutoff S (s'' + 1) + 1) v').A.saved_confirmation s'' = some C' →
    (s < s'' → C.AncestorEq C') ∧ (s = s'' → C.compatible C' = true)

/-- The whole chain gives every prefix of it: `ConfirmationsChain S Sched x s₀` implies
`ConfirmationsChainBefore S Sched x s₀ s'` for every `s'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot; `s'`: the
  bound on the slots.

Read aloud: when the updaters' confirmations from slot `s₀` on form one chain, so do those of the
slots from `s₀` to before `s'`. -/
theorem confirmationsChainBefore_of_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s' : ℕ) (h : ConfirmationsChain S Sched x s₀) :
    ConfirmationsChainBefore S Sched x s₀ s' :=
  fun s s'' v v' C C' h₀ hle _ => h s s'' v v' C C' h₀ hle

end Executions

end GoldilocksCorrectness.Statements.Executions
