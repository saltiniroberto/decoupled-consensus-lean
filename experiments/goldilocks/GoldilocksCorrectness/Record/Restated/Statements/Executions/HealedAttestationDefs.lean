module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateDefs
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs

@[expose] public section

/-!
# HealedAttestationDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/HealedAttestationDefs.lean` over a
model `M`, for an execution `x` of `protocolOf M S`: the honest attestations name the honest chain's
entry blocks, and the heights of the attestations sent before a time.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `HonestAttestationsOnChain M S Sched x s₀ t₀`: whenever the step `i` is the tick of every awake
validator at a time `t ≥ t₀`, and puts on the wire an attestation `a` of the validator `v` whose
tick it is, some slot `s ≥ s₀` has `t = M.supportCutoff S.C (s + 1)`, and some
block `E` is on the honest chain from slot `s₀` at slot `s` (`OnHonestChainAt M S Sched x s₀ s E`),
is an entry block, has the chain-state height `a.h`, and has the root `a.T`.

No `v ∈ A.awakeAtTime x t` is asked beside the tick: a tick is by
a validator awake at its own step (the environment's `tick_active`).
The attester is asked outside the adversary set after every step whose time is at most the real
time of its tick (`v ∉ A.corruptedAtTime x (x.time i)`): the honesty asked is the honesty the
validator has beside its own tick, read at the tick's real time, not at the clock value `t` the
tick reads (which a clock ahead of real time puts after the tick).

The slot `s` is the slot whose confirmation update the attestation followed: the attestation is
sent at that update's time, so a bound on the time of the send bounds the time at which `E` is on
the honest chain.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `t₀`: the time from which the attestations are read;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation; `s`: the slot whose
  update the attestation followed; `E`: the entry block.

Read aloud: every attestation a validator's tick puts on the wire at or after `t₀`, by a validator
honest up to the real time of its tick, is sent at the update time of
a slot `s` and names, by its root, the honest chain's entry block of slot `s` at the
attestation's height. -/
def HonestAttestationsOnChain (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ t₀ : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V),
    x.lbl i = Event.tick v t → t₀ ≤ t → v ∉ A.corruptedAtTime x (x.time i) →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i →
    ∃ (s : ℕ) (E : Block V), s₀ ≤ s ∧ t = M.supportCutoff S.C (s + 1) ∧
      OnHonestChainAt M S A x s₀ s E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = a.h ∧ a.T = E.root

/-- `OldAttestationsAtMost M S Sched x t₀ H`: whenever the step `i` is the tick of every awake
validator at a time `t < t₀`, and puts on the wire an attestation `a` of the validator `v` whose
tick it is, the height `a.h` is at most `H`.

No `v ∈ A.awakeAtTime x t` is asked beside the tick: a tick is by
a validator awake at its own step (the environment's `tick_active`).
No `v ∉ A.corruptedAtTime x t` is asked beside the tick either: a tick is
by a validator outside the adversary set at its own step (the environment's `tick_active`).

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound on their heights;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation.

Read aloud: every attestation a validator's tick put on the wire before `t₀` has height at most
`H`. -/
def OldAttestationsAtMost (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (t₀ H : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V),
    x.lbl i = Event.tick v t → t < t₀ →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i →
    a.h ≤ H

/-- `OldAttestationsAtMostHonestAt M S Sched x t₀ tH H`: whenever the step `i` is the tick of every
awake validator at a time `t < t₀`, and puts on the wire an attestation `a` of a validator `v`
outside the adversary set at the time `tH`, the height `a.h` is at most `H`.
With permanent corruption and `t ≤ tH`, `v` is honest at `t` too, so this is
`OldAttestationsAtMost M S Sched x t₀ H` (`HealedAttestationDefs.lean:75`) restricted to the senders
still honest at `tH`.

No `v ∈ A.awakeAtTime x t` is asked beside the tick: a tick is by
a validator awake at its own step (the environment's `tick_active`).

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `tH`: the time at which the senders' honesty is read; `H`: the bound.

Read aloud: every attestation a validator honest at `tH` put on the wire at a tick before `t₀` has
height at most `H`. -/
def OldAttestationsAtMostHonestAt (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (t₀ tH : ℝ) (H : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V),
    x.lbl i = Event.tick v t → t < t₀ →
    v ∉ A.corruptedAtTime x tH →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i →
    a.h ≤ H

end GoldilocksCorrectness.Record.Statements.Executions

