module
public import GoldilocksCorrectness.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Statements.Routines.ChainStateDefs

@[expose] public section

/-!
# The attestations after the healed round: the definitions

The definitions the statements about the attestations and the certificates after the healed round
(`HealedAttestationStatements.lean`) read:

- `IsEntry C E`, the block `E` took its own chain into its height;
- `HonestAttestationsOnChain S Sched x s₀ t₀`, every attestation an honest awake validator puts
  on the wire at a tick at or after `t₀` is sent at the support cutoff of slot `s + 1` for some
  slot `s ≥ s₀`, and names, by its root, the entry block of the honest chain at slot `s` at the
  attestation's height;
- `OldAttestationsAtMost S Sched x t₀ H`, every attestation an honest awake validator put on the
  wire at a tick before `t₀` has height at most `H`.


-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `HonestAttestationsOnChain S Sched x s₀ t₀`: whenever the step `i` is the tick of every awake
validator at a time `t ≥ t₀`, and puts on the wire an attestation `a` of a validator `v` awake and
outside the adversary set at `t`, some slot `s ≥ s₀` has `t = supportCutoff S (s + 1)`, and some
block `E` is on the honest chain from slot `s₀` at slot `s` (`OnHonestChainAt S Sched x s₀ s E`), is
an entry block, has the chain-state height `a.h`, and has the root `a.T`.

The slot `s` is the slot whose confirmation update the attestation followed: the attestation is
sent at that update's time, so a bound on the time of the send bounds the time at which `E` is on
the honest chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `t₀`: the time from which the attestations are read;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation; `s`: the slot whose
  update the attestation followed; `E`: the entry block.

Read aloud: every honest attestation sent at or after `t₀` is sent at the update time of a slot `s`
and names, by its root, the honest chain's entry block of slot `s` at the attestation's height. -/
def HonestAttestationsOnChain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V),
    x.lbl i = AtomicAction.tickAllAwake t → t₀ ≤ t →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.adv (t : Int) →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent →
    ∃ (s : ℕ) (E : Block V), s₀ ≤ s ∧ t = supportCutoff S (s + 1) ∧
      OnHonestChainAt S Sched x s₀ s E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = a.h ∧ a.T = E.root

/-- `OldAttestationsAtMost S Sched x t₀ H`: whenever the step `i` is the tick of every awake
validator at a time `t < t₀`, and puts on the wire an attestation `a` of a validator `v` awake and
outside the adversary set at `t`, the height `a.h` is at most `H`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound on their heights;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation.

Read aloud: every attestation an honest awake validator put on the wire at a tick before `t₀` has
height at most `H`. -/
def OldAttestationsAtMost (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ H : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V),
    x.lbl i = AtomicAction.tickAllAwake t → t < t₀ →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.adv (t : Int) →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent →
    a.h ≤ H

/-- `OldAttestationsAtMostHonestAt S Sched x t₀ tH H`: whenever the step `i` is the tick of every
awake validator at a time `t < t₀`, and puts on the wire an attestation `a` of a validator `v`
awake at `t` and outside the adversary set at the time `tH`, the height `a.h` is at most `H`.
With permanent corruption and `t ≤ tH`, `v` is honest at `t` too, so this is
`OldAttestationsAtMost S Sched x t₀ H` (`HealedAttestationDefs.lean:75`) restricted to the senders
still honest at `tH`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `tH`: the time at which the senders' honesty is read; `H`: the bound.

Read aloud: every attestation a validator honest at `tH` put on the wire at a tick before `t₀` has
height at most `H`. -/
def OldAttestationsAtMostHonestAt (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ tH H : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V),
    x.lbl i = AtomicAction.tickAllAwake t → t < t₀ →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.adv (tH : Int) →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent →
    a.h ≤ H

end GoldilocksCorrectness.Statements.Executions
