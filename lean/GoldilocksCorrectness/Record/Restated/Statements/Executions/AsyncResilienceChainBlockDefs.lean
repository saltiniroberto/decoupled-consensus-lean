module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceChainBlockDefs

@[expose] public section

/-!
# AsyncResilienceChainBlockDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/AsyncResilienceChainBlockDefs.lean`
over a model `M`, for an execution `x` of `protocolOf M S`: the certificates on a held chain
compatible with a block, the new honest attestations naming a held entry compatible with it, and the
facts at the hand-over read with them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

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

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

section Kit

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `CertificatesCompatibleWithAtOfChainBlock M S Sched x H B j`: for every block `D` a validator
honest at step `j` holds then, and every block `T` of `D`'s chain (`T` is `D` or an ancestor of
`D`), every progress certificate at a height `h` greater than `H` on `D`'s chain for `T` has `T`
compatible with `B`.

 The original concludes
that some block `E` with the certificate's root and height is compatible with `B`; `E` is held by
nobody, so the original says nothing about any certificate at a height at least `B`'s
. Here the certificate's own block
`T`, a block of `D`'s chain, is compatible with `B`. A certificate on `D`'s chain for a block off
`D`'s chain is not covered: the chain-state computation counts only the votes for its own entry
at its height, so such a certificate moves no chain state.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step.

Read aloud: at step `j`, every certificate at a height greater than `H` on a held chain, for a
block of that chain, is for a block compatible with `B`. -/
def CertificatesCompatibleWithAtOfChainBlock (H : ℕ) (B : Block V) (j : ℕ) : Prop :=
  ∀ (w : V) (D T : Block V) (h : Height),
    w ∉ A.corrupted j → D ∈ (x.st j w).tree → T.AncestorEq D →
    ProgressCertOn D h T → H < h →
    (T.AncestorEq B ∨ B.AncestorEq T)

/-- `CertificatesCompatibleWithOfChainBlock M S Sched x H B`: at every step, every progress
certificate at a height greater than `H` on the chain of a block `D` a validator honest then
holds, for a block `T` of `D`'s chain, has `T` compatible with `B`.



The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block.

Read aloud: no honest validator ever holds a chain with a certificate at a height greater than
`H` for a block of that chain conflicting with `B`. -/
def CertificatesCompatibleWithOfChainBlock (H : ℕ) (B : Block V) : Prop :=
  ∀ (j : ℕ) (w : V) (D T : Block V) (h : Height),
    w ∉ A.corrupted j → D ∈ (x.st j w).tree → T.AncestorEq D →
    ProgressCertOn D h T → H < h →
    (T.AncestorEq B ∨ B.AncestorEq T)

/-- `AttestationsCompatibleWithBeforeOfHeldEntry M S Sched x B H t₀ j`: every attestation a
validator's tick put on the wire at a step before `j` has height at most `H` when the
tick is before `t₀` and the sender is still outside the adversary set at `t₀`, and, when the tick
is at or after `t₀`, names by root an entry block compatible with `B` at its height that some
validator honest then holds at a step of time at most the tick's.

 an attestation sent before `t₀` by a validator corrupted by `t₀` is not bounded.

No `v ∈ A.awakeAtTime x t` is asked beside the tick: a tick is by
a validator awake at its own step (the environment's `tick_active`).
For a tick at or after `t₀`, the sender is asked outside the adversary set after every step whose
real time is at most the tick's real time `x.time i`; for a tick before `t₀`, at `t₀`.

 The original's `E` is held by nobody, so no
root comparison with a held block can identify it; the attestation's entry is in its sender's tree when it attests.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `j`: the step.

Read aloud: up to step `j`, the attestations ticks put on the wire before `t₀` by a validator still
honest at `t₀` have height at most `H`, and those sent from `t₀` on by a validator still honest once
the steps at the real time of its tick are over name an entry of a chain compatible with `B` that an
honest validator held by that real time. -/
def AttestationsCompatibleWithBeforeOfHeldEntry (B : Block V) (H t₀ j : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V), i < j →
    x.lbl i = Event.tick v t →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i →
    (t < t₀ → v ∉ A.corruptedAtTime x t₀ → a.h ≤ H) ∧
    (t₀ ≤ t → v ∉ A.corruptedAtTime x (x.time i) →
      ∃ E : Block V, (E.AncestorEq B ∨ B.AncestorEq E) ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = a.h ∧ a.T = E.root ∧ inHonestTreeBy M A x (x.time i) E)

end Kit

section Period

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `HandoverFactsOfChainBlock M S Sched x tW s B H t₀ tAwakeEnd`: `HandoverFacts S Sched x s B H t₀
tAwakeEnd` with the certificate clause `CertificatesCompatibleWithAtOfChainBlock` and the
attestation clause `AttestationsCompatibleWithBeforeOfHeldEntry`. The facts right after the hand-over
update at the cutoff `c = M.supportCutoff S.C (s + 1)`: `H` is less than `B`'s chain-state height;
every lock holder, in the state its own tick to `c` leaves (`x.tickOutput w c`, the configuration
`x.tickStep w c + 1`), saved `B` for slot `s`, records `B`, and satisfies `HolderInvAt`; at every
configuration whose time is from `c` to the window's end `tW`, every validator outside the adversary set there has its caches
compatible with `B`, every certificate at a height greater than `H` on a held chain, for a block of
that chain, is for a block compatible with `B`, and every honest attestation sent before that
configuration is old (height at most `H`, when sent before `t₀`) or names an entry compatible with
`B` held by an honest validator by its time; every honest active voter of slot `s + 1` voted on
`B`'s chain; and every confirmed tip read at a step from `tAwakeEnd` to the cutoff is `B` or an
ancestor of `B`.

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
def HandoverFactsOfChainBlock (tW : ℝ) (s : ℕ) (B : Block V) (H t₀ tAwakeEnd : ℕ) : Prop :=
  H < (M.chainStateOf S.C B).h ∧
  (∀ w ∈ updaterAt M S A x s,
    (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
    (x.tickOutput w (M.supportCutoff S.C (s + 1))).latestConfirmed = B ∧
    HolderInvAt M S x s B (x.tickStep w (M.supportCutoff S.C (s + 1)) + 1) w) ∧
  (∀ (j : ℕ) (u : V), (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → u ∉ A.corrupted j →
    CachesCompatibleWith M S B H (x.st j u)) ∧
  (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → CertificatesCompatibleWithAtOfChainBlock M A x H B j) ∧
  (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW →
    AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ j) ∧
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

