module
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs

@[expose] public section

/-!
The originals stay byte-identical;

- `CertificatesCompatibleWithAtOfChainBlock`, the copy of `CertificatesCompatibleWithAt`: the
  certificate's own block, a block of the held chain, is compatible with `B`, in place of "some
  block with the certificate's root and height is compatible with `B`";
- `CertificatesCompatibleWithOfChainBlock`, the copy of `CertificatesCompatibleWith`, the same
  change at every step;
- `AttestationsCompatibleWithBeforeOfHeldEntry`, the copy of `AttestationsCompatibleWithBefore`:
  the entry an honest attestation names is one honest validators hold by the tick's time
  (`inHonestTreeBy x t E`), a conjunct added;
- `HandoverFactsOfChainBlock`, the copy of `HandoverFacts`, which names the two copied clauses in
  place of the originals, and nothing else.

 Deleted then: `PeriodInvOfChainBlock`,
the copy of `PeriodInv` and itself the original of `PeriodInvOfChainBlockDueByCutoff`,
and with it `PeriodInv` and `CertificatesCompatibleWith`. `CertificatesCompatibleWithAt`,
`AttestationsCompatibleWithBefore` and `HandoverFacts` stay: the proofs of the top statements
reach them through `handoverFacts_of_ofChainBlock` and `AsyncHyps`.

Why the originals cannot be used: their block `E` is a
bare value of `Block V`, held by nobody, and a block's root is a free field, so at every height
at least `B`'s the original certificate clause holds of every certificate whatever block it is
for; the step of Lemma 103 (the caches stay compatible with `B`) and the step of Lemma 106 (a held
block two heights past `B` descends from `B`) are false over it.
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Kit

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `CertificatesCompatibleWithAtOfChainBlock S Sched x H B j`: for every block `D` a validator
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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step.

Read aloud: at step `j`, every certificate at a height greater than `H` on a held chain, for a
block of that chain, is for a block compatible with `B`. -/
def CertificatesCompatibleWithAtOfChainBlock (H : ℕ) (B : Block V) (j : ℕ) : Prop :=
  ∀ (w : V) (D T : Block V) (h : Height),
    w ∉ Sched.adv (x[j].time : Int) → D ∈ (x[j][w].st).S.T → T.AncestorEq D →
    ProgressCertOn D h T → H < h →
    (T.AncestorEq B ∨ B.AncestorEq T)

/-- `CertificatesCompatibleWithOfChainBlock S Sched x H B`: at every step, every progress
certificate at a height greater than `H` on the chain of a block `D` a validator honest then
holds, for a block `T` of `D`'s chain, has `T` compatible with `B`.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block.

Read aloud: no honest validator ever holds a chain with a certificate at a height greater than
`H` for a block of that chain conflicting with `B`. -/
def CertificatesCompatibleWithOfChainBlock (H : ℕ) (B : Block V) : Prop :=
  ∀ (j : ℕ) (w : V) (D T : Block V) (h : Height),
    w ∉ Sched.adv (x[j].time : Int) → D ∈ (x[j][w].st).S.T → T.AncestorEq D →
    ProgressCertOn D h T → H < h →
    (T.AncestorEq B ∨ B.AncestorEq T)

/-- `AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ j`: every attestation an honest
awake validator put on the wire at a tick at a step before `j` has height at most `H` when the
tick is before `t₀`, and, when the tick is at or after `t₀`, names by root an entry block
compatible with `B` at its height that some validator honest then holds at a step of time at most
the tick's.

 The original's `E` is held by nobody, so no
root comparison with a held block can identify it; the attestation's entry is in its sender's tree when it attests.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `j`: the step.

Read aloud: up to step `j`, the honest attestations are old (height at most `H`) or name an
entry of a chain compatible with `B` that an honest validator held by then. -/
def AttestationsCompatibleWithBeforeOfHeldEntry (B : Block V) (H t₀ j : ℕ) : Prop :=
  ∀ (i t : ℕ) (v : V) (a : Attestation V), i < j →
    x.lbl i = AtomicAction.tickAllAwake t →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.adv (t : Int) →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent →
    (t < t₀ → a.h ≤ H) ∧
    (t₀ ≤ t → ∃ E : Block V, (E.AncestorEq B ∨ B.AncestorEq E) ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = a.h ∧ a.T = E.root ∧ inHonestTreeBy x t E)

end Kit

section Period

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `HandoverFactsOfChainBlock S Sched x s B H t₀ tAwakeEnd`: `HandoverFacts S Sched x s B H t₀
tAwakeEnd` with the certificate clause `CertificatesCompatibleWithAtOfChainBlock` and the
attestation clause `AttestationsCompatibleWithBeforeOfHeldEntry`. The facts at the step
`stepBefore x (supportCutoff S (s + 1) + 1)`, whose configuration is the one right after the
hand-over update: `H` is less than `B`'s chain-state height; every lock holder saved `B` for slot
`s`, records `B`, and satisfies `HolderInvAt`; every validator outside the adversary set after a
step whose time is the cutoff has, after that step, its caches compatible with `B`; every certificate at a height greater than `H` on a held chain, for a block
of that chain, is for a block compatible with `B`; every honest attestation sent before then is
old (height at most `H`, when sent before `t₀`) or names an entry compatible with `B` held by an
honest validator by its time; every honest active voter of slot `s + 1` voted on `B`'s chain; and
every confirmed tip read at a step from `tAwakeEnd` to the cutoff is `B` or an ancestor of `B`.





The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `H`: the height threshold; `t₀`: the time from which the attestations are new;
  `tAwakeEnd`: the time from which the confirmed tips are read.

Read aloud: right after the hand-over update every honest validator that ran it holds a live fast
lock on `B` and records `B`; nobody's caches, certificates or attestations conflict with `B`; and
what anyone had confirmed from `tAwakeEnd` on is an ancestor of `B`. -/
def HandoverFactsOfChainBlock (s : ℕ) (B : Block V) (H t₀ tAwakeEnd : ℕ) : Prop :=
  H < (chainStateOf S.C B).h ∧
  (∀ w ∈ updaterAt S Sched s,
    (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s = some B ∧
    (stateBefore x (supportCutoff S (s + 1) + 1) w).A.latest_confirmed = B ∧
    HolderInvAt S Sched x s B (stepBefore x (supportCutoff S (s + 1) + 1)) w) ∧
  (∀ (j : ℕ) (u : V), x[j].time = supportCutoff S (s + 1) → u ∉ Sched.adv (x[j].time : Int) →
    CachesCompatibleWith S B H (x[j][u].st)) ∧
  CertificatesCompatibleWithAtOfChainBlock S Sched x H B
    (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
  AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀
    (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
  (∀ b₀ b₁ : ℕ, VotesExtendAt S Sched x s B b₀ b₁ (s + 1)) ∧
  (∀ (v : V) (T : ℕ) (P : Block V), HonestThrough x T v → tAwakeEnd ≤ x[T].time →
    x[T].time ≤ supportCutoff S (s + 1) →
    P.AncestorEq (confirmedOf (x[T][v].st)) → P.AncestorEq B)

end Period

section After

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end After

end GoldilocksCorrectness.Statements.Executions
