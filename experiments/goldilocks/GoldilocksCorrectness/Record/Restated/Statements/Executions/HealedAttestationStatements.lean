module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma83

@[expose] public section

/-!
# HealedAttestationStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealedAttestationStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the block that took
a chain into its height is an entry block, Lemma 82 and its part (b), the honest attestations after
the healed round name the honest chain's entries, Lemma 83, one certificate and one justification
per height greater than the threshold, and the bound on the old attestations in the form with the
senders honest at a time. Each is the theorem of the same name of
`Record/Restated/Proofs/Routines/ChainStateOf.lean`,
`Record/Restated/Proofs/Executions/Lemma82.lean` or
`Record/Restated/Proofs/Executions/Lemma83.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry)
open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn ProgressCertOn)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

omit [RootOrder] in
/-- **Kit fact, the block that took a chain into its height is an entry block.** For every block
`D`, the block `(M.chainStateOf C D).T_h` is an entry block, has `D`'s chain-state height, and is
`D` or an ancestor of `D`.

Why: the last two are the specification of `T_h` along a chain; two blocks of one chain at one
height have one `T_h` (Lemma 47 (e)), so the `T_h` of `T_h` is itself.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block.

Read aloud: the block that took `D`'s chain into its height is an entry block, has `D`'s height,
and is `D` or an ancestor of `D`.

 -/
theorem isEntry_T_h (C : Config) (D : Block V) :
    IsEntry M C (M.chainStateOf C D).T_h ∧
      (M.chainStateOf C (M.chainStateOf C D).T_h).h = (M.chainStateOf C D).h ∧
      (M.chainStateOf C D).T_h.AncestorEq D :=
  (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) C D

/-- **Lemma 82, the honest attestations after the healed round name the honest chain's
entries.** In an execution where every time is reached and corruption is permanent, every
attestation an honest awake validator puts on the wire at a tick at or after the support cutoff of
slot `s₀ + 1` is sent at the support cutoff of slot `s + 1` for some slot `s ≥ s₀`, and names, by
its root, an entry block of the honest chain from slot `s₀` at slot `s`
(`OnHonestChainAt M S Sched x s₀ s E`) whose chain-state height is the attestation's height.

Why: the attestation was built at the action time of a round, the support cutoff of slot `s + 1`
with `s` the round's first slot and `s₀ ≤ s`, from the height and the `T_h` of the duty's source;
the tick passed the duty test, so it ran the confirmation update of slot `s + 1`, whose fast blocks
hold the source; that update saved a confirmation for slot `s`, the source being that block or an
ancestor of it; the validator was awake through the update's window, so it is an updater of slot
`s`; the source's `T_h` is the entry block (`isEntry_T_h`). This is Lemma 82 (b),
`lem82b_entry_at_slot`, with the updater and its confirmation put together.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot.

Read aloud: from the action time of the healed round on, every attestation an honest awake
validator sends is sent at the update time of a slot `s`, and names the honest chain's entry block
of slot `s` at the attestation's height.

 -/
theorem lem82_honest_attestations_on_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    :
    HonestAttestationsOnChain M S A x s₀ (M.supportCutoff S.C (s₀ + 1)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem82_honest_attestations_on_chain M F U) S A
    x R s₀ E

/-- **Lemma 83, one progress certificate per height greater than the threshold.** Under
unforgeability, take a block `B` that `w` holds after `j` steps, and a progress certificate on the
chain of `B` at a height `h` greater than `H` naming `T`'s root; when fewer than a quorum of
validators have been in the adversary set up to the time after `j` steps, every attestation an
honest awake validator sends at or after `t₀` names the honest chain's entry block at its height,
and every one a validator honest at the time after `j` steps sent before `t₀` has height at most
`H`, then for some slot `s_a` to whose support cutoff
of slot `s_a + 1` some validator ticked at a step before `j`,
`T`'s root is the root of an entry block of the honest chain from slot `s₀` at slot `s_a` at the
height `h`.

Why: some member `u` of the certificate's quorum was never in the adversary set up to that time;
`u`'s vote is in `u`'s record (Lemma 74), so `u`'s tick sent an attestation with its content,
awake and honest then, at a tick before the step `j`; `u` is honest at the time after `j` steps, so
at the height `h > H` it was not sent before `t₀`, and it names the entry of the slot `s_a` to whose
support cutoff of slot `s_a + 1` its tick was.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the bound on the heights of the
  earlier ones;
- `j`: the step; `w`: the holder; `B`: the held block; `T`: the block whose root the certificate
  names; `h`: the certificate's height; `s_a`: the slot of the entry `E`.

Read aloud: a progress certificate at a height greater than `H`, on the chain of a held block,
names by root the honest chain's entry block at that height, at a slot whose update some validator ran at a tick before the step `j`.

 -/
theorem lem83_one_certificate_greater_than_threshold (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    -- fewer than a quorum of validators have been in the adversary set up to the time after `j`
    -- steps
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time j))
    -- every honest attestation sent at or after `t₀` is sent at the support cutoff of slot `s + 1`
    -- for a slot `s`, and names the honest chain's entry of slot `s` at its height
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    -- every attestation sent before `t₀` by a validator honest after `j` steps has height at most
    -- `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ (x.time j) H)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x.st j w).tree)
    -- a quorum of votes at `h` naming `T`'s root is included on the chain of `B`
    (hJ : ProgressCertOn M B h T)
    -- the height is greater than `H`
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem83_one_certificate_greater_than_threshold M F Fx)
    S A x R E s₀ t₀ H j w B T h hAdvQ hAgree hOld hB hJ hH

/-- **Lemma 83, one justification per height greater than the threshold.** Under
unforgeability, take a block `B` that `w` holds after `j`
steps, and a justification certificate on the chain of `B` at a height `h` greater than `H` for
`T`'s root; when fewer than a quorum of validators have been in the adversary set up to the time
after `j` steps, every attestation an honest awake validator sends at or after `t₀` names the
honest chain's entry block at its height, and every one a validator honest at the time after `j`
steps sent before `t₀` has height at most `H`, then
for some slot `s_a` to whose support cutoff of slot `s_a + 1` some validator ticked at a step before
`j`, `T`'s root is the root of an entry block of the honest chain from slot `s₀` at slot `s_a` at the
height `h`.

Why: a justification certificate is a progress certificate (its target votes are votes at `h`
naming `T`'s root).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the bound on the heights of the
  earlier ones;
- `j`: the step; `w`: the holder; `B`: the held block; `T`: the justified block; `h`: the
  certificate's height; `s_a`: the slot of the entry `E`.

Read aloud: a justification certificate at a height greater than `H`, on the chain of a held
block, names by root the honest chain's entry block at that height, at a slot whose update some validator ran at a tick before the step `j`.

 -/
theorem lem83_one_justification_greater_than_threshold (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    -- fewer than a quorum of validators have been in the adversary set up to the time after `j`
    -- steps
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time j))
    -- every honest attestation sent at or after `t₀` is sent at the support cutoff of slot `s + 1`
    -- for a slot `s`, and names the honest chain's entry of slot `s` at its height
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    -- every attestation sent before `t₀` by a validator honest after `j` steps has height at most
    -- `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ (x.time j) H)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x.st j w).tree)
    -- a quorum of target votes at `h` for `T`'s root is included on the chain of `B`
    (hJ : JustificationCertOn M B h T)
    -- the height is greater than `H`
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem83_one_justification_greater_than_threshold M F Fx)
    S A x R E s₀ t₀ H j w B T h hAdvQ hAgree hOld hB hJ hH

/-- **Kit fact, the bound on the old attestations in the honest-at form.** When every attestation
an honest awake validator put on the wire at a tick before `t₀` has height at most `H`, then for
every time `tH`, every attestation a validator honest at `tH` put on the wire at a tick before `t₀`
has height at most `H`.

Why: what a tick puts on the wire is signed by a validator awake and outside the adversary set at
the tick, so the sender was honest at the send.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `tH`: the time at which the senders' honesty is read; `H`: the bound.

Read aloud: a bound on the attestations of the validators honest at the send bounds those of the
validators honest at any later or earlier time.

 -/
theorem oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t₀ tH H : ℕ)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMost M S A x t₀ H) :
    OldAttestationsAtMostHonestAt M S A x t₀ tH H :=
  (GoldilocksCorrectness.Record.Proofs.Executions.oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost M F)
    S A x R E t₀ tH H hOld

/-- **Lemma 82 (b), the honest attestation's entry at its slot.** In an execution where every
time is reached and corruption is permanent: when the step `i` is the tick of every awake
validator at a time `t` at or after the support cutoff of slot `s₀ + 1`, and puts on the wire an
attestation `a` of the validator `v` whose tick it is, then for some slot
`s ≥ s₀`: `t` is the support cutoff of slot `s + 1`; `v` is an updater of slot `s`; `v` holds some
block `C` as its confirmation of slot `s` right after that support cutoff; and some entry block `E`,
`C` or an ancestor of `C`, has the chain-state height `a.h` and the root `a.T`.

Why: the route of Lemma 82, which puts the updater and its confirmation together as
`OnHonestChainAt`; the slot is what turns a bound on the attestation's time into a bound on the slot
of its confirmation.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `i`: the step of the tick; `t`: its time; `v`: the attester; `a`: the attestation;
- `s`: the slot whose update the attestation followed; `E`: the entry; `C`: `v`'s confirmation.

Read aloud: the entry an honest attestation names was confirmed by the attester at the slot whose
update the attestation followed, and the attestation was sent at that update's time.

 -/
theorem lem82b_entry_at_slot (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i t : ℕ) (v : V) (a : Attestation V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the step `i` is the tick at `t`, at or after the support cutoff of slot `s₀ + 1`
    (hl : x.lbl i = Event.tick v t) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ t)
    -- the step puts `v`'s attestation `a` on the wire
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ (s : ℕ) (E C : Block V), s₀ ≤ s ∧ t = M.supportCutoff S.C (s + 1) ∧
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C ∧
      E.AncestorEq C ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = a.h ∧ a.T = E.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem82b_entry_at_slot M F U) S A x R s₀ i t v a
    E hl ht₀ hSent

end GoldilocksCorrectness.Record.Statements.Executions

