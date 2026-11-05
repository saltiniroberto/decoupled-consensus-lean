module
public import GoldilocksCorrectness.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Proofs.Executions.Lemma83

@[expose] public section

/-!
# The attestations and the certificates after the healed round

The audited statements about the attestations honest validators send from the action time of the
healed round on, and about the certificates at heights greater than a threshold, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma82.lean` and
`GoldilocksCorrectness/Proofs/Executions/Lemma83.lean`:

- `isEntry_T_h`: the block that took a chain into its height is an entry block at that height;
- Lemma 82, `lem82_honest_attestations_on_chain`: from the action time of the healed round on,
  every honest attestation is sent at the support cutoff of slot `s + 1` for a slot `s`, and names
  the honest chain's entry block of slot `s` at its height;
- Lemma 83, `lem83_one_certificate_greater_than_threshold`: a progress certificate at a height
  greater than the threshold names the honest chain's entry block at that height, at a slot whose
  support cutoff of the next slot is at most the time of the step at which the certificate is
  read, and its corollary for a justification certificate,
  `lem83_one_justification_greater_than_threshold`.
- the kit fact `oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost`: the bound on the old
  attestations with the senders honest at the send gives the bound in the honest-at form that
  Lemma 83 reads.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Framework.StsMultisetLog (AtomicAction SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **Kit fact, the block that took a chain into its height is an entry block.** For every block
`D`, the block `(chainStateOf C D).T_h` is an entry block, has `D`'s chain-state height, and is
`D` or an ancestor of `D`.

Why: the last two are the specification of `T_h` along a chain; two blocks of one chain at one
height have one `T_h` (Lemma 47 (e)), so the `T_h` of `T_h` is itself.

The variables:
- `C`: the parameters; `D`: the block.

Read aloud: the block that took `D`'s chain into its height is an entry block, has `D`'s height,
and is `D` or an ancestor of `D`.

 -/
theorem isEntry_T_h (C : Config) (D : Block V) :
    IsEntry C (chainStateOf C D).T_h ∧
      (chainStateOf C (chainStateOf C D).T_h).h = (chainStateOf C D).h ∧
      (chainStateOf C D).T_h.AncestorEq D :=
  GoldilocksCorrectness.Proofs.Routines.isEntry_T_h C D

/-- **Lemma 82, the honest attestations after the healed round name the honest chain's
entries.** In an execution where every time is reached and corruption is permanent, every
attestation an honest awake validator puts on the wire at a tick at or after the support cutoff of
slot `s₀ + 1` is sent at the support cutoff of slot `s + 1` for some slot `s ≥ s₀`, and names, by
its root, an entry block of the honest chain from slot `s₀` at slot `s`
(`OnHonestChainAt S Sched x s₀ s E`) whose chain-state height is the attestation's height.

Why: the attestation was built at the action time of a round, the support cutoff of slot `s + 1`
with `s` the round's first slot and `s₀ ≤ s`, from the height and the `T_h` of the duty's source;
the tick passed the duty test, so it ran the confirmation update of slot `s + 1`, whose fast blocks
hold the source; that update saved a confirmation for slot `s`, the source being that block or an
ancestor of it; the validator was awake through the update's window, so it is an updater of slot
`s`; the source's `T_h` is the entry block (`isEntry_T_h`). This is Lemma 82 (b),
`lem82b_entry_at_slot`, with the updater and its confirmation put together.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot.

Read aloud: from the action time of the healed round on, every attestation an honest awake
validator sends is sent at the update time of a slot `s`, and names the honest chain's entry block
of slot `s` at the attestation's height.

 -/
theorem lem82_honest_attestations_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) :
    HonestAttestationsOnChain S Sched x s₀ (supportCutoff S (s₀ + 1)) :=
  GoldilocksCorrectness.Proofs.Executions.lem82_honest_attestations_on_chain S Sched x s₀ hDiv
    hMono

/-- **Lemma 83, one progress certificate per height greater than the threshold.** Under
unforgeability, take a block `B` that `w` holds after `j` steps, and a progress certificate on the
chain of `B` at a height `h` greater than `H` naming `T`'s root; when fewer than a quorum of
validators have been in the adversary set up to the time after `j` steps, every attestation an
honest awake validator sends at or after `t₀` names the honest chain's entry block at its height,
and every one a validator honest at the time after `j` steps sent before `t₀` has height at most
`H`, then for some slot `s_a` whose support cutoff
of slot `s_a + 1` is at most the time after `j` steps, `T`'s root is the root of an entry block of
the honest chain from slot `s₀` at slot `s_a` at the height `h`.

Why: some member `u` of the certificate's quorum was never in the adversary set up to that time;
`u`'s vote is in `u`'s record (Lemma 74), so `u`'s tick sent an attestation with its content,
awake and honest then, at a tick before the step `j`; `u` is honest at the time after `j` steps, so
at the height `h > H` it was not sent before `t₀`, and it names the entry of the slot `s_a` whose
support cutoff of slot `s_a + 1` is its time of sending.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the bound on the heights of the
  earlier ones;
- `j`: the step; `w`: the holder; `B`: the held block; `T`: the block whose root the certificate
  names; `h`: the certificate's height; `s_a`: the slot of the entry `E`.

Read aloud: a progress certificate at a height greater than `H`, on the chain of a held block,
names by root the honest chain's entry block at that height, at a slot whose update ran by the
time after `j` steps.

 -/
theorem lem83_one_certificate_greater_than_threshold (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators have been in the adversary set up to the time after `j`
    -- steps
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    -- every honest attestation sent at or after `t₀` is sent at the support cutoff of slot `s + 1`
    -- for a slot `s`, and names the honest chain's entry of slot `s` at its height
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    -- every attestation sent before `t₀` by a validator honest after `j` steps has height at most
    -- `H`
    (hOld : OldAttestationsAtMostHonestAt S Sched x t₀ x[j].time H)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x[j][w].st).S.T)
    -- a quorum of votes at `h` naming `T`'s root is included on the chain of `B`
    (hJ : ProgressCertOn B h T)
    -- the height is greater than `H`
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), supportCutoff S (s_a + 1) ≤ x[j].time ∧
      OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = h ∧ T.root = E.root :=
  GoldilocksCorrectness.Proofs.Executions.lem83_one_certificate_greater_than_threshold S Sched x
    s₀ t₀ H j w B T h hU hAdvQ hAgree hOld hB hJ hH

/-- **Lemma 83, one justification per height greater than the threshold.** Under
unforgeability, take a block `B` that `w` holds after `j`
steps, and a justification certificate on the chain of `B` at a height `h` greater than `H` for
`T`'s root; when fewer than a quorum of validators have been in the adversary set up to the time
after `j` steps, every attestation an honest awake validator sends at or after `t₀` names the
honest chain's entry block at its height, and every one a validator honest at the time after `j`
steps sent before `t₀` has height at most `H`, then
for some slot `s_a` whose support cutoff of slot `s_a + 1` is at most the time after `j` steps,
`T`'s root is the root of an entry block of the honest chain from slot `s₀` at slot `s_a` at the
height `h`.

Why: a justification certificate is a progress certificate (its target votes are votes at `h`
naming `T`'s root).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the bound on the heights of the
  earlier ones;
- `j`: the step; `w`: the holder; `B`: the held block; `T`: the justified block; `h`: the
  certificate's height; `s_a`: the slot of the entry `E`.

Read aloud: a justification certificate at a height greater than `H`, on the chain of a held
block, names by root the honest chain's entry block at that height, at a slot whose update ran by
the time after `j` steps.

 -/
theorem lem83_one_justification_greater_than_threshold (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators have been in the adversary set up to the time after `j`
    -- steps
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    -- every honest attestation sent at or after `t₀` is sent at the support cutoff of slot `s + 1`
    -- for a slot `s`, and names the honest chain's entry of slot `s` at its height
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    -- every attestation sent before `t₀` by a validator honest after `j` steps has height at most
    -- `H`
    (hOld : OldAttestationsAtMostHonestAt S Sched x t₀ x[j].time H)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x[j][w].st).S.T)
    -- a quorum of target votes at `h` for `T`'s root is included on the chain of `B`
    (hJ : JustificationCertOn B h T)
    -- the height is greater than `H`
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), supportCutoff S (s_a + 1) ≤ x[j].time ∧
      OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = h ∧ T.root = E.root :=
  GoldilocksCorrectness.Proofs.Executions.lem83_one_justification_greater_than_threshold S Sched
    x s₀ t₀ H j w B T h hU hAdvQ hAgree hOld hB hJ hH

/-- **Kit fact, the bound on the old attestations in the honest-at form.** When every attestation
an honest awake validator put on the wire at a tick before `t₀` has height at most `H`, then for
every time `tH`, every attestation a validator honest at `tH` put on the wire at a tick before `t₀`
has height at most `H`.

Why: what a tick puts on the wire is signed by a validator awake and outside the adversary set at
the tick, so the sender was honest at the send.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `tH`: the time at which the senders' honesty is read; `H`: the bound.

Read aloud: a bound on the attestations of the validators honest at the send bounds those of the
validators honest at any later or earlier time.

 -/
theorem oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ tH H : ℕ)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x t₀ H) :
    OldAttestationsAtMostHonestAt S Sched x t₀ tH H :=
  GoldilocksCorrectness.Proofs.Executions.oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost S
    Sched x t₀ tH H hOld

/-- **Lemma 82 (b), the honest attestation's entry at its slot.** In an execution where every
time is reached and corruption is permanent: when the step `i` is the tick of every awake
validator at a time `t` at or after the support cutoff of slot `s₀ + 1`, and puts on the wire an
attestation `a` of a validator `v` awake and outside the adversary set at `t`, then for some slot
`s ≥ s₀`: `t` is the support cutoff of slot `s + 1`; `v` is an updater of slot `s`; `v` holds some
block `C` as its confirmation of slot `s` right after that support cutoff; and some entry block `E`,
`C` or an ancestor of `C`, has the chain-state height `a.h` and the root `a.T`.

Why: the route of Lemma 82, which puts the updater and its confirmation together as
`OnHonestChainAt`; the slot is what turns a bound on the attestation's time into a bound on the slot
of its confirmation.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `i`: the step of the tick; `t`: its time; `v`: the attester; `a`: the attestation;
- `s`: the slot whose update the attestation followed; `E`: the entry; `C`: `v`'s confirmation.

Read aloud: the entry an honest attestation names was confirmed by the attester at the slot whose
update the attestation followed, and the attestation was sent at that update's time.

 -/
theorem lem82b_entry_at_slot (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i t : ℕ) (v : V) (a : Attestation V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    -- the step `i` is the tick at `t`, at or after the support cutoff of slot `s₀ + 1`
    (hl : x.lbl i = AtomicAction.tickAllAwake t) (ht₀ : supportCutoff S (s₀ + 1) ≤ t)
    -- `v` is awake and outside the adversary set at `t`
    (hAwake : v ∈ Sched.awake (t : Int)) (hHon : v ∉ Sched.adv (t : Int))
    -- the step puts `v`'s attestation `a` on the wire
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    ∃ (s : ℕ) (E C : Block V), s₀ ≤ s ∧ t = supportCutoff S (s + 1) ∧ v ∈ updaterAt S Sched s ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C ∧
      E.AncestorEq C ∧ IsEntry S.C E ∧ (chainStateOf S.C E).h = a.h ∧ a.T = E.root :=
  GoldilocksCorrectness.Proofs.Executions.lem82b_entry_at_slot S Sched x s₀ i t v a hDiv hMono hl
    ht₀ hAwake hHon hSent

end GoldilocksCorrectness.Statements.Executions
