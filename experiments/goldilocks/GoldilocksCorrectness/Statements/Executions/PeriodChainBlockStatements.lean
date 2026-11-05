module
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceChainBlockDefs
public import GoldilocksCorrectness.Statements.Routines.ReceiveStatements

@[expose] public section

/-! Every landed definition and statement of record stays byte-identical; Proved in `GoldilocksCorrectness/Proofs/Executions/PeriodChainBlock.lean`.

- `AsyncHypsOfChainBlock.toAsyncHyps`: the copied bundle gives `AsyncHyps`;
- `certificatesCompatibleWithOfChainBlock_iff`: the copied certificate clause at every step;
- `attest_source_fast_block_updater_inTree`: the copy of `attest_source_fast_block_updater`, the
  fast block also in the attester's tree before the tick;
- `certificatesCompatibleWithAtOfChainBlock_of_attestations`: the copy of
  `certificatesCompatibleWithAt_of_attestations` (Lemma 102's step) concluding the copied
  certificate clause;

- `anchor_extends_B_of_inv_orTwoPast`: the copy of `anchor_extends_B_of_inv` with "not contested"
  weakened to "not contested, or `h_max` at least `h(B) + 2`".

 Deleted then:
`attestations_step_ofHeldEntry` and `holder_vote_extends_B_orTwoPast`, the originals of the later
copies `attestations_step_ofHeldEntry_ofCompat` and `holder_vote_extends_B_orTwoPast_ofCompat`
(`Statements/Executions/PeriodCompatCopiesStatements.lean`).

Each copy's docstring lists the callers of its original and where its changed hypothesis comes
from there (the away rule's call-site list).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The copied bundle and the copied certificate clause -/

/-- **The copied bundle gives the original.** Every field of `AsyncHypsOfChainBlock` is a field
of `AsyncHyps`, except the hand-over facts, and `HandoverFactsOfChainBlock` gives `HandoverFacts`
under unforgeability and with fewer than a quorum ever corrupted: the original attestation clause
drops the conjunct `inHonestTreeBy x t E`, and the original certificate clause follows from it by
the landed Lemma 102 step (`certificatesCompatibleWithAt_of_attestations`).



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `s`, `B`, `H`, `t₀`,
  `anchor`, `b₀`, `b₁`: the parameters of `AsyncHyps`; `P`: the copied hypotheses.

Read aloud: the hypotheses over the copied clauses are at least the original hypotheses. -/
theorem AsyncHypsOfChainBlock.toAsyncHyps {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlock S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ :=
  GoldilocksCorrectness.Proofs.Executions.AsyncHypsOfChainBlock.toAsyncHyps P

section Period

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `CertificatesCompatibleWithOfChainBlock` is `CertificatesCompatibleWithAtOfChainBlock` at every
step. The copy of `certificatesCompatibleWith_iff`
(`Statements/Executions/AsyncDeliveryStatements.lean:199`) for the copied definitions.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block.

Read aloud: the copied certificate clause for ever is the copied certificate clause at every
step. -/
theorem certificatesCompatibleWithOfChainBlock_iff (H : ℕ) (B : Block V) :
    CertificatesCompatibleWithOfChainBlock S Sched x H B ↔
      ∀ j, CertificatesCompatibleWithAtOfChainBlock S Sched x H B j :=
  GoldilocksCorrectness.Proofs.Executions.certificatesCompatibleWithOfChainBlock_iff S Sched x H B

/-! ## The attestation's source, in the attester's tree -/

/-- **The attestation's source is a fast block of the update its tick ran, held before the
tick.** In an execution that reaches every time, with permanent corruption: when step `i` is the
tick at `t`, and `v`, awake and honest at `t`, put the attestation `a` on the wire at that step,
then `t` is the support cutoff of some slot `s' + 1`, `v` is in `updaterAt S Sched s'`, and some
entry block `E`, an ancestor of a fast block `F` of `v`'s state right after `t` or `F` itself, has
the chain-state height `a.h` and the root `a.T`; and `F` is in `v`'s tree after `i` steps.

Why: the proof of `attest_source_fast_block_updater`; the attestation's source is the deepest
fast block of the update in the viable tree of `v`'s frame, whose tree is part of `v`'s tree
before the tick (`ac_to_fg_source_mem`, `mem_fg_to_ac_tree`).

Rendering note. No hypothesis changes. Callers of
the original: `attestations_step` (`Proofs/Executions/PeriodFinality.lean:440`) and the
statement wrapper; the copy's caller is `attestations_step_ofHeldEntry`, which reads the new
conjunct for the copied attestation clause. Read aloud: the fast block the attestation is built
from is a block the attester holds when it attests.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step of the tick; `t`: its
  time; `v`: the attester; `a`: the attestation;
- `hDiv`: the execution reaches every time; `hMono`: corruption is permanent; `hl`: step `i` is
  the tick at `t`; `hAwake`, `hHon`: `v` is awake and honest at `t`; `hSent`: `v` put `a` on the
  wire at step `i`.

Read aloud: nobody attests without having just run the update, and the attestation names the
chain of one of that update's fast blocks, a block the attester holds; the attester is awake
through that update. -/
theorem attest_source_fast_block_updater_inTree (i t : ℕ) (v : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    (hAwake : v ∈ Sched.awake (t : Int)) (hHon : v ∉ Sched.adv (t : Int))
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    ∃ (s' : ℕ) (E F : Block V), t = supportCutoff S (s' + 1) ∧ v ∈ updaterAt S Sched s' ∧
      F ∈ (stateBefore x (t + 1) v).A.fast_blocks ∧ F ∈ (x[i][v].st).S.T ∧
      E.AncestorEq F ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = a.h ∧ a.T = E.root :=
  GoldilocksCorrectness.Proofs.Executions.attest_source_fast_block_updater_inTree S Sched x i t v a
    hDiv hMono hl hAwake hHon hSent

/-! ## The certificates, over the copied clauses -/

/-- **Lemma 102 at a step, concluding the copied certificate clause.** Under unforgeability, with
roots naming blocks among what honest validators hold up to `x[j].time`, with fewer than a quorum
ever corrupted up to that time: when every honest attestation sent at a step before `j` is old
(height at most `H`) or names an entry compatible with `B` held by an honest validator by its
time, then every progress certificate at a height greater than `H` on the chain of a block `D` a
validator honest at `j` holds, for a block `T` of `D`'s chain, has `T` compatible with `B`.

Why: Lemma 83's route: some signer of the quorum was never corrupted up to `x[j].time`; its
attestation is in its record (Lemma 74), so its tick sent it at a step before `j`, at a height
greater than `H`, hence not old: it names an entry `E` compatible with `B`, held by the time of
that tick. `T` is held by the certificate's holder at `j`; `E` and `T` have one root, both held by
`x[j].time`, so they are one block.

Rendering note. Callers of the original: its statement wrapper (`PeriodFinalityStatements.lean:198`) and
`handoverFacts_of_ofChainBlock` (`Proofs/Executions/PeriodChainBlock.lean`), which keep the
original. Read aloud: the certificate's
own block is the block the honest signer's attestation named.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `t₀`: the
  time from which the attestations are new; `B`: the protected block; `j`: the step;
- `hU`: unforgeability; `hRoots`: roots name blocks among what honest validators hold up to
  `x[j].time`; `hAdvQ`: fewer than a quorum have been corrupted up to `x[j].time`; `hAtt`: the
  attestations sent before step `j` are old, or compatible with `B` and held.

Roots name blocks until `x[j].time`: the attestation's entry and the certificate's block.

Read aloud: a certificate is a quorum, a quorum has an honest signer, and honest signers only
name blocks compatible with `B`; so the block of a held chain a certificate is for is compatible
with `B`. -/
theorem certificatesCompatibleWithAtOfChainBlock_of_attestations {H t₀ : ℕ} {B : Block V} (j : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ j) :
    CertificatesCompatibleWithAtOfChainBlock S Sched x H B j :=
  GoldilocksCorrectness.Proofs.Executions.certificatesCompatibleWithAtOfChainBlock_of_attestations
    S Sched x j hU hRoots hAdvQ hAtt

/-! ## Not contested, or two past `B` -/

/-- **The finality gadget of an honest validator is not contested, or its greatest chain-state
height is at least `B`'s plus two.** When `w` is honest at step `j`, the copied certificate clause
holds at `j`, and `w`'s caches are compatible with `B` (`J` compatible with `B`, an entry at the
height `h_j > H`, `F` an ancestor of `J`), then `fg_contest` answers `false` at `w`'s FG state, or
its `h_max` is at least `(chainStateOf S.C B).h + 2`.

Why: contested means `h_max = h_j + 1` and a held block `D` at height `h_max` of which `J` is not
an ancestor. When `h_j ≥ h(B) + 1`, `h_max ≥ h(B) + 2`. Otherwise `h_j ≤ h(B)`: `D`'s chain passed
height `h_j`, so (Lemma 67) it holds a progress certificate at `h_j` for its own entry `T'` at
`h_j`, an ancestor of `D`; the certificate clause makes `T'` compatible with `B`; `T'` and `J` are
two entries compatible with `B` at one height at most `h(B)`, so one block, and `J = T'` is an
ancestor of `D`: not contested.

Rendering note. never landed, so no original page exists). The conclusion is the disjunction in place
of `fg_contest … = false`; the certificate clause is the copied one. The probe's `hU`, `hRoots`
and `hAdvQ` are not read and are not taken. No caller of the probe's statement exists; Read aloud: a contest inside and after the period
is only between two descendants of `B`, and then the top height is two past `B`'s.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step; `w`: the validator;
- `hw`: `w` is honest at step `j`; `hCert`: the copied certificate clause at `j`; `hC`: `w`'s
  caches at `j` are compatible with `B`.

Read aloud: inside and after the period, an honest validator's finality gadget is not contested,
or its greatest chain-state height is at least two past `B`'s. -/
theorem not_contested_or_two_past_of_certificates {H : ℕ} {B : Block V} (j : ℕ) (w : V)
    (hw : w ∉ Sched.adv (x[j].time : Int))
    (hCert : CertificatesCompatibleWithAtOfChainBlock S Sched x H B j)
    (hC : CachesCompatibleWith S B H (x[j][w].st)) :
    fg_contest (x[j][w].st).S = false ∨
      (chainStateOf S.C B).h + 2 ≤ (x[j][w].st).S.h_max :=
  GoldilocksCorrectness.Proofs.Executions.not_contested_or_two_past_of_certificates S Sched x j w
    hw hCert hC

end Period

/-! ## The anchor and the vote, with not contested or two past `B` -/

section Holders

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end Holders

end GoldilocksCorrectness.Statements.Executions
