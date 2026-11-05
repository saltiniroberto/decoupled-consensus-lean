module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceChainBlockDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFinality
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ChainState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Accountable
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersContest
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ReceiveDefs
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodChainBlock, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodChainBlock.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the bundle `AsyncHypsOfChainBlock`
of the asynchronous period's hypotheses over the copied certificate and attestation clauses, the
copied clauses against the originals, the attestation's source in the attester's tree, Lemma 102's
step concluding the copied certificate clause, and the finality gadget not contested or two past
`B`. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq supportCutoff_slot supportCutoff_succ_times voteTime_cast
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart
  duty_window_start_lt_supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)

open GoldilocksCorrectness.Statements.Executions (acObject fgObject)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

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

open GoldilocksCorrectness.Statements.AbstractTrace (SyncedWithinOutside)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

section Period

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `AsyncHypsOfChainBlock M S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F`: `AsyncHyps S Sched x
GST s B H t₀ anchor tAwakeEnd b₀ b₁` with the hand-over facts `HandoverFactsOfChainBlock` in place
of `HandoverFacts`.
unforgeability; fewer than a quorum ever corrupted; committee sleepiness from `anchor`, at or
before the start of slot `s + 1`; `GST` at or before `b₀`; the period's bounds; the
lock holders' majority; `t₀` at or before the hand-over cutoff; and the hand-over
facts over the copied clauses, whose last clause reads the confirmed tips from `tAwakeEnd` on
.


`AsyncHypsOfChainBlock.toAsyncHyps`, the conversion of this page, gives the
original.

The variables:
- `M`: the model.

Read aloud: the hypotheses of the asynchronous period's step lemmas over the copied certificate and
attestation clauses, bundled. -/
structure AsyncHypsOfChainBlock (GST s : ℕ) (B : Block V) (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) (Δs Δs_F : ℕ) (release : NamedObject V → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (tW : ℝ) :
    Prop where
  hSync : x.SynchronyFromWakeOutside A (Δ S) ΔRedeliver GST release acObject b₀ b₁
  /-- What an honest active validator would serve at a time `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST` when that is at or before `b₀`, and within `Δs`
  of the latest of `t`, `b₁` and `GST` otherwise (blocks and Goldfish votes). -/
  Sy : SyncedWithinOutside A x (servesMin M S.C) acObject release ΔRedeliver Δs GST b₀ b₁
  hSyncF : x.SynchronyFromWakeOutside A (Δ_F S) ΔRedeliver GST release fgObject b₀ b₁
  /-- The same for attestations, within `Δs_F`. -/
  Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST b₀ b₁
  hParent : ParentHeldAtDelivery M x
  hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t
  hSleepK : CommitteeSleepiness M S A x anchor
  hAnchor : anchor ≤ M.slotStart S.C (s + 1)
  hGST : GST ≤ b₀
  hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀
  hb : b₀ ≤ b₁
  /-- The period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`. -/
  hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)
  hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁
  ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1)
  hHand : HandoverFactsOfChainBlock M S A x tW s B H t₀ tAwakeEnd

/-- `AsyncHypsOfChainBlockUntil M S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T`:
`AsyncHypsOfChainBlock` with its two premises bounded as in `AsyncHypsUntil`: fewer than a quorum corrupted up to `T` (`hAdvQ`), and committee sleepiness from
`anchor` for every slot whose support cutoff is at most `T` (`hSleepK`). Every other field is
`AsyncHypsOfChainBlock`'s, with the same name.

`AsyncHypsOfChainBlock.toUntil` gives it at every `T`; `AsyncHypsOfChainBlockUntil.toAsyncHypsUntil`
gives `AsyncHypsUntil` when the hand-over cutoff is at most `T`.

The variables:
- `M`: the model; `T`: the time up to which the premises are read.

Read aloud: the hypotheses of the asynchronous period's step lemmas over the copied certificate and
attestation clauses, bundled, with fewer than a quorum corrupted up to `T` and committee sleepiness
for the committees counted up to `T`. -/
structure AsyncHypsOfChainBlockUntil (GST s : ℕ) (B : Block V) (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ)
    (Δs Δs_F T : ℕ) (release : NamedObject V → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (tW : ℝ) : Prop where
  hSync : x.SynchronyFromWakeOutside A (Δ S) ΔRedeliver GST release acObject b₀ b₁
  /-- What an honest active validator would serve at a time `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST` when that is at or before `b₀`, and within `Δs`
  of the latest of `t`, `b₁` and `GST` otherwise (blocks and Goldfish votes). -/
  Sy : SyncedWithinOutside A x (servesMin M S.C) acObject release ΔRedeliver Δs GST b₀ b₁
  hSyncF : x.SynchronyFromWakeOutside A (Δ_F S) ΔRedeliver GST release fgObject b₀ b₁
  /-- The same for attestations, within `Δs_F`. -/
  Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST b₀ b₁
  hParent : ParentHeldAtDelivery M x
  /-- Fewer than a quorum have been corrupted up to `T`. -/
  hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T
  /-- From `anchor` on, for every slot whose support cutoff is at most `T`, the honest active
  members of the previous slot's committee outnumber the rest. -/
  hSleepK : CommitteeSleepinessUntil M S A x anchor T
  hAnchor : anchor ≤ M.slotStart S.C (s + 1)
  hGST : GST ≤ b₀
  hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀
  hb : b₀ ≤ b₁
  /-- The period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`. -/
  hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)
  hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁
  ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1)
  hHand : HandoverFactsOfChainBlock M S A x tW s B H t₀ tAwakeEnd

end Period

end GoldilocksCorrectness.Record.Statements.Executions

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry hMax CachesCompatibleWith)
open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

section Clauses

open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans tick_attest_awake
  awakeSince_of_record_awake create_attestation_cases compatible_iff
  compatible_of_ancestorEq_compatible ancestorEq_compatible goldfish_score_eq_ok dre_bind_ok)

/-! ## The copied clauses against the originals -/

/-- The copied attestation clause gives the original: the conjunct `inHonestTreeBy M x t E` is
dropped.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `j`: the step.

Read aloud: the copied attestation clause gives the original one. -/
theorem attestationsCompatibleWithBefore_of_heldEntry {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {B : Block V} {H t₀ j : ℕ}
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ j) :
    AttestationsCompatibleWithBefore M S A x B H t₀ j := by
  intro i t v a hi hl hsent
  obtain ⟨hOld, hNew⟩ := hAtt i t v a hi hl hsent
  refine ⟨hOld, fun ht hc => ?_⟩
  obtain ⟨E, h1, h2, h3, h4, -⟩ := hNew ht hc
  exact ⟨E, h1, h2, h3, h4⟩

/-- The copied hand-over facts give the original, under unforgeability and with fewer than a
quorum corrupted up to the later of the hand-over cutoff and `t₀`: the original attestation clause
from the copied one, and the original certificate clause from it by the landed Lemma 102 step
(`certificatesCompatibleWithAt_of_attestations`), at every configuration whose time is the hand-over
cutoff.

The quorum premise is bounded at the later of the window's end `tW` and `t₀` (a helper, its callers pass
the premise they hold): the two clauses are read at every configuration whose time is in
`[M.supportCutoff S.C (s + 1), tW]`, and the step reads the quorum premise up to that configuration's time.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `H`: the height threshold; `t₀`: the time from which the attestations are new;
  `tAwakeEnd`: the time from which the confirmed tips are read.

Read aloud: the hand-over facts over the copied clauses give the original hand-over facts, under
unforgeability and with fewer than a quorum corrupted up to the later of the hand-over window's end
and `t₀`. -/
theorem handoverFacts_of_ofChainBlock {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {s : ℕ} {B : Block V} {H t₀ tAwakeEnd : ℕ}
      -- fewer than a quorum of validators have been in the adversary set up to the later of the
      -- window's end `tW` and `t₀`
      (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max tW t₀))
    (hHand : HandoverFactsOfChainBlock M S A x tW s B H t₀ tAwakeEnd) :
    HandoverFacts M S A x tW s B H t₀ tAwakeEnd := by
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := hHand
  -- the attestation and certificate clauses at every configuration of the hand-over window
  have h5' : ∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j →
      x.time j ≤ tW →
      AttestationsCompatibleWithBefore M S A x B H t₀ j :=
    fun j hj hj' => (attestationsCompatibleWithBefore_of_heldEntry M F) (h5 j hj hj')
  exact ⟨h1, h2, h3, fun j hj hj' => (certificatesCompatibleWithAt_of_attestations M F) S A x R E _
    (hAdvQ.mono (max_le_max hj' le_rfl)) (h5' j hj hj'), h5', h6, h7⟩

/-- The copied bundle gives the original: every field is kept, and the hand-over facts by
`handoverFacts_of_ofChainBlock`.

The variables:
- `M`: the model; `F`: its facts;
- `P`: the copied hypotheses.

Read aloud: the hypotheses over the copied clauses are at least the original hypotheses. -/
theorem AsyncHypsOfChainBlock.toAsyncHyps {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    (P : AsyncHypsOfChainBlock M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind tW) :
    AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind tW := by
  exact
    ⟨P.hSync, P.Sy, P.hSyncF, P.Sy_F, P.hParent, P.hAdvQ,
      P.hSleepK, P.hAnchor, P.hGST, P.hb₀, P.hb, P.hb₁, P.hHold, P.ht₀,
      (handoverFacts_of_ofChainBlock M F R E)
        ((P.hAdvQ ⌈max tW t₀⌉₊).mono (Nat.le_ceil _)) P.hHand⟩

/-- The copied bundle with its two premises for all time gives the bounded copied bundle at every
`T`: fewer than a quorum corrupted up to any time gives it up to `T`, and committee
sleepiness gives its bounded form (`committeeSleepinessUntil_of_committeeSleepiness`).

The variables:
- `M`: the model; `F`: its facts;
- `P`: the copied hypotheses; `T`: the time up to which the bounded premises are read.

Read aloud: the hypotheses over the copied clauses with the premises for all time give those with
the premises bounded at any time `T`. -/
theorem AsyncHypsOfChainBlock.toUntil {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} (P : AsyncHypsOfChainBlock M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW) (T : ℕ) :
    AsyncHypsOfChainBlockUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind tW := by
  exact
    ⟨P.hSync, P.Sy, P.hSyncF, P.Sy_F, P.hParent, P.hAdvQ T,
      committeeSleepinessUntil_of_committeeSleepiness M S A x _ T P.hSleepK, P.hAnchor, P.hGST, P.hb₀,
      P.hb, P.hb₁, P.hHold, P.ht₀, P.hHand⟩

/-- The bounded copied bundle gives the bounded original at the same `T`, when the hand-over cutoff
is at most `T`: every field of the bounded original is a field of the copied bundle.

The variables:
- `M`: the model; `F`: its facts;
- `P`: the bounded copied hypotheses; `hT`: the hand-over cutoff is at most `T`.

Read aloud: the bounded hypotheses over the copied clauses are at least the bounded original
hypotheses, once the hand-over cutoff is at most `T`. -/
theorem AsyncHypsOfChainBlockUntil.toAsyncHypsUntil {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind tW)
    (hT : M.supportCutoff S.C (s + 1) ≤ T) :
    AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind := by
  exact ⟨P.hSync, P.Sy, P.hSyncF, P.Sy_F, P.hParent, P.hAdvQ, P.hSleepK, P.hAnchor, P.hGST, P.hb₀, P.hb,
    P.hb₁, P.hHold, P.ht₀⟩

/-- `CertificatesCompatibleWithOfChainBlock` is `CertificatesCompatibleWithAtOfChainBlock` at every
step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block.

Read aloud: the copied certificate clause for ever is the copied certificate clause at every step.
-/
theorem certificatesCompatibleWithOfChainBlock_iff (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (H : ℕ) (B : Block V) :
    CertificatesCompatibleWithOfChainBlock M A x H B ↔
      ∀ j, CertificatesCompatibleWithAtOfChainBlock M A x H B j :=
  ⟨fun h j => h j, fun h j => h j⟩

/-! ## The attestation's source is in the attester's tree -/

/-- **The attestation's source is a fast block of the update its tick ran, held before the
tick.** The proof; the audited statement is in
`Statements/Executions/PeriodChainBlockStatements.lean`. The proof of
`attest_source_fast_block_updater`, with the fact `hsT` it has kept in the conclusion.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step of the tick; `t`: its
  time; `v`: the attester; `a`: the attestation.

Read aloud: nobody attests without having just run the update, and the attestation names the chain
of one of that update's fast blocks, a block the attester holds; the attester is awake through that
update. -/
theorem attest_source_fast_block_updater_inTree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i t : ℕ) (v : V) (a : Attestation V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hl : x.lbl i = Event.tick v t)
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ (s' : ℕ) (E F : Block V), t = M.supportCutoff S.C (s' + 1) ∧
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.supportCutoff S.C (s' + 1)) ∧
      F ∈ (x.tickOutput v t).fastBlocks ∧ F ∈ (x.st i v).tree ∧
      E.AncestorEq F ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = a.h ∧ a.T = E.root := by
  obtain ⟨s', source, C, hs1, hv, hF, hsT, -, -, hh, hT⟩ :=
    (attest_tick_update_source M F U) S A x R i t v a E hl hSent
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  exact ⟨s', (M.chainStateOf S.C source).T_h, source, hs1, hv, hF, hsT, hE3, hE1, hE2.trans hh, hT⟩

/-! ## The certificates, over the copied clauses -/

/-- **Lemma 102 at a step, concluding the copied certificate clause.** The proof; the audited
statement is in `Statements/Executions/PeriodChainBlockStatements.lean`. The proof of
`certificatesCompatibleWithAt_of_attestations` up to the honest signer's attestation, which names
an entry `E` compatible with `B` held by an honest validator by the attestation's time, at most
`x[j].time`; the certificate's block `T`, a block of `D`'s chain, is held by `w` at `j`
(`ancestors_mem_T_of_exec`); `E` and `T` have one root, so are one block.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `t₀`: the
  time from which the attestations are new; `B`: the protected block; `j`: the step.

Roots name blocks until `x[j].time`: the attestation's entry, held by the attestation's time, and
the certificate's block, held by `w` at step `j`, have one root.

Read aloud: a certificate is a quorum, a quorum has an honest signer, and honest signers only name
blocks compatible with `B`; so the block of a held chain a certificate is for is compatible with
`B`. -/
theorem certificatesCompatibleWithAtOfChainBlock_of_attestations (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {H t₀ : ℕ} {B : Block V} (j : ℕ)
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ j) :
    CertificatesCompatibleWithAtOfChainBlock M A x H B j := by
  intro w D T h hw hD hTD hJ hH
  obtain ⟨Q, hqA, hQ⟩ := hJ
  -- a member of the quorum outside the adversary set after every step read as a time at most the
  -- later of `x.time j` and `t₀`
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) t₀) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) t₀ ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u := fun i' hi' =>
    hhonM i' (le_trans (R.time_mono hi') (le_max_left _ _))
  have hu₀ : u ∉ A.corruptedAtTime x t₀ :=
    Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (by
      have := le_max_right (x.time j) (t₀ : ℝ); linarith)
  -- its vote of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations := by
    exact (GoldilocksCorrectness.Record.Statements.Executions.lem74_honest_attestations_recorded M F) S
      A x R E j w D a hD ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F a D).2
      ((GoldilocksCorrectness.Proofs.Routines.on_chain_iff a D).1 hon)) (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  obtain ⟨hOld, hNew⟩ := hAtt j' t' u a' hj' hl hsent
  -- the tick's step is before `j`
  have hj'j : x.time j' ≤ x.time j := R.time_mono (Nat.le_of_lt hj')
  rcases Nat.lt_or_ge t' t₀ with hlt | hge
  · -- before `t₀`, its height would be at most `H`
    have hle := hOld hlt hu₀
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · -- from `t₀` on, it names an entry compatible with `B`, held by the tick's real time
    obtain ⟨Eb, hEB, -, -, hET, i₀, v₀, hv₀, hti₀, hE₀⟩ := hNew hge
      (Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (le_trans hi (le_trans hj'j (le_max_left _ _))))
    -- the certificate's block is held by `w` at `j`
    have hTT : T ∈ (x.st j w).tree := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w D T hD hTD
    have hEq : Eb = T := hRoots Eb T ⟨i₀, v₀, hv₀, le_trans hti₀ hj'j, hE₀⟩
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw le_rfl hTT)
      (hET.symm.trans hT')
    rw [← hEq]
    exact hEB

/-! ## Not contested, or two past `B` -/

/-- **Not contested, or two past `B`, at an honest validator.** The proof; the audited statement
is in `Statements/Executions/PeriodChainBlockStatements.lean`. `not_contested_or_two_past` at `w`'s
FG state after `j` steps: its chain states are computed (Lemma 11), its caches are compatible with
`B` (`hC`), and the copied certificate clause at `j` covers every held chain.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step; `w`: the validator.

Read aloud: inside and after the period, an honest validator's finality gadget is not contested, or
its greatest chain-state height is at least two past `B`'s. -/
theorem not_contested_or_two_past_of_certificates (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {H : ℕ} {B : Block V} (j : ℕ) (w : V)
    (hw : w ∉ A.corrupted j)
    (hCert : CertificatesCompatibleWithAtOfChainBlock M A x H B j)
    (hC : CachesCompatibleWith M S B H (x.st j w)) :
    M.fg_contest (x.st j w) = false ∨
      (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.st j w) := by
  refine (GoldilocksCorrectness.Record.Proofs.Routines.not_contested_or_two_past M F) S.C S.P S.X
    (x.st j w) (lem11_node_invariant M F S A x R E j w hw).1 B H
    hC.2.1 hC.2.2.1 hC.2.2.2.1 hC.1 (fun D hD h T hTD hcert hH _ => hCert w D T h hw hD hTD ?_ hH)
  -- the record's progress certificate on `D`'s chain (some block `X ⪯ D` with a set reaching the
  -- quorum at `X`) is the copied clause's (the spec's): with fixed validators the quorum at `X` is
  -- `quorum V`, and a vote on `X`'s chain is on `D`'s chain
  obtain ⟨X, hXD, A, hA, hvA⟩ := hcert
  refine ⟨A, ?_, fun u hu => ?_⟩
  · rw [← GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X]
    exact hA
  · obtain ⟨a, h1, h2, h3, h4⟩ := hvA u hu
    refine ⟨a, h1, h2, h3, ?_⟩
    exact GoldilocksCorrectness.Proofs.Routines.on_chain_mono a hXD
      ((GoldilocksCorrectness.Proofs.Routines.on_chain_iff a X).2
        ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F a X).1 h4))

end Clauses

section Holders

open GoldilocksCorrectness.Record.Proofs.Routines
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_compatible ancestorEq_trans
  awakeSince_of_record_awake compatible_iff compatible_of_ancestorEq_compatible
  create_attestation_cases dre_bind_ok duty_window_start_le_dutyWindowStart
  duty_window_start_lt_supportCutoff goldfish_score_eq_ok one_le_Δ slotStart_eq slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq supportCutoff_slot supportCutoff_succ_times
  tick_attest_awake voteTime_cast voteTime_eq)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

/-! ## The anchor and the vote, with not contested or two past `B` -/

end Holders

end GoldilocksCorrectness.Record.Proofs.Executions

