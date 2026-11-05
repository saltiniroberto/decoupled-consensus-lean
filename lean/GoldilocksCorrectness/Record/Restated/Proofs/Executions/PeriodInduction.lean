module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PeriodChainBlockStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PeriodInductionDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodInduction, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodInduction.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the bundle
`AsyncHypsOfChainBlockGSTBeforeVotes` of the asynchronous period's hypotheses with `GST` at or
before the vote time of slot `s + 1`, its two conversions, and the voters of a slot whose votes are
on `B`'s chain, with their majority of the committee. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono slotStart_mono supportCutoff_eq
  voteTime_mono')

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

/-- `AsyncHypsOfChainBlockGSTBeforeVotes M S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F`:
`AsyncHypsOfChainBlock M S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F` with `GST` at or before the
vote time of slot `s + 1`, the first votes after the hand-over proposal, in place of `GST` at or
before `b₀`.


With `GST = b₀` after the support cutoff of slot `s + 1`, the slot-`(s + 1)` honest votes are due
only after the view freeze of `s + 1`, so a voter of slot `s + 2` outside the lock holders may be
shown only the adversary's votes and vote off `B`'s chain while every other hypothesis of the
timely-view statement holds. The old field follows from the new one
(`M.voteTime S.C (s + 1) < M.supportCutoff S.C (s + 1) ≤ b₀`): `toAsyncHypsOfChainBlock` and
`toAsyncHyps` give the landed bundles, so every landed step lemma is called through them. Lemma 105 builds it from its
spelled-out hypotheses with `GST ≤ M.voteTime S.C (s + 1)` in place of `GST ≤ b₀`, and the top
statement derives that from `GST ≤ tGAT`, the honest round opening slots and
`tAwakeEnd < M.slotStart S.C s` (`gst_le_voteTime_succ_of_top`,
`scratch/goldilocks_async/probe_ar4_replan.lean`). No top-level claim changes.

 the four restated asynchrony top statements take it as their
hypothesis `hDelT`. The conversions `toAsyncHypsOfChainBlock`, `toAsyncHyps` do not read it.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the hypotheses with `GST` before the hand-over votes are at least the hypotheses with
`GST` before the period. -/
structure AsyncHypsOfChainBlockGSTBeforeVotes (GST s : ℕ) (B : Block V)
    (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) (Δs Δs_F : ℕ) (release : NamedObject V → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) (tW : ℝ) : Prop where
  /-- Blocks and Goldfish votes are delivered as in the synchronous network outside `[b₀, b₁)`, within
  the network delay `ΔNet`. -/
  hSync : x.SynchronyFromWakeOutside A ΔNet ΔRedeliver GST release acObject b₀ b₁
  /-- What an honest active validator would serve at a time `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST` when that is at or before `b₀`, and within `Δs`
  of the latest of `t`, `b₁` and `GST` otherwise (blocks and Goldfish votes). -/
  Sy : SyncedWithinOutside A x (servesMin M S.C) acObject release ΔRedeliver Δs GST b₀ b₁
  /-- Attestations are delivered as in the synchronous network outside `[b₀, b₁)`. -/
  hSyncF : x.SynchronyFromWakeOutside A (Δ_F S) ΔRedeliver GST release fgObject b₀ b₁
  /-- The same for attestations, within `Δs_F`. -/
  Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST b₀ b₁
  /-- A block reaches a validator only once the validator holds its parent. -/
  hParent : ParentHeldAtDelivery M x
  /-- Fewer than a quorum have been corrupted up to any time. -/
  hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t
  /-- From `anchor` on, the honest active members of each committee outnumber the rest. -/
  hSleepK : CommitteeSleepiness M S A x anchor
  /-- `anchor` is at or before the start of slot `s + 1`. -/
  hAnchor : anchor ≤ M.slotStart S.C (s + 1)
  /-- The network has recovered by the hand-over cutoff: `GST` is one delay or one sync delay,
  whichever is longer, before the support cutoff of slot `s + 1`. -/
  hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1)
  /-- The period starts at or after the hand-over update. -/
  hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀
  /-- The period is an interval. -/
  hb : b₀ ≤ b₁
  /-- The period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`. -/
  hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)
  /-- Wherever the previous votes are owed inside the period, the lock holders outweigh the
  rest of the committee. -/
  hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁
  /-- `t₀` is at or before the hand-over cutoff. -/
  ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1)
  /-- The hand-over facts, over the copied certificate and attestation clauses. -/
  hHand : HandoverFactsOfChainBlock M S A x tW s B H t₀ tAwakeEnd
  /-- A certified entry an honest validator held at a step whose time is at most the start of a
  voter's duty window reaches the voter by its view freeze. -/
  hDelT : DelTLine M S A x s B b₀ b₁ Δs

/-- `AsyncHypsOfChainBlockGSTBeforeVotesUntil M S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T`:
`AsyncHypsOfChainBlockGSTBeforeVotes` with its two premises bounded as in `AsyncHypsUntil`
: fewer than a quorum corrupted up to `T` (`hAdvQ`), and
committee sleepiness from `anchor` for every slot whose support cutoff is at most `T`
(`hSleepK`). Every other field is
`AsyncHypsOfChainBlockGSTBeforeVotes`'s, with the same name.

`AsyncHypsOfChainBlockGSTBeforeVotes.toUntil` gives it at every `T`, so the three corollaries over
the bundle for all time (`after_period_compat`, `certificates_compatible_with_ofChainBlock`,
`blocks_two_past_descend`) are proved through it; `confirmedPersists_throughPeriod_until` builds it
at its `t` from its bounded premises. `toAsyncHypsOfChainBlockUntil` and `toAsyncHypsUntil` give
the bounded forms of the landed bundles.

The variables:
- `M`: the model; `T`: the time up to which the premises are read.

Read aloud: the hypotheses with `GST` before the hand-over votes, with fewer than a quorum corrupted
up to `T` and committee sleepiness for the committees counted up to `T`. -/
structure AsyncHypsOfChainBlockGSTBeforeVotesUntil (GST s : ℕ) (B : Block V)
    (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) (Δs Δs_F T : ℕ) (release : NamedObject V → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) (tW : ℝ) : Prop where
  /-- Blocks and Goldfish votes are delivered as in the synchronous network outside `[b₀, b₁)`, within
  the network delay `ΔNet`. -/
  hSync : x.SynchronyFromWakeOutside A ΔNet ΔRedeliver GST release acObject b₀ b₁
  /-- What an honest active validator would serve at a time `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST` when that is at or before `b₀`, and within `Δs`
  of the latest of `t`, `b₁` and `GST` otherwise (blocks and Goldfish votes). -/
  Sy : SyncedWithinOutside A x (servesMin M S.C) acObject release ΔRedeliver Δs GST b₀ b₁
  /-- Attestations are delivered as in the synchronous network outside `[b₀, b₁)`. -/
  hSyncF : x.SynchronyFromWakeOutside A (Δ_F S) ΔRedeliver GST release fgObject b₀ b₁
  /-- The same for attestations, within `Δs_F`. -/
  Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST b₀ b₁
  /-- A block reaches a validator only once the validator holds its parent. -/
  hParent : ParentHeldAtDelivery M x
  /-- Fewer than a quorum have been corrupted up to `T`. -/
  hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T
  /-- From `anchor` on, for every slot whose support cutoff is at most `T`, the honest active
  members of the previous slot's committee outnumber the rest. -/
  hSleepK : CommitteeSleepinessUntil M S A x anchor T
  /-- `anchor` is at or before the start of slot `s + 1`. -/
  hAnchor : anchor ≤ M.slotStart S.C (s + 1)
  /-- The network has recovered by the hand-over cutoff: `GST` is one delay or one sync delay,
  whichever is longer, before the support cutoff of slot `s + 1`. -/
  hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1)
  /-- The period starts at or after the hand-over update. -/
  hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀
  /-- The period is an interval. -/
  hb : b₀ ≤ b₁
  /-- The period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`. -/
  hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)
  /-- Wherever the previous votes are owed inside the period, the lock holders outweigh the
  rest of the committee. -/
  hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁
  /-- `t₀` is at or before the hand-over cutoff. -/
  ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1)
  /-- The hand-over facts, over the copied certificate and attestation clauses. -/
  hHand : HandoverFactsOfChainBlock M S A x tW s B H t₀ tAwakeEnd
  /-- A certified entry an honest validator held at a step whose time is at most the start of a
  voter's duty window reaches the voter by its view freeze. -/
  hDelT : DelTLine M S A x s B b₀ b₁ Δs

end Period

end GoldilocksCorrectness.Record.Statements.Executions

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The bundle's conversions -/

/-- The copied bundle gives `AsyncHypsOfChainBlock` when the network delay is at most the slot delay:
`GST ≤ b₀` from `GST ≤ M.voteTime S.C (s + 1)`, `M.voteTime S.C (s + 1) < M.supportCutoff S.C (s + 1)`
and `M.supportCutoff S.C (s + 1) ≤ b₀`.

The delivery promise of the bundle is at the network delay `ΔNet`; the target's is at the slot
delay, a deadline no earlier when `ΔNet ≤ Δ S` (`deadlineOutsideR_mono_delay`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the copied hypotheses; `hΔn`: the network delay is at most the slot delay.

Read aloud: the hypotheses with `GST` before the hand-over votes are at least the hypotheses with
`GST` before the period. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock
    (U : UniformSchedule M.toSlotLayout)
    {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (hΔn : ΔNet ≤ Δ S) :
    AsyncHypsOfChainBlock M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW :=
  -- the delivery promise at the network delay gives it at the slot delay (a deadline no earlier)
  ⟨fun i k v sm t hs hok hk hik hact hdl hre =>
      P.hSync i k v sm t hs hok hk hik hact
        (le_trans (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_mono_delay hΔn) hdl) hre,
    P.Sy, P.hSyncF, P.Sy_F, P.hParent, P.hAdvQ, P.hSleepK, P.hAnchor,
    by have := P.hGST; have := P.hb₀; omega,
    P.hb₀, P.hb, P.hb₁, P.hHold, P.ht₀, P.hHand⟩

/-- The copied bundle gives `AsyncHyps`, through `AsyncHypsOfChainBlock`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the copied hypotheses.

Read aloud: the hypotheses with `GST` before the hand-over votes are at least the original
hypotheses. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHyps (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW) :
    AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind tW :=
  (GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlock.toAsyncHyps M F R E)
    hNet hSkew hRedeliver ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock M F U) P
      (by have h1 := E.ahead_nonneg; have h2 := E.behind_nonneg
          have : (ΔNet : ℝ) ≤ Δ S := by linarith
          exact_mod_cast this))

/-! ## The bounded bundle's conversions -/

/-- The bundle with its two premises for all time gives the bounded bundle at every `T`
: fewer than a quorum corrupted up to any time gives it up to `T`, and committee
sleepiness gives its bounded form (`committeeSleepinessUntil_of_committeeSleepiness`).

The variables:
- `M`: the model; `F`: its facts;
- `P`: the hypotheses; `T`: the time up to which the bounded premises are read.

Read aloud: the hypotheses with `GST` before the hand-over votes and the premises for all time give
those with the premises bounded at any time `T`. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toUntil {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (T : ℕ) :
    AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW :=
  ⟨P.hSync, P.Sy, P.hSyncF, P.Sy_F, P.hParent, P.hAdvQ T,
    committeeSleepinessUntil_of_committeeSleepiness M S A x anchor _ P.hSleepK, P.hAnchor, P.hGST,
    P.hb₀, P.hb, P.hb₁, P.hHold, P.ht₀, P.hHand, P.hDelT⟩

/-- The bounded bundle gives the bounded `AsyncHypsOfChainBlockUntil` at the same `T`: `GST ≤ b₀`
from `GST ≤ M.voteTime S.C (s + 1)`, as `toAsyncHypsOfChainBlock`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the bounded hypotheses.

The delivery promise of the bounded bundle is at the network delay `ΔNet`; the target's is at the slot
delay, a deadline no earlier when `ΔNet ≤ Δ S` (`deadlineOutsideR_mono_delay`).

Read aloud: the bounded hypotheses with `GST` before the hand-over votes are at least the bounded
hypotheses with `GST` before the period. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotesUntil.toAsyncHypsOfChainBlockUntil
    (U : UniformSchedule M.toSlotLayout)
    {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (hΔn : ΔNet ≤ Δ S) :
    AsyncHypsOfChainBlockUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind tW :=
  -- the delivery promise at the network delay gives it at the slot delay (a deadline no earlier)
  ⟨fun i k v sm t hs hok hk hik hact hdl hre =>
      P.hSync i k v sm t hs hok hk hik hact
        (le_trans (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_mono_delay hΔn) hdl) hre,
    P.Sy, P.hSyncF, P.Sy_F, P.hParent, P.hAdvQ, P.hSleepK, P.hAnchor,
    by have := P.hGST; have := P.hb₀; omega,
    P.hb₀, P.hb, P.hb₁, P.hHold, P.ht₀, P.hHand⟩

/-- The bounded bundle gives the bounded `AsyncHypsUntil` at the same `T`, through
`AsyncHypsOfChainBlockUntil`, when the hand-over cutoff is at most `T`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the bounded hypotheses; `hT`: the hand-over cutoff is at most `T`.

Read aloud: the bounded hypotheses with `GST` before the hand-over votes are at least the bounded
original hypotheses, once the hand-over cutoff is at most `T`. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotesUntil.toAsyncHypsUntil (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (hT : M.supportCutoff S.C (s + 1) ≤ T) :
    AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind :=
  (GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockUntil.toAsyncHypsUntil M F R E)
    hNet hSkew hRedeliver ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotesUntil.toAsyncHypsOfChainBlockUntil M F U) P
      (by have h1 := E.ahead_nonneg; have h2 := E.behind_nonneg
          have : (ΔNet : ℝ) ≤ Δ S := by linarith
          exact_mod_cast this)) hT
/-! ## The voters of a slot on `B`'s chain -/

/-- The members of a set `Q` of honest active committee members of slot `σ`, each of whose slot-`σ`
votes is for a block it holds on `B`'s chain, have such a vote: a block `H u` for each, `u`'s
slot-`σ` vote for `H u` is on the wire at its tick at the vote time of `σ`, `u` holds `H u` then,
`H u` is `B` or a descendant of `B`, and `u` is a committee member honest at the support cutoff of
slot `σ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot; `Q`: the voters;
  `B`: the block.

Read aloud: every honest active committee member of slot `σ` whose slot-`σ` votes are on `B`'s chain
has such a vote, for a block it holds that is `B` or a descendant of `B`. -/
theorem exists_votes_on_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (σ : ℕ) (Q : Finset V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hQ : Q ⊆ honestActiveAt M S A x σ ∩ S.P.committee σ)
    (hExt : ∀ u ∈ Q, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
        vote = GoldfishVote.mk u σ H_u.root ∧ B.AncestorEq H_u) :
    ∃ H : V → Block V, ∀ u ∈ Q, u ∈ S.P.committee σ ∧
      u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C σ)).tree ∧ B.AncestorEq (H u) := by
  classical
  have key : ∀ u ∈ Q, ∃ Hu : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ Hu.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      Hu ∈ (x.tickInput u (M.voteTime S.C σ)).tree ∧ B.AncestorEq Hu := by
    intro u hu
    obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.honest_active_votes M F U) S A x R σ u E hSkew hA hK
    obtain ⟨Hu, hHuT, hveq, hBH⟩ := hExt u hu vote ⟨i, hl, hsent⟩
    exact ⟨Hu, ⟨i, hl, hveq ▸ hsent⟩, hHuT, hBH⟩
  refine ⟨fun u => if h : u ∈ Q then Classical.choose (key u h) else B, fun u hu => ?_⟩
  obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
  have hspec := Classical.choose_spec (key u hu)
  simp only [dif_pos hu]
  exact ⟨hK, fun h => (Finset.mem_sdiff.1 hA).2 (Finset.mem_union_left _ h), hspec⟩

/-- The voters of slot `s'` whose votes `VotesExtendAt` puts on `B`'s chain outweigh the rest of the
committee: the lock holders' members of the committee when the previous votes were owed inside the
period (`P.hHold`), and the honest active members otherwise (`P.hSleepK`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s' + 1` is at most `T`, so the committee of `s'` is
  among those `P.hSleepK` covers.

Read aloud: the voters of slot `s'` whose votes are on `B`'s chain outweigh the rest of its
committee. -/
theorem voters_on_chain_majority (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
      (s' : ℕ)
    -- the committee of slot `s'` is among those `P` counts
    (hT : M.supportCutoff S.C (s' + 1) ≤ T)
    (hs' : s + 1 ≤ s') (hVotes : VotesExtendAt M S A x s B Δs b₀ b₁ s') :
    ∃ Q : Finset V, Q ⊆ honestActiveAt M S A x s' ∩ S.P.committee s' ∧
      (∀ u ∈ Q, ∀ vote : GoldfishVote V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i) →
        ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
          vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
      (S.P.committee s' \ Q).card < Q.card := by
  classical
  by_cases hOwed : VotesOwedInPeriod M S Δs b₀ b₁ s'
  · have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 : s' - 1 ≤ s + 1 := by omega
      have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' - 1)
      have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
      have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono' M.toSlotLayout F.sched) S h1
      have h5 := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold s' hs2 hOwed.1 hOwed.2
    refine ⟨holdersAt M S A x s s' ∩ S.P.committee s', ?_,
      fun u hu => hVotes.1 u (Finset.mem_inter.1 hu).1, ?_⟩
    · intro u hu
      simp only [holdersAt, Finset.mem_inter] at hu ⊢
      exact ⟨hu.1.2, hu.2⟩
    · have heq : S.P.committee s' \ (holdersAt M S A x s s' ∩ S.P.committee s') =
          S.P.committee s' \ holdersAt M S A x s s' := by
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [heq]
      exact hlt
  · refine ⟨honestActiveAt M S A x s' ∩ S.P.committee s', subset_rfl,
      fun u hu => hVotes.2 hOwed u (Finset.mem_inter.1 hu).1, ?_⟩
    have hanchor : anchor ≤ M.slotStart S.C (s' + 1) :=
      le_trans P.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    have hK := P.hSleepK (s' + 1) (by omega) hanchor hT
    rw [Nat.add_sub_cancel] at hK
    have hsub : S.P.committee s' \ (honestActiveAt M S A x s' ∩ S.P.committee s') ⊆
        S.P.committee s' \ honestActiveAt M S A x s' := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
      tauto
    exact lt_of_le_of_lt (Finset.card_le_card hsub) hK

end GoldilocksCorrectness.Record.Proofs.Executions

