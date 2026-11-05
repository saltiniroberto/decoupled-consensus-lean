module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncResilience
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncResilienceStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/AsyncResilienceStatements.lean`, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 105 (the confirmed
tip persists through one asynchronous period, from the hand-over facts), and the asynchrony top
statement, up to a time `t` and read forever. Each is a one-line call of its proof page's twin of
the same name, under `Record/Restated/Proofs/Executions/`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  proposalWindowStart anchorCW)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryOutside SyncedWithinOutside)

open GoldilocksCorrectness.Statements.Executions (healFrontSlots)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith)
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows Vocab.goldilocks
  acObject fgObject healFrontSlots)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 105, the confirmed tip persists through one asynchronous period, from the hand-over
facts.** In an execution where every time is reached and corruption is permanent; blocks, Goldfish
votes and attestations are delivered within their delays after `GST` outside the period `[b₀, b₁)`
(synchrony from the receiver's wake, and catch-up on wake, suspended on the period); a block
reaches a validator only once it holds the parent; nobody votes or signs in an honest validator's
name; fewer than a quorum of validators are ever in the adversary set; committee sleepiness holds
from `anchor`, at or before the start of slot `s + 1`; `GST` is at most the vote time of slot
`s + 1`; the period starts at or after the hand-over update `c := M.supportCutoff S.C (s + 1)` and
ends one delay before the vote time of slot `s + k`; wherever the previous slot's votes are owed
inside the period, the lock holders outweigh the rest of the committee; `t₀` is at or before `c`;
and the hand-over facts `HandoverFactsOfChainBlock M S Sched x s B H t₀ tAwakeEnd` hold. Then, for
every time `t` up to which roots name blocks among what honest validators hold:

- `ConfirmedPersistsBetween M S Sched x s tAwakeEnd b₀ t`: every block that is, at a
  step `T` at a time from `tAwakeEnd` to `c`, the confirmed tip of a validator honest through `T`, or
  an ancestor of it, is the confirmed tip or an ancestor of the confirmed tip of every updater of
  slot `s` honest through any step at a time from `b₀` to `t` that comes after its own tick to `c`;
- `FinalizedCompatibleBetween M S Sched x s tAwakeEnd b₀ t`: every such block is compatible with the
  finalized block of every validator honest through any step at a time from `b₀` to `t`.

Why: the hand-over facts' last clause makes every such block `B` or an ancestor of `B`. At a step
after `c`, `period_inv_compat_all` gives the lock holders' records `B` or a descendant of `B`, held
(its second clause), and every honest finalized block compatible with `B` (its third clause, the
caches), at the steps after every updater's tick to `c`; before them, each updater's own record from the
configuration its tick to `c` leaves (the hand-over facts' second clause). At a step at the time `c` the finalized
blocks are read by `finalized_compatible_from_cutoff`. Then the confirmed tip is `B` or a descendant of `B`
(`preceq_confirmedOf_of_record_and_F`).

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `s`: the hand-over slot; `B`: its proposal; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `anchor`: the time from
  which committee sleepiness holds; `tAwakeEnd`: the time from which the confirmed tips are read;
  `b₀`, `b₁`: the start and the end of the period; `t`: the time up to which the steps are read; `T`: the
  bound up to which the premises are counted, at least `t` and at least the clock value of every tick at a
  step at a time at most `t`.

Read aloud: for every time `t`, if a root names one block among what honest validators hold by
`t`, every block confirmed from `tAwakeEnd` to the hand-over update is an ancestor of the confirmed
tip of every validator that ran that update, at every step from `b₀` up to `t`, and compatible with
every honest finalized block at those steps.

 The hypothesis `b₀ ≤ t` is deleted as unused: when `t < b₀` both
conclusions hold with no step to read.

  every finalized block at a step at a time at most `c + ΔClockBehind` is read
from the hand-over facts (`finalized_compatible_from_cutoff`).

 It is derived from the catch-up premise by `delT_of_catchUp`
(`Proofs/Executions/PeriodEntryDeliveryLine.lean`).

 The proof builds the bounded bundle `AsyncHypsOfChainBlockGSTBeforeVotesUntil` at `T`.

 At both clock bounds 0 the
statement at `T := t` is the earlier one. The roots premise stays at `t`: every read of it is at a real time at
most `t`.

The hand-over facts are read up to the window's end `tW`, which is at least `t` or at least the end of the whole
window `M.supportCutoff S.C (s + 1) + ΔClockBehind` (`htW`): every step at which the proof reads them is at a real time
at most `t` and at most that end. -/
theorem confirmedPersists_throughPeriod_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (B : Block V)
    (H t₀ anchor tAwakeEnd b₀ b₁ t T : ℕ)
    -- the premises are counted up to a bound `T` that every clock value reached by a tick at a step at a time at
    -- most `t` respects
    (hTt : t ≤ T) (hTk : ∀ (k : ℕ) (v : V) (c : ℕ), x.time k ≤ t → x.lbl k = Event.tick v c → c ≤ T)
    -- every time is reached; corruption is permanent
    {Δs Δs_F : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ` of the later of their time and `GST` when that
    -- is at or before `b₀`, and of the latest of their time, `b₁` and `GST` otherwise; attestations
    -- likewise within `Δ_F`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- what an honest active validator would serve at `t` reaches every validator active from `t`
    -- within `Δs` (`Δs_F` for attestations) of the later of `t` and `GST` when that is at or before
    -- `b₀`, and of the latest of `t`, `b₁` and `GST` otherwise
    (Sy : SyncedWithinOutside A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁)
    (Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST b₀ b₁)
    -- the trace is wake-shaped; the sync delay is at most the slow window less three delays
 (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a block reaches a validator only once it holds the parent; nobody votes or signs in an
    -- honest validator's name
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum have been corrupted up to `T`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T)
    -- committee sleepiness from `anchor`, at or before the start of slot `s + 1`, for every slot
    -- whose support cutoff is at most `T` (the committees counted up to `T`)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor T) (hAnchor : anchor ≤ M.slotStart S.C (s + 1))
    -- the network has recovered by the hand-over cutoff: `GST` is one delay or one sync delay,
    -- whichever is longer, before the support cutoff of slot `s + 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1))
    -- the period starts at or after the hand-over update and is an interval
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    -- the period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    -- wherever the previous votes are owed inside the period, the lock holders outweigh the rest
    (hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁)
    -- a certified entry an honest validator held at a step whose time is at most the start of a voter's duty window reaches the
    -- voter by its view freeze
    (hDelT : DelTLine M S A x s B b₀ b₁ Δs)
    -- `t₀` is at or before the hand-over update
    (ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1))
    -- the hand-over facts, over the copied certificate and attestation clauses, the confirmed tips
    -- read from `tAwakeEnd` on
    -- the window's end up to which the hand-over facts are read: at least `t`, or the end of the whole window
    (tW : ℝ) (htW : (t : ℝ) ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW)
    (hHand : HandoverFactsOfChainBlock M S A x tW s B H t₀ tAwakeEnd)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    -- roots name blocks among what honest validators hold by `t`
    (hRoots : RootsNameBlocksUntil M A x t) :
    ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t ∧
      FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.confirmedPersists_throughPeriod_until M F U Fx) S
    A x R GST s B H t₀ anchor tAwakeEnd b₀ b₁ t T hTt hTk E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy Sy_F hΔs hParent
     hAdvQ hSleepK hAnchor hGST hb₀ hb hb₁ hHold hDelT ht₀ tW htW hHand hWin hRoots

open Classical in
/-- **The asynchrony top statement: the confirmed tip survives one asynchronous period after
healing.** Under the top statements' premises without a premise on roots, with the hand-over slot
`s` starting after `tAwakeEnd` and its proposer awake and honest from the start of its proposal
window to the hand-over update `c := M.supportCutoff S.C (s + 1)`, and one asynchronous period
`[b₀, b₁)` that starts at or after `c` and after every validator's tick to `c`, and ends one delay before the vote time of slot `s + k`,
with the lock holders outweighing the rest of the committee wherever the previous slot's votes are
owed inside it: for every time `t`, some honest round opening slot's proposal has the root of a block its
proposer held (`RootCollisionAtOpening`); or two distinct blocks that honest validators hold at
steps at times at most `t` have the same root (`RootCollisionHeldBy M S Sched x t`); or, for every
block `B` the proposer of slot `s` puts on the wire at its tick at the start of `s`, `B` has the
root of a block that proposer held then (`RootCollisionAtProposal`), or:

- `ConfirmedPersistsBetween M S Sched x s tAwakeEnd b₀ t`: every block that is, at a
  step `T` at a time from `tAwakeEnd` to `c`, the confirmed tip of a validator honest through `T`, or
  an ancestor of it, is the confirmed tip or an ancestor of the confirmed tip of every updater of
  slot `s` honest through any step at a time from `b₀` to `t` that comes after its own tick to `c`;
- `FinalizedCompatibleBetween M S Sched x s tAwakeEnd b₀ t`: every such block is compatible with the
  finalized block of every validator honest through any step at a time from `b₀` to `t`.

The hypotheses, in words: `GST` is at most `tGAT`; every time is reached; corruption is permanent;
blocks, Goldfish votes and attestations are delivered within their delays after `GST` outside the
period `[b₀, b₁)` (synchrony from the receiver's wake, and catch-up on wake, suspended on the
period); a block reaches a validator only once it holds the parent; unforgeability; fewer than a
third of the validators have been in the adversary set up to `tAwakeEnd`; every validator outside
the adversary set at a time from `tGAT` to `tAwakeEnd` is awake then; committee sleepiness from
`anchorCW S tGAT` for the slots whose update is at most `T`; the honest round opening slots of the
rounds `r 0 < … < r m` lie between `tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`; nine honest round
opening slots lie outside every two spans of `δt` slots and five spans of `k + 2` slots; fewer than
two thirds of the validators have been in the adversary set up to `T`, a bound at least `t` and at least the clock
value of every tick at a step at a time at most `t`; the slot `s` starts after `tAwakeEnd`; its proposer is awake and outside the adversary
set from the start of its proposal window to `c`; `c ≤ b₀ ≤ b₁`; every validator's tick to `c` is at a real time at most `b₀`; `b₁ + Δ` is at most the vote time
of slot `s + k`; and wherever the previous slot's votes are owed inside the period, the lock
holders outweigh the rest of the committee; the honest voters of slots `s − 1` and `s` stay active for `Δs` after
Lemma 12's read time of their slot, and the proposer of `s` for `Δs` after `M.slotStart S.C s − max (Δ S) Δs`. No premise on roots: the conclusion names the
collision. Only environment and proposer premises.

Why: when no collision has hit by `t`, roots name blocks up to `t`; the facts after the hand-over
up to `c` (`healed_handover_facts_until_upTo`, the delivery premises up to `b₀ ≥ c` from the
suspended ones), the chain invariant and the lock invariant (`lem81_inv_before_upTo`,
`base_locks_on_chain`), the voter condition at slot `s + 1` and the records on the honest chain (`lem90a_latest_confirmed_honest_at`) give Lemma
99's two theorems, `handoverFacts_six_of_healed_upTo` and `confirmed_tips_preceq_handover_upTo`;
the latter reads the confirmed tips from the end of the healed phase `x[i₂].time ≤ tAwakeEnd` on,
so together they give `HandoverFactsOfChainBlock` with the lower end `tAwakeEnd`. Lemma 105
(`confirmedPersists_throughPeriod_until`) then concludes, with `GST ≤ M.voteTime S.C (s + 1)`
derived from `GST ≤ tGAT`, the honest round opening slots and `tAwakeEnd < M.slotStart S.C s`
(`gst_le_voteTime_succ_of_top`).

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `tGAT`, `tAwakeEnd`: the start and end of the healing
  phase; `m`: the index of the last honest round opening slot; `r`: the rounds of the honest round opening slots; `s`: the hand-over
  slot; `b₀`, `b₁`: the start and the end of the period.

`hHoldF` and `hStay`: the attestations' holders at each honest round
opening slot, and every updater of a slot from the first honest round opening slot on whose update is at most `T`,
stay active for their sync delays, as the facts after the hand-over read them. `hTicksBy`: `t` is a time at which no slot's update is half run (`TicksToUpdatesBy`).

Read aloud: after the healing phase, for every time `t`: a digest collision hit an honest
opening's proposal, or two blocks honest validators hold by `t` share a root, or, for every block
`B` the hand-over slot's proposer puts on the wire at the start of its slot, `B` collides by root
with a block the proposer held, or every block confirmed from `tAwakeEnd` to `B`'s update persists
at every validator that ran that update, at every step from `b₀` to `t`, and no honest validator
finalizes a conflicting block by `t`: one asynchronous period of fewer than `k` slots, started
after that update, abandons nothing confirmed from `tAwakeEnd` on before it.

Not claimed: the records made at the updates of the slots `s'` with `M.supportCutoff S.C s' ≤ b₁`
.

 The condition `b₀ ≤ t` on
`t` is deleted as unused: when `t < b₀` both conclusions hold with no step to read.

  every finalized block at a step at a time at most `c + ΔClockBehind` is read
from the hand-over facts (`finalized_compatible_from_cutoff`).

 It is derived from the catch-up premise by `delT_of_catchUp`
(`Proofs/Executions/PeriodEntryDeliveryLine.lean`).

 at both clock bounds 0 the statement at `T := t` is the earlier one. -/
theorem confirmedPersists_asyncPeriod_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ) (s b₀ b₁ : ℕ)
    -- `GST` is at most the start of the healing phase
    (hGST : GST ≤ tGAT)
    -- every time is reached; corruption is permanent
    {Δs Δs_F : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ` of the later of their time and `GST` when that
    -- is at or before `b₀`, and of the latest of their time, `b₁` and `GST` otherwise; attestations
    -- likewise within `Δ_F`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- what an honest active validator would serve at `t` reaches every validator active from `t`
    -- within `Δs` (`Δs_F` for attestations) of the later of `t` and `GST` when that is at or before
    -- `b₀`, and of the latest of `t`, `b₁` and `GST` otherwise
    (Sy : SyncedWithinOutside A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁)
    (Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST b₀ b₁)
    -- the trace is wake-shaped; the sync delay is at most the slow window less three delays
 (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    -- a block reaches a validator only once it holds the parent; unforgeability
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a third corrupted up to `tAwakeEnd`
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- every validator outside the adversary set in a configuration in force at a time from `tGAT` to `tAwakeEnd` is awake in it
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read
    (t T : ℕ)
    -- the premises are counted up to a bound `T` that every clock value reached by a tick at a step at a time at
    -- most `t` respects
    (hTt : t ≤ T) (hTk : ∀ (k : ℕ) (v : V) (c : ℕ), x.time k ≤ t → x.lbl k = Event.tick v c → c ≤ T)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t`
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `T`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) T)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `T`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ T → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    -- the honest round opening slots between `tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- the honest round opening slots outside the spans
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    -- fewer than two thirds of the validators corrupted up to `T`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) T)
    -- the hand-over slot starts after the healing phase
    (hs : tAwakeEnd < M.slotStart S.C s)
    -- its proposer ticks to the hand-over update, awake and honest since the trace's start or since a tick,
    -- after its last restart, to a clock value at most its proposal window's start; honest at that update and
    -- at every step at which an honest validator ticks to it
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot
    (hHoldV : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer of slot `s` is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the period starts at or after the hand-over update and is an interval
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀)
    -- every validator's tick to the hand-over update is at a real time at most `b₀`
    (hTicks₀ : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → (x.time k : ℝ) ≤ b₀)
    (hb : b₀ ≤ b₁)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    -- the period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    -- wherever the previous votes are owed inside the period, the lock holders outweigh the rest
    (hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁)
    -- a certified entry an honest validator held at a step whose time is at most the start of a voter's duty window reaches the
    -- voter by its view freeze
    (hDelT : ∀ B : Block V, DelTLine M S A x s B b₀ b₁ Δs) :
    RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
        (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i →
        RootCollisionAtProposal M S A x s B ∨
          (ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t ∧
            FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.confirmedPersists_asyncPeriod_until M F U Fx) S
    A x R GST tGAT tAwakeEnd m r s b₀ b₁ hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy Sy_F hΔs hΔs_F hHoldF hParent
    hThird hAwake hActive t T hTt hTk hTicksBy hCommittees hStay hSeq hOpenings hAdvQ hs hp hHoldV hHoldP hb₀ hTicks₀ hb hWin hb₁ hHold hDelT

open Classical in
/-- **The asynchrony top statement, read forever: the confirmed tip persists through one
asynchronous period, at every later step.** The weaker "forever" reading of
`confirmedPersists_asyncPeriod_until`, with its premises read for all time: in an execution where every time is
reached and corruption is permanent; blocks, Goldfish votes and attestations are delivered within
their delays after `GST` outside the period `[b₀, b₁)`; a block reaches a validator only once it
holds the parent; unforgeability; fewer than a third of the validators have been in the adversary
set up to `tAwakeEnd`; every validator outside the adversary set at a time from `tGAT` to
`tAwakeEnd` is awake then; committee sleepiness from `anchorCW S tGAT`; the honest round opening slots
`r 0 < … < r m` lie between `tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`; nine honest round
opening slots lie outside every two spans of `δt` slots and five spans of `k + 2` slots; fewer than
two thirds of the validators have been in the adversary set up to every time; the slot `s` starts after
`tAwakeEnd`; its proposer is awake and outside the adversary set from the start of its proposal
window to `c := M.supportCutoff S.C (s + 1)`; `c ≤ b₀ ≤ b₁`; every validator's tick to `c` is at a real time at most `b₀`; `b₁ + Δ` is at most the vote time of
slot `s + k`; and wherever the previous slot's votes are owed inside the period, the lock holders
outweigh the rest of the committee; the honest voters of slots `s − 1` and `s` stay active for `Δs` after
Lemma 12's read time of their slot, and the proposer of `s` for `Δs` after `M.slotStart S.C s − max (Δ S) Δs`. Then one of:

- `RootCollisionAtOpening M S Sched x r m`: some honest round opening slot's proposal of the healing phase has
  the root of a block its proposer held;
- `RootCollisionHeldBy M S Sched x t` at some time `t`: two distinct blocks that honest validators
  hold at steps at times at most `t` have the same root;
- for every block `B` the hand-over slot's proposer puts on the wire at its tick at the start of
  slot `s`: `RootCollisionAtProposal M S Sched x s B` (`B` has the root of a block the proposer
  held), or both unbounded forms hold, `ConfirmedPersistsFrom M S Sched x s tAwakeEnd b₀` (every
  block that is, at a step `T` at a time from `tAwakeEnd` to `c`, the confirmed tip of a validator
  honest through `T`, or an ancestor of it, is, at every step from `b₀` on, the confirmed tip or an
  ancestor of the confirmed tip of every validator honest through that step that ran slot `s`'s
  update) and `FinalizedCompatibleFrom M S Sched x s tAwakeEnd b₀` (every such block is compatible
  with the finalized block of every validator honest through any step from `b₀` on).

Why: `confirmedPersists_asyncPeriod_until` holds at every time `t`, the premises at `t` given by the
ones for all time. When no root collision at an
opening occurred and none among held blocks at any time, its last disjunct holds at every `t`;
for a proposal with no root collision, both bounded forms then hold up to every `t`, which are the
unbounded forms (`confirmedPersistsFrom_iff`, `finalizedCompatibleFrom_iff`).

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `tGAT`, `tAwakeEnd`: the start and end of the healing
  phase; `m`: the index of the last honest round opening slot; `r`: the rounds of the honest round opening slots; `s`: the hand-over
  slot; `b₀`, `b₁`: the start and the end of the period.

`hHoldF` and `hStay`: the forms for all time of the until form's rows.
The until form is called at slot starts at which no slot's update is half run.

Read aloud: after the healing phase, a digest collision hit an honest round opening slot's proposal, or two
blocks honest validators hold at some time share a root, or, for every block `B` the hand-over
slot's proposer puts on the wire at the start of its slot, `B` collides by root with a block the
proposer held, or every block confirmed from `tAwakeEnd` to `B`'s update persists forever, from
`b₀` on, at every validator that ran that update, and no honest validator ever finalizes a
conflicting block from `b₀` on.

Weaker than `confirmedPersists_asyncPeriod_until`: a root collision among held blocks at any time,
however late, discharges it, while the `_until` form, read at a time `t`, is discharged only by a
collision by `t`.

  every finalized block at a step at a time at most `c + ΔClockBehind` is read
from the hand-over facts (`finalized_compatible_from_cutoff`).

 It is derived from the catch-up premise by `delT_of_catchUp`
(`Proofs/Executions/PeriodEntryDeliveryLine.lean`). -/
theorem confirmedPersists_asyncPeriod (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ) (s b₀ b₁ : ℕ)
    -- `GST` is at most the start of the healing phase
    (hGST : GST ≤ tGAT)
    -- every time is reached; corruption is permanent
    {Δs Δs_F : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ` of the later of their time and `GST` when that
    -- is at or before `b₀`, and of the latest of their time, `b₁` and `GST` otherwise; attestations
    -- likewise within `Δ_F`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- what an honest active validator would serve at `t` reaches every validator active from `t`
    -- within `Δs` (`Δs_F` for attestations) of the later of `t` and `GST` when that is at or before
    -- `b₀`, and of the latest of `t`, `b₁` and `GST` otherwise
    (Sy : SyncedWithinOutside A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁)
    (Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST b₀ b₁)
    -- the trace is wake-shaped; the sync delay is at most the slow window less three delays
 (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    -- a block reaches a validator only once it holds the parent; unforgeability
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a third corrupted up to `tAwakeEnd`
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- every validator outside the adversary set in a configuration in force at a time from `tGAT` to `tAwakeEnd` is awake in it
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- committee sleepiness from `anchorCW S tGAT`
    (hCommittees : CommitteeSleepiness M S A x (anchorCW S tGAT))
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    -- the honest round opening slots between `tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- the honest round opening slots outside the spans
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    -- fewer than two thirds of the validators corrupted up to any time
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- the hand-over slot starts after the healing phase
    (hs : tAwakeEnd < M.slotStart S.C s)
    -- its proposer ticks to the hand-over update, awake and honest since the trace's start or since a tick,
    -- after its last restart, to a clock value at most its proposal window's start; honest at that update and
    -- at every step at which an honest validator ticks to it
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot
    (hHoldV : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer of slot `s` is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the period starts at or after the hand-over update and is an interval
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀)
    -- every validator's tick to the hand-over update is at a real time at most `b₀`
    (hTicks₀ : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → (x.time k : ℝ) ≤ b₀)
    (hb : b₀ ≤ b₁)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    -- the period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    -- wherever the previous votes are owed inside the period, the lock holders outweigh the rest
    (hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁)
    -- a certified entry an honest validator held at a step whose time is at most the start of a voter's duty window reaches the
    -- voter by its view freeze
    (hDelT : ∀ B : Block V, DelTLine M S A x s B b₀ b₁ Δs) :
    RootCollisionAtOpening M S A x r m ∨ (∃ t : ℕ, RootCollisionHeldBy M S A x t) ∨
      ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
        (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i →
        RootCollisionAtProposal M S A x s B ∨
          (ConfirmedPersistsFrom M S A x s tAwakeEnd b₀ ∧
            FinalizedCompatibleFrom M S A x s tAwakeEnd b₀) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.confirmedPersists_asyncPeriod M F U Fx) S A x R
    GST tGAT tAwakeEnd m r s b₀ b₁ hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy Sy_F hΔs hΔs_F hHoldF hParent hThird
    hAwake hActive hCommittees hStay hSeq hOpenings hAdvQ hs hp hHoldV hHoldP hb₀ hTicks₀ hb hWin hb₁ hHold hDelT

end GoldilocksCorrectness.Record.Statements.Executions

