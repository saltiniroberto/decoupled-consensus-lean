import LARuns.Statements.Statement4Defs
import Goldilocks
import GoldilocksSts
import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
import GoldilocksCorrectness.Statements.Executions.PhaseDefs
import GoldilocksCorrectness.Statements.Routines.AccountableDefs

/-!
# What Goldilocks passes to statement 4 over its runs, read off Goldilocks's specification

The definitions LARuns's Goldilocks claim reads, stated over Goldilocks's specification
(LConcrete): the library `Goldilocks`, its parameters `Goldilocks.Config`, its provisional values
`Goldilocks.Provisional` (the proposer and the committee of each slot), its schedule
(`Goldilocks.Config.t_`, the start of a slot, and `Goldilocks.duty_window_start`,
`Goldilocks.proposal_window_start`, the starts of the wake rule's windows) and its objects. Every
time is the spec's own value, an integer (`Goldilocks.Time`), read as a real number; a window start
the spec computes as a negative time for a small slot is kept negative.

Four definitions of `GoldilocksCorrectness`'s statements over the spec (not of its record) are used
directly: Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, the
two kinds of conflicting attestations `GoldilocksCorrectness.Statements.Routines.E1` and `E2`, the
number of slots `GoldilocksCorrectness.Statements.Executions.healFrontSlots` (`3 * S.C.k + 1`), and
the count of honest round opening slots outside the spans
`GoldilocksCorrectness.Statements.Executions.OpeningsOutsideWaitsAndWindows`; each reads the spec's
types and the setup alone.

The page defines what Goldilocks's instance of `LARuns.ProtocolCommittees` (on
`LARuns.Goldilocks.Instance`) fills in: its committees
(`goldilocksCommitteeSpecs`) and its proposer requirements (`goldilocksProposerReqs`, each with a
block its proposer sent at the start of its slot, `ProposedAtSlotStart`); and its
release readings (`goldilocksRelease`) and the condition on their redelivery its claim takes as an
extra condition on its observed runs (`RedeliveredAfterReleaseFromDelivery`), its catch-up delays per
object (`goldilocksΔSyncCatchUp`), its constants (`goldilocksDelayConditions`), its premise on the
healing phase (`goldilocksHealingConditions`), the condition that its holders stay online
(`HoldersStayOnline`) and the condition that the validators never corrupted by the end of the
healing phase can form a quorum (`AdversaryLeavesQuorumBy`); and the validator set at each of its blocks, `goldilocksRegistry`,
read through the class `RStsVariant2.BlockRegistry`; and its vocabulary, the instances of the classes
`LARuns.BlockVocab` and `LARuns.MessageVocab` on its blocks and objects. LARuns's Goldilocks claim,
`LARuns.GoldilocksInstance.GoldilocksSatisfiesStatement4OnRuns` (`LARuns.Goldilocks.Instance`),
passes them. Section 4 holds what Goldilocks's claims for the three statements after healing pass
besides: the readers of an honest active validator of a slot and of a proposer that ran its slot up
to the update (`UpToTickG`, `UpAndHonestToTickG`, `HonestActiveG`, `HonestProposerToUpdateG`), the
conditions that its holders stay online after the phase (`HoldersStayOnlineAfterHealing`,
`FinalityHoldersStayOnline`) and that no block held at a round's action time includes an attestation
sent at that time (`NoAttestationOfActionTickInHeldBlocks`), its network delays from two numbers
(`goldilocksΔNetDelivery`), its healing premises with
room for the clocks (`goldilocksAfterHealingConditions`,
`goldilocksFinalityLivenessHealingConditions`) and its finality premise on a window
(`goldilocksFinalityConditions`, with `HonestOpenerOn` and `QuorumActiveOn`). Nothing is proved:
the page defines.

The variables of this page: `V`, the validators; `S : Setup V`, the setup (its parameters `S.C`
give the slot layout's times, its values `S.P` the committees and the proposers).

This page imports Goldilocks, `GoldilocksSts` (the setup), the three pages of
`GoldilocksCorrectness`'s statements named above, and `LARuns.Statements.Statement4Defs`.
-/

set_option autoImplicit false

namespace LARuns.GoldilocksInstance

open Goldilocks (NamedObject RootOrder Block Attestation Time duty_window_start
  proposal_window_start)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Executions (healFrontSlots OpeningsOutsideWaitsAndWindows)
open LARuns.RealTrace
open RStsVariant2 (Registry)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## 1. The vocabulary -/

/-- The validator set at every block, as Goldilocks's specification has it: every validator
active, none slashed, each of weight one, the quorum `Goldilocks.quorum V`, two thirds of the
validator count rounded up.

Read aloud: every validator counts once. -/
def goldilocksRegistry : Registry V where
  weight _ := 1
  active := Finset.univ
  slashed := ∅
  quorum := Goldilocks.quorum V

/-- The validator set at each of Goldilocks's blocks is `goldilocksRegistry`. The condition on
executions `RStsVariant2.WeightBoundsG` reads a block's validator set through it.

Read aloud: at every block, every validator counts once. -/
instance : RStsVariant2.BlockRegistry (Block V) V :=
  ⟨fun _ => goldilocksRegistry⟩

/-- `conflicts o o'`: `o` and `o'` are attestations `a`, `a'` with `E1 a a'` (`a` carries a
finality pair `(h, T)` and `a'` is a vote at the height `h` naming a block other than `T`) or
`E2 a a'` (two target votes at one height for different blocks). Not read by statement 4.

Read aloud: `o` and `o'` are two attestations that conflict. -/
def conflicts (o o' : NamedObject V) : Prop :=
  ∃ a a' : Attestation V, o = .attest a ∧ o' = .attest a' ∧
    (GoldilocksCorrectness.Statements.Routines.E1 a a' ∨
      GoldilocksCorrectness.Statements.Routines.E2 a a')

/-- Goldilocks's blocks as the statements read them: the ancestry and the roots of
`Vocab.goldilocks` (ancestry `Block.AncestorEq`, one root when the `root` fields are equal).

Read aloud: what a statement reads of Goldilocks's blocks. -/
instance : BlockVocab (Block V) :=
  let W := GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (V := V)
  { anc := W.anc, sameRoot := W.sameRoot }

/-- Goldilocks's objects as the statements read them: the block an object is, its author and its
inclusions of `Vocab.goldilocks` (`blockOf`, `author`, `carries`, over the spec's objects), and
`conflicts` of this page. A proposal is a block object: the object `.block B` proposes `B`, the
only object a proposer broadcasts when it proposes (`Goldilocks.propose_block`), so the block an
object proposes is the block it is.

Read aloud: what a statement reads of Goldilocks's objects. -/
instance : MessageVocab (NamedObject V) V (Block V) :=
  let W := GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (V := V)
  { blockOf := W.blockOf, proposalOf := W.blockOf, author := W.author, carries := W.carries,
    conflicts := conflicts }

/-! ## 2. The committees, the proposers, the release readings and their redelivery,
the delays -/

/-- Goldilocks's committee `ci`, slot `ci`'s committee, for clocks that lead the real time by at most
`ΔClockAhead` and lag it by at most `ΔClockBehind`: its members `S.P.committee ci` in every view (the
spec's committee of slot `ci`); its sleepiness window from `ΔClockAhead` before the start of the window
of slot `ci`'s duties, `duty_window_start S.C ci − ΔClockAhead` (a member up from then ticks at the
reading of that start), to `ΔClockBehind` after the support cutoff of slot `ci + 1`,
`S.C.t_ (ci + 1) + 2 * S.C.Δ + ΔClockBehind` (a member's tick at the reading of that cutoff is at a
real time at most that); and it needs synchrony until the support cutoff of slot `ci − 1`,
`S.C.t_ (ci − 1) + 2 * S.C.Δ`, when the previous slot's votes have reached every honest node.

Read aloud: slot `ci`'s committee, how long its members must stay up and honest, and until when it
needs the network synchronous. -/
def goldilocksCommitteeSpecs (S : Setup V) (ΔClockAhead ΔClockBehind : ℝ) (ci : ℕ) :
    CommitteeSpec V (Block V) where
  members _ := S.P.committee ci
  sleepinessWindow :=
    { tStart := ((duty_window_start S.C ci : Time) : ℝ) - ΔClockAhead,
      tEnd := ((S.C.t_ (ci + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind }
  tSyncNeededUntil := ((S.C.t_ (ci - 1) + 2 * S.C.Δ : Time) : ℝ)

/-- Goldilocks's proposer requirement of the slot `s` for the block `B`, for clocks that lead the real
time by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`: the proposer `S.P.proposer s`, the
block it protects `B`, awake and honest from `ΔClockAhead` before the start of the window of slot `s`'s
proposal, `proposal_window_start S.C s − ΔClockAhead` (a node up from then ticks at the reading of the
window's start even if its clock leads), to
`ΔClockBehind` after the support cutoff of slot `s + 1`, `S.C.t_ (s + 1) + 2 * S.C.Δ + ΔClockBehind`
(the hand-over update `tPreAsync`, by which every node's tick at the reading of that cutoff has run),
and the period plus its recovery
over by the vote time of slot `s + k` less one delay, `S.C.t_ (s + S.C.k) + S.C.Δ − S.C.Δ` (with the
recovery `max S.C.Δ Δs − S.C.Δ`, this asks the period's end plus `max S.C.Δ Δs` to be at most that
vote time).

Read aloud: slot `s`'s proposer, the block `B`, its window, the hand-over update done at every node,
and by when the period must be over. -/
def goldilocksProposerReq (S : Setup V) (ΔClockAhead ΔClockBehind : ℝ) (s : ℕ) (B : Block V) :
    ProposerRequirement V (Block V) where
  proposer := S.P.proposer s
  block := B
  tProposalStart := ((proposal_window_start S.C s : Time) : ℝ) - ΔClockAhead
  tPreAsync := ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind
  tPeriodEndBy := ((S.C.t_ (s + S.C.k) + S.C.Δ : Time) : ℝ) - ((S.C.Δ : Time) : ℝ)

/-- `ProposedAtSlotStart S x s B`: in the execution `x`, at some step `i`, the proposer of slot `s`,
`S.P.proposer s`, ticks when its clock reads the start of slot `s`, `S.C.t_ s` (`TickAtG`), and that
step puts on the wire an envelope signed by `S.P.proposer s` whose object is the block `B` (the
object a proposer broadcasts when it proposes, `Goldilocks.propose_block`). Written over any
execution with an `RStsVariant2.Observable` (a run of a protocol of `RStsVariant2`, or an observed
run). The start of a slot is never negative, so it is read as a value of the node's clock, a
natural number, unchanged.

Read aloud: at its tick at the start of slot `s`, slot `s`'s proposer sent the block `B`.

Kind: a reading of an execution. -/
def ProposedAtSlotStart {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev]
    (S : Setup V) (x : X) (s : ℕ) (B : Block V) : Prop :=
  -- some step `i` of `x` and some envelope `e`
  ∃ (i : ℕ) (e : RStsVariant2.Envelope V (NamedObject V)),
    -- step `i` is the tick of slot `s`'s proposer when its clock reads the start of slot `s`
    TickAtG x i (S.P.proposer s) (S.C.t_ s).toNat ∧
    -- step `i` adds a copy of `e` to the sent envelopes
    e ∈ RStsVariant2.Observable.sent x (i + 1) - RStsVariant2.Observable.sent x i ∧
    -- `e` is signed by slot `s`'s proposer
    e.sender = S.P.proposer s ∧
    -- the object of `e` is the block `B`
    e.msg = NamedObject.block B

/-- Goldilocks's proposer requirements in the execution `x` after the healing phase, for clocks that
lead the real time by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`: one per slot
`s` that starts after `tAwakeEnd` (`tAwakeEnd < S.C.t_ s`, stronger than the generic
`tAwakeEnd ≤ tPreAsync` of `HonestProposerThroughG`; hence the set reads `tAwakeEnd`) and per block
`B` that slot `s`'s proposer sent at its tick at the start of slot `s` in `x`
(`ProposedAtSlotStart`).

Read aloud: for every slot that starts after healing, its proposer with each block it sent at its
tick at the start of that slot. -/
def goldilocksProposerReqs {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev]
    (S : Setup V) (ΔClockAhead ΔClockBehind tAwakeEnd : ℝ) (x : X) :
    Set (ProposerRequirement V (Block V)) :=
  { p | ∃ (s : ℕ) (B : Block V),
      -- slot `s` starts after `tAwakeEnd`
      tAwakeEnd < ((S.C.t_ s : Time) : ℝ) ∧
      -- slot `s`'s proposer sent `B` at its tick at the start of slot `s`
      ProposedAtSlotStart S x s B ∧
      -- `p` is slot `s`'s requirement for `B`
      p = goldilocksProposerReq S ΔClockAhead ΔClockBehind s B }

/-- Goldilocks's release reading per object: the start of the block's slot, `S.C.t_ B.slot`, for
a block, of the vote's slot for a Goldfish vote, nothing for an attestation (a block or a vote of
a later slot than the receiver's clock's is not processed before that slot). The start of a slot
is never negative, so it is read as a value of the node's clock, a natural number, unchanged.

Read aloud: a block or a vote may be processed from its slot's start. -/
def goldilocksRelease (S : Setup V) : NamedObject V → Option ℕ
  | .block B => some (S.C.t_ B.slot).toNat
  | .gfVote vote => some (S.C.t_ vote.slot).toNat
  | .attest _ => none

/-- Whenever an honest envelope `e`, sent at step `iSend`, whose message has a release reading
`tRelease` under `release` (`release e.msg = some tRelease`: the reading from which its object may
be processed) reaches a node `v` at step `jDeliver`, while `v` is up and honest, before `v` has
reacted to `tRelease`, and `v` stays up and honest in every configuration from `jDeliver`'s on that
is entered before `ΔRedeliver` after `v`'s first tick at a clock reading `tTick` at least
`tRelease` (the step `kAct`), the network delivers the envelope to `v` again after that tick, within
`ΔRedeliver` of it, and before `v` ticks at or after that deadline. Written over any execution with
an `RStsVariant2.Observable` (a run of a protocol of `RStsVariant2`, or an observed run), through the
readings of `LARuns.Environment`'s section on an `Observable`.

The receiver's activity is read from the delivery step on: a configuration entered at the delivery's
real time but before step `jDeliver` is not asked of it, since several steps may share one real
time.

Goldilocks's claim takes it, with Goldilocks's release readings `goldilocksRelease S`, as an extra
condition on its observed runs (`ObservedRunWithCommittees`): Goldilocks's wired protocol runs its
receive code at delivery and does not keep a message that arrives before its release reading. A
protocol that keeps early messages until their release does not need it.

Read aloud: a message that arrived too early for its release is delivered again once the receiver
has ticked at or past the release, within `ΔRedeliver`, when the receiver stays up and honest from
the first delivery until then.

Kind: a condition on executions (no step of `RStsVariant2` reads it; Goldilocks's claim takes it as
an extra condition). -/
def RedeliveredAfterReleaseFromDelivery {X Node Msg L Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] [RStsVariant2.Observable X Node Msg L Ev]
    (release : (m : Msg) → Option ℕ) (ΔRedeliver : ℝ) (x : X) : Prop :=
  ∀ (iSend jDeliver kAct : ℕ) (v : Node) (e : RStsVariant2.Envelope Node Msg) (tRelease tTick : ℕ),
    DeliversToUpAndHonestG x jDeliver v e → release e.msg = some tRelease →
    HonestSendAtG x iSend e →
    ¬ ReactedAtLeastG x (iBefore := jDeliver) v (tAtLeast := tRelease) →
    jDeliver < kAct → TickAtG x kAct v tTick → tRelease ≤ tTick →
    NoTickAtLeastBetweenG x (iAfter := jDeliver) (iBefore := kAct) tRelease v →
    (∀ c : ℕ, jDeliver ≤ c →
      RStsVariant2.Observable.stamp x c < RStsVariant2.Observable.stamp x (kAct + 1) + ΔRedeliver →
      v ∉ RStsVariant2.Observable.crashed x c ∧ RStsVariant2.Observable.state x c v ≠ none ∧
        RStsVariant2.HonestG x c v) →
    DeliveredAgainByG x kAct (tBy := RStsVariant2.Observable.stamp x (kAct + 1) + ΔRedeliver) v e

/-- Goldilocks's catch-up delay per object on the run, from the sync delays `Δs` (a block or a
Goldfish vote) and `Δs_F` (an attestation) as the run read through the nodes' clocks counts them:
each less the clock's lead `ΔClockAhead`. The run compares a catch-up deadline with the real time,
the run read through the clocks with the node's clock, which may read up to `ΔClockAhead` more; so a
catch-up within `Δs − ΔClockAhead` of the real time is one within `Δs` of the clock.

Read aloud: the run catches a node up within the sync delay less the clock's lead. -/
def goldilocksΔSyncCatchUp (Δs Δs_F : ℕ) (ΔClockAhead : ℝ) : NamedObject V → ℝ
  | .block _ => (Δs : ℝ) - ΔClockAhead
  | .gfVote _ => (Δs : ℝ) - ΔClockAhead
  | .attest _ => (Δs_F : ℝ) - ΔClockAhead

/-! ## 3. The premise on the healing phase -/

/-- The honest round opening slots on the healing-phase segment, for clocks that lead the real time
by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`: `m + 1` rounds `r 0 < … < r m` whose
first slots `r i * S.C.R` start at least `ΔClockAhead` after `tFirst` (the first), the last one's
support cutoff `S.C.t_ (r m * S.C.R) + 2 * S.C.Δ` plus `ΔClockBehind` at most `tLast` (the last),
each first slot's proposer `S.P.proposer (r i * S.C.R)` outside the corrupted set of every
configuration of the segment entered at or before that support cutoff, and the first slots spaced at
most `δt + 1` slots apart two by two.

Read aloud: `m + 1` increasing round opening slots between `tFirst` and `tLast`, each with an
honest proposer, spaced at most `δt + 1` slots apart two by two. -/
structure HonestOpeningSeqOn (S : Setup V)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V)))
    (r : (i : ℕ) → ℕ) (m : ℕ) (ΔClockAhead ΔClockBehind tFirst tLast : ℝ) : Prop where
  /-- The rounds increase. -/
  mono : ∀ i : ℕ, i < m → r i < r (i + 1)
  /-- The first slot of the first opening starts at least the clock's lead bound `ΔClockAhead` after
  `tFirst` (a node up from `tFirst` ticks at the reading of that start). -/
  first : tFirst + ΔClockAhead ≤ ((S.C.t_ (r 0 * S.C.R) : Time) : ℝ)
  /-- The last opening's support cutoff, plus the clock's lag bound `ΔClockBehind`, is at most
  `tLast` (every tick to a reading at most that cutoff is at a real time at most `tLast`). -/
  last : ((S.C.t_ (r m * S.C.R) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ tLast
  /-- The proposer of every opening is outside the corrupted set of every configuration of the
  segment entered at or before the support cutoff `c` of its own slot (a corruption step taken at
  the real time `c` included). -/
  honest : ∀ i : ℕ, i ≤ m →
    ∀ (j : ℕ) (st : PhaseStep V (NamedObject V) (Block V)),
      segment j = some st →
      st.time ≤ ((S.C.t_ (r i * S.C.R) + 2 * S.C.Δ : Time) : ℝ) →
      S.P.proposer (r i * S.C.R) ∉ st.corrupted
  /-- The first slot of opening `i + 2` is at most `δt + 1` slots after the first slot of opening
  `i`. -/
  spacing : ∀ i : ℕ, i + 2 ≤ m → r (i + 2) * S.C.R ≤ r i * S.C.R + S.C.δt + 1

/-- The conjunct of Goldilocks's healing premises that reads the segment, for clocks that lead the
real time by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`: the honest round opening
slots between
`tGAT + 4 * S.C.Δ * healFrontSlots S` and `tAwakeEnd` (`HonestOpeningSeqOn`), nine of them outside
every two spans of `δt` slots and five spans of `k + 2` slots (`OpeningsOutsideWaitsAndWindows`).

Read aloud: enough honest round opening slots inside the healing phase. -/
def goldilocksOpeningsOn (S : Setup V) (ΔClockAhead ΔClockBehind tGAT tAwakeEnd : ℝ)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) : Prop :=
  ∃ (r : ℕ → ℕ) (m : ℕ),
    HonestOpeningSeqOn S segment r m ΔClockAhead ΔClockBehind
      (tFirst := tGAT + 4 * ((S.C.Δ : Time) : ℝ) * (healFrontSlots S : ℕ))
      (tLast := tAwakeEnd) ∧
    OpeningsOutsideWaitsAndWindows S r m

/-- Goldilocks's constants, with room for the clocks, the same for its four claims with a healing
phase. `ΔNet`, `ΔNet_F` (the network's delays for a block or a Goldfish vote, and for an attestation),
`ΔRedeliver` (the redelivery delay) and `Δs`, `Δs_F` (the sync delays) are the delays as the run read
through the nodes' clocks counts them (`goldilocksΔNetDelivery`, `goldilocksΔSyncCatchUp`): the
network's delays plus the clock bounds fit the protocol's delays (`ΔNet + ΔClockAhead + ΔClockBehind ≤
Δ`, `ΔNet_F + ΔClockAhead + ΔClockBehind ≤ Δ_F`), the clock bounds are less than each delay, the
redelivery delay plus the clock bounds fits `Δ`, the sync delays plus the clock bounds fit the slow
window (`max Δ Δs + 3Δ + ΔClockAhead + ΔClockBehind < 4Δk`, and for attestations either
`Δs_F + ΔClockAhead + ΔClockBehind ≤ Δ_F` or `Δs_F + 3Δ + ΔClockAhead + ΔClockBehind ≤ 4Δk`), and the
attestations' sync delay covers their network delay and the clock's lead
(`ΔNet_F + ΔClockAhead ≤ Δs_F`).

Read aloud: Goldilocks's delays, with room for the clocks. -/
def goldilocksDelayConditions (S : Setup V) (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ)
    (ΔClockAhead ΔClockBehind : ℝ) : Prop :=
  (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ ((S.C.Δ : Time) : ℝ) ∧
  ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ) ∧
  (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ ((S.C.Δ : Time) : ℝ) ∧
  (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ ((S.C.Δ_F : Time) : ℝ) ∧
  ΔClockAhead + ΔClockBehind < ((S.C.Δ_F : Time) : ℝ) ∧
  max ((S.C.Δ : Time) : ℝ) Δs + 3 * ((S.C.Δ : Time) : ℝ) + ΔClockAhead + ΔClockBehind <
    4 * ((S.C.Δ : Time) : ℝ) * S.C.k ∧
  ((Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ ((S.C.Δ_F : Time) : ℝ) ∨
    (Δs_F : ℝ) + 3 * ((S.C.Δ : Time) : ℝ) + ΔClockAhead + ΔClockBehind ≤
      4 * ((S.C.Δ : Time) : ℝ) * S.C.k) ∧
  (ΔNet_F : ℝ) + ΔClockAhead ≤ Δs_F

/-- What Goldilocks passes as `healingConditions` to statement 4: a predicate on the healing-phase
segment. Its conjuncts that read no trace are constants captured by the closure: Goldilocks's
delays with room for the clocks (`goldilocksDelayConditions`, the same as for the statements after
healing), and `ΔPreAsync` is the length of the updaters' window, from `ΔClockAhead` before the
start of the window of slot `s + 1`'s duties, `duty_window_start S.C (s + 1) − ΔClockAhead`, to
`ΔClockBehind` after the support cutoff of slot `s + 1` (the hand-over update `tPreAsync` of
`goldilocksProposerReq`), which is `S.C.Δ + 4 * S.C.Δ * S.C.k + ΔClockAhead + ΔClockBehind` for every
slot. Its conjunct that reads the segment: the honest round
opening slots of the phase (`goldilocksOpeningsOn`).

Goldilocks's slot layout is uniform and its validator set fixed by the spec's definitions, so no
conjunct says so.

Not here, because they read the observed run outside the phase: the parent-first delivery order,
the redelivery and the holders staying online (`goldilocksAfterHealingExtraConditions`, the extra
conditions on the observed runs in `GoldilocksSatisfiesStatement4OnRuns`) and the catch-up after a
restart (the statement's hypothesis `CatchUpAfterRestartG TickStepG`).

Read aloud: Goldilocks's own premise on the healing phase: its constants, with room for the clocks,
and honest round opening slots inside the phase. -/
def goldilocksHealingConditions (S : Setup V) (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ)
    (ΔClockAhead ΔClockBehind ΔPreAsync tGAT tAwakeEnd : ℝ)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) : Prop :=
  goldilocksDelayConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind ∧
  (∀ s : ℕ, ΔPreAsync =
    ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind -
      (((duty_window_start S.C (s + 1) : Time) : ℝ) - ΔClockAhead)) ∧
  goldilocksOpeningsOn S ΔClockAhead ΔClockBehind tGAT tAwakeEnd segment

/-- `HonestByG x c v`: in the execution `x`, `v` is outside the corrupted set of every configuration
entered at or before the real time `c`.

Read aloud: `v` is honest up to the real time `c`.

Kind: a reading of an execution. -/
def HonestByG {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev] (x : X) (c : ℝ)
    (v : V) : Prop :=
  ∀ j : ℕ, RStsVariant2.Observable.stamp x j ≤ c → RStsVariant2.HonestG x j v

/-- Goldilocks's holders stay online: in the execution `x`, after the start of the healing phase
`tGAT`, the validators whose objects the sync delays read stay up and honest for those delays after
serving them, and the validators honest at a support cutoff of the phase stay up and honest until
their clocks have read it.

The variables: `S`, the setup; `Δs`, `Δs_F`, the sync delays of the claims
(`goldilocksDelayConditions`); `ΔClockBehind`, the clock's lag bound; `tGAT`, `tAwakeEnd`, the
healing phase; `x`, the execution.

Read aloud: the validators that serve something stay up and honest for the sync delay after serving,
and the validators honest at a support cutoff of the phase stay up and honest for the clock's lag
after it.

Kind: a condition on executions (no step of `RStsVariant2` reads it; Goldilocks's claims take it as
an extra condition). -/
structure HoldersStayOnline {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev]
    (S : Setup V) (Δs Δs_F : ℕ) (ΔClockBehind tGAT tAwakeEnd : ℝ) (x : X) : Prop where
  /-- For every round `r'` whose first slot `s = r' * S.C.R` has the window of its duties
  starting at or after `tGAT` and the support cutoff of slot `s + 1` at most `tAwakeEnd`, every
  validator honest up to that cutoff is up and honest from the start of the window of slot `s`'s
  duties for the attestations' sync delay `Δs_F`. -/
  attesters : ∀ r' : ℕ, tGAT ≤ ((duty_window_start S.C (r' * S.C.R) : Time) : ℝ) →
    ((S.C.t_ (r' * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) ≤ tAwakeEnd →
    ∀ v : V, HonestByG x ((S.C.t_ (r' * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) v →
      RStsVariant2.UpAndHonestThroughoutG x ((duty_window_start S.C (r' * S.C.R) : Time) : ℝ)
        (((duty_window_start S.C (r' * S.C.R) : Time) : ℝ) + Δs_F) v
  /-- For every slot `σ` whose duties' window starts at or after `tGAT`, every validator honest
  when it ticks at the reading of the support cutoff of slot `σ + 1` is up and honest from that
  tick's real time for the sync delay `max Δ Δs`. -/
  updaters : ∀ σ : ℕ, tGAT ≤ ((duty_window_start S.C σ : Time) : ℝ) →
    ∀ (k : ℕ) (u : V), TickAtG x k u (S.C.t_ (σ + 1) + 2 * S.C.Δ).toNat →
      RStsVariant2.HonestG x k u →
      RStsVariant2.UpAndHonestThroughoutG x (RStsVariant2.Observable.stamp x (k + 1))
        (RStsVariant2.Observable.stamp x (k + 1) + max ((S.C.Δ : Time) : ℝ) Δs) u
  /-- For every slot `s` whose duties' window starts at or after `tGAT` and whose next slot's
  support cutoff is at most `tAwakeEnd`, every validator honest up to that cutoff is up and honest
  from it for the clock's lag bound `ΔClockBehind`. -/
  phaseEnd : ∀ s : ℕ, tGAT ≤ ((duty_window_start S.C s : Time) : ℝ) →
    ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) ≤ tAwakeEnd →
    ∀ v : V, HonestByG x ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) v →
      RStsVariant2.UpAndHonestThroughoutG x ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ)
        (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind) v

/-- `AdversaryLeavesQuorumBy tAwakeEnd x`: in the execution `x`, every set `A` of validators, each
outside the honest set (`RStsVariant2.HonestG`) in some configuration entered at or before the real
time `tAwakeEnd`, leaves at least Goldilocks's quorum of validators outside it:
`quorum V ≤ validator_count V − |A|`.

The variables: `tAwakeEnd`, the end of the healing phase; `x`, the execution.

Read aloud: the validators never corrupted by the end of the healing phase can form a quorum.

Kind: a condition on executions (no step of `RStsVariant2` reads it; Goldilocks's claims take it as
an extra condition). -/
def AdversaryLeavesQuorumBy {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev]
    (tAwakeEnd : ℝ) (x : X) : Prop :=
  ∀ A : Finset V, (∀ v ∈ A, ∃ i : ℕ, RStsVariant2.Observable.stamp x i ≤ tAwakeEnd ∧
      ¬ RStsVariant2.HonestG x i v) →
    Goldilocks.quorum V ≤ Goldilocks.validator_count V - A.card

/-! ## 4. What Goldilocks passes to the statements after healing -/

/-- `UpToTickG x a b v`: in the execution `x`, `v` ticks at the reading `b` at some step `k'`, and
either is up (outside the crashed set, with its state known) in every configuration up to the one
step `k'` is taken from, or ticks at a reading `c` at most `a` at some step `k ≤ k'` and is up in
every configuration from the one step `k` is taken from to the one step `k'` is taken from. The
window opens at the integer reading `a` and ends at `v`'s own tick at `b`; nothing is asked of the
configurations after that tick. At a negative `a` no reading is at most `a`, and only the first case
counts.

Read aloud: `v` ticks at `b`, and has been up since the execution's start, or since a tick at a
reading at most `a`, up to that tick.

Kind: a reading of an execution. -/
def UpToTickG {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev] (x : X) (a : ℤ)
    (b : ℕ) (v : V) : Prop :=
  ∃ k' : ℕ, TickAtG x k' v b ∧
    ((∀ i : ℕ, i ≤ k' →
        v ∉ RStsVariant2.Observable.crashed x i ∧ RStsVariant2.Observable.state x i v ≠ none) ∨
     (∃ k ≤ k', ∃ c : ℕ, (c : ℤ) ≤ a ∧ TickAtG x k v c ∧
        ∀ i : ℕ, k ≤ i → i ≤ k' →
          v ∉ RStsVariant2.Observable.crashed x i ∧ RStsVariant2.Observable.state x i v ≠ none))

/-- `UpAndHonestToTickG x a b v`: as `UpToTickG x a b v`, with `v` also outside the corrupted set in
every configuration the window reads.

Read aloud: `v` ticks at `b`, and has been up and honest since the execution's start, or since a
tick at a reading at most `a`, up to that tick.

Kind: a reading of an execution. -/
def UpAndHonestToTickG {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev] (x : X)
    (a : ℤ) (b : ℕ) (v : V) : Prop :=
  ∃ k' : ℕ, TickAtG x k' v b ∧
    ((∀ i : ℕ, i ≤ k' →
        v ∉ RStsVariant2.Observable.crashed x i ∧ RStsVariant2.Observable.state x i v ≠ none ∧
          RStsVariant2.HonestG x i v) ∨
     (∃ k ≤ k', ∃ c : ℕ, (c : ℤ) ≤ a ∧ TickAtG x k v c ∧
        ∀ i : ℕ, k ≤ i → i ≤ k' →
          v ∉ RStsVariant2.Observable.crashed x i ∧ RStsVariant2.Observable.state x i v ≠ none ∧
            RStsVariant2.HonestG x i v))

/-- `HonestActiveG S x s v`: in the execution `x`, `v` is an honest active validator of slot `s`: it
ticks at the reading of the support cutoff of slot `s + 1`, `S.C.t_ (s + 1) + 2 * S.C.Δ`, up since
the execution's start or since a tick at a reading at most the start of the window of slot `s`'s
duties, `duty_window_start S.C s` (`UpToTickG`); it is outside the corrupted set of every
configuration entered at or before that cutoff's real time (`HonestByG`); and it is outside the
corrupted set of every configuration from which a validator outside the corrupted set ticks at that
cutoff's reading.

Read aloud: `v` ran slot `s`'s duties up to its update, honest through the update's real time and
whenever an honest validator ran that update.

Kind: a reading of an execution. -/
def HonestActiveG {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev] (S : Setup V)
    (x : X) (s : ℕ) (v : V) : Prop :=
  UpToTickG x (duty_window_start S.C s) (S.C.t_ (s + 1) + 2 * S.C.Δ).toNat v ∧
  HonestByG x ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) v ∧
  ∀ (k : ℕ) (w : V), TickAtG x k w (S.C.t_ (s + 1) + 2 * S.C.Δ).toNat →
    RStsVariant2.HonestG x k w → RStsVariant2.HonestG x k v

/-- `HonestProposerToUpdateG S x s`: in the execution `x`, the proposer of slot `s`,
`S.P.proposer s`, ticks at the reading of the support cutoff of slot `s + 1`, up and honest since the
execution's start or since a tick at a reading at most the start of the window of slot `s`'s
proposal, `proposal_window_start S.C s` (`UpAndHonestToTickG`); it is outside the corrupted set of
every configuration entered at or before that cutoff's real time (`HonestByG`); and it is outside the
corrupted set of every configuration from which a validator outside the corrupted set ticks at that
cutoff's reading.

Read aloud: slot `s`'s proposer ran its proposal and the slot's update up and honest, honest through
the update's real time and whenever an honest validator ran that update.

Kind: a reading of an execution. -/
def HonestProposerToUpdateG {X L Ev : Type} [RStsVariant2.Observable X V (NamedObject V) L Ev]
    (S : Setup V) (x : X) (s : ℕ) : Prop :=
  UpAndHonestToTickG x (proposal_window_start S.C s) (S.C.t_ (s + 1) + 2 * S.C.Δ).toNat
    (S.P.proposer s) ∧
  HonestByG x ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) (S.P.proposer s) ∧
  ∀ (k : ℕ) (w : V), TickAtG x k w (S.C.t_ (s + 1) + 2 * S.C.Δ).toNat →
    RStsVariant2.HonestG x k w → RStsVariant2.HonestG x k (S.P.proposer s)

/-- Goldilocks's holders stay online after the healing phase: in the execution `x`, the honest active
committee members and the honest proposers of the slots after `tAwakeEnd` stay up and honest for the
sync delay `Δs` after the real time at which the synchronous delivery reads what they hold.

The variables: `S`, the setup; `Δs`, the sync delay of blocks and Goldfish votes; `tAwakeEnd`, the
end of the healing phase; `x`, the execution.

Read aloud: after the healing phase, the honest active committee members and the honest proposers stay
up and honest for the sync delay after the time their votes and blocks are read.

Kind: a condition on executions (no step of `RStsVariant2` reads it; Goldilocks's claims take it as
an extra condition). -/
structure HoldersStayOnlineAfterHealing {X L Ev : Type}
    [RStsVariant2.Observable X V (NamedObject V) L Ev] (S : Setup V) (Δs : ℕ) (tAwakeEnd : ℝ)
    (x : X) : Prop where
  /-- For every slot `s'` whose next slot starts at or after `tAwakeEnd`, every honest active member of
  slot `s'`'s committee is up and honest from the support cutoff of slot `s' − 1`,
  `S.C.t_ s' + 2 * S.C.Δ`, less the larger of two delays and the sync delay, for the sync delay. -/
  committee : ∀ s' : ℕ, tAwakeEnd ≤ ((S.C.t_ (s' + 1) : Time) : ℝ) →
    ∀ u ∈ S.P.committee s', HonestActiveG S x s' u →
      RStsVariant2.UpAndHonestThroughoutG x
        ((S.C.t_ s' + 2 * S.C.Δ - max (2 * S.C.Δ) (Δs : Time) : Time) : ℝ)
        (((S.C.t_ s' + 2 * S.C.Δ - max (2 * S.C.Δ) (Δs : Time) : Time) : ℝ) + Δs) u
  /-- For every slot `s` starting at or after `tAwakeEnd` whose proposer ran its proposal and the
  slot's update up and honest, that proposer is up and honest from the start of slot `s` less the
  larger of the delay and the sync delay, for the sync delay. -/
  proposer : ∀ s : ℕ, tAwakeEnd ≤ ((S.C.t_ s : Time) : ℝ) → HonestProposerToUpdateG S x s →
    RStsVariant2.UpAndHonestThroughoutG x ((S.C.t_ s - max S.C.Δ (Δs : Time) : Time) : ℝ)
      (((S.C.t_ s - max S.C.Δ (Δs : Time) : Time) : ℝ) + Δs) (S.P.proposer s)

/-- Goldilocks's holders stay online for finality after the healing phase: in the execution `x`, the
honest active committee members and the honest proposers of the slots after `tAwakeEnd` stay up and
honest through their slot's duties and the sync delay `Δs` after its update, an honest round opening
slot's proposer stays up and honest from its proposal window's start to its slot's start, and the
honest active validators of a round stay up and honest for the attestations' sync delay `Δs_F` after
the next round's proposal window's start.

The variables: `S`, the setup; `Δs`, `Δs_F`, the sync delays; `tAwakeEnd`, the end of the healing
phase; `x`, the execution.

Read aloud: after the healing phase, the validators that run a slot's or a round's duties stay up and
honest until what they sent has reached the next ones.

Kind: a condition on executions (no step of `RStsVariant2` reads it; Goldilocks's claim for statement
3 takes it as an extra condition). -/
structure FinalityHoldersStayOnline {X L Ev : Type}
    [RStsVariant2.Observable X V (NamedObject V) L Ev] (S : Setup V) (Δs Δs_F : ℕ) (tAwakeEnd : ℝ)
    (x : X) : Prop where
  /-- For every slot `σ'` starting at or after `tAwakeEnd`, every honest active member of slot `σ'`'s
  committee is up and honest from the start of the window of slot `σ'`'s duties to the sync delay
  after the support cutoff of slot `σ' + 1`. -/
  committeeDuties : ∀ σ' : ℕ, tAwakeEnd ≤ ((S.C.t_ σ' : Time) : ℝ) →
    ∀ u ∈ S.P.committee σ', HonestActiveG S x σ' u →
      RStsVariant2.UpAndHonestThroughoutG x ((duty_window_start S.C σ' : Time) : ℝ)
        (((S.C.t_ (σ' + 1) + 2 * S.C.Δ : Time) : ℝ) + Δs) u
  /-- For every slot `s` starting at or after `tAwakeEnd` whose proposer ran its proposal and the
  slot's update up and honest, that proposer is up and honest from the start of slot `s` less the
  larger of the delay and the sync delay to the sync delay after the support cutoff of slot
  `s + 1`. -/
  proposer : ∀ s : ℕ, tAwakeEnd ≤ ((S.C.t_ s : Time) : ℝ) → HonestProposerToUpdateG S x s →
    RStsVariant2.UpAndHonestThroughoutG x ((S.C.t_ s - max S.C.Δ (Δs : Time) : Time) : ℝ)
      (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + Δs) (S.P.proposer s)
  /-- For every round `r'` whose first slot starts at or after `tAwakeEnd`, when the proposer of the
  next round's first slot ran its proposal and that slot's update up and honest, it is up and honest
  from that slot's proposal window's start to that slot's start. -/
  opener : ∀ r' : ℕ, tAwakeEnd ≤ ((S.C.t_ (r' * S.C.R) : Time) : ℝ) →
    HonestProposerToUpdateG S x ((r' + 1) * S.C.R) →
      RStsVariant2.UpAndHonestThroughoutG x
        ((proposal_window_start S.C ((r' + 1) * S.C.R) : Time) : ℝ)
        ((S.C.t_ ((r' + 1) * S.C.R) : Time) : ℝ) (S.P.proposer ((r' + 1) * S.C.R))
  /-- For every round `r'` whose first slot starts at or after `tAwakeEnd`, every honest active
  validator of that first slot is up and honest from the next round's first slot's proposal window's
  start for the attestations' sync delay. -/
  attesters : ∀ r' : ℕ, tAwakeEnd ≤ ((S.C.t_ (r' * S.C.R) : Time) : ℝ) →
    ∀ u : V, HonestActiveG S x (r' * S.C.R) u →
      RStsVariant2.UpAndHonestThroughoutG x
        ((proposal_window_start S.C ((r' + 1) * S.C.R) : Time) : ℝ)
        (((proposal_window_start S.C ((r' + 1) * S.C.R) : Time) : ℝ) + Δs_F) u

/-- `NoAttestationOfActionTickInHeldBlocks S tAwakeEnd x`: in the execution `x`, at every round `r'`
whose first slot `r' * S.C.R` starts at or after `tAwakeEnd` and whose proposer ran its proposal and
the slot's update up and honest (`HonestProposerToUpdateG`), no block that an honest active validator
`v` of that slot holds (the blocks `T` of its view) when it ticks at the reading of the round's
action time, the support cutoff of slot `r' * S.C.R + 1`, includes an attestation that some
validator `w` put on the wire, signed by itself, at a step at which it ticks at that same reading.

The variables: `S`, the setup; `tAwakeEnd`, the end of the healing phase; `x`, the execution.

Read aloud: an attestation sent at a round's action time is not already inside a block an honest
active validator holds when it ticks at that time.

Kind: a condition on executions (no step of `RStsVariant2` reads it; Goldilocks's claim for statement
3 takes it as an extra condition). -/
def NoAttestationOfActionTickInHeldBlocks {X L Ev : Type}
    [RStsVariant2.Observable X V (NamedObject V) L Ev] [NodeViewOf L (Block V)] (S : Setup V)
    (tAwakeEnd : ℝ) (x : X) : Prop :=
  ∀ r' : ℕ, tAwakeEnd ≤ ((S.C.t_ (r' * S.C.R) : Time) : ℝ) →
    HonestProposerToUpdateG S x (r' * S.C.R) →
    ∀ v : V, HonestActiveG S x (r' * S.C.R) v →
    ∀ (k : ℕ) (l : L), TickAtG x k v (S.C.t_ (r' * S.C.R + 1) + 2 * S.C.Δ).toNat →
      RStsVariant2.Observable.state x k v = some l →
    ∀ Z ∈ (NodeViewOf.view l).T, ∀ a ∈ Z.attestations,
    ∀ (j : ℕ) (w : V) (e : RStsVariant2.Envelope V (NamedObject V)),
      TickAtG x j w (S.C.t_ (r' * S.C.R + 1) + 2 * S.C.Δ).toNat →
      e ∈ RStsVariant2.Observable.sent x (j + 1) - RStsVariant2.Observable.sent x j →
      e.sender = w → e.msg ≠ NamedObject.attest a

/-- Goldilocks's network delivery delay per object on the run, from the delays `ΔNet` (a block or a
Goldfish vote) and `ΔNet_F` (an attestation) as the run read through the nodes' clocks counts them:
each less the clock's lead `ΔClockAhead`, as for `goldilocksΔSyncCatchUp`.

Read aloud: the network delivers blocks and votes within `ΔNet` less the clock's lead, attestations
within `ΔNet_F` less the clock's lead. -/
def goldilocksΔNetDelivery (ΔNet ΔNet_F : ℕ) (ΔClockAhead : ℝ) : NamedObject V → ℝ
  | .block _ => (ΔNet : ℝ) - ΔClockAhead
  | .gfVote _ => (ΔNet : ℝ) - ΔClockAhead
  | .attest _ => (ΔNet_F : ℝ) - ΔClockAhead

/-- What Goldilocks passes as `healingConditions` to the three statements after healing
(`LARuns.FinalizedCompatibleAfterHealingOnRuns`, `LARuns.ConfirmedTipAfterHealingOnRuns`,
`LARuns.FinalityLivenessAfterHealingOnRuns`): a predicate on the healing-phase segment. Its
conjuncts that read no trace are constants captured by the closure: Goldilocks's delays with room
for the clocks (`goldilocksDelayConditions`, the same as for statement 4). Its conjunct that reads
the segment: the honest round opening slots of the phase (`goldilocksOpeningsOn`).

Read aloud: Goldilocks's own premise on the healing phase for the statements after healing: its
constants, with room for the clocks, and honest round opening slots inside the phase. -/
def goldilocksAfterHealingConditions (S : Setup V) (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ)
    (ΔClockAhead ΔClockBehind tGAT tAwakeEnd : ℝ)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) : Prop :=
  goldilocksDelayConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind ∧
  goldilocksOpeningsOn S ΔClockAhead ΔClockBehind tGAT tAwakeEnd segment

/-- What Goldilocks passes as `healingConditions` to `LARuns.FinalityLivenessAfterHealingOnRuns`:
`goldilocksAfterHealingConditions`, and one more constant, that the attestations of a round reach
the next round's proposer even when it woke at the start of its proposal window, with room for its
clock (`Δ_F + Δ + ΔClockAhead + ΔClockBehind < 4Δ(k + 1)`).

Read aloud: the premise of the statements after healing, and room for a round's attestations to
reach the next proposer. -/
def goldilocksFinalityLivenessHealingConditions (S : Setup V) (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ)
    (ΔClockAhead ΔClockBehind tGAT tAwakeEnd : ℝ)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) : Prop :=
  goldilocksAfterHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind tGAT
    tAwakeEnd segment ∧
  ((S.C.Δ_F : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) + ΔClockAhead + ΔClockBehind <
    4 * ((S.C.Δ : Time) : ℝ) * (S.C.k + 1)

/-- `HonestOpenerOn S ΔClockAhead ΔClockBehind segment s`: on the segment, for clocks that lead the
real time by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`, the proposer of slot `s`,
`S.P.proposer s`, is awake and outside the corrupted set in every configuration in force at a time
from `ΔClockAhead` before the start of slot `s`'s proposal window,
`proposal_window_start S.C s − ΔClockAhead` (a node up from then ticks at the reading of that start),
to `ΔClockBehind` after the support cutoff of slot `s + 1`, `S.C.t_ (s + 1) + 2 * S.C.Δ + ΔClockBehind`
(its tick at the reading of that cutoff is at a real time at most that): every configuration `j` of
the segment entered at or before that end whose successor, when the segment shows it, is entered at
or after that start.

Read aloud: slot `s`'s proposer is up and honest from the clock's lead before its proposal window's
start to the clock's lag after the slot's update. -/
def HonestOpenerOn (S : Setup V) (ΔClockAhead ΔClockBehind : ℝ)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) (s : ℕ) : Prop :=
  ∀ (j : ℕ) (st : PhaseStep V (NamedObject V) (Block V)),
    segment j = some st →
    st.time ≤ ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind →
    (∀ st' : PhaseStep V (NamedObject V) (Block V), segment (j + 1) = some st' →
      ((proposal_window_start S.C s : Time) : ℝ) - ΔClockAhead ≤ st'.time) →
    S.P.proposer s ∈ st.awake ∧ S.P.proposer s ∉ st.corrupted

open Classical in
/-- `QuorumActiveOn S ΔClockAhead ΔClockBehind segment s`: on the segment, for clocks that lead the
real time by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`, at least a quorum of
validators (`Goldilocks.quorum V`) are honest active validators of slot `s`: awake in every
configuration in force at a time from `ΔClockAhead` before the start of the window of slot `s`'s
duties, `duty_window_start S.C s − ΔClockAhead`, to `ΔClockBehind` after the support cutoff of slot
`s + 1`, `S.C.t_ (s + 1) + 2 * S.C.Δ + ΔClockBehind`, and outside the corrupted set in every
configuration in force at a time at most that end.

Read aloud: a quorum of validators runs slot `s`'s duties awake and honest, from the clock's lead
before the duties' window to the clock's lag after the slot's update. -/
def QuorumActiveOn (S : Setup V) (ΔClockAhead ΔClockBehind : ℝ)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) (s : ℕ) : Prop :=
  Goldilocks.quorum V ≤
    (Finset.univ.filter fun v : V =>
      ∀ (j : ℕ) (st : PhaseStep V (NamedObject V) (Block V)),
        segment j = some st →
        st.time ≤ ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind →
        v ∉ st.corrupted ∧
        ((∀ st' : PhaseStep V (NamedObject V) (Block V), segment (j + 1) = some st' →
            ((duty_window_start S.C s : Time) : ℝ) - ΔClockAhead ≤ st'.time) →
          v ∈ st.awake)).card

/-- What Goldilocks passes as `finalityConditions` to `LARuns.FinalityLivenessAfterHealingOnRuns`,
for clocks that lead the real time by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`:
for the proposer requirement `p`, the window `[tWindowStart, tWindowEnd]` and its segment, `p` is
the requirement of some slot `s` for some block, and some round `r` with `s ≤ r * R` opens a
finality window inside `[tWindowStart, tWindowEnd]`: the proposal window of round `r`'s first slot
starts at least `ΔClockAhead` after `tWindowStart`, the update of round `r + 3`'s first slot (the
support cutoff of the slot after it) is at least `ΔClockBehind` before `tWindowEnd` (so the window
holds the windows `HonestOpenerOn` and `QuorumActiveOn` read), the first slots of the four rounds
`r` to `r + 3` have honest openers on the segment (`HonestOpenerOn`), and the first three have a
quorum of honest active validators (`QuorumActiveOn`), each read with the clock bounds.

Read aloud: four consecutive honest round opening slots with quorums at the first three follow the
proposal, inside the window. -/
def goldilocksFinalityConditions (S : Setup V) (ΔClockAhead ΔClockBehind : ℝ)
    (p : ProposerRequirement V (Block V))
    (tWindowStart tWindowEnd : ℝ)
    (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) : Prop :=
  ∃ (s r : ℕ) (B : Block V),
    -- `p` is slot `s`'s requirement for `B`
    p = goldilocksProposerReq S ΔClockAhead ΔClockBehind s B ∧
    -- round `r`'s first slot is at or after slot `s`
    s ≤ r * S.C.R ∧
    -- the proposal window of round `r`'s first slot starts at least `ΔClockAhead` after
    -- `tWindowStart`
    tWindowStart ≤ ((proposal_window_start S.C (r * S.C.R) : Time) : ℝ) - ΔClockAhead ∧
    -- the update of round `r + 3`'s first slot is at least `ΔClockBehind` before `tWindowEnd`
    ((S.C.t_ ((r + 3) * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ tWindowEnd ∧
    -- the first slots of the rounds `r` to `r + 3` have honest openers on the segment
    (∀ i : ℕ, i < 4 → HonestOpenerOn S ΔClockAhead ΔClockBehind segment ((r + i) * S.C.R)) ∧
    -- the first slots of the rounds `r` to `r + 2` have a quorum of honest active validators
    (∀ i : ℕ, i < 3 → QuorumActiveOn S ΔClockAhead ΔClockBehind segment ((r + i) * S.C.R))

end LARuns.GoldilocksInstance
