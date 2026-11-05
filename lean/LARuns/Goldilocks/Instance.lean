import LARuns.Statements.Statement1OnRuns
import LARuns.Statements.Statement2OnRuns
import LARuns.Statements.Statement3OnRuns
import LARuns.Statements.Statement4OnRuns
import LARuns.Statements.Statement5OnRuns
import LARuns.Statements.Statement6OnRuns
import LARuns.Statements.Statement7OnRuns
import LARuns.Goldilocks.Defs
import GoldilocksVariant.WiringDefs
import GoldilocksCorrectness.Record.ModelGoldilocks

/-!
# Goldilocks's claim, over the runs of its specification

Goldilocks's claim as statement 4 over runs, over Goldilocks's specification
(LConcrete): `ConfirmedPersistsThroughAsyncPeriodOnRuns` at Goldilocks's node wired as a protocol
of `RStsVariant2`, `goldilocksProtocol S`, with its instances of `LARuns.NodeViewOf` (which reads the
spec's node state `Goldilocks.NodeState V` as a view) and `LARuns.ProtocolCommittees` (its committees
and proposer requirements, the same in every run), over its runs, each read as observed,
`observeWithCommittees π` (each node's local state replaced by its view, with Goldilocks's committees and
proposer requirements), with five extra conditions on the observed runs
(`goldilocksConfirmedExtraConditions`): `ParentHeldAtDelivery`, the redelivery condition
`RedeliveredAfterReleaseFromDelivery` at Goldilocks's release readings, `HoldersStayOnline`,
`AdversaryLeavesQuorumBy` and `HoldersStayOnlineAfterHealing`; and the delays, the healing premise and
the recovery of `LARuns.Goldilocks.Defs`. The first two extra conditions are needed because of what
Goldilocks's wired protocol does: it runs its receive code at delivery, so it needs a block's parent
first and does not keep a message that arrives before its release reading; a protocol that keeps
early messages until their release does not need the second. The other three are conditions on the
environment: on when the validators that serve something are up, and on how many validators the
adversary corrupts by the end of the healing phase.

The section "The three statements after healing" holds Goldilocks's claims for statements 1 to 3
(`GoldilocksSatisfiesStatement1OnRuns`, `GoldilocksSatisfiesStatement2OnRuns`,
`GoldilocksSatisfiesStatement3OnRuns`): the first four extra conditions for statement 1
(`goldilocksAfterHealingExtraConditions`), the five for statement 2, and for statement 3 the five with
`FinalityHoldersStayOnline` and `NoAttestationOfActionTickInHeldBlocks`
(`goldilocksFinalityExtraConditions`); the redelivery delay a parameter, the network delays from two
numbers, and the premises of `LARuns.Goldilocks.Defs`'s section 4.

The section "The three statements without healing premises" holds Goldilocks's claims for
statements 5 to 7 (`GoldilocksSatisfiesStatement5OnRuns`, `GoldilocksSatisfiesStatement6OnRuns`,
`GoldilocksSatisfiesStatement7OnRuns`): no extra condition, and for statement 7 Goldilocks's
slashable evidence between two blocks, `GoldilocksCorrectness.Statements.Routines.SlashableBetween`.

The one thing read through `GoldilocksCorrectness`'s record is the wiring: no protocol of
`RStsVariant2` is stated directly on the spec, and the wiring `GoldilocksVariant.variantProtocolOf`
is stated for any model of the record; `goldilocksProtocol S` takes it at the spec's model
`GoldilocksCorrectness.Record.Model.goldilocks`, whose every member is the spec's definition (its
node state `Goldilocks.NodeState V`, its initial state `Goldilocks.initial`, its wake
`Goldilocks.wake`, its tick the outcomes of `Goldilocks.tick`, its receive
`Goldilocks.Sts.receive`).
-/

set_option autoImplicit false

open scoped NNReal

namespace LARuns.GoldilocksInstance

open Goldilocks (NamedObject RootOrder Block NodeState Time)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Goldilocks's specification with the setup `S`, as a protocol of `RStsVariant2`: the wiring
`GoldilocksVariant.variantProtocolOf` at the spec's model `Model.goldilocks`. Its node state is the
spec's `Goldilocks.NodeState V`; a validator that comes online at the clock value `t` starts in
`Goldilocks.wake (Goldilocks.initial S.C v) t`; a step runs the spec's tick or receive routine; a restart with the boot reading `t` gives
`Goldilocks.wake n t`.

Read aloud: Goldilocks's node, as a protocol of the framework. -/
noncomputable def goldilocksProtocol (S : Setup V) :
    RStsVariant2.Protocol V (NamedObject V) (NodeState V) Empty :=
  GoldilocksVariant.variantProtocolOf GoldilocksCorrectness.Record.Model.goldilocks S

/-- Goldilocks's node state `n` read as a view: its finalized block `n.S.F`, its confirmed tip
`Goldilocks.ac_confirmed n.A (Goldilocks.fg_to_ac n.S)` and its tree `n.S.T`, the spec's fields and
readers.

Read aloud: Goldilocks's node states as views. -/
instance : NodeViewOf (NodeState V) (Block V) where
  view n := { F := n.S.F, C := Goldilocks.ac_confirmed n.A (Goldilocks.fg_to_ac n.S), T := n.S.T }

/-- Goldilocks's committees and proposer requirements, in every run `π` of `goldilocksProtocol S`, for
clocks that lead the real time by at most `ΔClockAhead` and lag it by at most `ΔClockBehind`: its
committees `goldilocksCommitteeSpecs S ΔClockAhead ΔClockBehind`, which come from the setup `S`, so every run gives the same
ones; and for a healing phase that ends at `tAwakeEnd` its proposer requirements
`goldilocksProposerReqs S ΔClockAhead ΔClockBehind tAwakeEnd π`, one per slot that starts after `tAwakeEnd` and per block its
proposer sent in `π` at its tick at the start of that slot. A definition, not an instance: the
committees' windows read the clock bound, which the claims pass (`letI`).

Read aloud: in every run, Goldilocks's committees, and its proposers after healing with the blocks
they proposed. -/
@[reducible] def goldilocksProtocolCommittees (S : Setup V) (ΔClockAhead ΔClockBehind : ℝ) :
    ProtocolCommittees (goldilocksProtocol S) (Block V) where
  committees _ := goldilocksCommitteeSpecs S ΔClockAhead ΔClockBehind
  proposerReqs tAwakeEnd π := goldilocksProposerReqs S ΔClockAhead ΔClockBehind tAwakeEnd π
  updateReadings c :=
    ∃ σ : ℕ, c = (GoldilocksCorrectness.Record.Model.goldilocks (V := V)).supportCutoff S.C (σ + 1)

/-- In the execution `τ`, any execution with an `RStsVariant2.Observable` whose nodes' states are
read as views (`NodeViewOf`: a run, an observed run, or an `ObservedRunWithCommittees`), a block delivered to a
validator reaches it only once the validator holds the block's parent, unless the block conflicts
with the validator's finalized block: at every step `j` that delivers the envelope `e` carrying the
block `B` (not genesis) to `v`, if the view `NodeViewOf.view l` of `v`'s state `l` in configuration
`j` (before the delivery) has a finalized block compatible with `B`, then `B`'s parent is among the
blocks `T` of that view. A condition on
executions (no step of `RStsVariant2` reads it): it reads the delivery step and the node's view.

Read aloud: a block that does not conflict with a validator's finalized block reaches that validator
only once the validator holds its parent. -/
def ParentHeldAtDelivery {X L : Type}
    [RStsVariant2.Observable X V (NamedObject V) L Empty] [NodeViewOf L (Block V)] (τ : X) : Prop :=
  ∀ (j : ℕ) (v : V) (e : RStsVariant2.Envelope V (NamedObject V)) (B : Block V) (l : L),
    RStsVariant2.Observable.lbl τ j = .deliver v e → RStsVariant2.Observable.state τ j v = some l →
    e.msg = NamedObject.block B → B ≠ Block.genesis →
    (NodeViewOf.view l).F.compatible B = true →
    B.parent ∈ (NodeViewOf.view l).T

/-- The extra conditions Goldilocks's four claims with a healing phase take on its observed runs:
`ParentHeldAtDelivery`, `RedeliveredAfterReleaseFromDelivery` at Goldilocks's release readings
`goldilocksRelease S` with a redelivery within `ΔRedeliver`, `HoldersStayOnline` at the sync
delays `Δs`, `Δs_F`, the clock's lag bound `ΔClockBehind` and the healing phase `[tGAT, tAwakeEnd]`,
and `AdversaryLeavesQuorumBy` at the end of the healing phase `tAwakeEnd`.

Read aloud: deliveries are parent-first, a message that arrived before its release is delivered
again within `ΔRedeliver` once the receiver has ticked at or past the release, the validators
that serve something stay up and honest for the sync delay after serving, and the validators never
corrupted by the end of the healing phase can form a quorum. -/
def goldilocksAfterHealingExtraConditions (S : Setup V) (Δs Δs_F ΔRedeliver : ℕ)
    (ΔClockBehind tGAT tAwakeEnd : ℝ) :
    Set (ObservedRunWithCommittees V (NamedObject V) Empty (Block V) → Prop) :=
  {ParentHeldAtDelivery,
    fun τ => RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ) τ,
    fun τ => HoldersStayOnline S Δs Δs_F ΔClockBehind tGAT tAwakeEnd τ,
    fun τ => AdversaryLeavesQuorumBy tAwakeEnd τ}

/-- The extra conditions Goldilocks's claims for statements 2 and 4 take on its observed runs:
`goldilocksAfterHealingExtraConditions`, and `HoldersStayOnlineAfterHealing` at the sync delay `Δs`
and the end of the healing phase `tAwakeEnd`.

Read aloud: the extra conditions of statement 1, and after the healing phase the honest active
committee members and the honest proposers stay up and honest for the sync delay after the time
their votes and blocks are read. -/
def goldilocksConfirmedExtraConditions (S : Setup V) (Δs Δs_F ΔRedeliver : ℕ)
    (ΔClockBehind tGAT tAwakeEnd : ℝ) :
    Set (ObservedRunWithCommittees V (NamedObject V) Empty (Block V) → Prop) :=
  insert (fun τ => HoldersStayOnlineAfterHealing S Δs tAwakeEnd τ)
    (goldilocksAfterHealingExtraConditions S Δs Δs_F ΔRedeliver ΔClockBehind tGAT tAwakeEnd)

/-- The extra conditions Goldilocks's claim for statement 3 takes on its observed runs:
`goldilocksConfirmedExtraConditions`, `FinalityHoldersStayOnline` at the sync delays `Δs`, `Δs_F`
and the end of the healing phase `tAwakeEnd`, and `NoAttestationOfActionTickInHeldBlocks` at
`tAwakeEnd`.

Read aloud: the extra conditions of statement 2; after the healing phase, the validators that run a
slot's or a round's duties stay up and honest until what they sent has reached the next ones; and an
attestation sent at a round's action time is not already inside a block an honest active validator
holds when it ticks at that time. -/
def goldilocksFinalityExtraConditions (S : Setup V) (Δs Δs_F ΔRedeliver : ℕ)
    (ΔClockBehind tGAT tAwakeEnd : ℝ) :
    Set (ObservedRunWithCommittees V (NamedObject V) Empty (Block V) → Prop) :=
  insert (fun τ => NoAttestationOfActionTickInHeldBlocks S tAwakeEnd τ)
    (insert (fun τ => FinalityHoldersStayOnline S Δs Δs_F tAwakeEnd τ)
      (goldilocksConfirmedExtraConditions S Δs Δs_F ΔRedeliver ΔClockBehind tGAT tAwakeEnd))

/-- Goldilocks's specification satisfies statement 4 over its runs:
`ConfirmedPersistsThroughAsyncPeriodOnRuns` at `goldilocksProtocol S` (with Goldilocks's instances of
`NodeViewOf` and `ProtocolCommittees`, the committees' windows at the clock bound `ΔClockBehind`),
with the extra conditions on its observed runs (`ObservedRunWithCommittees`)
`goldilocksConfirmedExtraConditions`, the network delays `ΔNet` and `ΔNet_F` and the catch-up
delays `Δs` and `Δs_F` per object (each as the run read through the nodes' clocks counts it, the
run's promise being that delay less `ΔClockAhead`), Goldilocks's healing premise with room for the
clocks and the recovery `max S.C.Δ Δs − S.C.Δ`. A `Prop`, not a theorem: nothing is proved here.

Read aloud: for every run of Goldilocks's node, seen through its nodes' views with Goldilocks's
committees and proposer requirements, whose deliveries are
parent-first, in which a message that arrived before its release is delivered again within
`ΔRedeliver` once the receiver has ticked at or past the release, in which the validators that
serve something stay up and honest for the sync delay after serving, in which the validators
never corrupted by the end of the healing phase can form a quorum, and in which, after the healing
phase, the honest active committee members and the honest proposers stay up and honest for the sync
delay after the time their votes and blocks are read, after a healing phase with
honest round opening slots, any slot's proposer that stays up and honest from `ΔClockAhead` before its
proposal window's start through the hand-over update protects the block it proposed at its tick at the start of its slot against one
asynchronous period starting after the hand-over update, unless a root collision hits. -/
noncomputable def GoldilocksSatisfiesStatement4OnRuns (S : Setup V)
    (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ) (tGST : ℝ)
    -- the clock bounds, each at least `0` (the type `ℝ≥0` carries the bound)
    (ΔClockAhead ΔClockBehind : ℝ≥0)
    (tGAT tAwakeEnd ΔPreAsync tAsyncStart : ℝ)
    -- the length of the asynchronous period, at least `0` (the type `ℝ≥0` carries the bound)
    (ΔAsyncLength : ℝ≥0) : Prop :=
  letI := goldilocksProtocolCommittees S ΔClockAhead ΔClockBehind
  ConfirmedPersistsThroughAsyncPeriodOnRuns (goldilocksProtocol S)
    (goldilocksConfirmedExtraConditions S Δs Δs_F ΔRedeliver ΔClockBehind tGAT tAwakeEnd)
    tGST
    (ΔSyncDelivery := goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
    (ΔSyncCatchUp := goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
    ΔClockAhead ΔClockBehind
    tGAT tAwakeEnd
    (goldilocksHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind ΔPreAsync
      tGAT tAwakeEnd)
    ΔPreAsync tAsyncStart ΔAsyncLength
    (ΔRecovery := max ((S.C.Δ : Time) : ℝ) Δs - ((S.C.Δ : Time) : ℝ))

#check @GoldilocksSatisfiesStatement4OnRuns

/-! ## The three statements after healing -/

/-- Goldilocks's specification satisfies statement 1 over its runs, finality safety after healing:
`FinalizedCompatibleAfterHealingOnRuns` at `goldilocksProtocol S` (with Goldilocks's instances of
`NodeViewOf` and `ProtocolCommittees`, the committees' windows at the clock bound `ΔClockBehind`),
with the extra conditions `goldilocksAfterHealingExtraConditions`, the network delays `ΔNet` and
`ΔNet_F` and the catch-up delays `Δs` and `Δs_F` per object (each as the run read through the
nodes' clocks counts it, the run's promise being that delay less `ΔClockAhead`), and Goldilocks's healing premise with room for the
clocks, `goldilocksAfterHealingConditions`. A `Prop`, not a theorem: nothing is proved here.

Read aloud: for every run of Goldilocks's node, seen through its nodes' views with Goldilocks's
committees, whose deliveries are parent-first, in which early messages are delivered again
after their release, and in which the validators never corrupted by the end of the healing phase
can form a quorum, after a healing phase with honest round opening slots, no two honest nodes
have finalized conflicting blocks, unless a root collision hits. -/
noncomputable def GoldilocksSatisfiesStatement1OnRuns (S : Setup V)
    (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ) (tGST : ℝ)
    -- the clock bounds, each at least `0` (the type `ℝ≥0` carries the bound)
    (ΔClockAhead ΔClockBehind : ℝ≥0) (tGAT tAwakeEnd : ℝ) : Prop :=
  letI := goldilocksProtocolCommittees S ΔClockAhead ΔClockBehind
  FinalizedCompatibleAfterHealingOnRuns (goldilocksProtocol S)
    (goldilocksAfterHealingExtraConditions S Δs Δs_F ΔRedeliver ΔClockBehind tGAT tAwakeEnd)
    tGST
    (ΔSyncDelivery := goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
    (ΔSyncCatchUp := goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
    ΔClockAhead ΔClockBehind
    tGAT tAwakeEnd
    (goldilocksAfterHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind
      tGAT tAwakeEnd)

#check @GoldilocksSatisfiesStatement1OnRuns

/-- Goldilocks's specification satisfies statement 2 over its runs, the confirmed tip after
healing: `ConfirmedTipAfterHealingOnRuns` at `goldilocksProtocol S` (with Goldilocks's instances of
`NodeViewOf` and `ProtocolCommittees`), with the extra conditions `goldilocksConfirmedExtraConditions`
and the same delays and healing premise as `GoldilocksSatisfiesStatement1OnRuns`. A `Prop`, not a
theorem: nothing is proved here.

Read aloud: for every run of Goldilocks's node, seen through its nodes' views with Goldilocks's
committees and proposer requirements, whose deliveries are parent-first, in which early
messages are delivered again after their release, in which the validators never corrupted by the
end of the healing phase can form a quorum, and in which, after the healing phase, the honest active
committee members and the honest proposers stay up and honest for the sync delay after the time their
votes and blocks are read, after a healing phase with honest round opening slots, honest nodes agree
on the confirmed tip, it only grows, and every block a slot's proposer
proposed at its tick at the start of its slot, staying up and honest through the hand-over update,
joins it and strictly extends what was confirmed before it, unless a root collision hits. -/
noncomputable def GoldilocksSatisfiesStatement2OnRuns (S : Setup V)
    (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ) (tGST : ℝ)
    -- the clock bounds, each at least `0` (the type `ℝ≥0` carries the bound)
    (ΔClockAhead ΔClockBehind : ℝ≥0) (tGAT tAwakeEnd : ℝ) : Prop :=
  letI := goldilocksProtocolCommittees S ΔClockAhead ΔClockBehind
  ConfirmedTipAfterHealingOnRuns (goldilocksProtocol S)
    (goldilocksConfirmedExtraConditions S Δs Δs_F ΔRedeliver ΔClockBehind tGAT tAwakeEnd)
    tGST
    (ΔSyncDelivery := goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
    (ΔSyncCatchUp := goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
    ΔClockAhead ΔClockBehind
    tGAT tAwakeEnd
    (goldilocksAfterHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind
      tGAT tAwakeEnd)

#check @GoldilocksSatisfiesStatement2OnRuns

/-- Goldilocks's specification satisfies statement 3 over its runs, finality liveness after
healing: `FinalityLivenessAfterHealingOnRuns` at `goldilocksProtocol S` (with Goldilocks's
instances of `NodeViewOf` and `ProtocolCommittees`), with the extra conditions
`goldilocksFinalityExtraConditions`, the same delays as `GoldilocksSatisfiesStatement1OnRuns`, its
healing premise with room for the clocks and for a
round's attestations to reach the next proposer (`goldilocksFinalityLivenessHealingConditions`),
its finality premise on a window (`goldilocksFinalityConditions`: four consecutive honest round
opening slots with quorums at the first three) and the delay `max S.C.Δ Δs + ΔClockBehind` a node
must have been up and honest for, from the clock value of one of its ticks after the window. A
`Prop`, not a theorem: nothing is proved here.

Read aloud: for every run of Goldilocks's node, seen through its nodes' views with Goldilocks's
committees and proposer requirements, whose deliveries are parent-first, in which early
messages are delivered again after their release, in which the validators never corrupted by the
end of the healing phase can form a quorum, in which, after the healing phase, the validators that
run a slot's or a round's duties stay up and honest until what they sent has reached the next ones,
and in which an attestation sent at a round's action time is not already inside a block an honest
active validator holds when it ticks at that time, after a healing phase with honest round opening
slots, whenever four consecutive honest round opening slots with quorums at the first three follow
a block a slot's proposer proposed at its tick at the start of its slot, every node up and honest
for `max Δ Δs` plus the clock's lag, from one of its ticks after the fourth, has finalized that
block or a descendant of it, a block nobody had finalized before, which strictly extends every
finalized block honest nodes had before the proposal, unless a root collision hits. -/
noncomputable def GoldilocksSatisfiesStatement3OnRuns (S : Setup V)
    (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ) (tGST : ℝ)
    -- the clock bounds, each at least `0` (the type `ℝ≥0` carries the bound)
    (ΔClockAhead ΔClockBehind : ℝ≥0) (tGAT tAwakeEnd : ℝ) : Prop :=
  letI := goldilocksProtocolCommittees S ΔClockAhead ΔClockBehind
  FinalityLivenessAfterHealingOnRuns (goldilocksProtocol S)
    (goldilocksFinalityExtraConditions S Δs Δs_F ΔRedeliver ΔClockBehind tGAT tAwakeEnd)
    tGST
    (ΔSyncDelivery := goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
    (ΔSyncCatchUp := goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
    ΔClockAhead ΔClockBehind
    tGAT tAwakeEnd
    (goldilocksFinalityLivenessHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd)
    (goldilocksFinalityConditions S ΔClockAhead ΔClockBehind)
    (ΔFinalityDelivery := max ((S.C.Δ : Time) : ℝ) Δs + ΔClockBehind)

#check @GoldilocksSatisfiesStatement3OnRuns

/-! ## The three statements without healing premises -/

/-- Goldilocks's specification satisfies statement 5 over its runs, the finalized block on the
confirmed tip's chain: `FinalizedOnConfirmedChainOnRuns` at `goldilocksProtocol S` (with
Goldilocks's instance of `NodeViewOf`), with no extra condition. A `Prop`, not a theorem: nothing is
proved here.

Read aloud: in every run of Goldilocks's node, seen through its nodes' views, an honest node's
finalized block is always its confirmed tip or an ancestor of it. -/
def GoldilocksSatisfiesStatement5OnRuns (S : Setup V) : Prop :=
  FinalizedOnConfirmedChainOnRuns (goldilocksProtocol S) ∅

#check @GoldilocksSatisfiesStatement5OnRuns

/-- Goldilocks's specification satisfies statement 6 over its runs, the finalized block only
extends: `FinalizedOnlyExtendsOnRuns` at `goldilocksProtocol S` (with Goldilocks's instance of
`NodeViewOf`), with no extra condition. A `Prop`, not a theorem: nothing is proved here.

Read aloud: in every run of Goldilocks's node, seen through its nodes' views, an honest node never
abandons a block it has finalized. -/
def GoldilocksSatisfiesStatement6OnRuns (S : Setup V) : Prop :=
  FinalizedOnlyExtendsOnRuns (goldilocksProtocol S) ∅

#check @GoldilocksSatisfiesStatement6OnRuns

/-- Goldilocks's specification satisfies statement 7 over its runs, finalized blocks agree unless
there is slashable evidence: `FinalizedCompatibleUnlessSlashableOnRuns` at `goldilocksProtocol S`
(with Goldilocks's instance of `NodeViewOf`), with no extra condition and Goldilocks's slashable
evidence `GoldilocksCorrectness.Statements.Routines.SlashableBetween`: at least
`2 * quorum V - validator_count V` validators each signed two attestations, one included in each of
the two chains, that together meet `E1` or `E2`. A `Prop`, not a theorem: nothing is proved here.

Read aloud: in every run of Goldilocks's node, seen through its nodes' views, with no slashable
evidence between the blocks honest nodes hold, no two honest nodes finalize conflicting blocks,
unless a root collision hits the blocks they hold. -/
def GoldilocksSatisfiesStatement7OnRuns (S : Setup V) : Prop :=
  FinalizedCompatibleUnlessSlashableOnRuns (goldilocksProtocol S) ∅
    GoldilocksCorrectness.Statements.Routines.SlashableBetween

#check @GoldilocksSatisfiesStatement7OnRuns

end LARuns.GoldilocksInstance
