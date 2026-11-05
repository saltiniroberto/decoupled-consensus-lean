import LARuns.Statements.Statement4Defs
import LARuns.Bridge
import Mathlib.Data.NNReal.Defs

/-!
# Statement 4 over the runs of a protocol of `RStsVariant2`, read as observed

The statement takes a protocol `Pr` of the bare framework `RStsVariant2`, and reads it through
instances of two classes, each a reading of a protocol, not part of the bare framework
(`LARuns.Readers`): `NodeViewOf` on its node states (a single node state read as a view) and
`ProtocolCommittees` on `Pr` (the committees and the proposer requirements of each run); it reads the
blocks and messages through instances of the classes `LARuns.BlockVocab` and `LARuns.MessageVocab` on
their types, and quantifies over every run `π : Exec Pr` whose observed run `τ` meets a set of extra
conditions, `extraConditions`: a claim may first be proved for a more constrained environment and
the constraint later dropped by enriching the protocol, the enriched protocol's claim passing `∅`.

The run `π` as observed, with its committees, is `τ = observeWithCommittees π` (`LARuns.ObservedRunWithCommittees`, `LARuns.Bridge`, a
reading of an execution, not part of the bare framework): its observed run
`τ.run = RStsVariant2.observe NodeViewOf.view π` (the run's actions, the real times
of its configurations, and in each configuration each node's clock, the messages delivered to each
node, the envelopes sent, the corrupted set and the crashed set, with each node's local state
replaced by its view as `NodeViewOf` reads it: its finalized block, its confirmed tip and the blocks
it holds), with the run's committees `τ.committees = ProtocolCommittees.committees π` and its proposer
requirements `τ.proposerReqs tAwakeEnd = ProtocolCommittees.proposerReqs tAwakeEnd π` (the
requirements for a healing phase that ends at `tAwakeEnd`). It has no step relation. The statement
hands `τ`, and only `τ`, to every condition, to the segment and to the conclusions:

- the conditions on executions of `RStsVariant2`, in their forms over any execution with an
  `RStsVariant2.Observable`: those every top statement takes, gathered in
  `LARuns.TopStatementConditions` (`TickOncePerReadingG`, `ClockWithinSkew`, `ClockAdvancesWithin`,
  `TicksWithin`, `ActsWithinSkewG`, `UnforgeableSendsG`, `DeliveredBeforeActingG`, `CatchUpAfterRestartG`,
  `WeightBoundsG` (which reads a node's blocks through the class `RStsVariant2.BlockTree`, a view's
  tree being its `T`, `LARuns.Statements.Statement4Defs`, and a block's validator set
  through the class `RStsVariant2.BlockRegistry`, which the statement takes as an instance on the
  block type), `HealingPhaseG`, `CommitteeSleepinessFromG`), this statement's own
  (`HonestProposerThroughG`, `AsyncPeriodSleepinessG`) and its condition on the parameters
  `AsyncPeriodEndsInTime`; the two committee conditions read
  `τ`'s committees through the class `RStsVariant2.ObservableWithCommittees` (an extension of `Observable`
  with an execution's committees, whose instance on `ObservedRunWithCommittees` reads `τ.committees`, members
  computed from a node's view), the proposer requirements are `τ`'s, and a node's state is its view
  (the blocks `T` it holds); the two network conditions are read at the acting steps `TickStepG` (a
  node's completed ticks), so that a delivery is owed before each tick;
- the healing-phase segment and the conclusions (`LARuns.Statements.Statement4Defs`), read on `τ`, each written
  over any execution with an `Observable` whose nodes' states are read as views (`NodeViewOf`), so
  over a run too.

The same conditions apply to a run: `Exec Pr` has an instance of `ObservableWithCommittees` too (the
protocol's committees, members read through the view of a node's memory state). The segment and the
conclusions read a node's state through `NodeViewOf`, whose instance on a run's local state reads the
view of its memory state, so they apply to `π` as well.

The asynchronous period is `[tAsyncStart, tAsyncStart + ΔAsyncLength)`, given by its start
`tAsyncStart` and its length `ΔAsyncLength`. Every condition that reads the end of the period is
passed `tAsyncStart + ΔAsyncLength`.

The length `ΔAsyncLength` and the two clock bounds `ΔClockAhead`, `ΔClockBehind` have the type
`ℝ≥0` (`NNReal`, the reals at least `0`), so the type carries the bound `0 ≤ ·`; a condition on
executions that takes a real is passed the parameter's coercion to `ℝ`.

This page imports `LARuns.Statements.Statement4Defs` (the segment, the conclusions and, through it, the
conditions), `LARuns.Bridge` (`ObservedRunWithCommittees`, `observeWithCommittees`, the classes `NodeViewOf` and
`ProtocolCommittees`, `RStsVariant2`) and
`Mathlib.Data.NNReal.Defs` (the type `ℝ≥0`).
-/

set_option autoImplicit false

open scoped NNReal

namespace LARuns

open RStsVariant2 (Exec Protocol TickOncePerReadingG ClockWithinSkew
  ClockAdvancesWithin TicksWithin UnforgeableSendsG DeliveredBeforeActingG CatchUpAfterRestartG
  TickStepG deadlineOutside WeightBoundsG HealingPhaseG CommitteeSleepinessFromG
  HonestProposerThroughG AsyncPeriodEndsInTime AsyncPeriodSleepinessG BlockRegistry)

/-! ## The statement -/

/-- Top statement 4 over the runs of a protocol of `RStsVariant2`: for every run `π` of the protocol
`Pr` whose observed run `τ` (the run with each node's local state replaced by its view, with the run's
committees and proposer requirements) meets each extra condition in `extraConditions`, under the
hypotheses on `τ`, the block each proposer requirement names, once its honest proposer has
proposed it, survives the asynchronous period in the confirmed tips.

Read aloud: for every run of the protocol, seen through its nodes' views, that meets the extra
conditions, after a healing phase in which every honest node is online and up, with
committees mostly up and honest from `tGAT` on, any proposer that stays up and honest through its
window `[p.tProposalStart, p.tPreAsync]` and proposes its requirement's block `p.block` protects
`p.block` against one asynchronous period starting after `p.tPreAsync`, up to any time `t`, unless a
root collision hit by `t`.

Variables: the instance of `BlockRegistry` on `Block`, the validator set at each block; the
instances of `BlockVocab` on `Block` and `MessageVocab` on `Msg`, the ancestry and roots of blocks
and the block, proposed block, author, inclusions and conflicts of a message; `Pr`, the protocol; the instances of
`NodeViewOf` on its node states and `ProtocolCommittees` on `Pr`, a node state's view and each run's
committees and proposer requirements; `extraConditions`, the conditions on the observed runs a claim assumes
on top of the others (`∅` for none); `tGST`, the time from which the network is synchronous outside
the asynchronous period; `ΔSyncDelivery`, `ΔSyncCatchUp`, the delivery and catch-up delays per
message; `ΔClockAhead`, `ΔClockBehind`, how far a node's clock may run ahead of or lag the real time,
each of type `ℝ≥0`, so at least `0`; `tGAT`, `tAwakeEnd`, the start and the end of the healing
phase; `healingConditions`, the protocol's own premise on the healing-phase segment; `ΔPreAsync`,
the length of the window before a proposer's `tPreAsync`; `tAsyncStart`, `ΔAsyncLength`, the start and the length of the
asynchronous period `[tAsyncStart, tAsyncStart + ΔAsyncLength)`, the length of type `ℝ≥0`, so at
least `0`; `ΔRecovery`, how long after the end of the period, `tAsyncStart + ΔAsyncLength`, a
committee that needs synchrony until then still counts.

Kind: part of the statements. -/
noncomputable def ConfirmedPersistsThroughAsyncPeriodOnRuns {Node Msg NodeState Ev Block : Type}
    [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
    -- the validator set at each block (read by `WeightBoundsG`)
    [BlockRegistry Block Node]
    -- the ancestry and the roots of blocks (read by the conclusions)
    [BlockVocab Block]
    -- the block a message carries, the block it proposes, its author and its inclusions (read by
    -- `UnforgeableSendsG`, `RootCollisionBy` and the two conclusions)
    [MessageVocab Msg Node Block]
    -- the protocol of `RStsVariant2`
    (Pr : Protocol Node Msg NodeState Ev)
    -- a node state read as a view: its finalized block, its confirmed tip and the blocks it holds
    [NodeViewOf NodeState Block]
    -- each run's committees, and its proposer requirements for a healing phase ending at a time
    [ProtocolCommittees Pr Block]
    -- the extra conditions on the observed runs that the claim assumes, `∅` for none
    (extraConditions : Set (ObservedRunWithCommittees Node Msg Ev Block → Prop))
    -- the time from which the network is synchronous outside an asynchronous period
    (tGST : ℝ)
    -- the network's delivery delay, per message (read by `DeliveredBeforeActingG` and
    -- `CatchUpAfterRestartG`)
    (ΔSyncDelivery : (m : Msg) → ℝ)
    -- the catch-up delay, per message (read by `CatchUpAfterRestartG`)
    (ΔSyncCatchUp : (m : Msg) → ℝ)
    -- how far a node's clock may run ahead of the real time, at least `0` (the type `ℝ≥0` carries
    -- the bound)
    (ΔClockAhead : ℝ≥0)
    -- how far a node's clock may lag the real time, at least `0` (the type `ℝ≥0` carries the bound)
    (ΔClockBehind : ℝ≥0)
    -- the start of the healing phase
    (tGAT : ℝ)
    -- the end of the healing phase; the proposer requirements are those of the slots after it
    (tAwakeEnd : ℝ)
    -- the protocol's own premise, a property of the observed run within the healing phase only
    (healingConditions : (segment : (i : ℕ) → Option (PhaseStep Node Msg Block)) → Prop)
    -- the length of the window before a proposer's `tPreAsync` through which a node must have been
    -- up and honest to be counted in `AsyncPeriodSleepinessG`
    (ΔPreAsync : ℝ)
    -- the start of the asynchronous period
    (tAsyncStart : ℝ)
    -- the length of the asynchronous period, which is
    -- `[tAsyncStart, tAsyncStart + ΔAsyncLength)`, at least `0` (the type `ℝ≥0` carries the bound)
    (ΔAsyncLength : ℝ≥0)
    -- how long after the end of the asynchronous period, `tAsyncStart + ΔAsyncLength`, a committee
    -- that needs synchrony until then still counts in `AsyncPeriodSleepinessG`
    (ΔRecovery : ℝ) : Prop :=
  -- every run `π` of the protocol
  ∀ π : Exec Pr,
    -- `τ`, the run `π` as observed: the run with each node's local state replaced by its view, with the
    -- committees and the proposer requirements of `π`
    let τ : ObservedRunWithCommittees Node Msg Ev Block := observeWithCommittees π
    -- `τ` meets each extra condition the claim assumes (none when `extraConditions` is `∅`)
    (∀ condition ∈ extraConditions, condition τ) →
    -- the conditions every top statement takes: the clocks, unforgeability, the network delivering
    -- within `ΔSyncDelivery` of the later of a send and `tGST` and catching a restarted node up
    -- within `ΔSyncCatchUp` of its restart, except that what falls due inside the asynchronous
    -- period falls due after its end; the weight bounds at `tAwakeEnd`; the healing phase
    -- `[tGAT, tAwakeEnd]` with the protocol's premise on it; committee sleepiness from `tGAT`
    TopStatementConditions tGST
      (deadlineOutside tGST ΔSyncDelivery tAsyncStart (tAsyncStart + ΔAsyncLength))
      (deadlineOutside tGST ΔSyncCatchUp tAsyncStart (tAsyncStart + ΔAsyncLength))
      ΔClockAhead ΔClockBehind tGAT tAwakeEnd healingConditions τ →
    -- for every proposer requirement `p` of `τ`, for the healing phase that ends at `tAwakeEnd`
    ∀ p ∈ τ.proposerReqs tAwakeEnd,
      -- the proposer is up and honest from `p.tProposalStart` through `p.tPreAsync`, which is at
      -- or after `tAwakeEnd`
      HonestProposerThroughG tAwakeEnd p.tPreAsync p.tProposalStart p.proposer τ →
      -- the asynchronous period starts after `p.tPreAsync`
      p.tPreAsync < tAsyncStart →
      -- the asynchronous period and its recovery are over by `p.tPeriodEndBy`
      AsyncPeriodEndsInTime p.tPeriodEndBy (tAsyncStart + ΔAsyncLength) ΔRecovery →
      -- for every committee of `τ` that needs synchrony until a time in the asynchronous period
      -- or its recovery, as any honest node computes it from its view in `τ`, the members up and
      -- honest through `[p.tPreAsync − ΔPreAsync, p.tPreAsync]` and through its sleepiness window
      -- outnumber the rest
      AsyncPeriodSleepinessG p.tPreAsync ΔPreAsync tAsyncStart (tAsyncStart + ΔAsyncLength)
        ΔRecovery τ →
      -- the conclusion, at every real time `t`:
      ∀ t : ℝ,
        -- either, by `t`, two distinct blocks with one root were each held or sent by an honest node
        RootCollisionBy τ t ∨
        -- or, if the proposer `p.proposer`, while honest, proposed the block `p.block`, then
        -- `p.block` is, in every configuration entered within `[tAsyncStart, t]`, the confirmed tip or an
        -- ancestor of the confirmed tip of every honest node that was up and honest throughout
        -- `[p.tPreAsync − ΔPreAsync, p.tPreAsync]`
        (ConfirmedPersistsBetween τ p.tPreAsync ΔPreAsync tAsyncStart (tBy := t)
            p.proposer p.block ∧
          -- and, if `p.proposer`, while honest, proposed `p.block`, then `p.block` is compatible
          -- with the finalized block of every node honest in a configuration within
          -- `[tAsyncStart, t]`
          FinalizedCompatibleBetween τ tAsyncStart (tBy := t) p.proposer p.block)

#check @ConfirmedPersistsThroughAsyncPeriodOnRuns

end LARuns
