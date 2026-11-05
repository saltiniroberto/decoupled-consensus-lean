import LARuns.Statements.Statement3Defs
import LARuns.Bridge

/-!
# Statement 3, finality liveness after healing, over the runs of a protocol of `RStsVariant2`

The statement takes a protocol `Pr` of the bare framework `RStsVariant2` and reads it as statement 4
does (`LARuns.Statements.Statement4OnRuns`): through the classes `NodeViewOf` and
`ProtocolCommittees`, the vocabularies `BlockVocab` and `MessageVocab`, and over every run
`π : Exec Pr` as observed, `τ = observeWithCommittees π`, that meets a set of extra conditions.

The conditions on `τ` are those every top statement takes, `TopStatementConditions`
(`LARuns.Statements.Statement4Defs`), at the deadlines of a network synchronous from `tGST` on
(`RStsVariant2.syncDeadline`): there is no asynchronous period.

The protocol supplies, besides what statement 4's protocol supplies, its premise on a finality
window: `finalityConditions p tWindowStart tWindowEnd segment`, a property of the observed run
within `[tWindowStart, tWindowEnd]` only (read through `phaseSegment`, as `healingConditions` is),
under which the block the proposer requirement `p` names is finalized by the window's end; and
`ΔFinalityDelivery`, how long a node must have been up and honest, from the clock value of one of
its ticks at or after the window's end, to hold that finalization.

The conclusion, at every real time `t` after the healing phase at which no update is half run
(`SettledAtG`, read at the update readings `ProtocolCommittees.updateReadings Pr`): either a root
collision has hit by `t` (`RootCollisionBy`), or for every proposer requirement `p` of `τ` whose
proposer is up and honest through its window and every window `[tWindowStart, tWindowEnd]` after
the healing phase and ending by `t` on which the protocol's finality premise holds, the block
`p.block`, once `p.proposer` proposed it, is finalized by every node up and honest for
`ΔFinalityDelivery` after the window, a new block (`FinalizedIncludedBetween`), which strictly
extends every finalized block an honest node had while its clock was before the proposal's reading
(`FinalizedExtendedBetween`); both on `LARuns.Statements.Statement3Defs`.

Each proposer requirement is read without an asynchronous period: `p.tPreAsync` is the time of the
proposer's hand-over, the end of the window `[p.tProposalStart, p.tPreAsync]` through which it must
be up and honest; `p.tPeriodEndBy` is not read.

This page imports `LARuns.Statements.Statement3Defs` (the conclusions and, through it,
`LARuns.Statements.Statement4Defs`) and `LARuns.Bridge`.
-/

set_option autoImplicit false

open scoped NNReal

namespace LARuns

open RStsVariant2 (Exec Protocol syncDeadline BlockRegistry HonestProposerThroughG)

/-! ## The statement -/

/-- Top statement 3 over the runs of a protocol of `RStsVariant2`, finality liveness after healing:
for every run `π` of the protocol `Pr` whose observed run `τ` meets each extra condition in
`extraConditions` and the conditions every top statement takes, at every real time `t` after the
healing phase at which no update is half run, either a root collision has hit by `t`, or every block an honest proposer
proposed, as its requirement names it, that is followed by a window on which the protocol's
finality premise holds is finalized by every node up and honest for `ΔFinalityDelivery` after that
window, a new block that strictly extends every finalized block honest nodes had before the
proposal.

Read aloud: for every run of the protocol, seen through its nodes' views, that meets the extra
conditions, after a healing phase in which every honest node is online and up, with
committees mostly up and honest from `tGAT` on, whenever a window on which the protocol's finality
premise holds follows an honest proposal, every node up and honest for `ΔFinalityDelivery` after
the window has finalized that proposal or a descendant of it, a block nobody had finalized before,
which strictly extends every finalized block honest nodes had before the proposal, unless a root
collision hit by then.

Variables: the instance of `BlockRegistry` on `Block`, the validator set at each block; the
instances of `BlockVocab` on `Block` and `MessageVocab` on `Msg`, the ancestry and roots of blocks
and the block, proposed block, author, inclusions and conflicts of a message; `Pr`, the protocol;
the instances of `NodeViewOf` on its node states and `ProtocolCommittees` on `Pr`, a node state's
view and each run's committees and proposer requirements; `extraConditions`, the conditions on the
observed runs a claim assumes on top of the others (`∅` for none); `tGST`, the time from which the
network is synchronous; `ΔSyncDelivery`, `ΔSyncCatchUp`, the delivery and catch-up delays per
message; `ΔClockAhead`, `ΔClockBehind`, how far a node's clock may run ahead of or lag the real
time, each of type `ℝ≥0`, so at least `0`; `tGAT`, `tAwakeEnd`, the start and the end of the
healing phase; `healingConditions`, the protocol's own premise on the healing-phase segment;
`finalityConditions`, the protocol's own premise on a finality window for a proposer requirement;
`ΔFinalityDelivery`, how long a node must have been up and honest after the window to hold the
finalization.

Kind: part of the statements. -/
noncomputable def FinalityLivenessAfterHealingOnRuns {Node Msg NodeState Ev Block : Type}
    [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
    -- the validator set at each block (read by `WeightBoundsG`)
    [BlockRegistry Block Node]
    -- the ancestry and the roots of blocks (read by the conclusions)
    [BlockVocab Block]
    -- the block a message carries, the block it proposes, its author and its inclusions (read by
    -- `UnforgeableSendsG`, `RootCollisionBy` and the conclusions)
    [MessageVocab Msg Node Block]
    -- the protocol of `RStsVariant2`
    (Pr : Protocol Node Msg NodeState Ev)
    -- a node state read as a view: its finalized block, its confirmed tip and the blocks it holds
    [NodeViewOf NodeState Block]
    -- each run's committees, and its proposer requirements for a healing phase ending at a time
    [ProtocolCommittees Pr Block]
    -- the extra conditions on the observed runs that the claim assumes, `∅` for none
    (extraConditions : Set (ObservedRunWithCommittees Node Msg Ev Block → Prop))
    -- the time from which the network is synchronous
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
    -- the protocol's own premise on a finality window `[tWindowStart, tWindowEnd]` for the
    -- proposer requirement `p`, a property of the observed run within the window only, under
    -- which `p.block` is finalized by `tWindowEnd`
    (finalityConditions : (p : ProposerRequirement Node Block) → (tWindowStart tWindowEnd : ℝ) →
      (segment : (i : ℕ) → Option (PhaseStep Node Msg Block)) → Prop)
    -- how long a node must have been up and honest, from the clock value of one of its ticks at or
    -- after the window's end, to hold the finalization
    (ΔFinalityDelivery : ℝ) : Prop :=
  -- every run `π` of the protocol
  ∀ π : Exec Pr,
    -- `τ`, the run `π` as observed: the run with each node's local state replaced by its view, with the
    -- committees and the proposer requirements of `π`
    let τ : ObservedRunWithCommittees Node Msg Ev Block := observeWithCommittees π
    -- `τ` meets each extra condition the claim assumes (none when `extraConditions` is `∅`)
    (∀ condition ∈ extraConditions, condition τ) →
    -- the conditions every top statement takes: the clocks, unforgeability, the network delivering
    -- within `ΔSyncDelivery` of the later of a send and `tGST` and catching a restarted node up
    -- within `ΔSyncCatchUp` of its restart; the weight bounds at `tAwakeEnd`; the healing phase
    -- `[tGAT, tAwakeEnd]` with the protocol's premise on it; committee sleepiness from `tGAT`
    TopStatementConditions tGST (syncDeadline tGST ΔSyncDelivery) (syncDeadline tGST ΔSyncCatchUp)
      ΔClockAhead ΔClockBehind tGAT tAwakeEnd healingConditions τ →
    -- the conclusion, at every real time `t` from the end of the healing phase on at which no
    -- update is half run:
    ∀ t : ℝ, tAwakeEnd ≤ t → SettledAtG (ProtocolCommittees.updateReadings Pr) τ t →
      -- either, by `t`, two distinct blocks with one root were each held or sent by an honest node
      RootCollisionBy τ t ∨
      -- or, for every proposer requirement `p` of `τ`, for the healing phase that ends at
      -- `tAwakeEnd`
      ∀ p ∈ τ.proposerReqs tAwakeEnd,
        -- whose proposer is up and honest from `p.tProposalStart` through its hand-over
        -- `p.tPreAsync`, which is at or after `tAwakeEnd`
        HonestProposerThroughG tAwakeEnd p.tPreAsync p.tProposalStart p.proposer τ →
        -- for every window `[tWindowStart, tWindowEnd]`
        ∀ tWindowStart tWindowEnd : ℝ,
          -- that starts at or after the end of the healing phase
          tAwakeEnd ≤ tWindowStart →
          -- and ends at or before `t`
          tWindowEnd ≤ t →
          -- on which the protocol's finality premise for `p` holds, read on the observed run
          -- within the window only
          finalityConditions p tWindowStart tWindowEnd
            (phaseSegment τ (tStart := tWindowStart) (tEnd := tWindowEnd)) →
          -- once `p.proposer`, while honest, proposed `p.block`, every node up and honest for
          -- `ΔFinalityDelivery` from one of its ticks at or after `tWindowEnd` has, up to `t`,
          -- finalized `p.block` or a descendant of it, a block nobody had finalized at the proposal
          FinalizedIncludedBetween τ tWindowEnd ΔFinalityDelivery (tBy := t) p.proposer p.block ∧
            -- and that finalized block strictly extends the finalized block of every honest node
            -- whose clock read less than the proposal's reading, from `tAwakeEnd` up to `t`
            FinalizedExtendedBetween τ tAwakeEnd tWindowEnd ΔFinalityDelivery (tBy := t)
              p.proposer p.block

#check @FinalityLivenessAfterHealingOnRuns

end LARuns
