import LARuns.Goldilocks.Instance

/-!
# The proofs about LARuns's Goldilocks pages

This page holds the proofs about the pages it imports: `LARuns.Goldilocks.Defs` and
`LARuns.Goldilocks.Instance`. Those pages define and prove nothing; every theorem and example about
them is here.

What it holds: the example that writes out Goldilocks's claim over its runs, read through their observed
runs,
`GoldilocksSatisfiesStatement4OnRuns`, over Goldilocks's specification (LConcrete), with every
argument Goldilocks passes put in place, checked against the definition by `Iff.rfl`.
-/

set_option autoImplicit false

open scoped NNReal

namespace LARuns.GoldilocksInstance

open Goldilocks (NamedObject RootOrder Block NodeState Time)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## Example: statement 4 over the runs of Goldilocks's specification, written out

`GoldilocksSatisfiesStatement4OnRuns` is one application of
`ConfirmedPersistsThroughAsyncPeriodOnRuns`, over Goldilocks's specification (LConcrete): the
protocol is Goldilocks's node wired as a protocol of `RStsVariant2`, `goldilocksProtocol S`, whose
node state is `Goldilocks.NodeState V`, read as observed, `τ = observeWithCommittees π`, for each run
`π`. The
example states, without proving it, the same claim written out: every argument Goldilocks passes put
in place, every hypothesis on `τ` (Goldilocks's committees and proposer requirements are the same in
every run `π`, and `τ` carries them), and the four extra conditions on the observed runs,
`ParentHeldAtDelivery`, `RedeliveredAfterReleaseFromDelivery` at Goldilocks's release readings,
`HoldersStayOnline` and `AdversaryLeavesQuorumBy`. Its proof `Iff.rfl` only checks that the text written out is the
definition's; nothing about Goldilocks is proved. -/

section Example

open LARuns

example (S : Setup V) (Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ)
    (tGST : ℝ) (ΔClockAhead ΔClockBehind : ℝ≥0)
    (tGAT tAwakeEnd ΔPreAsync tAsyncStart : ℝ) (ΔAsyncLength : ℝ≥0) :
    GoldilocksSatisfiesStatement4OnRuns S Δs Δs_F ΔNet ΔNet_F ΔRedeliver tGST ΔClockAhead
        ΔClockBehind tGAT tAwakeEnd ΔPreAsync tAsyncStart ΔAsyncLength ↔
      -- every run `π` of Goldilocks's specification, wired as a protocol of `RStsVariant2`
      -- (`goldilocksProtocol S`), whose observed run `τ` (the run, each node's local state replaced by its
      -- view, with Goldilocks's committees and proposer requirements) is one in which a block reaches a validator only once the validator
      -- holds its parent, a message that arrived before its release reading is delivered again
      -- within `ΔRedeliver` of the receiver's first tick at or past that reading, the
      -- validators that serve something stay up and honest for the sync delay after serving, the
      -- validators never corrupted by the end of the healing phase can form a quorum, and after the
      -- healing phase the honest active committee members and the honest proposers stay up and
      -- honest for the sync delay after the time their votes and blocks are read
      letI := goldilocksProtocolCommittees S ΔClockAhead ΔClockBehind
      ∀ π : RStsVariant2.Exec (goldilocksProtocol S),
        let τ : ObservedRunWithCommittees V (NamedObject V) Empty (Block V) := observeWithCommittees π
        (∀ condition ∈ ({fun τ => HoldersStayOnlineAfterHealing S Δs tAwakeEnd τ,
            ParentHeldAtDelivery,
            fun τ => RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ) τ,
            fun τ => HoldersStayOnline S Δs Δs_F ΔClockBehind tGAT tAwakeEnd τ,
            fun τ => AdversaryLeavesQuorumBy tAwakeEnd τ} :
              Set (ObservedRunWithCommittees V (NamedObject V) Empty (Block V) → Prop)),
            condition τ) →
        -- the conditions every top statement takes, with Goldilocks's delivery and catch-up delays
        -- per object owed before each tick, outside the asynchronous period; its validator set,
        -- every validator of weight one at every block (its instance of
        -- `RStsVariant2.BlockRegistry`); its healing premise, read within the healing phase; and
        -- its committees, the same in every run, carried by `τ`
        TopStatementConditions tGST
          (RStsVariant2.deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
            tAsyncStart (tAsyncStart + ΔAsyncLength))
          (RStsVariant2.deadlineOutside tGST (goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
            tAsyncStart (tAsyncStart + ΔAsyncLength))
          ΔClockAhead ΔClockBehind tGAT tAwakeEnd
          (goldilocksHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind
            ΔPreAsync tGAT tAwakeEnd) τ →
        -- the proposers of the slots that start after `tAwakeEnd`, each with a block it sent at its
        -- tick at the start of its slot in `π` (`τ.proposerReqs tAwakeEnd`)
        ∀ p ∈ goldilocksProposerReqs S ΔClockAhead ΔClockBehind tAwakeEnd π,
          RStsVariant2.HonestProposerThroughG tAwakeEnd p.tPreAsync p.tProposalStart p.proposer
            τ →
          p.tPreAsync < tAsyncStart →
          -- the recovery `max S.C.Δ Δs − S.C.Δ`
          RStsVariant2.AsyncPeriodEndsInTime p.tPeriodEndBy (tAsyncStart + ΔAsyncLength)
            (ΔRecovery := max ((S.C.Δ : Time) : ℝ) Δs - ((S.C.Δ : Time) : ℝ)) →
          RStsVariant2.AsyncPeriodSleepinessG p.tPreAsync ΔPreAsync tAsyncStart
            (tAsyncStart + ΔAsyncLength)
            (ΔRecovery := max ((S.C.Δ : Time) : ℝ) Δs - ((S.C.Δ : Time) : ℝ)) τ →
          ∀ t : ℝ,
            -- Goldilocks's ancestry, roots and blocks of objects (its instances of `BlockVocab`
            -- and `MessageVocab`)
            RootCollisionBy τ t ∨
            -- the block `p.block`, if `p.proposer`, while honest, proposed it
            (ConfirmedPersistsBetween τ p.tPreAsync ΔPreAsync tAsyncStart (tBy := t) p.proposer
                p.block ∧
              FinalizedCompatibleBetween τ tAsyncStart (tBy := t) p.proposer p.block) :=
  Iff.rfl

end Example

end LARuns.GoldilocksInstance
