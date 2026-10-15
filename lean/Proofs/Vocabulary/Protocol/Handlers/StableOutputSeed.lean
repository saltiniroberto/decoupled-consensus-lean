module
public import Proofs.Vocabulary.Protocol.Schedule.StableRootSuffixOrigin
public import Proofs.Vocabulary.ModelProperties.gradeBool
public import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedSlotInterval
public import Proofs.Vocabulary.Objects.FixedHeightRootCore
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import Proofs.Vocabulary.Execution.PreparedReadBridge
public import Proofs.Vocabulary.Execution.IdxDriverHelpers
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.WeakBootstrapJoin
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
public import Proofs.Vocabulary.Protocol.Grades.JointHistoryB4B5Idx
public import Proofs.Vocabulary.Protocol.Handlers.HandlerAdmissionGuards
public import Model.Vocabulary.Statements.Instantiation.OutageWindow
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
import Proofs.Vocabulary.Protocol.ForkChoice.Views.WeakConfirmationSupport
import Proofs.Vocabulary.Protocol.Schedule.WeakGoldfishCone
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The schedule in time terms -/

theorem early_g2_eq (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 = S.a r - 11 * S.E.Δ := by
  simp only [early, opening, Protocol.proposal_time, Env.t, slotStart, Setup.a,
    Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, Phase.earlyOffset]
  push_cast
  ring

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
