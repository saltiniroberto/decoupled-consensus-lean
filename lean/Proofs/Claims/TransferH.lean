module
public import Proofs.Vocabulary.Internal.Definitions.LeakFairnessL1
public import Proofs.Vocabulary.Protocol.Handlers.NestedOutputs
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalWalkTransportCore
public import Proofs.Vocabulary.Protocol.Schedule.WeakGoldfishCone
public import Proofs.Vocabulary.Execution.CommonAncestorBound
public import Proofs.Vocabulary.Protocol.Handlers.ConfirmationRecordOrigin
public import Proofs.Vocabulary.Execution.UserConfirmationFreshness
public import Proofs.Vocabulary.Protocol.Schedule.GSTZeroReorgResilience
public import Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBaseDeadline
public import Proofs.Vocabulary.Protocol.Duties.Inputs.RecoveryInitialSourceNamedRunHistory
public import Proofs.Vocabulary.Execution.RecoveryInitialSourceNamedActionHistory
public import Proofs.Vocabulary.Execution.HandoverLegacyFinality
public import Proofs.Vocabulary.Protocol.ChainState.Main
public import Proofs.Vocabulary.Protocol.ChainState.W4FKChainJustification
public import Proofs.Claims.SynchronyH
public import Mathlib.Data.Int.SuccPred
public import Proofs.Claims.Spec2Claims.Claim13bModel_Prec_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_author

@[expose] public section

/-!
# The proposal instant is not negative

The proposal instant `Protocol.proposal_time S.E s` of every slot `s` is at least `0`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The proposal instant of a slot is not negative. -/
theorem proposal_time_nonneg (S : Setup V) (s : Slot) :
    (0 : Int) ≤ Protocol.proposal_time S.E s :=
  zero_le_proposal_time S.E s

end DecoupledConsensusModel.Sts
