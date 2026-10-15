module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Event
public import Proofs.Vocabulary.ModelVocabulary.Execution.GradeRuntime.Transport
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedActionReads
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedAdmissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedEvent
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedReceiptCalls
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedRun
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Node
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Objects
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Setup
public import Proofs.Vocabulary.Internal.ModelVocabulary.FGForkChoice.Finality
public import Proofs.Vocabulary.ModelVocabulary.FinalityGadget.ChainState
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.ForkChoice
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.Objects
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
public import Proofs.Vocabulary.Internal.ModelVocabulary.Healing.Action
public import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
public import Proofs.Vocabulary.Internal.ModelVocabulary.MajoritySG.ForkChoice
public import Proofs.Vocabulary.Internal.ModelVocabulary.MajoritySG.Objects
public import Proofs.Vocabulary.Internal.ModelVocabulary.FinalityGadget.Crossing
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.Store
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Blocks
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Env
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedAttestations
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Pairs
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Time
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Weights
public import Proofs.Vocabulary.Generic.SlotFreshness
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace UserConfirmationFreshness

export NamedSlotFreshness (block_slot_lt_of_mem_beforeTime_of_le_proposal
  advance_eq_candidate_of_held_slot)

end UserConfirmationFreshness
end Proofs
end DecoupledConsensusModel

end
