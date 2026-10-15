module
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FrontierParent
public import Proofs.Vocabulary.Protocol.Grades.GoldfishConePersistence
public import Proofs.Vocabulary.Protocol.Schedule.WeakProcessedTree
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalCapInputs
public import Proofs.Vocabulary.ModelProperties.get_fg_root
public import Proofs.Vocabulary.ModelProperties.get_filtered_block_tree
public import Proofs.Vocabulary.ModelProperties.get_head_with
public import Proofs.Vocabulary.Objects.HealingDirectedHistory
public import Proofs.Vocabulary.Generic.SuffixHistory
public import Proofs.Vocabulary.Protocol.ChainState.EntryHeight
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Proofs.Vocabulary.Objects.Final
import Proofs.Vocabulary.Execution.RecoveryActionLiveSourceSplit
import Proofs.Vocabulary.Generic.EvaluationStore
import Proofs.Vocabulary.Protocol.ChainState.Main
import Proofs.Vocabulary.Protocol.ChainState.SlashableBoundBridge
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ConePersistence
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalWalkTransportCore
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Protocol.ForkChoice.Views.GoldfishCone
import Proofs.Vocabulary.Protocol.ForkChoice.Views.VoteSetValidityCore
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Protocol.Schedule.ProposalCanonicality
import Proofs.Vocabulary.Protocol.Schedule.RecoveryHandoffCore
import Mathlib.Data.Rat.Floor
import Proofs.Vocabulary.ModelProperties.Block_Preceq

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Round slots and opening outputs

The last slot of a round, and the confirmed block an honest validator holds at a round's action.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The last slot of round `q`. -/
def seedRoundLastSlot (S : Setup V) (q : Round) : Slot :=
  S.hc.opening_slot (q + 1) - 1


/-- The value of `live_confirmed` in `v`'s round-`q` action store. -/
def roundCeilingOpeningOutput
    (S : Setup V) (rho : Run V) (q : Round) (v : V) : Block V :=
  (actionStoreAt S rho v q).live_confirmed


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
