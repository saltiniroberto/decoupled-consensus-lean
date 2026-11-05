module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# ProposalPropagationUpTo, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/ProposalPropagationUpTo.lean` over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: block propagation from a given
send, with the delivery premises up to a bound, the node accepting the block by the field
`block_admissible_iff` of `F.ndAdded` under the model's node invariant (Lemma 11). The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

end GoldilocksCorrectness.Record.Proofs.Executions

