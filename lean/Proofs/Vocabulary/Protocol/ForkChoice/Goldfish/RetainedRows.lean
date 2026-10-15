module
public import Proofs.Vocabulary.Protocol.Grades.RowTrace
public import Proofs.Vocabulary.Internal.Definitions.OutageEntryRevision
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Projections -/

omit [DecidableEq V] [Fintype V] in
theorem sgVote_val (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).val_index = a.val_index := rfl

omit [DecidableEq V] [Fintype V] in
theorem sgVote_round (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).round = a.round := rfl

omit [DecidableEq V] [Fintype V] in
theorem sgVote_confirmed (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).confirmed = a.confirmed := rfl

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
