module
public import Model.Vocabulary.Execution.Setup
import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Internal.Definitions.PhaseGrades
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedDutyReads
public import Proofs.Vocabulary.Objects.ActionRound
public import Mathlib.Data.DFinsupp.Notation

@[expose] public section

/-!
# The opening slot's confirmation time

The confirmation time of a round's opening slot is the round's action time.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The opening slot's confirmation time is its round action time. -/
theorem opening_confirmation_time_eq_action
    (S : Setup V) (q : Round) :
    Protocol.confirmation_time S.E (S.hc.opening_slot q) = S.a q :=
  (Protocol.a_eq_confirmation_time S.hc S.E q).symm


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
