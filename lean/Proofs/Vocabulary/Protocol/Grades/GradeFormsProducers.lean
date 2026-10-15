module
public import Proofs.Vocabulary.Execution.FinalizedViable
public import Proofs.Vocabulary.ModelProperties.get_fg_root
public import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
public import Proofs.Vocabulary.Protocol.Handlers.FrozenRootOrder
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The origin of a G2 selection at an action read

A G2 block selected at an action read comes from the same validator's earlier freeze at the G2
domain time.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A G2 block `B` selected at `v`'s round-`r` action read before event `i` is an ancestor of the
    root that `v` froze at an earlier tick at the round-`r` G2 domain time. -/
theorem contractQ2_capture_at_action_index
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (r : Round) {B : Block V}
    (hQ : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (NamedActionReads.actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache)
      S.E S.hc
      (NamedActionReads.actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r =
        some B) :
    ∃ j raw, j < i ∧
      rho.events[j]? = some (.tick v (domain S.E S.hc r .g2)) ∧
      DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw ∧
      Block.Preceq B raw :=
  NamedOutageHistory.JointHistoryProducersTime.q2_capture_at_action_read
    S rho i v r hQ


end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms contractQ2_capture_at_action_index
end DecoupledConsensusModel.Proofs.HealingSurface

end
