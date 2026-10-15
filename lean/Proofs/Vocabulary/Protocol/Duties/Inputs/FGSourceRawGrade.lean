module
public import Proofs.Vocabulary.Protocol.Grades.RecoveryGenuineClearNextVote
import Proofs.Vocabulary.Protocol.Schedule.Action
import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# Grade 1 at another reader from a selected grade-2 block

A grade-2 block an honest validator selects at round `r`'s action has grade 1 at another honest
validator's grade-1 read of round `r`, when the bodies that read needs have arrived.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.HealingLemmas Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-- If the honest `p` selects `Q` as its grade-2 block at round `r`'s action and
    `CrossReaderBodyReadyGuard S rho r p w Q` holds, then `Q` has grade 1 at round `r` in the honest
    `w`'s read at the grade-1 domain time. -/
theorem selectedG2_G1_at_read_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (_hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    (_hhor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q)
    (hguard : CrossReaderBodyReadyGuard S rho r p w Q) :
    PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 Q = true := by
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
  exact storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
      ready.2 p w hp hw Q hG2 hguard


#print axioms selectedG2_G1_at_read_after_cutoff

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
