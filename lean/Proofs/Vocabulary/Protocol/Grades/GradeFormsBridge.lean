module
public import Proofs.Vocabulary.Protocol.Store.HonestPoolActionBridge
public import Proofs.Vocabulary.Protocol.Grades.Inclusions
import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
import Proofs.Vocabulary.Objects.BlockVisibilityCore
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Proofs.Vocabulary.Protocol.Schedule.Action
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Relative-grade inputs -/

def relativePositiveAt (S : Setup V) (rho : Run V) (r : Round)
    (reader author : V) (C : Block V) : Bool :=
  DecoupledConsensusModel.Protocol.positive
    (relativeG2Read S rho r reader).st.core.toHealing.gradeView
    (relativeG2Read S rho r reader).st.core.F
    S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) author C

def relativeOpposingAt (S : Setup V) (rho : Run V) (r : Round)
    (reader author : V) (C : Block V) : Bool :=
  DecoupledConsensusModel.Protocol.opposing
    (relativeG2Read S rho r reader).st.core.toHealing.gradeView
    (relativeG2Read S rho r reader).st.core.F
    S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) author C


/- The `Γ_neg1` cutoff of round `r + 1` is that round's G2 domain time. -/
theorem gammaNeg1_eq_domain_g2_succ (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ (r + 1) = domain S.E S.hc (r + 1) .g2 := by
  change slotStart S.E.Δ (S.hc.opening_slot (r + 1)) - S.E.Δ =
    slotStart S.E.Δ (S.hc.opening_slot (r + 1)) + (-1) * S.E.Δ
  ring


/- If every member of `Hon` positively supports `C`, every opposing validator is outside `Hon`, and
    `Hon` has more weight than its complement, then `C` has the grade. -/

theorem phaseGrade_of_honestPositiveSupport
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (Hon : Finset V) (eta r : Round) (ea la : Time) (C : Block V)
    (hmajority : E.electorate.weightOf (Finset.univ \ Hon) <
      E.electorate.weightOf Hon)
    (hpositive : ∀ v ∈ Hon,
      DecoupledConsensusModel.Protocol.positive gv F eta r ea la v C = true)
    (hopposing : ∀ v,
      DecoupledConsensusModel.Protocol.opposing gv F eta r ea la v C = true →
        v ∉ Hon) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta r ea la C = true := by
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq]
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F eta r ea la v C = true) ⊆
      Finset.univ \ Hon := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
      hopposing v (Finset.mem_filter.mp hv).2⟩
  have hPos : Hon ⊆ Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F eta r ea la v C = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hpositive v hv⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hmajority (E.electorate.weightOf_mono hPos))


end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms gammaNeg1_eq_domain_g2_succ
#print axioms phaseGrade_of_honestPositiveSupport
end DecoupledConsensusModel.Proofs.HealingSurface

end
