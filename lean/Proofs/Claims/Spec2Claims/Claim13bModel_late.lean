import Model.Sts
import Mathlib.Tactic.Ring
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.late`

A round's late cutoff at each phase, stated against the round's opening.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Phase.lateOffset
  DecoupledConsensusModel.Protocol.late DecoupledConsensusModel.Protocol.opening

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The late cutoff of round `r` at phase `.g0` is the opening of round `r` minus `3Δ`. -/
theorem late_g0_eq_opening (S : Setup V) (r : Round) :
    Protocol.late S.E S.hc r .g0 = Protocol.opening S.E S.hc r - 3 * S.E.Δ := by
  unfold Protocol.late
  simp only [Protocol.Phase.lateOffset]
  ring

/-- The late cutoff of round `r` at phase `.g1` is the opening of round `r` minus `2Δ`. -/
theorem late_g1_eq_opening (S : Setup V) (r : Round) :
    Protocol.late S.E S.hc r .g1 = Protocol.opening S.E S.hc r - 2 * S.E.Δ := by
  unfold Protocol.late
  simp only [Protocol.Phase.lateOffset]
  ring

/-- The late cutoff of round `r` at phase `.g2` is the opening of round `r` minus `Δ`. -/
theorem late_g2_eq_opening (S : Setup V) (r : Round) :
    Protocol.late S.E S.hc r .g2 = Protocol.opening S.E S.hc r - S.E.Δ := by
  unfold Protocol.late
  simp only [Protocol.Phase.lateOffset]
  ring

end DecoupledConsensusModel.Sts
