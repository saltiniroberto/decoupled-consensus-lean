import Model.Vocabulary.Execution.Setup
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.early`

A round's early grade cutoff for a phase, `opening r + earlyOffset · Δ` with the offsets `−3`, `−4`,
`−5` for `g0`, `g1`, `g2`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.HealConfig.a
  DecoupledConsensusModel.Protocol.HealConfig.opening_slot
  DecoupledConsensusModel.Protocol.Phase.domainOffset
  DecoupledConsensusModel.Protocol.Phase.earlyOffset DecoupledConsensusModel.Protocol.domain
  DecoupledConsensusModel.Protocol.early DecoupledConsensusModel.Protocol.opening
  DecoupledConsensusModel.Protocol.proposal_time DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Round `r`'s grade-1 early cutoff is its opening minus `4Δ`. -/
theorem early_g1_eq_opening (S : Setup V) (r : Round) :
    Protocol.early S.E S.hc r .g1 = Protocol.opening S.E S.hc r - 4 * S.E.Δ := by
  unfold Protocol.early
  simp only [Protocol.Phase.earlyOffset]
  ring

/-- Round `r`'s grade-0 early cutoff is its opening minus `3Δ`. -/
theorem early_g0_eq_opening (S : Setup V) (r : Round) :
    Protocol.early S.E S.hc r .g0 = Protocol.opening S.E S.hc r - 3 * S.E.Δ := by
  unfold Protocol.early
  simp only [Protocol.Phase.earlyOffset]
  ring

/-- For every round `r` and phase `p`, the early cutoff plus `2Δ` is at most the domain time. -/
theorem early_add_two_delta_le_domain (S : Setup V) (r : Round) (p : Protocol.Phase) :
    Protocol.early S.E S.hc r p + 2 * S.E.Δ ≤ Protocol.domain S.E S.hc r p := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  unfold Protocol.early Protocol.domain
  cases p <;> simp only [Protocol.Phase.earlyOffset, Protocol.Phase.domainOffset] <;> linarith

end DecoupledConsensusModel.Sts
