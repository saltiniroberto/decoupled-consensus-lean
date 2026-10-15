import Model.Vocabulary.Execution.Setup
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.domain`

The phase-domain time of a round, relative to the round's action time.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.HealConfig.a DecoupledConsensusModel.Protocol.Phase.domainOffset
  DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.opening
  DecoupledConsensusModel.Protocol.proposal_time DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- For every phase `p`, round `r`'s domain time for `p` plus `5Δ` is at most `S.a r`. -/
theorem domain_add_five_delta_le_action (S : Setup V) (r : Round) (p : Protocol.Phase) :
    Protocol.domain S.E S.hc r p + 5 * S.E.Δ ≤ S.a r := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  unfold Protocol.domain Protocol.opening Protocol.proposal_time Setup.a
    Protocol.HealConfig.a Env.t slotStart
  cases p <;> simp only [Protocol.Phase.domainOffset] <;> linarith

end DecoupledConsensusModel.Sts
