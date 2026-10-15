import Proofs.Claims.Spec2Claims.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Vocabulary.ModelProperties.Block_Preceq

/-!
# Two facts on blocks and slots

An ancestor of a block lies on one chain with it, and every slot `s` is at or before the opening
slot of round `r + 1 + s + 1`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Small facts -/

omit [Fintype V] in
/-- If `X` is an ancestor of `Y`, then `X` and `Y` lie on one chain. -/
theorem compatible_of_preceq_c2b {X Y : Block V} (h : Block.Preceq X Y) :
    Block.compatible X Y = true :=
  compatible_of_preceq_common_Preceq h (Proofs.ModelProperties.Preceq_self Y)

/-- Every slot `s` is at or before the opening slot of round `r + 1 + s + 1`. -/
theorem le_opening_slot_far (hc : Protocol.HealConfig) (r s : Nat) :
    s ≤ hc.opening_slot (r + 1 + s + 1) := by
  have hR : 1 ≤ hc.R := le_trans (by decide) hc.R_ge_three
  rw [opening_slot_closed]
  calc s ≤ (r + 1 + s + 1) * 1 := by omega
    _ ≤ (r + 1 + s + 1) * hc.R := Nat.mul_le_mul_left _ hR

end DecoupledConsensusModel.Sts
