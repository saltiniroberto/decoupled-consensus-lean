import Proofs.Claims.Spec2Claims.Claim13beRoute3_88
import Proofs.Claims.Spec2Claims.Claim13bK_GradeDescendant

/-!
# Round arithmetic over `Nat`

Two facts over `Nat` about the round before a round `w` with `d + 2 ≤ w`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `d + 2 ≤ w`, then `w − 1 < w`, over `Nat`. -/
theorem pred_lt_of_two_le_jb (d w : Nat) (h : d + 2 ≤ w) : w - 1 < w := by omega

/-- If `d + 2 ≤ w`, then `d ≤ w − 1`, `w − 1 + 1 = w` and `1 ≤ w`, over `Nat`. -/
theorem pred_facts_of_two_le_jb (d w : Nat) (h : d + 2 ≤ w) :
    d ≤ w - 1 ∧ w - 1 + 1 = w ∧ 1 ≤ w := by omega

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

end AtRn

end DecoupledConsensusModel.Sts
