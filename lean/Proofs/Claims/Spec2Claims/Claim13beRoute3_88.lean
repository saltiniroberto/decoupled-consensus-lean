import Proofs.Claims.Spec2Claims.Claim13beRoute3_86e
import Proofs.Claims.Spec2Claims.Claim13bInvariantActiveSinceW
import Proofs.Claims.Spec2Claims.Claim13beRoute3_78
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_mk

/-!
# Round and opening-slot arithmetic

A round at least `d + 2` is `c + 2` with `d ≤ c`, and consecutive opening slots differ by at least
one slot.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `d + 2 ≤ r`, then `r = c + 2` for some `c` with `d ≤ c`, `d ≤ c + 1` and `c + 2 − 1 = c + 1`. -/
theorem nat_round_split_l88 (d r : Nat) (h : d + 2 ≤ r) :
    ∃ c : Nat, r = c + 2 ∧ d ≤ c ∧ d ≤ c + 1 ∧ c + 2 - 1 = c + 1 :=
  ⟨r - 2, by omega, by omega, by omega, by omega⟩

/-- `opening_slot (c + 1) + 1 ≤ opening_slot (c + 2)`. -/
theorem opening_slot_succ_lt_l88 (S : Setup V) (c : Round) :
    S.hc.opening_slot (c + 1) + 1 ≤ S.hc.opening_slot (c + 2) := by
  rw [show c + 2 = c + 1 + 1 from rfl, opening_slot_succ_mk S.hc (c + 1)]
  exact Nat.add_le_add_left (le_trans (by decide : 1 ≤ 2) S.hc.R_ge_two) _

end DecoupledConsensusModel.Sts
