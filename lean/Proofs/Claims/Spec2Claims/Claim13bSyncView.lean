module
public import Model.Sts.Spec2Claims.Claim13be
public import Proofs.Claims.RunAll
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

/-!
# The attester window

The attester window `wAttest S` is at least twelve delays long.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The attester window `wAttest S` is at least `12 * S.E.Δ` long, whatever the number of slots per
    round. -/
theorem twelve_delta_le_wAttest (S : Setup V) : 12 * S.E.Δ ≤ wAttest S := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hprod : 3 * S.E.Δ ≤ (S.hc.R : Int) * S.E.Δ :=
    mul_le_mul_of_nonneg_right hR hd.le
  have hexp : wAttest S = 4 * ((S.hc.R : Int) * S.E.Δ) := by
    simp only [wAttest]; ring
  rw [hexp]
  linarith

end DecoupledConsensusModel.Sts
