import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_commitBlock
import Proofs.Claims.Spec2Claims.Claim13beRoute3_34
import Proofs.Claims.Spec2Claims.Claim13beRoute3_21
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_q
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with_layer
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block
import Proofs.Claims.Spec2Claims.Claim13bModel_domain

/-!
# Awake at the latest multiple of the delay

When validators wake only at multiples of `Δ`, a validator awake at an instant is awake at the
latest multiple of `Δ` at or before it.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Under `AwakeAtMultiples`, if `w` is awake at `td`, then `w` is awake at `(td / Δ) * Δ`, the
    latest multiple of `Δ` at most `td`. -/
theorem awake_at_floor_of_awakeAtMultiples (S : Setup V) (Sched : Schedule V)
    (hawm : AwakeAtMultiples S Sched) {w : V} {td : Int} (haw : w ∈ Sched.awake td) :
    w ∈ Sched.awake (td / S.E.Δ * S.E.Δ) := by
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  set q := td / S.E.Δ * S.E.Δ with hq
  have hqle : q ≤ td := Int.ediv_mul_le td (ne_of_gt hΔ)
  -- every multiple of `Δ` at most `td` is at most `q`
  have hmul : ∀ m : Int, m % S.E.Δ = 0 → m ≤ td → m ≤ q := by
    intro m hm hmt
    have hm' : m = m / S.E.Δ * S.E.Δ :=
      (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hm)).symm
    have hdiv : m / S.E.Δ ≤ td / S.E.Δ := Int.ediv_le_ediv hΔ hmt
    rw [hm', hq]
    exact Int.mul_le_mul_of_nonneg_right hdiv (le_of_lt hΔ)
  have hstep : ∀ d : Nat, q ≤ td - d → w ∈ Sched.awake (td - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using haw
    | succ d ih =>
      intro hd
      have hprev := ih (by push_cast at hd; linarith)
      by_contra hnot
      have hmod := hawm (td - d) w hprev (by rw [sub_sub]; push_cast at hnot; exact hnot)
      have := hmul (td - d) hmod (by linarith)
      push_cast at hd
      linarith
  have h := hstep (td - q).toNat (by rw [Int.toNat_of_nonneg (by linarith)]; linarith)
  rwa [Int.toNat_of_nonneg (by linarith), sub_sub_cancel] at h

section FromTGAT

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (v : V)
  (H : Finset V) (n : Nat) {tGAT tAwakeEnd : Int}
  (hsync : SynchronyFromWake S x) (hmono : Sched.MonotoneCorruption)
  (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
  (hgst : S.E.t_GST ≤ tGAT) (hcv : CommonViewAtGAT S Sched x tGAT)
  (hvalid : ExecutionValid S Sched (interface S Sched) x)
  (hawm : AwakeAtMultiples S Sched)
  (hH : ∀ v₀ ∈ H, v₀ ∉ Sched.adv (x[n].time : Int))
  (hn : (x[n].time : Int) ≤ tAwakeEnd)

include hsync hmono hawake hgst hcv hvalid hawm hH hn

end FromTGAT

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

section NotHeldFromTGAT

variable (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
  (x : Framework.StsMultisetLog.AtomicExec (protocol S) Sched) (v : V)
  (n : Nat) {tGAT tAwakeEnd : Int}
  (hsync : SynchronyFromWake S x) (hmono : Sched.MonotoneCorruption)
  (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
  (hgst : S.E.t_GST ≤ tGAT) (hcv : CommonViewAtGAT S Sched x tGAT)
  (hvalid : ExecutionValid S Sched (interface S Sched) x)
  (hawm : AwakeAtMultiples S Sched)
  (hthird : ∀ t : Int, t ≤ tAwakeEnd →
    3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
  (hn : (x[n].time : Int) ≤ tAwakeEnd)

include hsync hmono hawake hgst hcv hvalid hawm hn

include hthird

end NotHeldFromTGAT

end DecoupledConsensusModel.Sts
