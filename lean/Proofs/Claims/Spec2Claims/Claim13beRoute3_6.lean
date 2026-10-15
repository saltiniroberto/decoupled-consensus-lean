import Proofs.Claims.Spec2Claims.Claim13beRoute3_5
import Proofs.Claims.Spec2Claims.Claim13bStepConeIter
import Proofs.Claims.Spec2Claims.Claim13beRoute3_1
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial_stamp

/-!
# Awakeness between multiples of the delay

A validator awake at an instant, with no multiple of the delay between an earlier instant and it,
was already awake at that earlier instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `v` is awake at `t + k` and none of `t + 1, …, t + k` is a whole multiple of the delay, then
    `v` is awake at `t`. -/
theorem awake_of_awake_later (S : Setup V) (Sched : Schedule V)
    (hmult : AwakeAtMultiples S Sched) {v : V} (t : Int) :
    ∀ k : Nat, (∀ j : Nat, 1 ≤ j → j ≤ k → (t + (j : Int)) % S.E.Δ ≠ 0) →
      v ∈ Sched.awake (t + (k : Int)) → v ∈ Sched.awake t := by
  intro k
  induction k with
  | zero => intro _ haw; simpa using haw
  | succ n ih =>
      intro hno haw
      refine ih (fun j hj1 hj2 => hno j hj1 (Nat.le_succ_of_le hj2)) ?_
      by_contra hcon
      refine hno (n + 1) (Nat.le_add_left 1 n) (le_refl _) ?_
      refine hmult (t + ((n + 1 : Nat) : Int)) v haw ?_
      have hcast : t + ((n + 1 : Nat) : Int) - 1 = t + (n : Int) := by push_cast; ring
      rw [hcast]
      exact hcon

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

end DecoupledConsensusModel.Sts
