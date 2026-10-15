module
public import Proofs.Claims.Spec2Claims.Claim13bStepKitRecord
public import Proofs.Claims.Spec2Claims.Claim13bSyncView
public import Proofs.Claims.Spec2Claims.Claim13bModel_initial
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_slotOf_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_round_of_mk

@[expose] public section

/-!
# Awake throughout an interval

A validator awake throughout an interval is awake at every instant of it.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A validator in `Sched.awakeThroughout t_0 t_1` is in `Sched.awake t` for every `t` with
    `t_0 ≤ t ≤ t_1`. -/
theorem mem_awake_of_awakeThroughout (Sched : Schedule V) {t_0 t_1 t : Int} {w : V}
    (hawT : w ∈ Sched.awakeThroughout t_0 t_1) (h0 : t_0 ≤ t) (h1 : t ≤ t_1) :
    w ∈ Sched.awake t := by
  have hsub : Sched.awakeThroughout t_0 t_1 ≤ Sched.awake t :=
    Finset.inf_le (Finset.mem_Icc.mpr ⟨h0, h1⟩)
  exact Finset.mem_of_subset hsub hawT

end DecoupledConsensusModel.Sts
