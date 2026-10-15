module
public import Proofs.Claims.Spec2Claims.Claim13bStepKitDelivery

@[expose] public section

/-!
# Awake throughout a window

A validator awake at every instant of a window is in that window's `awakeThroughout` set.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A validator awake at every instant of `[a, b]` is in `Sched.awakeThroughout a b`. -/
theorem mem_awakeThroughout_of_forall (Sched : Schedule V) {a b : Int} {w : V}
    (h : ∀ t : Int, a ≤ t → t ≤ b → w ∈ Sched.awake t) :
    w ∈ Sched.awakeThroughout a b := by
  refine Finset.singleton_subset_iff.1 (Finset.le_inf ?_)
  intro t ht
  obtain ⟨h0, h1⟩ := Finset.mem_Icc.1 ht
  exact Finset.singleton_subset_iff.2 (h t h0 h1)


end DecoupledConsensusModel.Sts
