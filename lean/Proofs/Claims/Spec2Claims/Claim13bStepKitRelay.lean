module
public import Proofs.Claims.Spec2Claims.Claim13bRelay
public import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
public import Proofs.Claims.Spec2Claims.Claim13bModel_initial
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
public import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_snd
public import Proofs.Claims.Spec2Claims.Claim13bModel_opening_inclRelay
public import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_inclRelay
public import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_slotOf_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_goldfish_vote_checked_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
public import Proofs.Vocabulary.ModelProperties.on_goldfish_vote_checked
public import Proofs.Vocabulary.Protocol.Handlers.TickBridges

@[expose] public section

/-!
# Slot starts, round openings and awake intervals

The slot of a slot's start instant, a round's opening instant as the start of its opening slot, and
the shrinking of an interval a validator is awake throughout.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The instant slot `s` starts at falls in slot `s`. -/
theorem slotOf_slotStart (S : Setup V) (s : Slot) :
    S.E.slotOf (slotStart S.E.Δ s) = s := by
  rw [slotStart_eq_proposal_time]
  exact Proofs.Optimistic.slotOf_proposal_time S.E s

/-- Round `r` opens at the start of its opening slot `S.hc.opening_slot r`. -/
theorem opening_eq_slotStart (S : Setup V) (r : Round) :
    Protocol.opening S.E S.hc r = slotStart S.E.Δ (S.hc.opening_slot r) :=
  (opening_eq_proposal_time_inclRelay S.E S.hc r).trans
    (slotStart_eq_proposal_time S.E (S.hc.opening_slot r)).symm

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

/-- A validator awake at every instant of `[t_0, t_1]` is awake at every instant of `[t_0, t_2]`
    whenever `t_2 ≤ t_1`. -/
theorem awakeThroughout_shrink (Sched : Schedule V) {t_0 t_1 t_2 : Int} {w : V}
    (hawT : w ∈ Sched.awakeThroughout t_0 t_1) (h : t_2 ≤ t_1) :
    w ∈ Sched.awakeThroughout t_0 t_2 := by
  have hsub : Sched.awakeThroughout t_0 t_1 ≤ Sched.awakeThroughout t_0 t_2 :=
    Finset.inf_mono (Finset.Icc_subset_Icc (le_refl _) h)
  exact Finset.mem_of_subset hsub hawT

/-- A validator awake at every instant of `[t_0, t_1]` is awake at every instant of `[t_2, t_1]`
    whenever `t_0 ≤ t_2`. -/
theorem awakeThroughout_shrink_left (Sched : Schedule V) {t_0 t_1 t_2 : Int} {w : V}
    (hawT : w ∈ Sched.awakeThroughout t_0 t_1) (h : t_0 ≤ t_2) :
    w ∈ Sched.awakeThroughout t_2 t_1 := by
  have hsub : Sched.awakeThroughout t_0 t_1 ≤ Sched.awakeThroughout t_2 t_1 :=
    Finset.inf_mono (Finset.Icc_subset_Icc h (le_refl _))
  exact Finset.mem_of_subset hsub hawT

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

end DecoupledConsensusModel.Sts
