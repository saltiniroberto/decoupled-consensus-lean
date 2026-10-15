import Proofs.Claims.Spec2Claims.Claim13bStepCone
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_sgVote
import Proofs.Claims.Spec2Claims.Claim13bModel_round_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_sg_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff

/-!
# Awake throughout a window inside the phase

A validator the adversary does not hold at a window's last instant is awake throughout any window
inside the phase `[tGAT, tE]`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If every validator the adversary does not hold is awake at every instant of `[tGAT, tE]`,
    corruption is monotone, `[a, b]` lies inside `[tGAT, tE]`, and the adversary does not hold `w`
    at `b`, then `w` is awake at every instant of `[a, b]`. -/
theorem awakeThroughout_phase (Sched : Schedule V) {tGAT tE a b : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hmono : Sched.MonotoneCorruption) {w : V}
    (ha : tGAT ≤ a) (hb : b ≤ tE) (hw : w ∉ Sched.adv b) :
    w ∈ Sched.awakeThroughout a b := by
  refine mem_awakeThroughout_of_forall Sched ?_
  intro t ht0 ht1
  refine hawake t (le_trans ha ht0) (le_trans ht1 hb) w ?_
  intro hmem
  exact hw (hmono t b ht1 hmem)

end DecoupledConsensusModel.Sts
