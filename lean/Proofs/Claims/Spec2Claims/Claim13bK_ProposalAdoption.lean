import Proofs.Claims.Spec2Claims.Claim13bK_HeadsPersist
import Proofs.Claims.Spec2Claims.Claim13bK_JointBase
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85d
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85c
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1

/-!
# The validators not held, clamped at an instant

`notHeldUpTo_i1b Sched T` gives, for each instant `t`, the validators the adversary does not hold at
the earlier of `t` and `T`. The file states its basic facts and one slot arithmetic helper.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The clamped family of validators not held -/

section ClampedFamily

/-- For each instant `t`, the set of validators the adversary does not hold at the earlier of `t`
    and `T`. -/
def notHeldUpTo_i1b (Sched : Schedule V) (T : Int) (t : Int) : Finset V :=
  notHeldAt Sched (min t T)

/-- At an instant `t ≤ T`, the clamped family is the set of validators not held at `t`. -/
theorem notHeldUpTo_eq_i1b (Sched : Schedule V) {T t : Int} (h : t ≤ T) :
    notHeldUpTo_i1b Sched T t = notHeldAt Sched t := by
  simp only [notHeldUpTo_i1b, min_eq_left h]

/-- Under monotone corruption, the validators not held at `t` are in the clamped family's set for
    `t`. -/
theorem notHeldAt_subset_notHeldUpTo_i1b {Sched : Schedule V} (hmono : Sched.MonotoneCorruption)
    (T t : Int) : notHeldAt Sched t ⊆ notHeldUpTo_i1b Sched T t :=
  notHeldAt_anti hmono (min_le_left t T)

/-- Under monotone corruption, the clamped family shrinks as time grows. -/
theorem notHeldUpTo_anti_i1b {Sched : Schedule V} (hmono : Sched.MonotoneCorruption) (T : Int)
    {t t' : Int} (h : t ≤ t') : notHeldUpTo_i1b Sched T t' ⊆ notHeldUpTo_i1b Sched T t :=
  notHeldAt_anti hmono (min_le_min_right T h)

end ClampedFamily

/-! ## Slot arithmetic -/

section GeneralPivot

open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Over `Nat`: if `2 ≤ R`, `y + R ≤ start` and `x + 2R ≤ start`, then `x + 1 ≤ start − 1`,
    `x + 2 ≤ start`, `y + 1 ≤ start − 1`, `0 < start − 1`, `start − 1 + 1 = start` and
    `x + 2 ≤ start − 1`. -/
theorem slotBookkeeping_i1b (x y R start : Nat) (hR : 2 ≤ R) (hy : y + R ≤ start)
    (hx : x + 2 * R ≤ start) :
    x + 1 ≤ start - 1 ∧ x + 2 ≤ start ∧ y + 1 ≤ start - 1 ∧ 0 < start - 1 ∧
      start - 1 + 1 = start ∧ x + 2 ≤ start - 1 := by
  omega

end GeneralPivot

end DecoupledConsensusModel.Sts
