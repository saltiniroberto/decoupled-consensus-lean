import Proofs.Claims.Spec2Claims.Claim13beRoute3_53b
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_head_covers
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_fork_choice
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf

/-!
# A weight majority is nonempty

A set that weighs more than its complement has a member.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

section GradeFormsBridge

/-- If the validators outside `X` weigh less than `X`, then `X` has a member. -/
theorem nonempty_of_honestWeightMajority_l54 {S : Setup V} {X : Finset V}
    (h : Execution.HonestWeightMajority S X) : X.Nonempty := by
  rcases Finset.eq_empty_or_nonempty X with hX | hX
  · subst hX
    have h' : S.E.electorate.weightOf (Finset.univ \ (∅ : Finset V)) <
        S.E.electorate.weightOf (∅ : Finset V) := h
    rw [weightOf_empty] at h'
    exact absurd h' (Nat.not_lt_zero _)
  · exact hX

end GradeFormsBridge

end DecoupledConsensusModel.Sts
