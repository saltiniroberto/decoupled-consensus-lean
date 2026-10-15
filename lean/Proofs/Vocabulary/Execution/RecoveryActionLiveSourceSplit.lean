module
public import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedActionCarrier
public import Proofs.Vocabulary.Protocol.Grades.ProposalLifecycleCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Source of an action's live confirmation

The `live_confirmed` value written at round `r`'s action is either a block that passes the
confirmation test of the opening-slot confirmation store, or that store's FG root.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The `live_confirmed` value written at round `r`'s action is either a block `C` satisfying
    `GenuineConfirmationWith` on the opening-slot confirmation store (the confirmation walk selects
    it and it passes the eligibility test), or that store's FG root. -/
theorem actionStoreAt_liveConfirmed_genuine_or_fgRoot
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (∃ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r) C ∧
      C = (actionStoreAt S rho v r).live_confirmed) ∨
    (∃ R : Block V,
      R = Protocol.get_fg_root
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).toHealing.toFG ∧
      R = (actionStoreAt S rho v r).live_confirmed) := by
  let contract := NamedProfile.gradeContract
    (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache
  let st := Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)
  by_cases hgate :
      confEligible S.E st
        (S.hc.opening_slot r)
        (confWalkWith contract S.E S.hc st (S.hc.opening_slot r)) = true
  · left
    refine ⟨confWalkWith contract S.E S.hc st (S.hc.opening_slot r),
      { selected := ?_, genuine := hgate }, ?_⟩
    · exact update_confirmation_with_live_confirmed contract S.E S.hc st
        (S.hc.opening_slot r) ▸ if_pos hgate
    · change confWalkWith contract S.E S.hc st (S.hc.opening_slot r) =
        (actionStoreAt S rho v r).st.core.live_confirmed
      rw [show (actionStoreAt S rho v r).st.core =
        Protocol.update_confirmation_with contract S.E S.hc st
        (S.hc.opening_slot r) by
          simpa only [contract, st] using
            actionStoreAt_eq_update_confirmation_confStore S rho v r]
      rw [update_confirmation_with_live_confirmed, if_pos hgate]
  · right
    refine ⟨Protocol.get_fg_root st.toHealing.toFG, rfl, ?_⟩
    change Protocol.get_fg_root st.toHealing.toFG =
      (actionStoreAt S rho v r).st.core.live_confirmed
    rw [show (actionStoreAt S rho v r).st.core =
        Protocol.update_confirmation_with contract S.E S.hc st
        (S.hc.opening_slot r) by
          simpa only [contract, st] using
            actionStoreAt_eq_update_confirmation_confStore S rho v r]
    rw [update_confirmation_with_live_confirmed, if_neg hgate]
    rfl


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
