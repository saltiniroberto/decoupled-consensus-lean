module
public import Proofs.Vocabulary.Protocol.Handlers.TickBridges
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
import Mathlib.RingTheory.WittVector.IsPoly
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section

/-!
# The action store as a confirmation update

The core store of round `r`'s action read is the confirmation update, at round `r`'s opening slot,
of the confirmation store of that slot.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The core store of `v`'s round-`r` action read is `update_confirmation_with`, under the grade
    contract of `v`'s confirmation read at `S.a r`, applied to `v`'s confirmation store of round
    `r`'s opening slot. -/
theorem actionStoreAt_eq_update_confirmation_openingConfStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r) := by
  have hsc : S.a r =
      Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) :=
    Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hslot : S.E.slotOf (S.a r) = S.hc.opening_slot r + 1 := by
    rw [hsc]
    exact Proofs.Optimistic.slotOf_support_cutoff S.E _
  have hidx : S.E.slotOf (S.a r) - 1 = S.hc.opening_slot r := by
    rw [hslot]; simp
  rw [Proofs.Optimistic.confStore_eq_confirmationInputRead]
  show (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).cache)
      S.E S.hc
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).st
      (S.E.slotOf (S.a r) - 1)).core = _
  rw [hidx, Proofs.ModelProperties.named_update_confirmation_with_core,
    show S.a r = Protocol.confirmation_time S.E (S.hc.opening_slot r) from
      Protocol.a_eq_confirmation_time S.hc S.E r]
  rfl


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
