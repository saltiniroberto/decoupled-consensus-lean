module
public import Proofs.Vocabulary.Protocol.Grades.ProposalLifecycleCore
public import Proofs.Vocabulary.Protocol.Schedule.RecoveryOpeningFrontierRunBlock
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Same-slot confirmations after GST

Confirmations of two honest validators at the same slot after GST are compatible.
-/

namespace DecoupledConsensusModel.Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-- For honest `v` and `w` and a slot `s` whose proposal time is at or after GST and whose
    confirmation time is within the horizon, blocks `B` and `C` that `v` and `w` confirm at `s`
    (`GenuineConfirmationWith`, each under its own read's grade contract) are compatible. -/
theorem sameSlot_genuine_compatible_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B C : Block V}
    (hB : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s B)
    (hC : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho w s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho w s) s C) :
    Block.compatible B C = true := by
  have hcross := opening_frontier_crossViews_confStore_after_gst
    S adm hv hw hpost hhor
  have hBeligible := hB.genuine
  have hCeligible := hC.genuine
  simp only [confEligible, confCount, confScore, decide_eq_true_eq]
    at hBeligible hCeligible
  rw [← hB.selected, ← hC.selected]
  rw [update_confirmation_with_live_confirmed,
    update_confirmation_with_live_confirmed, if_pos hB.genuine, if_pos hC.genuine]
  exact eligible_compatible (confNumerator S.E (Proofs.Optimistic.confStore S rho v s) s)
    (confNumerator S.E (Proofs.Optimistic.confStore S rho w s) s) hcross.1 hcross.2
    hBeligible hCeligible

#print axioms sameSlot_genuine_compatible_after_gst

end DecoupledConsensusModel.Protocol

end
