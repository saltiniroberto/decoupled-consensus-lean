module
public import Proofs.Vocabulary.Objects.AdmissibleCore
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Relay after GST

An honest emission at or after GST, and an accepted Goldfish vote forwarded at or after GST, are
handled by every honest node within one network delay.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Relay from a source at or after GST -/

/-- An object the honest validator `v` emits at time `t ≥ t_GST` is handled by the honest validator
    `w` at some time in `[t, t + Δ)`, when `w`'s store at `t + Δ` does not exclude it. -/
theorem broadcast_after_gst (S : Setup V) {rho : Run V}
    (adm : Proofs.AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {o : Object V} {t : Time} (hpost : S.E.t_GST ≤ t)
    (hemit : rho.emits S v o t) (hhor : t + S.E.Δ ≤ rho.horizon)
    (hguard : NamedReceipt.excludes
      (rho.stateBeforeTime S (t + S.E.Δ) w).st o = false) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w o t' := by
  have hmax : max t S.E.t_GST = t := max_eq_left hpost
  have h := adm.broadcast v hv o t hemit w hw (by simpa only [hmax] using hhor)
    (by simpa only [hmax] using hguard)
  simpa only [hmax] using h


/-- An accepted Goldfish vote forwarded at or after GST reaches every honest
node before one network delay. -/
theorem relay_gf_vote_after_gst_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {t : Time} (hpost : S.E.t_GST ≤ t)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hunaccepted : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t' := by
  have hmax : max t S.E.t_GST = t := max_eq_left hpost
  have h := adm.relay_gf_vote v hv i u t hacc w hw hunaccepted
    (by simpa only [hmax] using hhor) rfl
  simpa only [hmax] using h

theorem relay_gf_vote_after_gst (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {t : Time} (hpost : S.E.t_GST ≤ t)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hunaccepted : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t' :=
  relay_gf_vote_after_gst_core S adm.toNamedAdmissibleCore hv hw hpost
    hacc hunaccepted hhor

#print axioms relay_gf_vote_after_gst_core


end Protocol
end DecoupledConsensusModel

end
