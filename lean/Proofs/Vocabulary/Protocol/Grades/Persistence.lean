module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedAdmissible
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Model.Vocabulary.Execution.Run
public import Model.Vocabulary.Execution.Setup
public import Proofs.Vocabulary.Execution.PrefixThroughHistory
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedStableChainOutageInternal

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Post-GST delivery window -/


/-- Synchrony gives a healthy delivery window from GST to the horizon. -/
theorem healthyWindowDelivery_after_gst (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) :
    NamedHealthyWindowDelivery S rho S.E.t_GST rho.horizon where
  broadcast := by
    intro v hv o t hemit w hw hpost hhor hguard
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.broadcast v hv o t hemit w hw
      (by simpa only [hmax] using hhor)
      (by simpa only [hmax] using hguard)
    simpa only [hmax] using h
  relay_block := by
    intro v hv i B t hacc w hw hmissing hpost hhor hguard
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.relay_block v hv i B t hacc w hw hmissing
      (by simpa only [hmax] using hhor)
      (by simpa only [hmax] using hguard)
    simpa only [hmax] using h
  relay_gf_vote := by
    intro v hv i u t hacc w hw hmissing hpost hhor _
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.relay_gf_vote v hv i u t hacc w hw hmissing
      (by simpa only [hmax] using hhor) rfl
    simpa only [hmax] using h
  relay_attest := by
    intro v hv i a t hacc w hw hmissing hpost hhor _
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.relay_attest v hv i a t hacc w hw hmissing
      (by simpa only [hmax] using hhor) rfl
    simpa only [hmax] using h

#print axioms healthyWindowDelivery_after_gst


end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
