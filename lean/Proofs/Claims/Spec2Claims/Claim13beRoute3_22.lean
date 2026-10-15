import Proofs.Claims.VocabularyAssumptionsLemmas

/-!
# Unique indices of tick events

The property `TickIndexUnique` of a named run: a tick event sits at one index only.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A tick event sits at one index only: if the event at index `j` of `rho` is a tick and the event
    at index `k` equals it, then `j = k`. -/
def TickIndexUnique (rho : NamedRun V) : Prop :=
  ∀ {j k : Nat} {hj : j < rho.events.length} {hk : k < rho.events.length} {v : V} {t : Int},
    rho.events[j] = NamedEvent.tick v t → rho.events[j] = rho.events[k] → j = k

end DecoupledConsensusModel.Sts
