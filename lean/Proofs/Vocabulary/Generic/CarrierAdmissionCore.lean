module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Mathlib.Data.DFinsupp.Notation
public import Mathlib.Data.Finsupp.Notation
public import Proofs.Vocabulary.Internal.Legacy.Definitions.LeakLedger

@[expose] public section

/-!
# Finalized-ancestor condition on deliveries

The predicate `BlockFinalizedBelowAtDeliveriesBefore`, a receiver-local condition on deliveries
before a cutoff.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At every event prefix of `v` that contains only events before `Gamma`, `v`'s finalized block is
    an ancestor of `B`. -/
def BlockFinalizedBelowAtDeliveriesBefore
    (S : Setup V) (rho : Run V) (v : V) (B : NamedBlock V) (Gamma : Time) : Prop :=
  ∀ (i : Nat),
    i ≤ (rho.events.filter (fun e => decide (e.time < Gamma))).length →
    Block.Preceq (rho.stateBefore S i v).st.core.F B.erase


end Protocol
end DecoupledConsensusModel

end
