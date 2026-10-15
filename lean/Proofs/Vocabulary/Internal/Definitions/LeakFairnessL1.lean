module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ActionSources
public import Proofs.Vocabulary.Internal.Legacy.Definitions.LeakLedger
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight

@[expose] public section

/-!
# Leak-fairness helpers

The record `currentProductionRecord` a validator holds at a round's action time.
-/
namespace DecoupledConsensusModel.Internal.LeakFairness
open Execution Protocol
open Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

def currentProductionRecord (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.Record :=
  (rho.stateBeforeTime S (S.a r) v).Λ.legacy

end DecoupledConsensusModel.Internal.LeakFairness

end
