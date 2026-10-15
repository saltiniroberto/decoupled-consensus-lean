module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run

@[expose] public section

/-!
# Grade reads at an action

The healing store and the grade view of a validator strictly before a round's action time.
-/

namespace DecoupledConsensusModel
namespace Internal.HealingSurface

open Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- `v`'s healing store made of every event strictly before the action time of round `r`. -/
def healStoreAt (S : Setup V) (ρ : Run V) (v : V) (r : Round) : Protocol.HealingStore V :=
  (ρ.storeBeforeTime S v (S.a r)).core.toHealing

/-- The grade view of `healStoreAt`. -/
def gradeViewAt (S : Setup V) (ρ : Run V) (v : V) (r : Round) : GradeView V :=
  (healStoreAt S ρ v r).gradeView

end Internal.HealingSurface
end DecoupledConsensusModel

end
