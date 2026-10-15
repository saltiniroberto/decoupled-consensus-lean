module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedConfirmationWalk
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Honest maximum height

The largest `h_max` an honest store holds before an event index.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The largest `h_max` held by an honest store immediately before event index `n`, or zero if the
    honest set is empty. -/
noncomputable def honestHMaxBeforeIndex
    (S : Setup V) (rho : Run V) (n : Nat) : Height :=
  rho.honest.sup fun v => (rho.stateBefore S n v).st.h_max

end Internal
end DecoupledConsensusModel

end
