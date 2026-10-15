import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Canonical cone witness

A processed descendant of a block whose chain-state height is at least the store's `h_max − 1`, over
a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- Some block `W` of `st`'s tree with `P ⪯ W` has chain-state height `(st.σ W).h ≥ st.h_max − 1`. -/
def Vocabulary.Proofs.HealingSurface.CanonicalConeWitness (M : Record.Model V) (st : M.S) (P : Block V) : Prop :=
  ∃ W ∈ st.T, Block.Preceq P W ∧ st.h_max - 1 ≤ (st.σ W).h

end

end DecoupledConsensusModel.Sts.Restated
