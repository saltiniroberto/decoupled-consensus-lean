import Proofs.Vocabulary.Protocol.Evidence.ProvenanceBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Justification and finalization on a retained body

The conditions that a store's justification and finalization are derived from a body it retains,
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Internal Execution Protocol

/-- Some body `D` the store `st` retains derives `st`'s justified block `J` and its height `h_j`. -/
def Vocabulary.Proofs.Bridges.NamedStoreJustificationOnChain (M : Record.Model V) (S : Setup V) (st : M.NS) : Prop :=
  ∃ D ∈ st.bodies, (M.derive_named S.E S.cfg D).J = st.core.J ∧
    (M.derive_named S.E S.cfg D).h_j = st.core.h_j

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Internal Execution Protocol

/-- Some body the store `st` retains derives `st`'s finalized block `F` with a finalized height less
    than `st.core.h_max`, and `NamedStoreJustificationOnChain M S st` holds. -/
def Vocabulary.Proofs.Bridges.NamedProvenance (M : Record.Model V) (S : Setup V) (st : M.NS) : Prop :=
  (∃ D ∈ st.bodies, (M.derive_named S.E S.cfg D).F = st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < st.core.h_max) ∧
    Restated.Vocabulary.Proofs.Bridges.NamedStoreJustificationOnChain M S st

end

end DecoupledConsensusModel.Sts.Restated
