import Proofs.Vocabulary.Protocol.Handlers.StoreRoots
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Record.Wiring

/-!
# Store roots in the tree

The conditions that a named store's roots `F` and `J` are tree members and that the store is
coherent, stated over a model `M : Record.Model V`, and their agreement with the definitions of the
same name at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStoreRoots
open DecoupledConsensusModel Protocol

/-- The core store's `F` and `J` are members of its block tree. -/
def Vocabulary.Proofs.NamedStoreRoots.RootsInTree (M : Record.Model V) (st : M.NS) : Prop :=
  st.core.F ∈ st.core.T ∧ st.core.J ∈ st.core.T

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStoreRoots
open DecoupledConsensusModel Protocol

/-- The named store `st` is `Coherent` and satisfies `RootsInTree`. -/
def Vocabulary.Proofs.NamedStoreRoots.Invariant (M : Record.Model V) (E : Env V) (cfg : HeightConfig) (st : M.NS) : Prop :=
  Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg st ∧ Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree M st

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStoreRoots
open DecoupledConsensusModel Protocol

/-- `DecoupledConsensusModel.Proofs.NamedStoreRoots.RootsInTree` holds exactly when its form over
    the record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStoreRoots.RootsInTree_vocabulary_eq (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStoreRoots.RootsInTree (V := V) st ↔ Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree (V := V) Record.Model.vocabulary st :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.NamedStoreRoots.Invariant` holds exactly when its form over the
    record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStoreRoots.Invariant_vocabulary_eq (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStoreRoots.Invariant (V := V) E cfg st ↔ Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant (V := V) Record.Model.vocabulary E cfg st :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
