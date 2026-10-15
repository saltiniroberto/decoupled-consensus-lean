import Proofs.Vocabulary.Protocol.Handlers.NamedStore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Named stores

Conditions relating a named store's block bodies and vote rows to its core store, stated over a
model `M : Record.Model V`, and their agreement with the definitions of the same name at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults

/-- The core store's block tree is the erasure of the named store's bodies. -/
def Vocabulary.Proofs.NamedStore.TreeView (M : Record.Model V) (st : M.NS) : Prop :=
  st.core.T = st.bodies.image NamedBlock.erase

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults

/-- No two distinct bodies of the named store have the same erasure. -/
def Vocabulary.Proofs.NamedStore.ErasureUnique (M : Record.Model V) (st : M.NS) : Prop :=
  ∀ A ∈ st.bodies, ∀ B ∈ st.bodies, A.erase = B.erase → A = B

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults

/-- The named store's bodies contain the genesis body and the parent of each body. -/
def Vocabulary.Proofs.NamedStore.NamedParentClosed (M : Record.Model V) (st : M.NS) : Prop :=
  NamedBlock.genesis ∈ st.bodies ∧ ∀ B ∈ st.bodies, B.parent ∈ st.bodies

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults

/-- For every round `r`, the core store's SG votes are the erasures of the named store's SG rows. -/
def Vocabulary.Proofs.NamedStore.PoolView (M : Record.Model V) (st : M.NS) : Prop :=
  ∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults

/-- The chain state the core store holds for each body's erasure is the one `M.derive_named` derives
    for that body. -/
def Vocabulary.Proofs.NamedStore.DerivedView (M : Record.Model V) (E : Env V) (cfg : HeightConfig) (st : M.NS) : Prop :=
  ∀ B ∈ st.bodies, st.core.σ B.erase = M.derive_named E cfg B

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults

/-- The named store `st` satisfies `TreeView`, `ErasureUnique`, `NamedParentClosed`, `PoolView` and
    `DerivedView`. -/
def Vocabulary.Proofs.NamedStore.Coherent (M : Record.Model V) (E : Env V) (cfg : HeightConfig) (st : M.NS) : Prop :=
  Restated.Vocabulary.Proofs.NamedStore.TreeView M st ∧ Restated.Vocabulary.Proofs.NamedStore.ErasureUnique M st ∧ Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st ∧ Restated.Vocabulary.Proofs.NamedStore.PoolView M st ∧ Restated.Vocabulary.Proofs.NamedStore.DerivedView M E cfg st

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults

/-- `DecoupledConsensusModel.Proofs.NamedStore.TreeView` holds exactly when its form over the record
    holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStore.TreeView_vocabulary_eq (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStore.TreeView (V := V) st ↔ Restated.Vocabulary.Proofs.NamedStore.TreeView (V := V) Record.Model.vocabulary st :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.NamedStore.ErasureUnique` holds exactly when its form over the
    record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStore.ErasureUnique_vocabulary_eq (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStore.ErasureUnique (V := V) st ↔ Restated.Vocabulary.Proofs.NamedStore.ErasureUnique (V := V) Record.Model.vocabulary st :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.NamedStore.NamedParentClosed` holds exactly when its form over
    the record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStore.NamedParentClosed_vocabulary_eq (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStore.NamedParentClosed (V := V) st ↔ Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed (V := V) Record.Model.vocabulary st :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.NamedStore.PoolView` holds exactly when its form over the record
    holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStore.PoolView_vocabulary_eq (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStore.PoolView (V := V) st ↔ Restated.Vocabulary.Proofs.NamedStore.PoolView (V := V) Record.Model.vocabulary st :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.NamedStore.DerivedView` holds exactly when its form over the
    record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStore.DerivedView_vocabulary_eq (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStore.DerivedView (V := V) E cfg st ↔ Restated.Vocabulary.Proofs.NamedStore.DerivedView (V := V) Record.Model.vocabulary E cfg st :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.NamedStore.Coherent` holds exactly when its form over the record
    holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedStore.Coherent_vocabulary_eq (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedStore.Coherent (V := V) E cfg st ↔ Restated.Vocabulary.Proofs.NamedStore.Coherent (V := V) Record.Model.vocabulary E cfg st :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
