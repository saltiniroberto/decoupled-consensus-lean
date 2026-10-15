import Proofs.Vocabulary.Internal.Definitions.NamedDerived
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Named derivations of held bodies

Conditions on the named derivations of a store's held bodies, stated over a model
`M : Record.Model V`, and their counterparts at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Protocol

/-- Every held body's cached chain state is its named derivation. -/
def Vocabulary.Internal.NamedDerivedStateAgrees (M : Record.Model V) (E : Env V) (cfg : HeightConfig)
    (st : M.NS) : Prop :=
  ∀ B ∈ st.bodies, st.core.σ B.erase = M.derive_named E cfg B

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Protocol

/-- The named derivation of `C` justifies `T` at height `h`. -/
def Vocabulary.Internal.NamedJustifiedAt (M : Record.Model V) (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (M.derive_named E cfg C).J = T ∧ (M.derive_named E cfg C).h_j = h

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Protocol

/-- Every held body's named justification height is at most the store's current one. -/
def Vocabulary.Internal.NamedNoHighJustifications (M : Record.Model V) (E : Env V) (cfg : HeightConfig)
    (st : M.NS) : Prop :=
  ∀ B ∈ st.bodies, (M.derive_named E cfg B).h_j ≤ st.core.h_j

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Protocol

/-- At `Record.Model.vocabulary`, the restated `NamedDerivedStateAgrees` holds exactly when
    `DecoupledConsensusModel.Internal.NamedDerivedStateAgrees` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedDerivedStateAgrees_vocabulary_eq (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Internal.NamedDerivedStateAgrees (V := V) E cfg st ↔ Restated.Vocabulary.Internal.NamedDerivedStateAgrees (V := V) Record.Model.vocabulary E cfg st :=
  Iff.rfl

/-- At `Record.Model.vocabulary`, the restated `NamedJustifiedAt` holds exactly when
    `DecoupledConsensusModel.Internal.NamedJustifiedAt` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedJustifiedAt_vocabulary_eq (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V) (h : Height) :
    _root_.DecoupledConsensusModel.Internal.NamedJustifiedAt (V := V) E cfg C T h ↔ Restated.Vocabulary.Internal.NamedJustifiedAt (V := V) Record.Model.vocabulary E cfg C T h :=
  Iff.rfl

/-- At `Record.Model.vocabulary`, the restated `NamedNoHighJustifications` holds exactly when
    `DecoupledConsensusModel.Internal.NamedNoHighJustifications` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedNoHighJustifications_vocabulary_eq (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Internal.NamedNoHighJustifications (V := V) E cfg st ↔ Restated.Vocabulary.Internal.NamedNoHighJustifications (V := V) Record.Model.vocabulary E cfg st :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
