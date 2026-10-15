import Proofs.Vocabulary.Protocol.Handlers.ConfirmationMembership
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Record.Wiring

/-!
# Confirmation membership

The condition that a store's confirmed and stable blocks are tree members, stated over a model
`M : Record.Model V`, and its agreement with the definitions of the same name at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedConfirmationMembership
open Protocol

/-- The live confirmed, latest confirmed and latest stable blocks of `st` are members of its block
    tree. -/
def Vocabulary.Proofs.NamedConfirmationMembership.Confirmed (M : Record.Model V) (st : M.S) : Prop :=
  st.live_confirmed ∈ st.T ∧ st.latest_confirmed ∈ st.T ∧ st.latest_stable ∈ st.T

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedConfirmationMembership
open Protocol

/-- The store-roots invariant of `st` together with `Confirmed` of its core store. -/
def Vocabulary.Proofs.NamedConfirmationMembership.Invariant (M : Record.Model V) (E : Env V) (cfg : HeightConfig) (st : M.NS) : Prop :=
  Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant M E cfg st ∧ Restated.Vocabulary.Proofs.NamedConfirmationMembership.Confirmed M st.core

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedConfirmationMembership
open Protocol

/-- `DecoupledConsensusModel.Proofs.NamedConfirmationMembership.Confirmed` holds exactly when its
    form over the record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedConfirmationMembership.Confirmed_vocabulary_eq (st : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Proofs.NamedConfirmationMembership.Confirmed (V := V) st ↔ Restated.Vocabulary.Proofs.NamedConfirmationMembership.Confirmed (V := V) Record.Model.vocabulary st :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.NamedConfirmationMembership.Invariant` holds exactly when its
    form over the record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedConfirmationMembership.Invariant_vocabulary_eq (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Proofs.NamedConfirmationMembership.Invariant (V := V) E cfg st ↔ Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (V := V) Record.Model.vocabulary E cfg st :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
