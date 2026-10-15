import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_23

/-!
# Attestations refused or recorded for good

The conditions `SgRefused`, `IncludedAttestationsSettled` and `SgMono` on an SG attestation and a
store, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- At the store `c`, the round of `b` is more than `hc.η_SG` rounds before the store's round, or
    the confirmed block `b` names is already among those the store holds from `b`'s signer for `b`'s
    round, or the store already holds two such blocks. -/
def SgRefused (M : Record.Model V) (hc : HealConfig) (c : M.S) (b : CombinedAttestation V) : Prop :=
  b.round < (M.round_of hc c.s) - hc.η_SG ∨ b.confirmed ∈ M.round_votes c b ∨
    (M.round_votes c b).card = 2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- For every block `B` whose signed body the store holds and every attestation `a` that `B`
    includes, `a` is among the store's rows of `a`'s round, or `SgRefused` holds of `a`'s erasure at
    the store. -/
def IncludedAttestationsSettled (M : Record.Model V) (hc : HealConfig) (st : M.NS) : Prop :=
  ∀ B ∈ st.bodies, ∀ a ∈ B.attestations, a ∈ st.sg_rows a.round ∨ Restated.SgRefused M hc st.core a.erase

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- From the store `st` to the store `st'`: an attestation refused for good stays refused, a
    recorded attestation stays recorded, an attestation neither recorded nor admissible stays
    unrecorded, and `IncludedAttestationsSettled` is kept. -/
structure SgMono (M : Record.Model V) (hc : HealConfig) (st st' : M.NS) : Prop where
  refused : ∀ b : CombinedAttestation V, Restated.SgRefused M hc st.core b → Restated.SgRefused M hc st'.core b
  rows : ∀ a : NamedAttestation V, a ∈ st.sg_rows a.round → a ∈ st'.sg_rows a.round
  excluded : ∀ a : NamedAttestation V, a ∉ st.sg_rows a.round →
    Restated.SgRefused M hc st.core a.erase → a ∉ st'.sg_rows a.round
  settled : Restated.IncludedAttestationsSettled M hc st → Restated.IncludedAttestationsSettled M hc st'

end

/-! ## Agreement at the model `Record.Model.vocabulary` -/

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- `_root_.DecoupledConsensusModel.Sts.SgRefused` holds exactly when `Restated.SgRefused` holds at
    the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem SgRefused_vocabulary_eq (hc : HealConfig) (c : Store V) (b : CombinedAttestation V) :
    _root_.DecoupledConsensusModel.Sts.SgRefused (V := V) hc c b ↔ Restated.SgRefused (V := V) Record.Model.vocabulary hc c b :=
  Iff.rfl

/-- `_root_.DecoupledConsensusModel.Sts.IncludedAttestationsSettled` holds exactly when
    `Restated.IncludedAttestationsSettled` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem IncludedAttestationsSettled_vocabulary_eq (hc : HealConfig) (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Sts.IncludedAttestationsSettled (V := V) hc st ↔ Restated.IncludedAttestationsSettled (V := V) Record.Model.vocabulary hc st :=
  Iff.rfl

/-- `_root_.DecoupledConsensusModel.Sts.SgMono` holds exactly when `Restated.SgMono` holds at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem SgMono_vocabulary_eq (hc : HealConfig) (st st' : NamedStore V) :
    _root_.DecoupledConsensusModel.Sts.SgMono (V := V) hc st st' ↔ Restated.SgMono (V := V) Record.Model.vocabulary hc st st' :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [record_vocabulary] at *) <;> assumption

end

end DecoupledConsensusModel.Sts.Restated
