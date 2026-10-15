import Proofs.Vocabulary.Protocol.ChainState.FinalityCertificates
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Model.Record.Wiring

/-!
# Finality certificates

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a named block
whose derived finalized height is nonzero has a named ancestor that erases to its finalized block,
and a quorum each of whose signers has an attestation with that finality pair in an ancestor of the
block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedFinalityCertificates
open Protocol

/-- If the chain state derived from `D` has a nonzero finalized height `h_F`, some named ancestor
    `F` of `D` erases to that state's finalized block, and some quorum `Q` has, for each signer, an
    attestation by that signer included in an ancestor of `D` whose finality pair is `h_F` with
    `F`'s root. -/
theorem Vocabulary.Proofs.NamedFinalityCertificates.finality_certificate (facts : Record.Facts M) (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hnz : (M.derive_named E cfg D).h_F ≠ 0) :
    ∃ F : NamedBlock V, NamedBlock.Preceq F D ∧
      F.erase = (M.derive_named E cfg D).F ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
          NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
          a.val_index = signer ∧
          a.finality_pair = some ⟨(M.derive_named E cfg D).h_F, F.root⟩ :=
  facts.csAdded.finality_certificate E cfg D hnz

end

end DecoupledConsensusModel.Sts.Restated
