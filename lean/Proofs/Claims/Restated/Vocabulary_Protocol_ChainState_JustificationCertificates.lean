import Proofs.Vocabulary.Protocol.ChainState.JustificationCertificates
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Model.Record.Wiring

/-!
# Justification certificates

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a named block
whose derived justified height is nonzero has a named ancestor that erases to its justified block,
and a quorum each of whose signers has a vote for that height and root in an ancestor of the block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedJustificationCertificates
open Protocol

/-- If the chain state derived from `D` has a nonzero justified height `h_j`, some named ancestor
    `J` of `D` erases to that state's justified block, and some quorum `Q` has, for each signer, an
    attestation by that signer included in an ancestor of `D` whose height pair is the vote for
    `h_j` and `J`'s root with flag `false`. -/
theorem Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate (facts : Record.Facts M) (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hnz : (M.derive_named E cfg D).h_j ≠ 0) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J D ∧
      J.erase = (M.derive_named E cfg D).J ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
          NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
          a.val_index = signer ∧
          a.height_pair = .vote (M.derive_named E cfg D).h_j J.root false :=
  facts.csAdded.justification_certificate E cfg D hnz

end

end DecoupledConsensusModel.Sts.Restated
