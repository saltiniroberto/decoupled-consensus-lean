import Proofs.Vocabulary.Protocol.ChainState.W4FKChainFinalityWrite
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Protocol_ChainState_W4FKChainFinalityWrite
import Model.Conditions.Vocabulary_Statements_Instantiation_Certificates
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Named finality from honest action rows

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, under
`BelowOneThird` for the honest validators: finality coverage of every honest validator is a named
finality quorum, and a proposal whose parent or own rows cover every honest round-`r` action row
with one finality pair finalizes the parent's justified block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

/-- Under `BelowOneThird S rho.honest`, if `sigma` has justified height `h_j` and justified block
    `J`, and every honest validator is in the finality set of `sigma` or has an attestation in `B`
    with finality pair `h_j` and `J`'s root, then `NamedFinalityQuorumCoveredByChild` holds for
    `sigma`, `B`, `h_j` and `J`. -/
theorem Vocabulary.Proofs.HealingSurface.namedFinalityQuorumCoveredByChild_of_honest (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (hfb : DecoupledConsensusModel.Execution.BelowOneThird S rho.honest)
    {sigma : M.CS} {B : NamedBlock V} {h_j : Height} {J : Block V}
    (hhj : sigma.h_j = h_j) (hJ : sigma.J = J)
    (hcovered : ∀ i ∈ rho.honest,
      i ∈ M.finalize sigma ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.finality_pair = some ⟨h_j, J.root⟩) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityQuorumCoveredByChild M S.E sigma B h_j J :=
  ⟨hhj, hJ, rho.honest,
    Proofs.ModelProperties.isQuorum_of_q_le S.E
      (AlignedRoundLemmas.honestQuorum_of_belowOneThird hfb), hcovered⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

/-- Under `BelowOneThird S rho.honest`, if `some B` is a proposal of slot `s`, `A v` is a round-`r`
    action row of each honest validator `v`, every such row is live in `B`'s parent (with `v` in the
    parent's finality set) or included in `B`'s own rows, the parent's chain state has justified
    height `hJ` and justified block `J` with root `TJ`, its finalized height is less than `hJ`, and
    every such row has finality pair `(hJ, TJ)`, then the chain state derived for `B` has finalized
    block `J` at finalized height `hJ`. -/
theorem Vocabulary.Proofs.HealingSurface.namedFinalizedAt_of_actionRows (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (hbot : DecoupledConsensusModel.Execution.BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {hJ : Height} {TJ : BlockId} {J : Block V}
    {B : NamedBlock V}
    (hB : some B ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s)
    (A : V → NamedAttestation V)
    (hA : ∀ v ∈ rho.honest, A v ∈ Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt M S rho v r)
    (hcoverage : ∀ v ∈ rho.honest,
      let a := A v
      (a ∈ Protocol.named_chain_attestations B.parent ∧
          v ∈ M.finalize (M.derive_named S.E S.cfg B.parent)) ∨
        a ∈ B.attestations)
    (hparentHJ : (M.derive_named S.E S.cfg B.parent).h_j = hJ)
    (hparentJ : (M.derive_named S.E S.cfg B.parent).J = J)
    (hroot : J.root = TJ)
    (hdebt : (M.derive_named S.E S.cfg B.parent).h_F < hJ)
    (hfinality : ∀ v ∈ rho.honest,
      (A v).finality_pair = some ⟨hJ, TJ⟩) :
    Restated.Vocabulary.Statements.Instantiation.NamedFinalizedAt M S.E S.cfg B J hJ := by
  have hne : B ≠ NamedBlock.genesis := by
    obtain ⟨n, hn, hBn⟩ := hB
    obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract n.cache) S.E
      S.hc (S.node (S.E.proposer s)) (M.toHealing n.st.core)
    obtain ⟨p, hp, -⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho s
      n hn hBn input hinput
    intro hgen
    rw [hgen] at hp
    cases hp
  refine facts.csAdded.namedFinalizedAt_of_finalityQuorumCoveredByChild S.E S.cfg hne ?_ hdebt
  refine Restated.Vocabulary.Proofs.HealingSurface.namedFinalityQuorumCoveredByChild_of_honest facts S hbot hparentHJ hparentJ ?_
  intro v hv
  have hcovered := hcoverage v hv
  dsimp only at hcovered
  rcases hcovered with hparent | hchild
  · exact Or.inl hparent.2
  · obtain ⟨n, hn, ns, rec, hAn⟩ := hA v hv
    refine Or.inr ⟨A v, hchild, ?_, ?_⟩
    · obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
      obtain ⟨W, hW⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g2
      exact (Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho v r n hn
        (ns, rec, A v) hAn g2 hg2 W hW).1
    · rw [hfinality v hv, hroot]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

end

end DecoupledConsensusModel.Sts.Restated
