module
public import Proofs.Vocabulary.Execution.Acceptance
public import Proofs.Vocabulary.Protocol.ChainState.FinalityCertificates
public import Proofs.Vocabulary.Protocol.ValidatorClient.BlockEmission
public import Proofs.Vocabulary.Execution.FGSelectorWitness
public import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
public import Proofs.Vocabulary.Internal.Definitions.NamedCertificates
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Attestations carried by a named chain

Private facts on the attestations a named chain carries and on their heights.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem named_mem_chain_attestations {a : NamedAttestation V} :
    ∀ B : NamedBlock V, a ∈ Protocol.named_chain_attestations B →
      ∃ X : NamedBlock V, NamedBlock.Preceq X B ∧ a ∈ X.attestations := by
  intro B
  induction B with
  | genesis =>
      simp [Protocol.named_chain_attestations, NamedBlock.attestations]
  | node parent slot root votes support rows proposer ih =>
      intro h
      simp only [Protocol.named_chain_attestations, Finset.mem_union,
        List.mem_toFinset] at h
      rcases h with h | h
      · obtain ⟨X, hXB, hX⟩ := ih h
        exact ⟨X, Proofs.NamedAncestry.named_extend slot root votes support rows proposer hXB,
          hX⟩
      · exact ⟨.node parent slot root votes support rows proposer,
          Proofs.NamedAncestry.named_self _, by
            simpa only [NamedBlock.attestations] using h⟩

omit [Fintype V] in
private theorem named_row_mem_chain_of_ancestor
    {A B : NamedBlock V} {a : NamedAttestation V}
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations B := by
  induction B generalizing A with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst A
      simp [NamedBlock.attestations] at ha
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      simp only [Protocol.named_chain_attestations, Finset.mem_union,
        List.mem_toFinset]
      rcases hAB with rfl | hparent
      · exact Or.inr ha
      · exact Or.inl (ih hparent ha)

omit [DecidableEq V] [Fintype V] in
private theorem named_height_of_matches
    {a : NamedAttestation V} {H : Height} {root : BlockId}
    (hmatch : NamedHeightPair.matchesEntry H root a.height_pair = true) :
    a.height_pair.erase.height? = some H := by
  cases hp : a.height_pair with
  | empty =>
      simp [hp, NamedHeightPair.matchesEntry] at hmatch
  | vote height entry timeout =>
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hmatch
      cases timeout <;>
        simp [NamedHeightPair.erase, HeightPair.height?, hmatch.1]

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
