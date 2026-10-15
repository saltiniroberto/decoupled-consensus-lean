import Proofs.Vocabulary.Protocol.ChainState.AlignedRoundLemmas
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ChainState_AlignedRoundLemmas
import Model.Record.Wiring

/-!
# No slashable weight between two attestation sets

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, along a path `W`
of a run: when the validators of a set `H` hold less than a third of the weight, never emit two
slashable rows, and are the authors only of attestations that erase rows they emit, two attestation
sets have no slashable weight between them.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Execution

/-- If the validators of `H` have less than a third of the weight, no validator emits, along the
    path `W` of `ρ`, two rows whose erasures are slashable together, and every attestation of `A₁`
    and of `A₂` attributed to a member of `H` is the erasure of a row that validator emits along
    `W`, then `A₁` and `A₂` do not have slashable weight between them. -/
theorem Vocabulary.Proofs.AlignedRoundLemmas.noSlashableWeightBetween_of_belowOneThird (facts : Record.Facts M) {S : Setup V} {ρ : Record.Run V}
    (W : Nat → V → M.N)
    {H : Finset V} {A₁ A₂ : Finset (CombinedAttestation V)}
    (hbot : _root_.DecoupledConsensusModel.Execution.BelowOneThird S H)
    (hself : Restated.Vocabulary.Proofs.AlignedRoundLemmas.NoSelfSlashing M S ρ W)
    (h₁ : Restated.Vocabulary.Proofs.AlignedRoundLemmas.CarriedByHonest M S ρ W H A₁)
    (h₂ : Restated.Vocabulary.Proofs.AlignedRoundLemmas.CarriedByHonest M S ρ W H A₂) :
    ¬ M.HasSlashableWeightBetween S.E A₁ A₂ := by
  intro hS
  obtain ⟨X, hw, hX⟩ := facts.ev.hasSlashableWeightBetween_elim hS
  refine facts.ev.no_faulty_intersection hbot hw ?_
  intro i hi hiH
  obtain ⟨a, ha, b, hb, hav, hbv, hsl⟩ := facts.ev.slashableBetween_elim (hX i hi)
  obtain ⟨ra, ta, hra, hea⟩ := h₁ a ha (by rw [hav]; exact hiH)
  obtain ⟨rb, tb, hrb, heb⟩ := h₂ b hb (by rw [hbv]; exact hiH)
  have hsafe := hself i ra rb ⟨ta, hav ▸ hea⟩ ⟨tb, hbv ▸ heb⟩
  rw [hra, hrb] at hsafe
  have hsl' : M.slashable a b = true := facts.csAdded.Slashable_iff.mp hsl
  rw [hsafe] at hsl'
  simp at hsl'

end

end DecoupledConsensusModel.Sts.Restated
