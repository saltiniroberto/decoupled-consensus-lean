import Proofs.Vocabulary.Protocol.Grades.OppositionGradeTransport
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_ModelVocabulary_Execution_GradeRuntime_Transport
import Model.Record.Wiring

/-!
# Grade margins carried between token sets

A strict weighted-grade margin for a block carries from source token sets to target token sets,
stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol

/-- If each validator's source tokens are nested early in late in raw, its target early tokens are
    among its target late tokens, every source early token covering `B` reaches the target early
    tokens or a target raw equivocation at its round, every target late token comes back as a source
    late token or a source raw equivocation at its round, and every target raw equivocation comes
    back as a source one, then a strict grade margin for `B` at the source tokens is a strict grade
    margin for `B` at the target tokens. -/
theorem Vocabulary.Protocol.grade_transport_with_cap (facts : Record.Facts M) {Key Block : Type}
    (w : V → Nat) (covers : Key → Block → Prop)
    {se sl sr te tl tr : V → Finset (Token Key)} {B : Block}
    (hSourceLate : ∀ v, se v ⊆ sl v) (hSourceRaw : ∀ v, sl v ⊆ sr v)
    (hTargetLate : ∀ v, te v ⊆ tl v)
    (hForward : ∀ v u, u ∈ se v → covers u.key B →
      u ∈ te v ∨ EquivocationAt (tr v) u.round)
    (hLateBack : ∀ v x, x ∈ tl v → x ∈ sl v ∨ EquivocationAt (sr v) x.round)
    (hEqBack : ∀ v k, EquivocationAt (tr v) k → EquivocationAt (sr v) k)
    (h : Restated.Vocabulary.Protocol.grade M w covers se sl sr B) : Restated.Vocabulary.Protocol.grade M w covers te tl tr B := by
  classical
  have hp : Restated.Vocabulary.Protocol.coverSupporters M covers se sl sr B ⊆ Restated.Vocabulary.Protocol.coverSupporters M covers te tl tr B := by
    intro v hv
    simp only [Restated.Vocabulary.Protocol.coverSupporters, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact facts.gr.supports_transport_with_cap covers (hSourceLate v) (hSourceRaw v)
      (hTargetLate v) (hForward v) (hLateBack v) (hEqBack v) hv
  have hn : Restated.Vocabulary.Protocol.opponents M covers te tl tr B ⊆ Restated.Vocabulary.Protocol.opponents M covers se sl sr B := by
    intro v hv
    simp only [Restated.Vocabulary.Protocol.opponents, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact facts.gr.opposition_back_with_cap covers (hSourceLate v) (hForward v)
      (hLateBack v) (hEqBack v) hv
  exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset hn)
    (lt_of_lt_of_le h (Finset.sum_le_sum_of_subset hp))

end

end DecoupledConsensusModel.Sts.Restated
