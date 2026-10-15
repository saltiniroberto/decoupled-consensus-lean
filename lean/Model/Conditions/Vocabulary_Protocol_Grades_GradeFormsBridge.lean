import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Record.Wiring

/-!
# Relative grade answers

The answers a reader's G2 read gives to whether an author supports or opposes a block, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

/-- The set of answers to whether `author` supports `C` positively at round `r`'s G2 grade, computed
    from every G2 read of `reader` at round `r`. -/
def Vocabulary.Proofs.HealingSurface.relativePositiveAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (r : Round)
    (reader author : V) (C : Block V) : DC.NDR Bool :=
  { b | ∃ n ∈ Restated.Vocabulary.Proofs.HealingSurface.relativeG2Read M S rho r reader,
    M.positive (M.gradeView (M.toHealing n.st.core)) n.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) author C ⇢ b }

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

/-- The set of answers to whether `author` opposes `C` at round `r`'s G2 grade, computed from every
    G2 read of `reader` at round `r`. -/
def Vocabulary.Proofs.HealingSurface.relativeOpposingAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (r : Round)
    (reader author : V) (C : Block V) : DC.NDR Bool :=
  { b | ∃ n ∈ Restated.Vocabulary.Proofs.HealingSurface.relativeG2Read M S rho r reader,
    M.opposing (M.gradeView (M.toHealing n.st.core)) n.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) author C ⇢ b }

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Proofs.HealingSurface.relativePositiveAt` is the singleton of
    `DecoupledConsensusModel.Proofs.HealingSurface.relativePositiveAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.relativePositiveAt_vocabulary_eq (S : Setup V) (rho : Run V) (r : Round) (reader author : V) (C : Block V) :
    Restated.Vocabulary.Proofs.HealingSurface.relativePositiveAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) r reader author C =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.relativePositiveAt (V := V) S rho r reader author C} := by
  ext b
  rw [Restated.Vocabulary.Proofs.HealingSurface.relativePositiveAt,
    Vocabulary.Proofs.HealingSurface.relativeG2Read_vocabulary_eq]
  constructor
  · rintro ⟨n, hn, hb⟩
    rw [Set.mem_singleton_iff.1 hn] at hb
    exact (Record.returns_pure _ _).1 hb
  · intro hb
    exact ⟨_, Set.mem_singleton _, (Record.returns_pure _ _).2 hb⟩

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Proofs.HealingSurface.relativeOpposingAt` is the singleton of
    `DecoupledConsensusModel.Proofs.HealingSurface.relativeOpposingAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.relativeOpposingAt_vocabulary_eq (S : Setup V) (rho : Run V) (r : Round) (reader author : V) (C : Block V) :
    Restated.Vocabulary.Proofs.HealingSurface.relativeOpposingAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) r reader author C =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.relativeOpposingAt (V := V) S rho r reader author C} := by
  ext b
  rw [Restated.Vocabulary.Proofs.HealingSurface.relativeOpposingAt,
    Vocabulary.Proofs.HealingSurface.relativeG2Read_vocabulary_eq]
  constructor
  · rintro ⟨n, hn, hb⟩
    rw [Set.mem_singleton_iff.1 hn] at hb
    exact (Record.returns_pure _ _).1 hb
  · intro hb
    exact ⟨_, Set.mem_singleton _, (Record.returns_pure _ _).2 hb⟩

end

end DecoupledConsensusModel.Sts.Restated
