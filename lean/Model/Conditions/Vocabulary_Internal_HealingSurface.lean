import Proofs.Vocabulary.Internal.HealingSurface
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# Grade round readiness and honest targets

The window in which a round's grade deliveries can be produced, and the condition that an honest
validator never names two targets at one height, stated over a model `M : Record.Model V`, and their
counterparts at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open Execution
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open PhaseGrades NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- `S.E.t_GST` is at or before round `r`'s early G2 cutoff, and round `r`'s G0 domain instant is at
    most the horizon of `ρ`. -/
def Vocabulary.Internal.HealingSurface.GradeRoundReady (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (r : Round) : Prop :=
  S.E.t_GST ≤ M.early S.E S.hc r .g2 ∧
    M.domain S.E S.hc r .g0 ≤ ρ.horizon

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open Execution
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open PhaseGrades NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- For every honest validator `v` of `ρ` and named attestations `a`, `a'` that `v` emits along the
    path `W` of `ρ`, at every height `h` a target of `a`'s erasure at `h` and a target of `a'`'s
    erasure at `h` are the same block. -/
def Vocabulary.Internal.HealingSurface.HonestNoDoubleTarget (M : Record.Model V) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) : Prop :=
  ∀ v ∈ ρ.honest, ∀ (a a' : NamedAttestation V) (t t' : Time),
    (Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.attest a) t) → (Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.attest a') t') →
      ∀ (h : Height) (T T' : BlockId),
        T ∈ targetsAt a.erase h → T' ∈ targetsAt a'.erase h → T = T'

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open Execution
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open PhaseGrades NamedRecoveryRead DecoupledConsensusModel.Protocol

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `GradeRoundReady` holds exactly when
    `DecoupledConsensusModel.Internal.HealingSurface.GradeRoundReady` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.HealingSurface.GradeRoundReady_vocabulary_eq (S : Setup V) (ρ : Run V) (r : Round) :
    _root_.DecoupledConsensusModel.Internal.HealingSurface.GradeRoundReady (V := V) S ρ r ↔ Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) r :=
  Iff.rfl

/-- At `Record.Model.vocabulary`, along the path `fun i => NamedRun.stateBefore S ρ i`, the restated
    `HonestNoDoubleTarget` holds exactly when
    `DecoupledConsensusModel.Internal.HealingSurface.HonestNoDoubleTarget` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.HealingSurface.HonestNoDoubleTarget_vocabulary_eq (S : Setup V) (ρ : Run V) :
    _root_.DecoupledConsensusModel.Internal.HealingSurface.HonestNoDoubleTarget (V := V) S ρ ↔
      Restated.Vocabulary.Internal.HealingSurface.HonestNoDoubleTarget (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => NamedRun.stateBefore S ρ i) := by
  unfold _root_.DecoupledConsensusModel.Internal.HealingSurface.HonestNoDoubleTarget
    Restated.Vocabulary.Internal.HealingSurface.HonestNoDoubleTarget
  simp only [← Vocabulary.Execution.Run.emits_vocabulary_eq, Record.Run.ofVocabulary_honest]

end

end DecoupledConsensusModel.Sts.Restated
