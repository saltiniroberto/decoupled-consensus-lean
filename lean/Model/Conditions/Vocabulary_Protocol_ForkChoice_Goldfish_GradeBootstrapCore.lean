import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FGForkChoice_Finality
import Model.Record.Wiring

/-!
# SG votes, G2 reads and finalized viability

The SG votes a validator's round action can send, its node states at a round's G2 domain time, and
the condition that a store's finalized block is in its viable tree, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- The set of `v`'s round-`r` SG votes for the root of `B`, for every block `B` in
    `actionSGBlockAt M S rho v r`. -/
def Vocabulary.Proofs.HealingSurface.actionSGVoteAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    DC.NDR (Protocol.SGVote V) :=
  (fun B : Block V => (⟨v, r, some B.root⟩ : Protocol.SGVote V)) ''
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt M S rho v r

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- The set of `v`'s node states read at round `r`'s G2 domain time. -/
def Vocabulary.Proofs.HealingSurface.relativeG2Read (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (r : Round) (v : V) :
    DC.NDR M.N :=
  Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc r .g2) v

end

section
open DecoupledConsensusModel.Proofs
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- The store's finalized block `st.F` is in its viable tree. -/
def Vocabulary.Proofs.FinalizedViable (M : Record.Model V) (st : M.S) : Prop :=
  st.F ∈ Restated.Vocabulary.Protocol.V_tree M (M.toHealing st).toFG

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.actionSGVoteAt`
    is the singleton of `DecoupledConsensusModel.Proofs.HealingSurface.actionSGVoteAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.actionSGVoteAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Proofs.HealingSurface.actionSGVoteAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.actionSGVoteAt (V := V) S rho v r} := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.actionSGVoteAt,
    Vocabulary.Proofs.HealingSurface.actionSGBlockAt_vocabulary_eq]
  exact Set.image_singleton

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.relativeG2Read`
    is the singleton of `DecoupledConsensusModel.Proofs.HealingSurface.relativeG2Read`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.relativeG2Read_vocabulary_eq (S : Setup V) (rho : Run V) (r : Round) (v : V) :
    Restated.Vocabulary.Proofs.HealingSurface.relativeG2Read (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) r v =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.relativeG2Read (V := V) S rho r v} :=
  Vocabulary.Internal.PhaseGrades.readAt_vocabulary_eq S rho _ v

/-- `DecoupledConsensusModel.Proofs.FinalizedViable` holds exactly when
    `Restated.Vocabulary.Proofs.FinalizedViable` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.FinalizedViable_vocabulary_eq (st : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Proofs.FinalizedViable (V := V) st ↔ Restated.Vocabulary.Proofs.FinalizedViable (V := V) Record.Model.vocabulary st :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
