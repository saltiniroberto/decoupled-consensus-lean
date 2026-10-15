import Proofs.Vocabulary.Protocol.Grades.Anchor
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Model.Record.Wiring

/-!
# The equivocation time in a round summary

The field `e_v` of a round summary, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol (ChainState)
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open Internal
open Execution

/-- The field `e_v` of `v`'s round-`r` summary is the equivocation time
    `Protocol.equivocation_instant` of `v`'s SG vote timestamps. -/
theorem Vocabulary.Proofs.Optimistic.summary_e_v_eq (facts : Record.Facts M) (gv : M.GV) (r : Round) (v : V) :
    (Restated.Vocabulary.Protocol.summary M gv r v).e_v =
      Protocol.equivocation_instant gv.timestamp_sg_vote
        (Protocol.sg_votes_by (Restated.Vocabulary.Protocol.round_batch M gv r) v) := rfl

end

end DecoupledConsensusModel.Sts.Restated
