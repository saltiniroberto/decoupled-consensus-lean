import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Graded blocks of one view lie on one chain

Two blocks that pass the grade test of the same view are compatible, stated over a model
`M : Record.Model V`.
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
open Execution
open Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

/-- If `early ≤ late` and an outcome of the grade test of `gv` with the cutoffs `early` and `late`
    is `true` for `B` and an outcome is `true` for `B'`, then `B` and `B'` are compatible. -/
theorem Vocabulary.Proofs.HealingSurface.graded_oneChain_at_reader (facts : Record.Facts M)
    (E : Env V) (gv : M.GV) (F : Block V)
    (eta r : Round) {early late : Time} (hcut : early ≤ late)
    {B B' : Block V}
    (b : Bool) (hb : M.gradeBool E gv F eta r early late B ⇢ b) (hB : b = true)
    (b' : Bool) (hb' : M.gradeBool E gv F eta r early late B' ⇢ b') (hB' : b' = true) :
    Block.compatible B B' = true := by
  exact facts.gr.q10_graded_compatible E gv F eta r hcut b hb hB b' hb' hB'

end

end DecoupledConsensusModel.Sts.Restated
