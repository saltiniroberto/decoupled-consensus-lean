import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Node
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# Emitting tick

The answers a validator's tick can return, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution

/-- The set of pairs of a node state and the objects sent that `v`'s tick at `t` from node state `n`
    can return. -/
abbrev Vocabulary.Execution.on_tick_emit (M : Record.Model V) (S : Setup V) (v : V) (n : M.N) (t : Time) :
    DC.NDR (M.N × List (NamedObject V)) :=
  { out | M.tick S v n t ⇢ out }

end

end DecoupledConsensusModel.Sts.Restated
