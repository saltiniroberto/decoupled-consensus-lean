import Proofs.Vocabulary.ModelVocabulary.Goldfish.ForkChoice
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Goldfish supporters

The supporter set of a block in the Goldfish fork choice, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol

/-- The outcomes of the raw supporters of `B` in `T` at slot `s`, from `votes` and `support_votes`,
    each a set of validators or a failure. -/
def Vocabulary.Protocol.goldfishSupporters (M : Record.Model V) (_E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    DC.NDRE (Finset V) :=
  M.raw_supporters T votes support_votes s B

end

end DecoupledConsensusModel.Sts.Restated
