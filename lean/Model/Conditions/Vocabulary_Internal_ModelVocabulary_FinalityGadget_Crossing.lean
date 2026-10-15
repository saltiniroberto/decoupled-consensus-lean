import Proofs.Vocabulary.Internal.ModelVocabulary.FinalityGadget.Crossing
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Committee pools

The condition that every Goldfish vote in a store comes from its slot's committee, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol

/-- Every Goldfish vote of a slot `k` in `st` is cast by a member of slot `k`'s committee. -/
def Vocabulary.Protocol.CommitteePools (M : Record.Model V) (E : Env V) (st : M.S) : Prop :=
  ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k →
    u.val_index ∈ E.committee k

end

end DecoupledConsensusModel.Sts.Restated
