import Proofs.Vocabulary.Protocol.ChainState.NjGap
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Protocol_ChainState_NjGap
import Model.Record.Wiring

/-!
# The FG root when the justified height is less than the maximum minus one

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: when a store's
justified height is less than `H` and its maximum height is at least `H + 1`, its FG root is its
finalized block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NjGap
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal
open Execution

/-- If `st.h_j < H` and `H + 1 ≤ st.h_max`, the FG root of `st`'s healing store is `st`'s finalized
    block. -/
theorem Vocabulary.Proofs.NjGap.get_fg_root_eq_F_of_gap (facts : Record.Facts M) {st : M.S} {H : Height}
    (hj : st.h_j < H) (hmax : H + 1 ≤ st.h_max) :
    M.get_fg_root (M.toHealing st).toFG = st.F := by
  have hne : ¬(st.h_max = st.h_j + 1) := fun h => by
    have hlt : st.h_j + 1 < st.h_max := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hj) hmax
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  exact facts.fc.get_fg_root_toHealing_of_ne st hne

end

end DecoupledConsensusModel.Sts.Restated
