import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_NjGap
import Model.Record.Wiring

/-!
# The FG root when the justified height is two short of the maximum

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: when a store's
justified height plus two is at most `Hm` and its maximum height is `Hm`, its FG root is its
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
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

/-- If the store `st` has `st.h_j + 2 ≤ Hm` and `st.h_max = Hm`, the FG root of `st`'s healing store
    is `st`'s finalized block. -/
theorem Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame (facts : Record.Facts M) {st : M.S} {Hm : Height}
    (hgate : st.h_j + 2 ≤ Hm) (hmax : st.h_max = Hm) :
    M.get_fg_root (M.toHealing st).toFG = st.F := by
  apply Restated.Vocabulary.Proofs.NjGap.get_fg_root_eq_F_of_gap facts (H := Hm - 1)
  · exact Nat.lt_of_succ_le (Nat.le_sub_of_add_le hgate)
  · rw [hmax]
    have h1 : 1 ≤ Hm := le_trans (Nat.succ_le_succ (Nat.zero_le _))
      ((Nat.le_add_left 2 st.h_j).trans hgate)
    exact le_of_eq (Nat.sub_add_cancel h1)

end

end DecoupledConsensusModel.Sts.Restated
