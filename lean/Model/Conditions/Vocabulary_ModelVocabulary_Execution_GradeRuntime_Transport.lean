import Proofs.Vocabulary.ModelVocabulary.Execution.GradeRuntime.Transport
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Grade test over tokens

The supporters, the opponents and the grade test of a block over per-validator token sets, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol

/-- The validators `v` for which `M.Supports` holds of `B` on their early, late and raw tokens under
    `covers`. -/
noncomputable def Vocabulary.Protocol.coverSupporters (M : Record.Model V) {Key Block : Type} (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => M.Supports covers (early v) (late v) (raw v) B)

end

section
open DecoupledConsensusModel.Protocol

/-- The validators `v` for which `M.Opposes` holds of `B` on their early, late and raw tokens under
    `covers`. -/
noncomputable def Vocabulary.Protocol.opponents (M : Record.Model V) {Key Block : Type} (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => M.Opposes covers (early v) (late v) (raw v) B)

end

section
open DecoupledConsensusModel.Protocol

/-- `B` passes the grade test: the weight of its opponents is less than the weight of its
    supporters. -/
noncomputable def Vocabulary.Protocol.grade (M : Record.Model V) {Key Block : Type} (w : V → Nat) (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Prop :=
  weight w (Restated.Vocabulary.Protocol.opponents M covers early late raw B) <
    weight w (Restated.Vocabulary.Protocol.coverSupporters M covers early late raw B)

end

end DecoupledConsensusModel.Sts.Restated
