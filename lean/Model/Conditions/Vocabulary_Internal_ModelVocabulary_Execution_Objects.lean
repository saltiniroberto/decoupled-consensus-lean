import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Objects
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceipt_processed

/-!
# Processed objects

Whether a store has recorded a block, a Goldfish vote or an attestation, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Object

/-- Whether the store `st` has recorded an object: a block `B` when `B ∈ st.bodies`, a Goldfish vote
    `u` when `u ∈ st.core.gf_votes u.slot`, and an attestation `a` when `a ∈ st.sg_rows a.round`. -/
def Vocabulary.Execution.Object.processed (M : Record.Model V) (st : M.NS) : NamedObject V → Bool
  | .block B => decide (B ∈ st.bodies)
  | .gfVote u => decide (u ∈ st.core.gf_votes u.slot)
  | .attest a => decide (a ∈ st.sg_rows a.round)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Object

/-- `DecoupledConsensusModel.Execution.Object.processed` equals
    `Restated.Vocabulary.Execution.Object.processed` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Object.processed_vocabulary_eq  :
    _root_.DecoupledConsensusModel.Execution.Object.processed = Restated.Vocabulary.Execution.Object.processed (V := V) Record.Model.vocabulary := by
  funext st o
  cases o with
  | block B =>
      exact Bool.eq_iff_iff.2 ((_root_.DecoupledConsensusModel.Sts.processed_block_iff st B).trans
        (decide_eq_true_iff).symm)
  | gfVote u =>
      exact Bool.eq_iff_iff.2 ((_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff st u).trans
        (decide_eq_true_iff).symm)
  | attest a =>
      exact Bool.eq_iff_iff.2 ((_root_.DecoupledConsensusModel.Sts.processed_attest_iff st a).trans
        (decide_eq_true_iff).symm)

end

end DecoupledConsensusModel.Sts.Restated
