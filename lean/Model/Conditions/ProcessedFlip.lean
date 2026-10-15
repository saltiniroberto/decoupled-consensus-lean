import Proofs.Claims.ProcessedFlip
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects

/-!
# Objects a step records

The witness that an object reached a validator inside a block, and the condition that a step records
only given objects or objects carried by given blocks, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The witness that an object reached a validator inside the block `B`: the object's position in
    `B`'s own list, and `B`'s entry into the erased tree (for a Goldfish vote) or into the named
    bodies (for an attestation) of the store `before`. -/
def CarriedCall (M : Record.Model V) (S : Setup V) (before : M.NS) (B : NamedBlock V) :
    NamedObject V → Prop
  | .block _ => False
  | .gfVote u => (∃ j : Nat, B.gf_votes[j]? = some u) ∧ B.erase ∉ before.core.T ∧
      B.erase ∈ (M.postCore S before B).core.T
  | .attest a => (∃ j : Nat, B.attestations[j]? = some a) ∧ B ∉ before.bodies ∧
      B ∈ (M.postCore S before B).bodies

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Every object the step from `a` to `b` records was already recorded at `a`, or is one of the
    objects `es` names, or is carried by a block `es` names whose witness `CarriedCall` at `a`
    admits it. -/
def AddsOnlyCarried (M : Record.Model V) (S : Setup V) (a b : M.NS) (es : List (NamedObject V)) : Prop :=
  (∀ o : NamedObject V, Restated.Vocabulary.Execution.Object.processed M a o = true →
      Restated.Vocabulary.Execution.Object.processed M b o = true) ∧
    ∀ o : NamedObject V, Restated.Vocabulary.Execution.Object.processed M a o = false →
      Restated.Vocabulary.Execution.Object.processed M b o = true →
      o ∈ es ∨ ∃ B : NamedBlock V, NamedObject.block B ∈ es ∧ Restated.CarriedCall M S a B o

end

end DecoupledConsensusModel.Sts.Restated
