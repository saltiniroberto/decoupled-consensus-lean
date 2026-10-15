import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConeAnchor

/-!
# The vote-read conditions at a slot

The conditions `VoteGradeOneCompatible` and `VoteFinJustCompatible` on what an honest active voter's
store holds at its vote, stated over a model `M : Record.Model V`.
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

/-- For every honest active member `v` of slot `(s + 1)`'s committee and every tick step `mr` at
    that slot's vote time, every grade-1 root in the frame of every outcome of `v`'s slot-`(s + 1)`
    vote read, for the round of slot `s + 1`, lies on one chain with `B`. -/
def VoteGradeOneCompatible (M : Record.Model V) (S : Setup V) {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s : Slot) : Prop :=
  ∀ (v : V) (mr : Nat), v ∈ Restated.HonSlot M S Sched (s + 1) →
    Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)) →
    ∀ n, Restated.voteReadOf M S (x[mr][v].st) (s + 1) ⇢ n →
    ∀ root : Block V,
      (M.readFrame n.cache
        (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) (s + 1))) (M.round_of S.hc (s + 1))).g1
        = some (some root) →
      Block.compatible root B = true

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every honest active member `v` of slot `(s + 1)`'s committee and every tick step `mr` at
    that slot's vote time, the finalized block and the justified block of `v`'s store before that
    tick both lie on one chain with `B`. -/
def VoteFinJustCompatible (M : Record.Model V) (S : Setup V) {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s : Slot) : Prop :=
  ∀ (v : V) (mr : Nat), v ∈ Restated.HonSlot M S Sched (s + 1) →
    Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)) →
    Block.compatible (x[mr][v].st).st.core.F B = true ∧
      ((x[mr][v].st).st.core.h_max = (x[mr][v].st).st.core.h_j + 1 →
        Block.compatible (x[mr][v].st).st.core.J B = true)

end

end DecoupledConsensusModel.Sts.Restated
