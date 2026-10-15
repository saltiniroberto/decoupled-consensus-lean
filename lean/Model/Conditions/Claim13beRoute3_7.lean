import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_7

/-!
# The SG anchor's chain in the voter tree

The condition `ConeAnchorChainInTree` on the voter tree of a slot's honest committee members, stated
over a model `M : Record.Model V`.
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

/-- Whenever `v` is an honest active member of slot `s + 1`'s committee and `mr` is the tick step at
    slot `s + 1`'s vote instant, for every outcome of `v`'s vote node state and every outcome `A` of
    its SG anchor, every block other than `A` that descends from `A` and is an ancestor of `B` is in
    every outcome of the voter tree of `v`'s slot-`(s + 1)` vote duty. -/
def ConeAnchorChainInTree (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s : Slot) : Prop :=
  ∀ (v : V) (mr : Nat), v ∈ Restated.HonSlot M S Sched (s + 1) →
    Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)) →
    ∀ n, Restated.voteReadOf M S (x[mr][v].st) (s + 1) ⇢ n →
    ∀ A, Restated.voteAnchorOf M (M.gradeContract n.cache)
          S.E S.hc (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ A →
    ∀ C : Block V,
      Block.Preceq A C →
      C ≠ A →
      Block.Preceq C B →
      ∀ T, Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ T →
      C ∈ T

end

end DecoupledConsensusModel.Sts.Restated
