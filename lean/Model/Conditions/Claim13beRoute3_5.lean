import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_5

/-!
# Well-shaped tree blocks

The invariant `TreeBlockShaped` on the blocks of a store's tree, its one-step form, and the
condition `DeliveredDescendantUnderFinalizedInPhase` on deliveries inside a phase, stated over a
model `M : Record.Model V`.
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

/-- Every block of the store's tree other than genesis names its slot's proposer, has a parent of a
    strictly earlier slot, and carries only attestations of its own slot's round or an earlier one. -/
def TreeBlockShaped (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) : Prop :=
  ∀ B : Block V, B ∈ st.T → B ≠ Block.genesis →
    B.proposer? = some (E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
      M.carried_attestations_admissible hc B = true

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `st` satisfies `TreeBlockShaped`, so does `st'`. -/
def TreeBlockShapedStep (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (st st' : M.S) :
    Prop :=
  Restated.TreeBlockShaped M E hc st → Restated.TreeBlockShaped M E hc st'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Whenever a step whose instant lies between `tGAT` and `tE` delivers the named block `B` to a
    validator `v` the adversary has held at no instant up to that step, and `C` is an ancestor of
    `B`, the finalized block of `v`'s store at that step is an ancestor of `B`. -/
def DeliveredDescendantUnderFinalizedInPhase (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (C : Block V) : Prop :=
  ∀ (d : Nat) (v v' : V) (B : NamedBlock V),
    x.lbl d
        = AtomicAction.deliver v (⟨v', NamedObject.block B⟩ : SignedMsg V (NamedObject V)) →
    Restated.HonestThrough M Sched x d v →
    tGAT ≤ (x[d].time : Int) → (x[d].time : Int) ≤ tE →
    Block.Preceq C B.erase →
    Block.preceq (x[d][v].st).st.core.F B.erase = true

end

end DecoupledConsensusModel.Sts.Restated
