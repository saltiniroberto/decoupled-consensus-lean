import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# Finalized blocks at the steps of a window

Conditions on the finalized blocks of the validators the adversary has not held, at every step of a
time window, stated over a model `M : Record.Model V`.
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

/-- At every step `d` whose instant lies in `[tGAT, tR]` and through which the adversary has not
    held `v`, the finalized block of `v`'s store after `d` steps is an ancestor of `B`'s erasure, or
    `B` is among that store's bodies. -/
def ReaderAdmitsAtStepsInPhase (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tR : Int) (v : V) (B : NamedBlock V) : Prop :=
  ∀ (d : Nat), Restated.HonestThrough M Sched x d v →
    tGAT ≤ (x[d].time : Int) → (x[d].time : Int) ≤ tR →
    Block.preceq (x[d][v].st).st.core.F B.erase = true ∨ B ∈ (x[d][v].st).st.bodies

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every step `d` whose instant lies in `[lo, hi]`, every validator the adversary has not held
    through `d` has, after `d` steps, a finalized block that is an ancestor of `C`. -/
def FinalizedPreceqAtStepsInPhase (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (lo hi : Int) (C : Block V) : Prop :=
  ∀ (d : Nat) (v : V), Restated.HonestThrough M Sched x d v →
    lo ≤ (x[d].time : Int) → (x[d].time : Int) ≤ hi →
    Block.Preceq (x[d][v].st).st.core.F C

end

end DecoupledConsensusModel.Sts.Restated
