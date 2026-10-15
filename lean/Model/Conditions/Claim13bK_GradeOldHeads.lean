import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads

/-!
# A reader admits a delivered block

The condition `ReaderAdmitsInPhase`, stated over a model `M : Record.Model V`.
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

/-- Whenever a step `d` delivers the named block `B`, from any sender, to `v`, the adversary has
    held `v` at no time up to that step, and step `d`'s time lies in `[tGAT, tR]`, then `v`'s
    finalized block at `d` is an ancestor of `B`, or `B` is already among `v`'s bodies at `d`. -/
def ReaderAdmitsInPhase (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tR : Int) (v : V) (B : NamedBlock V) : Prop :=
  ∀ (d : Nat) (v_0 : V),
    x.lbl d
        = AtomicAction.deliver v (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) →
    Restated.HonestThrough M Sched x d v →
    tGAT ≤ (x[d].time : Int) → (x[d].time : Int) ≤ tR →
    Block.preceq (x[d][v].st).st.core.F B.erase = true ∨ B ∈ (x[d][v].st).st.bodies

end

end DecoupledConsensusModel.Sts.Restated
