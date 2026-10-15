import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# Accepting an object at a step

The steps at which a validator can come to accept an object, stated over a model
`M : Record.Model V`.
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

/-- At step `i`, `v` is delivered a message that is `o` or includes `o`, or `v` is awake at a tick
    at `t` and some outcome of its tick emits an object that is `o` or includes `o`, that outcome
    being the one step `i` took whenever step `i` runs `v`'s tick. -/
def AcceptsAtStep (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) (o : NamedObject V) : Prop :=
  (∃ sm : SignedMsg V (NamedObject V),
      x.lbl i = AtomicAction.deliver v sm ∧ (sm.msg = o ∨ carries sm.msg o)) ∨
    (∃ (t : Nat) (o' : NamedObject V), x.lbl i = AtomicAction.tickAllAwake t ∧
      v ∈ Sched.awake (t : Int) ∧
      (∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[i] v) (t : Int) ⇢ out ∧
        o' ∈ out.2 ∧
        (v ∉ Sched.adv (t : Int) → (t : Int) % S.E.Δ = 0 → x[i + 1][v].st = out.1)) ∧
      (o' = o ∨ carries o' o))

end

end DecoupledConsensusModel.Sts.Restated
