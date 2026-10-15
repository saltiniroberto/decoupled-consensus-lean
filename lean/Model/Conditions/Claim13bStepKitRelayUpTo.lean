import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# The relay of a Goldfish vote, up to a time

The condition `GfVoteRelayAtAcceptBefore`, asked only of the votes whose relay deadline is at most
`b`, stated over a model `M : Record.Model V`.
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

/-- Whenever `u` enters the pool of `u`'s slot in `v`'s store at step `i`, the deadline (one delay
    after the later of `x[i + 1].time` and GST) is at most `b`, `v` is honest through that step, and
    a receiver `w` is awake at that step and at every time from the time that step starts from to
    the deadline, some step from `x[i + 1].time` on and strictly before the deadline delivers to `w`
    a message whose payload is `u`. -/
def GfVoteRelayAtAcceptBefore (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (b : Int) : Prop :=
  ∀ (i : Nat) (v w : V) (u : GoldfishVote V),
    max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ b →
    u ∉ (M.store_pool (x[i][v].st).st.core u.slot) →
    u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot) →
    Restated.HonestThrough M Sched x i v →
    AtomicAwake x i w →
    w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ) →
    ∃ (k : Nat) (m : SignedMsg V (NamedObject V)),
      (x[i + 1].time : Int) ≤ (x[k].time : Int) ∧
      (x[k].time : Int) < max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ∧
      x.lbl k = AtomicAction.deliver w m ∧ m.msg = NamedObject.gfVote u

end

end DecoupledConsensusModel.Sts.Restated
