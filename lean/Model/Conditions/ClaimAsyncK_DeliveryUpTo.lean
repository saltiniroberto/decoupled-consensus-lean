import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_DeliveryUpTo

/-!
# Bounded synchrony and honest heads over a slot range

Synchrony from wake promised only up to a bound, and honest votes for descendants of a block over a
range of slots, stated over a model `M : Record.Model V`.
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

/-- Synchrony from wake for the sends whose deadline `max (x[k].time) S.E.t_GST + S.E.Δ` is at most
    `b₀`: every validator awake from the instant the message is on the wire through the deadline is
    delivered it at a step after the send, at an instant strictly before the deadline. -/
def SynchronyFromWakeBefore (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (b₀ : Int) : Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    Restated.HonestSendAt M S x k sm →
    max (x[k].time : Int) S.E.t_GST + S.E.Δ ≤ b₀ →
    w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every honest active member of the committee of every slot from `s` to `sEnd` votes there for a
    descendant of `B`. -/
def AncestorOfHonestHeadsFromTo (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s sEnd : Slot) : Prop :=
  ∀ s' : Slot, s ≤ s' → s' ≤ sEnd → Restated.HeadsBelow M S Sched x B s'

end

end DecoupledConsensusModel.Sts.Restated
