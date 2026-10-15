import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# Delivery, adversarial and forward steps

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a delivery step
gives the receiver an outcome of its receipt and leaves every other validator's entry unchanged, and
adversarial and forward steps change no validator's entry.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- After a `deliver w sm` step, `w` holds an outcome of the receipt of `sm`'s payload from the node
    state it held before; or that receipt has no outcome and `w`'s node state is unchanged. -/
theorem st_succ_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver w sm) :
    M.process (Setup.alwaysAwake S) (x[k][w].st) sm.msg ⇢ x[k + 1][w].st ∨
    ((∀ n' : M.N, ¬ M.process (Setup.alwaysAwake S) (x[k][w].st) sm.msg ⇢ n') ∧
      x[k + 1][w].st = x[k][w].st) :=
  Record.st_succ_of_deliver M S Sched x hl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- A delivery step to `p` leaves the entry `x[k][w]` of every other validator `w` unchanged. -/
theorem getElem_succ_of_deliver_ne (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {p w : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver p sm)
    (hne : p ≠ w) : x[k + 1][w] = x[k][w] := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, hns⟩ := hs
  have hstep : NodeStep (Record.protocolOf M S) p (.recv sm) (receive p sm x[k]) x[k + 1] := hns
  rw [hstep.other w (fun h => hne h.symm)]
  simp only [receive, Config.setNode_apply, if_neg hne]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- An adversarial step leaves every validator's entry `x[k][w]` unchanged. -/
theorem getElem_succ_of_adversarial (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {p w : V} {m : NamedObject V}
    (hl : x.lbl k = AtomicAction.adversarial p m) : x[k + 1][w] = x[k][w] := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  rw [hs.2]; rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- A forward step leaves every validator's entry `x[k][w]` unchanged. -/
theorem getElem_succ_of_forward (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {p w : V}
    {m : SignedMsg V (NamedObject V)}
    (hl : x.lbl k = AtomicAction.forward p m) : x[k + 1][w] = x[k][w] := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  rw [hs.2]; rfl

end

end DecoupledConsensusModel.Sts.Restated
