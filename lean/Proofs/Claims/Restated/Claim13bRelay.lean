import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bRelay

/-!
# Relaying an honest send

An honest send is delivered to a receiver awake through its deadline, inside the relay
window; stated over a model `M : Record.Model V`.
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

/-- If an honest validator put the accepted object on the wire at a step at or after the accepting
    step, at an instant at or before the one the accepting step leads to, and the receiver is awake
    at every instant from that send through its deadline, then some step at or after the accepting
    instant and strictly before the accepting instant's deadline delivers that object to the
    receiver. -/
theorem relay_of_honestSendAt_from (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x)
    {i k : Nat} {w : V} {o : NamedObject V} {sm : SignedMsg V (NamedObject V)}
    (hik : i ≤ k) (hkt : (x[k].time : Int) ≤ (x[i + 1].time : Int))
    (hsend : Restated.HonestSendAt M S x k sm) (hmsg : sm.msg = o)
    (hwaw : w ∈ Sched.awakeThroughout (x[k].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ (d : Nat) (m : SignedMsg V (NamedObject V)),
      (x[i + 1].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ∧
      x.lbl d = AtomicAction.deliver w m ∧ m.msg = o := by
  obtain ⟨d, hkd, hlbl, -, hlt⟩ := Restated.synchronyFromWake_from_step facts S hsync hsend hwaw
  refine ⟨d, sm, ?_, ?_, hlbl, hmsg⟩
  · have hid : i + 1 ≤ d := by omega
    exact_mod_cast Restated.time_mono facts S Sched x hid
  · have hmax : max (x[k].time : Int) S.E.t_GST ≤ max (x[i + 1].time : Int) S.E.t_GST :=
      max_le_max hkt (le_refl _)
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If an honest validator put `sm` on the wire at step `k₀`, `D` is an instant at or after that
    step's deadline, and the receiver is awake at every instant from the send's instant through that
    deadline, then some step after `k₀`, at an instant strictly before `D`, delivers `sm` to the
    receiver. -/
theorem deliver_of_honestSendAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x)
    {k₀ : Nat} {w : V} {sm : SignedMsg V (NamedObject V)} {D : Int}
    (hsend : Restated.HonestSendAt M S x k₀ sm)
    (hD : max (x[k₀].time : Int) S.E.t_GST + S.E.Δ ≤ D)
    (hwaw : w ∈ Sched.awakeThroughout (x[k₀].time : Int)
      (max (x[k₀].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ d : Nat, k₀ < d ∧ (x[d].time : Int) < D ∧
      x.lbl d = AtomicAction.deliver w sm := by
  obtain ⟨d, hkd, hlbl, -, hlt⟩ := Restated.synchronyFromWake_from_step facts S hsync hsend hwaw
  exact ⟨d, hkd, lt_of_lt_of_le hlt hD, hlbl⟩

end

end DecoupledConsensusModel.Sts.Restated
