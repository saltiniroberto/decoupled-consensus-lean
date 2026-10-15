module
public import Proofs.Vocabulary.Execution.OutageProvenance
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The shape of an emitted attestation

An emitted attestation is the emitter's own, emitted at its round's action time while the emitter is
awake, equal to the attest duty's output, and unique per round.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Internal Execution Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

/-- An emitted attestation is the emitter's own, at its round's action time. -/
theorem emits_attest_shape (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    a.val_index = v ∧ t = S.a a.round := by
  obtain ⟨-, -, -, -, hval, -, ht, -⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho h
  exact ⟨hval, ht⟩

/-- An attestation emission shows that its author was awake at that action. -/
theorem emits_attest_awake (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    (S.node v).awake a.round = true := by
  obtain ⟨-, -, -, -, -, -, -, hawake⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho h
  exact hawake


/-- The emitted attestation is the attest duty's output on that read, under the frame contract of
    the read's own cache. -/
theorem emits_attest_duty (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      (Protocol.NamedDuties.attest_with
        (NamedProfile.gradeContract
          (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).cache)
        S.E S.hc (S.node v)
        (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).st
        (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).record).2.2 = a := by
  obtain ⟨i, hi, -, hduty, -, -, -, -⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho h
  exact ⟨i, hi, hduty⟩

/-- An honest validator emits at most one attestation per round. -/
theorem emits_attest_unique (S : Setup V) {rho : NamedRun V}
    (sch : ScheduleWellFormed S rho)
    {v : V} {a b : NamedAttestation V} {t₁ t₂ : Time}
    (h₁ : NamedRun.emits S rho v (NamedObject.attest a) t₁)
    (h₂ : NamedRun.emits S rho v (NamedObject.attest b) t₂)
    (hround : a.round = b.round) : a = b :=
  NamedOutageProvenance.emitted_same_round_unique S rho sch h₁ h₂ hround

#print axioms emits_attest_shape
#print axioms emits_attest_awake
#print axioms emits_attest_duty
#print axioms emits_attest_unique


end Optimistic
end Proofs
end DecoupledConsensusModel

end
