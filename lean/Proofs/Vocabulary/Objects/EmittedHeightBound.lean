module
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
public import Proofs.Vocabulary.Execution.EmissionShape
public import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Bounds on the heights of honest attestations

The height of an attestation is at most the sender's `h_max` before the sending time, and, for an
honest sender, at most the honest maximum height before any later time.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem heightPair_vote_of_height {hp : NamedHeightPair} {h : Height}
    (he : hp.erase.height? = some h) :
    ∃ entry timeout, hp = .vote h entry timeout := by
  cases hp with
  | empty => simp [NamedHeightPair.erase, HeightPair.height?] at he
  | vote h' entry timeout =>
    have hEq : h' = h := by
      cases timeout <;>
        simpa [NamedHeightPair.erase, HeightPair.height?] using he
    exact ⟨entry, timeout, by rw [hEq]⟩

/-- An attestation `v` sends at time `t` with height `h` has `h` at most the `h_max` of `v`'s store
    before `t`. -/
theorem honestEmittedHeight_le_localHMaxBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {a : NamedAttestation V} {t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (rho.storeBeforeTime S v t).h_max := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have ht : t = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  subst ht
  have heq : a = Proofs.HealingSurface.actionAttestationAt S rho v a.round :=
    ((NamedActionSources.action_run_emission S rho sch v a.round a).mp hemit).2.2
  obtain ⟨entry, timeout, hvote⟩ := heightPair_vote_of_height hh
  rw [heq] at hvote
  obtain ⟨Cfg, hCfg, hheight, -⟩ :=
    NamedActionSources.action_source S rho v a.round h entry timeout hvote
  obtain ⟨C, hCmem, -, hCderiv, -⟩ :=
    NamedActionSources.action_witness S rho v a.round Cfg hCfg
  rw [hCderiv] at hheight
  have hbound :=
    Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime S rho (S.a a.round) v C hCmem
  rw [hheight] at hbound
  exact hbound

/-- An attestation the honest validator `v` sends at time `u ≤ t` with height `h` has `h` at most
    `honestHMaxBeforeIndex S rho (strictEventIndex rho t)`, the honest maximum height before time
    `t`. -/
theorem honestEmittedHeight_le_honestHMaxBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {a : NamedAttestation V}
    {u t : Time} {h : Height}
    (hemit : rho.emits S v (Object.attest a) u)
    (hh : a.height_pair.erase.height? = some h) (hut : u ≤ t) :
    h ≤ honestHMaxBeforeIndex S rho (strictEventIndex rho t) := by
  have sch : ScheduleWellFormed S rho := adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hlocal := (honestEmittedHeight_le_localHMaxBeforeTime S adm hemit hh).trans
    (storeBeforeTime_hMax_mono S sch v hut)
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch] at hlocal
  exact hlocal.trans (localHMax_le_honestHMaxBeforeIndex S rho _ hv)

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
