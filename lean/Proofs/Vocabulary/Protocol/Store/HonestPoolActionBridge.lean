module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Proofs.Vocabulary.Execution.EmissionShape
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Honest SG-pool votes are round actions

An SG vote in a pool, attributed to an honest validator, is that validator's SG vote of its round
action for the pool's round, and the validator emitted that attestation at the round's action time.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An SG vote in the round-`k` pool of any validator's store, by an honest `v`, is
    `actionSGVoteAt S rho v k`, and `v` emits `actionAttestationAt S rho v k` at `S.a k`. -/
theorem honestSGVote_actionEmission_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w v : V} {time : Time} {k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ rho.honest)
    (hu : u ∈ (rho.storeBeforeTime S w time).toHealing.sg_votes k)
    (huv : u.val_index = v) :
    u = actionSGVoteAt S rho v k ∧
      rho.emits S v (Object.attest (actionAttestationAt S rho v k)) (S.a k) := by
  change u ∈
      ((rho.stateBeforeTime S time w).st.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed time
  have haN : a ∈ (rho.stateBefore S n w).st.sg_pool k := by
    rw [← hn]
    exact ha
  have haround : a.round = k :=
    Proofs.NamedStoreBridge.sgRounds_stateBefore S rho n w k a
      (List.mem_toFinset.mp haN)
  have hav : a.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hau
    have havu : a.val_index = u.val_index := by
      simpa only [Protocol.sgVote] using h
    exact havu.trans huv
  obtain ⟨j, e, o, hj, hje, hproc, hcarry⟩ :=
    Proofs.Optimistic.processes_attest_of_mem_sg_pool S rho w n k a haN
  obtain ⟨row, hrowEq, t', hte, hemit⟩ :
      ∃ row : NamedAttestation V, a = row.erase ∧
        ∃ t' : Time, t' ≤ e.time ∧ rho.emits S row.val_index (Object.attest row) t' := by
    cases o with
    | block Bl =>
        obtain ⟨row, hrowMem, hrowEq⟩ := hcarry
        have hrowV : row.val_index = v := by rw [hrowEq] at hav; exact hav
        have hrowHon : row.val_index ∈ rho.honest := by rw [hrowV]; exact hv
        obtain ⟨t', hte, hemit⟩ :=
          adm.carried_attest w Bl e.time hproc row hrowMem hrowHon
        exact ⟨row, hrowEq, t', hte, hemit⟩
    | gfVote voteObj => simp only [Proofs.Optimistic.CarriesRow] at hcarry
    | attest row =>
        have hrowEq : a = row.erase := hcarry
        have hrowV : row.val_index = v := by rw [hrowEq] at hav; exact hav
        have hrowHon : row.val_index ∈ rho.honest := by rw [hrowV]; exact hv
        obtain ⟨t', hte, hemit⟩ :=
          adm.unforgeable w (Object.attest row) e.time hproc row.val_index hrowHon rfl
        exact ⟨row, hrowEq, t', hte, hemit⟩
  have hrowV : row.val_index = v := by rw [hrowEq] at hav; exact hav
  have hrowRound : row.round = k := by rw [hrowEq] at haround; exact haround
  have hemitV : rho.emits S v (Object.attest row) t' := hrowV ▸ hemit
  have hshape := Proofs.Optimistic.emits_attest_shape S hemitV
  have htime : t' = S.a k := by rw [hshape.2, hrowRound]
  have hemitVCopy := hemitV
  obtain ⟨i, hi, -⟩ := hemitVCopy
  have hiMem : Event.tick v t' ∈ rho.events := List.mem_of_getElem? hi
  have hactionHor : S.a k ≤ rho.horizon := by
    have h := (adm.in_horizon (Event.tick v t') hiMem).2
    simpa only [Event.time, htime, NamedEvent.time] using h
  have hrowAction : row = actionAttestationAt S rho v k := by
    have hcanonical := ((NamedActionSources.action_run_emission S rho
      adm.toNamedScheduleWellFormed v k row).mp
      (by simpa only [htime] using hemitV)).2.2
    simpa only [hrowRound] using hcanonical
  refine ⟨?_, ?_⟩
  · calc
      u = Protocol.sgVote a := hau.symm
      _ = Protocol.sgVote row.erase := by rw [hrowEq]
      _ = Protocol.sgVote (actionAttestationAt S rho v k).erase := by rw [hrowAction]
      _ = actionSGVoteAt S rho v k := sgVote_actionAttestationAt S rho v k
  · rw [← hrowAction, ← htime]
    exact hemitV


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
