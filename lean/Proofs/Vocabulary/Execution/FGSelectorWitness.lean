module
public import Proofs.Vocabulary.Execution.EmissionShape
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section

/-!
# FG-selector witness for emitted height rows

An honest emitted nonempty height row has its exact named FG-selector body.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest emitted nonempty height row has its exact named FG-selector body. -/
theorem honestEmittedHeightRow_exactFGSelectorWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D : NamedBlock V, ∃ J : Block V,
      ta = S.a a.round ∧
        a = actionAttestationAt S rho a.val_index a.round ∧
        actionFGSource S (actionStoreAt S rho a.val_index a.round) =
          some D.erase ∧
        D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h ∧
        (Protocol.derive_named S.E S.cfg D).h = h ∧
        J = (Protocol.derive_named S.E S.cfg D).T_h ∧
        (a.height_pair.erase = HeightPair.target h J.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  have hshape := Proofs.Optimistic.emits_attest_shape S hemit
  have htime : ta = S.a a.round := hshape.2
  have hemitCopy := hemit
  obtain ⟨i, hi, -⟩ := hemitCopy
  have hiMem : Event.tick a.val_index ta ∈ rho.events :=
    List.mem_of_getElem? hi
  have hactionHor : S.a a.round ≤ rho.horizon := by
    have hin := (adm.in_horizon (Event.tick a.val_index ta) hiMem).2
    simpa only [Event.time, htime, NamedEvent.time] using hin
  have haEq : a = actionAttestationAt S rho a.val_index a.round := by
    exact ((NamedActionSources.action_run_emission S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      a.val_index a.round a).mp (by simpa only [htime] using hemit)).2.2
  rw [haEq] at hh
  generalize hp : (actionAttestationAt S rho a.val_index a.round).height_pair = q at hh
  cases q with
  | empty =>
      cases hh
  | vote h' entry timeout =>
      have hh' : h' = h := by
        cases timeout <;>
          simpa [NamedHeightPair.erase, HeightPair.height?] using hh
      subst h'
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho a.val_index a.round h entry timeout
          hp
      obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
        NamedActionSources.action_witness S rho a.val_index a.round Cfg hCfg
      let J := (Protocol.derive_named S.E S.cfg D).T_h
      have hsource : actionFGSource S
          (actionStoreAt S rho a.val_index a.round) = some D.erase := by
        simpa only [actionStoreAt, hDerase] using hCfg
      have hheight :
          ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h := by
        simpa only [actionStoreAt, hDerase] using hCfgHeight
      have hnamedHeight :
          (Protocol.derive_named S.E S.cfg D).h = h := by
        simpa only [hDderive, actionStoreAt, hDerase] using hheight
      have hJroot : J.root = entry := by
        dsimp only [J]
        simpa only [hDderive] using hCfgRoot
      refine ⟨D, J, htime, haEq, hsource, hD, hheight,
        hnamedHeight, rfl, ?_⟩
      cases timeout with
      | false =>
          left
          rw [haEq, hp]
          simp [NamedHeightPair.erase, hJroot]
      | true =>
          right
          rw [haEq, hp]
          simp [NamedHeightPair.erase]

#print axioms honestEmittedHeightRow_exactFGSelectorWitness

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
