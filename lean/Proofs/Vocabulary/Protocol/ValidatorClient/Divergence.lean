module
public import Model.Vocabulary.Protocol.ValidatorClient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record height_pair own_lock record_attestation create_attestation)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## `own_lock` -/

/-- At its own height, `own_lock` returns the attestation's finality target, not the record's. -/
theorem own_lock_self (Λ : Record) (h : Height) (T : BlockId) :
    own_lock Λ h (some ⟨h, T⟩) = some T := by
  simp [own_lock]


/-! ## One attestation against itself -/

/-- A target height pair produced from height fields `(h_c, T_c, ν)` has height `h_c` and target
    `T_c`. -/
theorem height_pair_target_height {Λ : Record} {h_c h : Height}
    {T_c T : BlockId} {ν : Bool} {fp : Option FinalityPair}
    (hp : height_pair Λ (some (h_c, T_c, ν)) fp = HeightPair.target h T) :
    h = h_c ∧ T = T_c := by
  simp only [height_pair] at hp
  split at hp
  · exact absurd hp (by simp)
  · split at hp
    · split at hp
      · simp only [HeightPair.target.injEq] at hp
        exact ⟨hp.1.symm, hp.2.symm⟩
      · exact absurd hp (by simp)
    · split at hp
      · split at hp
        · simp only [HeightPair.target.injEq] at hp
          exact ⟨hp.1.symm, hp.2.symm⟩
        · exact absurd hp (by simp)
      · split at hp
        · exact absurd hp (by simp)
        · simp only [HeightPair.target.injEq] at hp
          exact ⟨hp.1.symm, hp.2.symm⟩

/-- When the height pair and the finality pair are at the same height, their targets agree. -/
theorem height_pair_no_self_E1 {Λ : Record}
    {fields : Option (Height × BlockId × Bool)} {h : Height} {T T' : BlockId}
    (hp : height_pair Λ fields (some ⟨h, T'⟩) = HeightPair.target h T) :
    T = T' := by
  cases fields with
  | none => simp [height_pair] at hp
  | some f =>
    obtain ⟨h_c, T_c, ν⟩ := f
    obtain ⟨hh, hT⟩ := height_pair_target_height hp
    subst hh
    subst hT
    simp only [height_pair, own_lock_self] at hp
    split at hp
    · exact absurd hp (by simp)
    · split at hp
      · rename_i heq
        exact heq.symm
      · exact absurd hp (by simp)

omit [DecidableEq V] [Fintype V] in
/-- When the attestation `create_attestation` returns has a target height pair and a finality pair
    at the same height, their targets agree. -/
theorem create_attestation_no_self_E1 (Λ : Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T T' : BlockId}
    (hhp : (create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
      HeightPair.target h T)
    (hfp : (create_attestation Λ val_index r confirmed fields h_j J h_F).2.finality_pair =
      some ⟨h, T'⟩) :
    T = T' := by
  simp only [create_attestation] at hhp hfp
  rw [hfp] at hhp
  exact height_pair_no_self_E1 hhp


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
