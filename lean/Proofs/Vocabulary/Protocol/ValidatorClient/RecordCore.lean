module
public import Proofs.Vocabulary.Protocol.ValidatorClient.FinalityPairCore
import Proofs.Vocabulary.Protocol.ValidatorClient.Divergence
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record height_pair own_lock record_attestation
  create_attestation finality_pair)
open Proofs.Records (LockCompatible)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Targets are written once -/


omit [DecidableEq V] [Fintype V] in
/-- When `a` has height pair `target h T` and the recorded target at `h` is empty or `T`,
    `record_attestation` records `T` at `h`. -/
theorem record_attestation_target_recorded (Λ : Record) (a : CombinedAttestation V)
    {h : Height} {T : BlockId} (hhp : a.height_pair = HeightPair.target h T)
    (hpre : Λ.target h = none ∨ Λ.target h = some T) :
    (record_attestation Λ a).target h = some T := by
  simp only [record_attestation, hhp]
  rcases hpre with hpre | hpre <;> cases a.finality_pair <;>
    simp_all [Record.with_lock, Record.with_target]

/-! ## The lock `height_pair` reads -/


/-- Under `LockCompatible`, a lock `own_lock` returns at `h` has an empty or matching recorded
    target at `h`. -/
theorem own_lock_compatible {Λ : Record} (hla : LockCompatible Λ) {h_j : Height}
    {J : BlockId} {h_F : Height} {h : Height} {X : BlockId}
    (hol : own_lock Λ h (finality_pair Λ h_j J h_F) = some X) :
    Λ.target h = none ∨ Λ.target h = some X := by
  cases hfp : finality_pair Λ h_j J h_F with
  | none =>
    rw [hfp] at hol
    exact (hla h X hol).2
  | some p =>
    rw [hfp] at hol
    simp only [own_lock] at hol
    split at hol
    · rename_i hph
      simp only [Option.some_inj] at hol
      subst hol
      rw [← hph]
      exact finality_pair_target_compatible hfp
    · exact (hla h X hol).2

/-! ## Emitted targets agree with the record -/

/-- Under `LockCompatible`, when `height_pair` emits `target h T`, the recorded target at `h` is
    empty or `T`. -/
theorem height_pair_target_compat {Λ : Record} (hla : LockCompatible Λ)
    {fields : Option (Height × BlockId × Bool)} {h_j : Height} {J : BlockId}
    {h_F : Height} {h : Height} {T : BlockId}
    (hp : height_pair Λ fields (finality_pair Λ h_j J h_F) =
      HeightPair.target h T) :
    Λ.target h = none ∨ Λ.target h = some T := by
  cases fields with
  | none => simp [height_pair] at hp
  | some f =>
    obtain ⟨h_c, T_c, ν⟩ := f
    obtain ⟨hh, hT⟩ := height_pair_target_height hp
    subst hh
    subst hT
    simp only [height_pair] at hp
    split at hp
    · exact absurd hp (by simp)
    · cases hol : own_lock Λ h (finality_pair Λ h_j J h_F) with
      | some X =>
        simp only [hol] at hp
        split at hp
        · rename_i heq
          subst heq
          exact own_lock_compatible hla hol
        · exact absurd hp (by simp)
      | none =>
        simp only [hol] at hp
        cases hs : Λ.target h with
        | some s =>
          simp only [hs] at hp
          split at hp
          · rename_i heq
            exact Or.inr (by rw [heq])
          · exact absurd hp (by simp)
        | none => exact Or.inl rfl


omit [DecidableEq V] [Fintype V] in
/-- Under `LockCompatible`, when `create_attestation` emits a target height pair `target h T`, the
    record it returns has target `T` at `h`. -/
theorem create_attestation_saves (Λ : Record) (hla : LockCompatible Λ) (val_index : V)
    (r : Round) (confirmed : Option BlockId)
    (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId)
    (h_F : Height) {h : Height} {T : BlockId}
    (hhp : (create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
      HeightPair.target h T) :
    (create_attestation Λ val_index r confirmed fields h_j J h_F).1.target h = some T := by
  simp only [create_attestation] at hhp ⊢
  exact record_attestation_target_recorded _ _ hhp (height_pair_target_compat hla hhp)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
