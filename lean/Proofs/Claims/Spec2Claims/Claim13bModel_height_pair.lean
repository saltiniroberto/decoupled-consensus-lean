module
public import Model.Vocabulary.Protocol.ValidatorClient
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.height_pair`

A lemma that unfolds the legacy height pair a validator's record gives at a source.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.height_pair

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol
open Protocol (Record height_pair own_lock)

/-- At the fields `(H, e, ν)`, the legacy pair is the target `(H, e)`; or the timeout at `H`, and
    then the record times `H` out, records a target at `H` other than `e`, or `ν` is set; or the
    empty pair, and then the own lock at `H` names a block other than `e`. -/
theorem height_pair_cases_l85c (Λ : Record) (H : Height) (e : BlockId) (ν : Bool)
    (fp : Option FinalityPair) :
    height_pair Λ (some (H, e, ν)) fp = .target H e ∨
    (height_pair Λ (some (H, e, ν)) fp = .timeout H ∧
      (Λ.timeout H = true ∨ (∃ rec, Λ.target H = some rec ∧ rec ≠ e) ∨ ν = true)) ∨
    (height_pair Λ (some (H, e, ν)) fp = .empty ∧
      ∃ locked, own_lock Λ H fp = some locked ∧ locked ≠ e) := by
  by_cases ht : Λ.timeout H = true
  · exact Or.inr (Or.inl ⟨by simp [height_pair, ht], Or.inl ht⟩)
  · have ht' : Λ.timeout H = false := Bool.eq_false_of_not_eq_true ht
    cases hl : own_lock Λ H fp with
    | some locked =>
      by_cases hle : locked = e
      · subst hle
        exact Or.inl (by simp [height_pair, ht', hl])
      · exact Or.inr (Or.inr ⟨by simp [height_pair, ht', hl, hle], locked, rfl, hle⟩)
    | none =>
      cases htg : Λ.target H with
      | some rec =>
        by_cases hre : rec = e
        · subst hre
          exact Or.inl (by simp [height_pair, ht', hl, htg])
        · exact Or.inr (Or.inl ⟨by simp [height_pair, ht', hl, htg, hre],
            Or.inr (Or.inl ⟨rec, rfl, hre⟩)⟩)
      | none =>
        cases ν with
        | false => exact Or.inl (by simp [height_pair, ht', hl, htg])
        | true => exact Or.inr (Or.inl ⟨by simp [height_pair, ht', hl, htg],
            Or.inr (Or.inr rfl)⟩)

end DecoupledConsensusModel.Sts
