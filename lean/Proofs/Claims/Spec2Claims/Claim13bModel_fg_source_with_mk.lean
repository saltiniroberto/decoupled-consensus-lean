module
public import Model.Vocabulary.Protocol.Duties.Inputs
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
public import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

@[expose] public section

/-!
# The two cases of `Protocol.fg_source_with`

The finality-gadget source is a block of the store's confirmed chain or the grade-2 candidate.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.fg_source_with

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The block the finality-gadget source selects is an ancestor of the store's `live_confirmed`, or
    it is the grade-2 candidate `A_G2` itself. -/
theorem fg_source_cases (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r₁ : Round)
    {A_G2 : Option (Block V)} {Cfg : Block V}
    (h : Protocol.fg_source_with contract E hc st r₁ A_G2 = some Cfg) :
    Block.Preceq Cfg st.live_confirmed ∨ A_G2 = some Cfg := by
  unfold Protocol.fg_source_with at h
  cases A_G2 with
  | none => exact absurd h (by simp)
  | some Q =>
      dsimp only at h
      cases hdc : Protocol.deepest_clear (some Q) st.live_confirmed
          (contract.read E hc st r₁).clear with
      | some B =>
          rw [hdc] at h
          dsimp only at h
          have hBC : B = Cfg := Option.some_inj.mp h
          rw [← hBC]
          exact Or.inl (preceq_eq_true_iff_Preceq.mp (Proofs.Engine.deepest_clear_preceq hdc))
      | none =>
          rw [hdc] at h
          dsimp only at h
          exact Or.inr h

end DecoupledConsensusModel.Sts
