import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Proofs.Claims.Spec2Claims.Claim13bModel_deepest_clear_attest

/-!
# Facts about `Protocol.fg_source_with`

The block a round action reads its height pair's fields from: `none` when the grade-2 candidate
`A_G2` is `none`; for `A_G2 = some q`, the clear walk's answer from `q` to `st.live_confirmed` when
there is one, else `q`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.deepest_clear DecoupledConsensusModel.Protocol.fg_source_with

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the finality-gadget source at the grade-2 candidate `A_G2` is `B`, then `A_G2` is some block
    `q` with `q ⪯ B`. -/
theorem fg_source_with_some (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    {A_G2 : Option (Block V)} {B : Block V}
    (h : Protocol.fg_source_with contract E hc st r A_G2 = some B) :
    ∃ q : Block V, A_G2 = some q ∧ Block.Preceq q B := by
  unfold Protocol.fg_source_with at h
  cases A_G2 with
  | none => exact absurd h (by simp)
  | some q =>
      refine ⟨q, rfl, ?_⟩
      dsimp only at h
      cases hdc : Protocol.deepest_clear (some q) st.live_confirmed
          (contract.read E hc st r).clear with
      | some D =>
          rw [hdc] at h
          dsimp only at h
          rw [← Option.some_inj.mp h]
          exact floor_preceq_deepest_clear hdc
      | none =>
          rw [hdc] at h
          dsimp only at h
          rw [← Option.some_inj.mp h]
          exact Block.preceq_self q

end DecoupledConsensusModel.Sts
