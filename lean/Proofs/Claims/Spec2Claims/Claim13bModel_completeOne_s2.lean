import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.completeOne`

The phase results of a frame after one of its phases is completed.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.completeOne
  DecoupledConsensusModel.Protocol.phaseResult DecoupledConsensusModel.Protocol.putPhase

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `Protocol.completeOne` at the phase `q` does not change the result of another phase `p`. -/
theorem phaseResult_completeOne_ne [Fintype V] (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r₁ : Round) (t : Int) (f : Protocol.Frame V)
    {q p : Protocol.Phase} (hqp : q ≠ p) :
    Protocol.phaseResult (Protocol.completeOne E hc st r₁ t q f) p =
      Protocol.phaseResult f p := by
  unfold Protocol.completeOne
  split
  · rfl
  · split
    · cases q <;> cases p <;> first | exact absurd rfl hqp | rfl
    · rfl

omit [Fintype V] in
/-- `Protocol.completeOne` at the phase `p` keeps a result already there, and otherwise writes
    `Protocol.freezeRoot` of the store when `t` is the phase's domain time. -/
theorem phaseResult_completeOne_self [Fintype V] (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r₁ : Round) (t : Int) (f : Protocol.Frame V)
    (p : Protocol.Phase) :
    Protocol.phaseResult (Protocol.completeOne E hc st r₁ t p f) p =
      match Protocol.phaseResult f p with
      | some o => some o
      | none =>
        if t = Protocol.domain E hc r₁ p then
          some (Protocol.freezeRoot E st.gradeView st.F hc.η_SG r₁
            (Protocol.early E hc r₁ p) (Protocol.late E hc r₁ p))
        else none := by
  unfold Protocol.completeOne
  cases hf : Protocol.phaseResult f p with
  | some o => exact hf
  | none =>
      simp only []
      split_ifs
      · cases p <;> rfl
      · exact hf

end DecoupledConsensusModel.Sts
