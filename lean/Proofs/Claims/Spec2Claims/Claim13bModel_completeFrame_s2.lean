import Proofs.Claims.Spec2Claims.Claim13bModel_completeOne_s2

/-!
# Facts about `Protocol.completeFrame`

The phase results of a frame after it is completed at a time.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.completeFrame

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Completing a frame at time `t` keeps a phase result already there, and writes
    `Protocol.freezeRoot` of the store into a pending one exactly when `t` is that phase's domain
    time. -/
theorem phaseResult_completeFrame [Fintype V] (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r₁ : Round) (t : Int) (f : Protocol.Frame V)
    (p : Protocol.Phase) :
    Protocol.phaseResult (Protocol.completeFrame E hc st r₁ t f) p =
      match Protocol.phaseResult f p with
      | some o => some o
      | none =>
        if t = Protocol.domain E hc r₁ p then
          some (Protocol.freezeRoot E st.gradeView st.F hc.η_SG r₁
            (Protocol.early E hc r₁ p) (Protocol.late E hc r₁ p))
        else none := by
  unfold Protocol.completeFrame
  cases p with
  | g0 =>
      rw [phaseResult_completeOne_self, phaseResult_completeOne_ne _ _ _ _ _ _ (by decide),
        phaseResult_completeOne_ne _ _ _ _ _ _ (by decide)]
      rfl
  | g1 =>
      rw [phaseResult_completeOne_ne _ _ _ _ _ _ (by decide), phaseResult_completeOne_self,
        phaseResult_completeOne_ne _ _ _ _ _ _ (by decide)]
      rfl
  | g2 =>
      rw [phaseResult_completeOne_ne _ _ _ _ _ _ (by decide),
        phaseResult_completeOne_ne _ _ _ _ _ _ (by decide), phaseResult_completeOne_self]
      rfl

end DecoupledConsensusModel.Sts
