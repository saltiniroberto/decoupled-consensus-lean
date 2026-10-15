import Proofs.Claims.Spec2Claims.Claim13bModel_clipCache_s2
import Proofs.Claims.Spec2Claims.Claim13bModel_alignRound
import Proofs.Claims.Spec2Claims.Claim13bModel_completeFrame_s2
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# Facts about `Protocol.onPhaseTick`

Where a non-empty phase result after a phase tick comes from.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.onPhaseTick
  DecoupledConsensusModel.Protocol.cacheAtRound DecoupledConsensusModel.Protocol.pendingFrame
  DecoupledConsensusModel.Protocol.phaseResult

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the cache a phase tick at `t` leaves holds the root `root` for round `r₁` and phase `p`, then
    either the cache before held a root there of which `root` is an ancestor, or `t` is that phase's
    domain instant and `root` is an ancestor of a block the store handed to the tick grades with
    that phase's cutoffs. -/
theorem phaseResult_onPhaseTick (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Int) (c : Protocol.Cache V) {r₁ : Round}
    {p : Protocol.Phase} {root : Block V}
    (h : Protocol.phaseResult (Protocol.cacheAtRound (Protocol.onPhaseTick E hc st t c) r₁) p
      = some (some root)) :
    (∃ root₀ : Block V,
      Protocol.phaseResult (Protocol.cacheAtRound c r₁) p = some (some root₀) ∧
        Block.Preceq root root₀) ∨
    (t = Protocol.domain E hc r₁ p ∧ ∃ B : Block V,
      Protocol.gradeBool E st.gradeView st.F hc.η_SG r₁ (Protocol.early E hc r₁ p)
        (Protocol.late E hc r₁ p) B = true ∧ Block.Preceq root B) := by
  unfold Protocol.onPhaseTick at h
  obtain ⟨root₁, h₁, hpre₁⟩ := phaseResult_clipCache h
  set c₁ := Protocol.alignRound c (hc.round_of (E.slotOf t)) with hc₁
  have hframe : Protocol.cacheAtRound
      (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t c₁.current,
        Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ : Protocol.Cache V) r₁ =
        Protocol.completeFrame E hc st r₁ t (Protocol.cacheAtRound c₁ r₁) ∨
      Protocol.cacheAtRound
      (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t c₁.current,
        Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ : Protocol.Cache V) r₁ =
        Protocol.pendingFrame := by
    unfold Protocol.cacheAtRound
    simp only
    split_ifs with h1 h2
    · subst h1; exact Or.inl rfl
    · subst h2; exact Or.inl rfl
    · exact Or.inr rfl
  have hpending : ∀ root' : Block V,
      Protocol.phaseResult (Protocol.pendingFrame : Protocol.Frame V) p ≠ some (some root') := by
    intro root' hc'
    cases p <;> simp [Protocol.phaseResult, Protocol.pendingFrame] at hc'
  rcases hframe with hframe | hframe
  · rw [hframe, phaseResult_completeFrame] at h₁
    cases hprev : Protocol.phaseResult (Protocol.cacheAtRound c₁ r₁) p with
    | some o =>
        rw [hprev] at h₁
        simp only at h₁
        cases h₁
        rcases cacheAtRound_alignRound c (hc.round_of (E.slotOf t)) r₁ with hal | hal
        · rw [hc₁, hal] at hprev
          exact Or.inl ⟨root₁, hprev, hpre₁⟩
        · rw [hc₁, hal] at hprev
          exact absurd hprev (hpending root₁)
    | none =>
        rw [hprev] at h₁
        simp only at h₁
        split_ifs at h₁ with ht
        · refine Or.inr ⟨ht, root₁, ?_, hpre₁⟩
          exact gradeBool_of_freezeRoot (Option.some.inj h₁)
  · rw [hframe] at h₁
    exact absurd h₁ (hpending root₁)

end DecoupledConsensusModel.Sts
