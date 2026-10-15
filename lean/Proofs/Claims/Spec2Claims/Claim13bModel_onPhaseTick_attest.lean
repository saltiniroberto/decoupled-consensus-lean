import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick

/-!
# Facts about `Protocol.onPhaseTick`: a result written only at its domain instant

A result the cache holds after the phase tick at `t` was held before, or `t` is that phase's domain
instant; and a phase tick at the domain instant of a phase of its own round writes the frozen root
into a pending result.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.alignRound
  DecoupledConsensusModel.Protocol.cacheAtRound DecoupledConsensusModel.Protocol.clipCache
  DecoupledConsensusModel.Protocol.onPhaseTick DecoupledConsensusModel.Protocol.pendingFrame
  DecoupledConsensusModel.Protocol.phaseResult

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the cache the phase tick at `t` leaves from the cache `c` holds a result for round `r` and
    phase `p`, then `t` is that phase's domain instant of round `r`, or `c` already held a result
    there. -/
theorem phaseResult_onPhaseTick_some_domain_or_kept (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Int) (c : Protocol.Cache V) {r : Round}
    {p : Protocol.Phase} {o : Option (Block V)}
    (h : Protocol.phaseResult (Protocol.cacheAtRound (Protocol.onPhaseTick E hc st t c) r) p
      = some o) :
    t = Protocol.domain E hc r p ∨
      ∃ o', Protocol.phaseResult (Protocol.cacheAtRound c r) p = some o' := by
  unfold Protocol.onPhaseTick at h
  obtain ⟨o₁, h₁⟩ := phaseResult_clipCache_isSome h
  set c₁ := Protocol.alignRound c (hc.round_of (E.slotOf t)) with hc₁
  have hpend : ∀ o' : Option (Block V),
      Protocol.phaseResult (Protocol.pendingFrame : Protocol.Frame V) p ≠ some o' := by
    intro o' h'; cases p <;> simp [Protocol.phaseResult, Protocol.pendingFrame] at h'
  have hframe : Protocol.cacheAtRound
      (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t c₁.current,
        Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ : Protocol.Cache V) r =
        Protocol.completeFrame E hc st r t (Protocol.cacheAtRound c₁ r) ∨
      Protocol.cacheAtRound
      (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t c₁.current,
        Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ : Protocol.Cache V) r =
        Protocol.pendingFrame := by
    unfold Protocol.cacheAtRound
    simp only
    split_ifs with h1 h2
    · subst h1; exact Or.inl rfl
    · subst h2; exact Or.inl rfl
    · exact Or.inr rfl
  rcases hframe with hframe | hframe
  · rw [hframe, phaseResult_completeFrame] at h₁
    cases hprev : Protocol.phaseResult (Protocol.cacheAtRound c₁ r) p with
    | some o' =>
        right
        rcases cacheAtRound_alignRound c (hc.round_of (E.slotOf t)) r with hal | hal
        · rw [hc₁, hal] at hprev
          exact ⟨o', hprev⟩
        · rw [hc₁, hal] at hprev
          exact absurd hprev (hpend o')
    | none =>
        rw [hprev] at h₁
        simp only at h₁
        split_ifs at h₁ with ht
        exact Or.inl ht
  · rw [hframe] at h₁
    exact absurd h₁ (hpend o₁)

/-- If the round of `t` is `r`, `t` is round `r`'s domain instant for the phase `p`, and the cache
    `c` holds no result for round `r` and phase `p`, then the cache the phase tick at `t` leaves
    from the store `st` holds there `Protocol.freezeRoot` of `st` with that phase's cutoffs, clipped
    to `st.F`. -/
theorem phaseResult_onPhaseTick_domain_current (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Int) (c : Protocol.Cache V) {r : Round}
    {p : Protocol.Phase} (hρ : hc.round_of (E.slotOf t) = r)
    (ht : t = Protocol.domain E hc r p)
    (h : Protocol.phaseResult (Protocol.cacheAtRound c r) p = none) :
    Protocol.phaseResult (Protocol.cacheAtRound (Protocol.onPhaseTick E hc st t c) r) p
      = some ((Protocol.freezeRoot E st.gradeView st.F hc.η_SG r (Protocol.early E hc r p)
          (Protocol.late E hc r p)).map (fun B => Protocol.clipGrade B st.F)) := by
  simp only [Protocol.onPhaseTick]
  rw [phaseResult_clipCache_map]
  set c₁ := Protocol.alignRound c (hc.round_of (E.slotOf t)) with hc₁
  have hround : c₁.round = hc.round_of (E.slotOf t) := alignRound_round c _
  have hr0 : r = c₁.round := by rw [hround, hρ]
  have hpend : Protocol.phaseResult (Protocol.pendingFrame : Protocol.Frame V) p = none := by
    cases p <;> rfl
  have hca : Protocol.cacheAtRound c₁ r = c₁.current := by
    unfold Protocol.cacheAtRound
    rw [if_pos hr0]
  have hcur : Protocol.phaseResult c₁.current p = none := by
    rcases cacheAtRound_alignRound c (hc.round_of (E.slotOf t)) r with hal | hal
    · rw [← hc₁, hca] at hal; rw [hal]; exact h
    · rw [← hc₁, hca] at hal; rw [hal]; exact hpend
  have hcomp : Protocol.cacheAtRound (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t
      c₁.current, Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ : Protocol.Cache V) r
      = Protocol.completeFrame E hc st r t c₁.current := by
    unfold Protocol.cacheAtRound
    rw [if_pos hr0, ← hr0]
  rw [hcomp, phaseResult_completeFrame, hcur]
  simp only [if_pos ht, Option.map_some]

end DecoupledConsensusModel.Sts
