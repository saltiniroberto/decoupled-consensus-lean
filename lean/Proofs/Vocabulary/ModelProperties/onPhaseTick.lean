module
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# Facts about `Protocol.onPhaseTick`

The cache preparation at a tick: it aligns the cache to the tick's round, completes the pending
phase results due at the tick, and clips the cache to the store's finalized block.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem phase_clip_frame (F : Block V) (f : Frame V) (p : Phase) :
    phaseResult (clipFrame F f) p = clipResult F (phaseResult f p) := by
  cases p <;> rfl

omit [Fintype V] in
private theorem cacheAtRound_clip (F : Block V) (c : Cache V) (r : Round) :
    cacheAtRound (clipCache F c) r = clipFrame F (cacheAtRound c r) := by
  unfold cacheAtRound clipCache
  split_ifs <;> rfl

private theorem complete_one_other (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V)
    (h : q ≠ p) :
    phaseResult (completeOne E hc st r t p f) q = phaseResult f q := by
  unfold completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;> simp_all only [putPhase, phaseResult, ne_eq, not_true_eq_false]
    · rfl

private theorem complete_one_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V)
    (h : phaseResult f p ≠ none) :
    phaseResult (completeOne E hc st r t q f) p = phaseResult f p := by
  by_cases hpq : p = q
  · subst hpq
    unfold completeOne
    split
    · rfl
    · rename_i hnone
      exact absurd hnone h
  · exact complete_one_other E hc st r t q p f hpq

private theorem complete_frame_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p : Phase) (f : Frame V)
    (h : phaseResult f p ≠ none) :
    phaseResult (completeFrame E hc st r t f) p = phaseResult f p := by
  have h2 := complete_one_some E hc st r t p .g2 f h
  have h2' : phaseResult (completeOne E hc st r t .g2 f) p ≠ none := by
    rw [h2]; exact h
  have h1 := complete_one_some E hc st r t p .g1 _ h2'
  have h1' : phaseResult (completeOne E hc st r t .g1
      (completeOne E hc st r t .g2 f)) p ≠ none := by
    rw [h1, h2]; exact h
  have h0 := complete_one_some E hc st r t p .g0 _ h1'
  unfold completeFrame
  rw [h0, h1, h2]

private theorem phase_completed_cache (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (c : Cache V) (t : Time) (r : Round) (p : Phase)
    (h : phaseResult (cacheAtRound c r) p ≠ none) :
    phaseResult (cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ r) p =
      phaseResult (cacheAtRound c r) p := by
  by_cases h1 : r = c.round
  · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ r =
        completeFrame E hc st c.round t c.current := by
      simp [cacheAtRound, h1]
    have e2 : cacheAtRound c r = c.current := by simp [cacheAtRound, h1]
    rw [e2] at h
    rw [e1, e2]
    exact complete_frame_some E hc st c.round t p c.current h
  · by_cases h2 : r = c.round + 1
    · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
          completeFrame E hc st (c.round + 1) t c.next⟩ r =
          completeFrame E hc st (c.round + 1) t c.next := by
        simp [cacheAtRound, h2]
      have e2 : cacheAtRound c r = c.next := by simp [cacheAtRound, h2]
      rw [e2] at h
      rw [e1, e2]
      exact complete_frame_some E hc st (c.round + 1) t p c.next h
    · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
          completeFrame E hc st (c.round + 1) t c.next⟩ r = pendingFrame := by
        simp [cacheAtRound, h1, h2]
      have e2 : cacheAtRound c r = pendingFrame := by simp [cacheAtRound, h1, h2]
      rw [e1, e2]

/-- A phase result already present in the cache aligned to the round of `t` survives the preparation
    at `t`, clipped to `st`'s finalized block. -/
theorem onPhaseTick_phase_of_align (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Time) (c : Cache V) (r : Round) (p : Phase)
    (h : phaseResult (cacheAtRound (alignRound c (hc.round_of (E.slotOf t))) r) p ≠ none) :
    phaseResult (cacheAtRound (onPhaseTick E hc st t c) r) p =
      clipResult st.F
        (phaseResult (cacheAtRound (alignRound c (hc.round_of (E.slotOf t))) r) p) := by
  unfold onPhaseTick
  rw [cacheAtRound_clip, phase_clip_frame, phase_completed_cache E hc st _ t r p h]

end DecoupledConsensusModel.Proofs.ModelProperties

end
