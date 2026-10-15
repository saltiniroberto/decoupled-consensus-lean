import Proofs.Claims.Spec2Claims.Claim13bInvariantActive
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick_mk_s2

/-!
# Facts about `Protocol.onPhaseTick` and the cache operations it calls

Lemmas that unfold the phase tick of the grade cache and the operations it is built from
(`Protocol.alignRound`, `Protocol.cacheAtRound`, `Protocol.clipCache`, `Protocol.completeFrame`),
the two node steps that write a cache, `NamedNode.tick` and `NamedNode.process`, and the initial
cache.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.process
  DecoupledConsensusModel.Execution.NamedNode.tick
  DecoupledConsensusModel.Protocol.HealConfig.round_of DecoupledConsensusModel.Protocol.alignRound
  DecoupledConsensusModel.Protocol.cacheAtRound DecoupledConsensusModel.Protocol.clipCache
  DecoupledConsensusModel.Protocol.clipFrame DecoupledConsensusModel.Protocol.clipResult
  DecoupledConsensusModel.Protocol.completeFrame DecoupledConsensusModel.Protocol.onPhaseTick
  DecoupledConsensusModel.Protocol.pendingFrame DecoupledConsensusModel.Protocol.phaseResult

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The clip -/

omit [Fintype V] in
/-- Clipping a cache to `F` leaves its round. -/
theorem clipCache_round (F : Block V) (c : Protocol.Cache V) :
    (Protocol.clipCache F c).round = c.round := rfl

omit [Fintype V] in
/-- The result the cache clipped to `F` holds for round `r` and phase `p` is the result the cache
    held there, with its root, if any, replaced by `Protocol.clipGrade root F`. -/
theorem phaseResult_clipCache_map (F : Block V) (c : Protocol.Cache V) (r : Round)
    (p : Protocol.Phase) :
    Protocol.phaseResult (Protocol.cacheAtRound (Protocol.clipCache F c) r) p
      = (Protocol.phaseResult (Protocol.cacheAtRound c r) p).map
          (fun o => o.map (fun B => Protocol.clipGrade B F)) := by
  unfold Protocol.cacheAtRound Protocol.clipCache
  split_ifs <;> cases p <;> rfl

omit [Fintype V] in
/-- If the cache `c` holds the root `e` for round `r` and phase `p`, the cache clipped to `F` holds
    `Protocol.clipGrade e F` there. -/
theorem phaseResult_clipCache_some {F : Block V} {c : Protocol.Cache V} {r : Round}
    {p : Protocol.Phase} {e : Block V}
    (h : Protocol.phaseResult (Protocol.cacheAtRound c r) p = some (some e)) :
    Protocol.phaseResult (Protocol.cacheAtRound (Protocol.clipCache F c) r) p
      = some (some (Protocol.clipGrade e F)) := by
  rw [phaseResult_clipCache_map, h]
  rfl

omit [Fintype V] in
/-- If the cache clipped to `F` holds a result for round `r` and phase `p`, the cache before the
    clip holds one there. -/
theorem phaseResult_clipCache_isSome {F : Block V} {c : Protocol.Cache V} {r : Round}
    {p : Protocol.Phase} {o : Option (Block V)}
    (h : Protocol.phaseResult (Protocol.cacheAtRound (Protocol.clipCache F c) r) p = some o) :
    ∃ o', Protocol.phaseResult (Protocol.cacheAtRound c r) p = some o' := by
  rw [phaseResult_clipCache_map] at h
  obtain ⟨o', ho', -⟩ := Option.map_eq_some_iff.1 h
  exact ⟨o', ho'⟩

/-! ## The phase tick -/

omit [Fintype V] in
/-- After `Protocol.alignRound c r₀`, the cache's round is `r₀`. -/
theorem alignRound_round (c : Protocol.Cache V) (r₀ : Round) :
    (Protocol.alignRound c r₀).round = r₀ := by
  unfold Protocol.alignRound
  split_ifs with h1 h2
  · exact h1.symm
  · rfl
  · rfl

/-- The cache a phase tick at `t` leaves has the round of `t`'s slot as its round. -/
theorem onPhaseTick_round (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (t : Int) (c : Protocol.Cache V) :
    (Protocol.onPhaseTick E hc st t c).round = hc.round_of (E.slotOf t) := by
  unfold Protocol.onPhaseTick
  rw [clipCache_round]
  exact alignRound_round c _

/-- If the cache `c` holds the root `e` for round `r` and phase `p`, and either the round of `t` is
    `c`'s round and `r` is that round or the next, or the round of `t` is the round after `c`'s and
    `r` is it, then the cache the phase tick at `t` leaves from the store `st` holds
    `Protocol.clipGrade e st.F` there. -/
theorem phaseResult_onPhaseTick_kept (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Int) (c : Protocol.Cache V) {r : Round}
    {p : Protocol.Phase} {e : Block V}
    (h : Protocol.phaseResult (Protocol.cacheAtRound c r) p = some (some e))
    (hr : (hc.round_of (E.slotOf t) = c.round ∧ (r = c.round ∨ r = c.round + 1)) ∨
      (hc.round_of (E.slotOf t) = c.round + 1 ∧ r = c.round + 1)) :
    Protocol.phaseResult (Protocol.cacheAtRound (Protocol.onPhaseTick E hc st t c) r) p
      = some (some (Protocol.clipGrade e st.F)) := by
  simp only [Protocol.onPhaseTick]
  apply phaseResult_clipCache_some
  have hne : c.round + 1 ≠ c.round := Nat.succ_ne_self _
  rcases hr with ⟨hρ, hr⟩ | ⟨hρ, hr⟩
  · have hal : Protocol.alignRound c (hc.round_of (E.slotOf t)) = c := by
      unfold Protocol.alignRound; rw [if_pos hρ]
    rw [hal]
    rcases hr with rfl | rfl
    · have hcur : Protocol.cacheAtRound c c.round = c.current := by
        unfold Protocol.cacheAtRound; rw [if_pos rfl]
      rw [hcur] at h
      have hsel : Protocol.cacheAtRound (⟨c.round, Protocol.completeFrame E hc st c.round t
          c.current, Protocol.completeFrame E hc st (c.round + 1) t c.next⟩ : Protocol.Cache V)
          c.round = Protocol.completeFrame E hc st c.round t c.current := by
        unfold Protocol.cacheAtRound; rw [if_pos rfl]
      rw [hsel, phaseResult_completeFrame, h]
    · have hnext : Protocol.cacheAtRound c (c.round + 1) = c.next := by
        unfold Protocol.cacheAtRound; rw [if_neg hne, if_pos rfl]
      rw [hnext] at h
      have hsel : Protocol.cacheAtRound (⟨c.round, Protocol.completeFrame E hc st c.round t
          c.current, Protocol.completeFrame E hc st (c.round + 1) t c.next⟩ : Protocol.Cache V)
          (c.round + 1) = Protocol.completeFrame E hc st (c.round + 1) t c.next := by
        unfold Protocol.cacheAtRound; rw [if_neg hne, if_pos rfl]
      rw [hsel, phaseResult_completeFrame, h]
  · have hal : Protocol.alignRound c (hc.round_of (E.slotOf t))
        = ⟨c.round + 1, c.next, Protocol.pendingFrame⟩ := by
      unfold Protocol.alignRound
      rw [hρ, if_neg hne, if_pos rfl]
    rw [hal]
    subst hr
    have hnext : Protocol.cacheAtRound c (c.round + 1) = c.next := by
      unfold Protocol.cacheAtRound; rw [if_neg hne, if_pos rfl]
    rw [hnext] at h
    have hsel : Protocol.cacheAtRound (⟨c.round + 1, Protocol.completeFrame E hc st (c.round + 1)
        t c.next, Protocol.completeFrame E hc st (c.round + 1 + 1) t Protocol.pendingFrame⟩ :
        Protocol.Cache V) (c.round + 1)
        = Protocol.completeFrame E hc st (c.round + 1) t c.next := by
      unfold Protocol.cacheAtRound; rw [if_pos rfl]
    rw [hsel, phaseResult_completeFrame, h]

/-- If the round after the round of `t` is `r`, `t` is round `r`'s domain instant for the phase `p`,
    and the cache `c` holds no result for round `r` and phase `p`, then the cache the phase tick at
    `t` leaves from the store `st` holds there `Protocol.freezeRoot` of `st` with that phase's
    cutoffs, clipped to `st.F`. -/
theorem phaseResult_onPhaseTick_domain (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Int) (c : Protocol.Cache V) {r : Round}
    {p : Protocol.Phase} (hρ : hc.round_of (E.slotOf t) + 1 = r)
    (ht : t = Protocol.domain E hc r p)
    (h : Protocol.phaseResult (Protocol.cacheAtRound c r) p = none) :
    Protocol.phaseResult (Protocol.cacheAtRound (Protocol.onPhaseTick E hc st t c) r) p
      = some ((Protocol.freezeRoot E st.gradeView st.F hc.η_SG r (Protocol.early E hc r p)
          (Protocol.late E hc r p)).map (fun B => Protocol.clipGrade B st.F)) := by
  simp only [Protocol.onPhaseTick]
  rw [phaseResult_clipCache_map]
  set c₁ := Protocol.alignRound c (hc.round_of (E.slotOf t)) with hc₁
  have hround : c₁.round = hc.round_of (E.slotOf t) := alignRound_round c _
  have hr0 : r ≠ c₁.round := by rw [hround, ← hρ]; exact Nat.succ_ne_self _
  have hr1 : r = c₁.round + 1 := by rw [hround, hρ]
  have hpend : Protocol.phaseResult (Protocol.pendingFrame : Protocol.Frame V) p = none := by
    cases p <;> rfl
  have hca : Protocol.cacheAtRound c₁ r = c₁.next := by
    unfold Protocol.cacheAtRound
    rw [if_neg hr0, if_pos hr1]
  have hnext : Protocol.phaseResult c₁.next p = none := by
    rcases cacheAtRound_alignRound c (hc.round_of (E.slotOf t)) r with hal | hal
    · rw [← hc₁, hca] at hal; rw [hal]; exact h
    · rw [← hc₁, hca] at hal; rw [hal]; exact hpend
  have hcomp : Protocol.cacheAtRound (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t
      c₁.current, Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ : Protocol.Cache V) r
      = Protocol.completeFrame E hc st r t c₁.next := by
    unfold Protocol.cacheAtRound
    rw [if_neg hr0, if_pos hr1, hr1]
  rw [hcomp, phaseResult_completeFrame, hnext]
  simp only [if_pos ht, Option.map_some]

/-- If the cache the phase tick at `t` leaves holds a result for round `r` and phase `p`, then `r`
    is the round of `t`, or `t` is that phase's domain instant, or the cache before the tick held a
    result there. -/
theorem phaseResult_onPhaseTick_some_cases (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Int) (c : Protocol.Cache V) {r : Round}
    {p : Protocol.Phase} {o : Option (Block V)}
    (h : Protocol.phaseResult (Protocol.cacheAtRound (Protocol.onPhaseTick E hc st t c) r) p
      = some o) :
    r = hc.round_of (E.slotOf t) ∨ t = Protocol.domain E hc r p ∨
      ∃ o', Protocol.phaseResult (Protocol.cacheAtRound c r) p = some o' := by
  unfold Protocol.onPhaseTick at h
  obtain ⟨o₁, h₁⟩ := phaseResult_clipCache_isSome h
  set c₁ := Protocol.alignRound c (hc.round_of (E.slotOf t)) with hc₁
  have hround : c₁.round = hc.round_of (E.slotOf t) := alignRound_round c _
  have hpend : ∀ o' : Option (Block V),
      Protocol.phaseResult (Protocol.pendingFrame : Protocol.Frame V) p ≠ some o' := by
    intro o' h'; cases p <;> simp [Protocol.phaseResult, Protocol.pendingFrame] at h'
  by_cases hr0 : r = c₁.round
  · exact Or.inl (hr0.trans hround)
  · by_cases hr1 : r = c₁.round + 1
    · have hcomp : Protocol.cacheAtRound (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t
          c₁.current, Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ :
          Protocol.Cache V) r = Protocol.completeFrame E hc st r t c₁.next := by
        unfold Protocol.cacheAtRound
        simp only
        rw [if_neg hr0, if_pos hr1, hr1]
      rw [hcomp, phaseResult_completeFrame] at h₁
      cases hprev : Protocol.phaseResult c₁.next p with
      | some o' =>
          right; right
          have hca : Protocol.cacheAtRound c₁ r = c₁.next := by
            unfold Protocol.cacheAtRound
            rw [if_neg hr0, if_pos hr1]
          rcases cacheAtRound_alignRound c (hc.round_of (E.slotOf t)) r with hal | hal
          · rw [← hc₁, hca] at hal
            rw [← hal]
            exact ⟨o', hprev⟩
          · rw [← hc₁, hca] at hal
            rw [hal] at hprev
            exact absurd hprev (hpend o')
      | none =>
          rw [hprev] at h₁
          simp only at h₁
          split_ifs at h₁ with ht
          exact Or.inr (Or.inl ht)
    · have hcomp : Protocol.cacheAtRound (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t
          c₁.current, Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ :
          Protocol.Cache V) r = Protocol.pendingFrame := by
        unfold Protocol.cacheAtRound
        simp only
        rw [if_neg hr0, if_neg hr1]
      rw [hcomp] at h₁
      exact absurd h₁ (hpend o₁)

/-! ## The node steps that write a cache, and the initial cache -/

/-- The cache the node tick at `t` leaves is the phase tick at `t` of the cache and store before it,
    clipped to the finalized block of the store the tick leaves. -/
theorem namedNode_tick_cache (S : Setup V) (v : V) (n : NamedNodeState V) (t : Int) :
    (NamedNode.tick S v n t).1.cache
      = Protocol.clipCache (NamedNode.tick S v n t).1.st.core.F
          (Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) := rfl

/-- The cache a node holds after processing an object is the cache before, clipped to the finalized
    block of the store after the receipt. -/
theorem namedNode_process_cache (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (NamedNode.process S n o).cache
      = Protocol.clipCache (NamedNode.process S n o).st.core.F n.cache := rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `r` is the round of `t` or the round after it, and `t` is round `r`'s domain instant for the
    phase `p`, then the cache the phase tick at `t` leaves from the store `st` and the cache `c`
    holds a result for round `r` and phase `p`. -/
theorem phaseResult_onPhaseTick_domain_ne_none (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (t : Int) (c : Protocol.Cache V) {r : Round}
    {p : Protocol.Phase}
    (hr : r = hc.round_of (E.slotOf t) ∨ r = hc.round_of (E.slotOf t) + 1)
    (ht : t = Protocol.domain E hc r p) :
    Protocol.phaseResult (Protocol.cacheAtRound (Protocol.onPhaseTick E hc st t c) r) p ≠ none := by
  simp only [Protocol.onPhaseTick]
  rw [phaseResult_clipCache_map]
  set c₁ := Protocol.alignRound c (hc.round_of (E.slotOf t)) with hc₁
  have hround : c₁.round = hc.round_of (E.slotOf t) := alignRound_round c _
  have hsel : Protocol.cacheAtRound (⟨c₁.round, Protocol.completeFrame E hc st c₁.round t
      c₁.current, Protocol.completeFrame E hc st (c₁.round + 1) t c₁.next⟩ : Protocol.Cache V) r
      = Protocol.completeFrame E hc st r t (Protocol.cacheAtRound c₁ r) := by
    unfold Protocol.cacheAtRound
    rcases hr with hr | hr
    · have hr' : r = c₁.round := hr.trans hround.symm
      rw [if_pos hr', if_pos hr', ← hr']
    · have hne : r ≠ c₁.round := by rw [hr, hround]; exact Nat.succ_ne_self _
      have hr' : r = c₁.round + 1 := by rw [hr, hround]
      rw [if_neg hne, if_neg hne, if_pos hr', if_pos hr', ← hr']
  rw [hsel, phaseResult_completeFrame]
  cases Protocol.phaseResult (Protocol.cacheAtRound c₁ r) p with
  | some o => simp
  | none => rw [if_pos ht]; simp

end DecoupledConsensusModel.Sts
