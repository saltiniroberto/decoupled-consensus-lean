module
public import Proofs.Vocabulary.Execution.ViabilityHistory
public import Proofs.Vocabulary.ModelProperties.grade2_block_with
public import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
public import Proofs.Vocabulary.ModelProperties.grade2Block
public import Proofs.Vocabulary.ModelProperties.readFrame
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.phaseResult
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.Protocol.Grades.CacheProvenance
public import Proofs.Vocabulary.Internal.Definitions.NamedOutageEntry
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Execution.Wire
import Proofs.Vocabulary.Objects.Weights
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryProducersTime
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The G2 capture behind an action read -/


omit [Fintype V] in
private theorem clip_preceq (g F : Block V) : Block.Preceq (clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · exact Block.preceq_self _
    · apply Block.preceq_trans ih
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self p)

omit [Fintype V] in
private theorem clip_result_prefix (F P root : Block V)
    (result : Option (Option (Block V)))
    (hresult : clipResult F result = some (some root)) (hP : Block.Preceq P root) :
    ∃ old : Block V, result = some (some old) ∧ Block.Preceq P old := by
  cases result with
  | none => simp only [clipResult, Option.map_none, reduceCtorEq] at hresult
  | some result =>
    cases result with
    | none =>
      change (some none : Option (Option (Block V))) = some (some root) at hresult
      have hbad : (none : Option (Block V)) = some root := Option.some.inj hresult
      cases hbad
    | some old =>
      have he : clipGrade old F = root := by
        simpa only [clipResult, Option.map_some, Option.some.injEq] using hresult
      exact ⟨old, rfl, Block.preceq_trans hP (by rw [← he]; exact clip_preceq old F)⟩

omit [DecidableEq V] [Fintype V] in
private theorem align_current (c : Cache V) (s : Round) :
    (alignRound c s).current = cacheAtRound c s ∧ (alignRound c s).round = s := by
  unfold alignRound
  split_ifs with hs hn
  · exact ⟨by simp only [cacheAtRound, if_pos hs], hs.symm⟩
  · exact ⟨by simp only [cacheAtRound, if_neg hs, if_pos hn], rfl⟩
  · exact ⟨by simp only [cacheAtRound, if_neg hs, if_neg hn], rfl⟩

private theorem complete_one_other (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V) (h : q ≠ p) :
    phaseResult (completeOne E hc st r t p f) q = phaseResult f q := by
  unfold completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;> simp_all only [putPhase, phaseResult, ne_eq, not_true_eq_false]
    · rfl

private theorem complete_frame_g2 (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (s : Round) (t : Time) (f : Frame V)
    (ht : t ≠ domain E hc s .g2) : (completeFrame E hc st s t f).g2 = f.g2 := by
  change phaseResult (completeFrame E hc st s t f) .g2 = phaseResult f .g2
  unfold completeFrame
  rw [complete_one_other E hc st s t .g0 .g2 _ (by decide),
    complete_one_other E hc st s t .g1 .g2 _ (by decide)]
  unfold completeOne
  split
  · rfl
  · simp only [if_neg ht]

/-- The G2 domain time of a round is strictly before the round's action. -/
theorem action_after_g2 (S : Setup V) (s : Round) : domain S.E S.hc s .g2 < S.a s := by
  have he : S.a s = domain S.E S.hc s .g2 + 7 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a domain opening Phase.domainOffset
      Protocol.proposal_time Env.t slotStart
    ring
  rw [he]
  exact lt_add_of_pos_right _
    (Int.mul_pos (by decide : (0 : Int) < 7) S.E.Δ_pos)

private theorem prepared_g2_from_old (S : Setup V) (before : NamedNodeState V) (s : Round) :
    (cacheAtRound (preparedCache S before (S.a s)) s).g2 =
      clipResult before.st.core.F (cacheAtRound before.cache s).g2 := by
  let aligned := alignRound before.cache s
  have hcurrent : aligned.current = cacheAtRound before.cache s := (align_current before.cache s).1
  have hround : aligned.round = s := (align_current before.cache s).2
  have htime : S.a s ≠ domain S.E S.hc s .g2 := ne_of_gt (action_after_g2 S s)
  unfold preparedCache NamedActionReads.preparedCache onPhaseTick
  rw [Proofs.HealingLemmas.round_of_slotOf_a S s]
  change (cacheAtRound (clipCache before.st.core.F
    ⟨aligned.round,
      completeFrame S.E S.hc before.st.core.toHealing aligned.round (S.a s) aligned.current,
      completeFrame S.E S.hc before.st.core.toHealing (aligned.round + 1) (S.a s)
        aligned.next⟩) s).g2 = _
  simp only [cacheAtRound, clipCache, hround]
  change clipResult before.st.core.F
    (completeFrame S.E S.hc before.st.core.toHealing s (S.a s) aligned.current).g2 = _
  rw [complete_frame_g2 S.E S.hc before.st.core.toHealing s (S.a s) aligned.current htime, hcurrent]
  rfl

/-- A G2 block `q` selected at `v`'s round-`r` action read before event `i` is an ancestor of a G2
    root that `v` froze at an earlier tick at the round-`r` G2 domain time. -/
theorem q2_capture_at_action_read (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (r : Round) {q : Block V}
    (hQ : Protocol.grade2_block_with
        (NamedProfile.gradeContract (actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache)
        S.E S.hc (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r =
      some q) :
    ∃ (j : Nat) (raw : Block V),
      j < i ∧
      rho.events[j]? = some (.tick v (domain S.E S.hc r .g2)) ∧
      freezeRoot S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw ∧
      Block.Preceq q raw := by
  set before := NamedRun.stateBefore S rho i v with hbefore
  set n := actionReadFrom S before r with hn
  rw [Proofs.ModelProperties.grade2_block_with_eq_read_Q2,
    Proofs.ModelProperties.gradeContract_read_Q2] at hQ
  obtain ⟨clipped, hfield, hqclip⟩ := Proofs.ModelProperties.grade2Block_some hQ
  have hF : n.st.core.F = before.st.core.F := by
    show (Protocol.NamedDuties.update_confirmation_with _ S.E S.hc
      (NamedActionReads.confirmationReadFrom S before (S.a r)).st _).core.F = _
    rw [Proofs.ModelProperties.named_update_confirmation_with_core,
      Proofs.ModelProperties.update_confirmation_with_F,
      Proofs.ModelProperties.confirmationReadFrom_st_core]
    rfl
  rw [Proofs.ModelProperties.readFrame_g2, Proofs.ModelProperties.toHealing_F, hF] at hfield
  obtain ⟨prepared, hprepared, hqprep⟩ :=
    clip_result_prefix before.st.core.F q clipped _ hfield hqclip
  have hcache : n.cache = preparedCache S before (S.a r) :=
    Proofs.ModelProperties.confirmationReadFrom_cache S before (S.a r)
  rw [hcache, prepared_g2_from_old S before r] at hprepared
  obtain ⟨old, hold, hqold⟩ :=
    clip_result_prefix before.st.core.F q prepared _ hprepared hqprep
  have hphase : phaseResult (cacheAtRound (NamedRun.stateBefore S rho i v).cache r) .g2 =
      some (some old) := by
    rw [Proofs.ModelProperties.phaseResult_g2]
    exact hold
  rcases NamedCacheProvenance.completed_phase_origin S rho i v r .g2 (some old) hphase with
    ⟨_, hzero⟩ | ⟨j, tt, hj, he, ht, hroot⟩
  · exact absurd hzero (by simp)
  · subst tt
    obtain ⟨raw, hraw, hclip⟩ := Option.map_eq_some_iff.mp hroot.symm
    refine ⟨j, raw, hj, he, hraw, ?_⟩
    exact Proofs.ModelProperties.Preceq_trans hqold (by rw [← hclip]; exact clip_preceq raw _)

#print axioms q2_capture_at_action_read
#print axioms action_after_g2
end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryProducersTime

end
