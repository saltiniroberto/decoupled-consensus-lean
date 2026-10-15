module
public import Proofs.Vocabulary.Execution.HealthyLocalFacts
public import Proofs.Vocabulary.Internal.Definitions.NamedJointOutage
public import Proofs.Vocabulary.ModelProperties.readFrame
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.NamedActionReads_preparedCache
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Vocabulary.Execution.Runtime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Forward persistence of completed grade results

Once a round-`r` phase-`p` result is completed in an honest node's cache, every later read of that
node up to `a_r` returns the same result, clipped to that read's finalized block.
-/

namespace DecoupledConsensusModel.Proofs.FrameForward
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Clipping algebra -/

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
private theorem clip_compatible (g F : Block V) : Block.compatible (clipGrade g F) F = true := by
  induction g with
  | genesis => simp [clipGrade, Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · assumption
    · exact ih

omit [Fintype V] in
private theorem retained_prefix (g F B : Block V) (hBF : Block.compatible B F = true) :
    Block.Preceq B (clipGrade g F) ↔ Block.Preceq B g := by
  constructor
  · intro h
    exact Block.preceq_trans h (clip_preceq g F)
  · induction g with
    | genesis => exact fun h => h
    | node p s root gv gsv ats v ih =>
      intro hBg
      by_cases hGF : Block.compatible (.node p s root gv gsv ats v) F = true
      · simpa only [clipGrade, hGF, ↓reduceIte] using hBg
      · have hBp : Block.Preceq B p := by
          simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBg
          rcases hBg with hEq | hBp
          · subst B
            exact False.elim (hGF hBF)
          · exact hBp
        simpa only [clipGrade, hGF, Bool.eq_false_iff.mpr hGF, Bool.false_eq_true,
          ↓reduceIte] using ih hBp

omit [Fintype V] in
private theorem compatible_ancestors {A B C D : Block V}
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D)
    (hBD : Block.compatible B D = true) : Block.compatible A C = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hBD
  rcases hBD with hBD | hDB
  · exact Block.compatible_of_preceq_common (Block.preceq_trans hAB hBD) hCD
  · exact Block.compatible_of_preceq_common hAB (Block.preceq_trans hCD hDB)

omit [Fintype V] in
private theorem clip_after_advance (B F G : Block V) (hFG : Block.Preceq F G) :
    clipGrade (clipGrade B F) G = clipGrade B G := by
  apply Block.preceq_antisymm
  · apply (retained_prefix B G _ (clip_compatible (clipGrade B F) G)).mpr
    exact Block.preceq_trans (clip_preceq (clipGrade B F) G) (clip_preceq B F)
  · apply (retained_prefix (clipGrade B F) G _ (clip_compatible B G)).mpr
    apply (retained_prefix B F _ ?_).mpr
    · exact clip_preceq B G
    · exact compatible_ancestors (Block.preceq_self _) hFG (clip_compatible B G)

omit [Fintype V] in
/-- Clipping against `F` and then against a later root `G` is clipping against `G`. -/
private theorem clip_result_advance (F G : Block V) (hFG : Block.Preceq F G)
    (x : Option (Option (Block V))) : clipResult G (clipResult F x) = clipResult G x := by
  cases x with
  | none => rfl
  | some root =>
    cases root with
    | none => rfl
    | some B =>
      simp only [clipResult, Option.map_some]
      exact congrArg (fun C => some (some C)) (clip_after_advance B F G hFG)

/-! ## Cache algebra -/

omit [Fintype V] in
private theorem phase_clip_frame (F : Block V) (f : Frame V) (p : Phase) :
    phaseResult (clipFrame F f) p = clipResult F (phaseResult f p) := by
  cases p <;> rfl

omit [Fintype V] in
private theorem cacheAtRound_clip (F : Block V) (c : Cache V) (r : Round) :
    cacheAtRound (clipCache F c) r = clipFrame F (cacheAtRound c r) := by
  unfold cacheAtRound clipCache
  split_ifs <;> rfl

omit [Fintype V] in
private theorem phase_clip (F : Block V) (c : Cache V) (r : Round) (p : Phase) :
    phaseResult (cacheAtRound (clipCache F c) r) p =
      clipResult F (phaseResult (cacheAtRound c r) p) := by
  rw [cacheAtRound_clip, phase_clip_frame]

omit [DecidableEq V] [Fintype V] in
/-- Alignment to the queried round itself is always safe. -/
private theorem cacheAtRound_align_self (c : Cache V) (r : Round) :
    cacheAtRound (alignRound c r) r = cacheAtRound c r := by
  by_cases h1 : r = c.round
  · rw [show alignRound c r = c by unfold alignRound; rw [if_pos h1]]
  · by_cases h2 : r = c.round + 1
    · rw [show alignRound c r = ⟨r, c.next, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_pos h2]]
      subst h2
      simp [cacheAtRound]
    · rw [show alignRound c r = ⟨r, pendingFrame, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_neg h2]]
      simp [cacheAtRound, h1, h2]

/-! ## The local clock round -/


/-- `6Δ < 4ΔR` for `R ≥ 2`. -/
private theorem six_lt_four_mul {d k : Int} (hd : 0 < d) (hk : 2 ≤ k) :
    6 * d < 4 * d * k := by
  have h1 : (8 : Int) ≤ 4 * k := by omega
  have h2 : d * 8 ≤ d * (4 * k) := Int.mul_le_mul_of_nonneg_left h1 hd.le
  calc 6 * d < 8 * d := by omega
    _ = d * 8 := by ring
    _ ≤ d * (4 * k) := h2
    _ = 4 * d * k := by ring

/-- The round action `S.a r` is strictly before the opening of round `r + 1`. -/
theorem a_lt_opening_succ (S : Setup V) (r : Round) :
    S.a r < opening S.E S.hc (r + 1) := by
  have hR : (2 : Time) ≤ ((S.hc.R : Nat) : Time) := by exact_mod_cast S.hc.R_ge_two
  have ha : S.a r = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + 6 * S.E.Δ := rfl
  have ho : opening S.E S.hc (r + 1)
      = 4 * S.E.Δ * ((S.hc.opening_slot (r + 1) : Nat) : Time) := rfl
  have hcast : ((S.hc.opening_slot (r + 1) : Nat) : Time)
      = ((S.hc.opening_slot r : Nat) : Time) + ((S.hc.R : Nat) : Time) := by
    simp only [Protocol.HealConfig.opening_slot]
    push_cast
    ring
  rw [ha, ho, hcast]
  have hexp : 4 * S.E.Δ * (((S.hc.opening_slot r : Nat) : Time) + ((S.hc.R : Nat) : Time))
      = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time)
        + 4 * S.E.Δ * ((S.hc.R : Nat) : Time) := by ring
  rw [hexp]
  exact Int.add_lt_add_left (six_lt_four_mul S.E.Δ_pos hR) _

/-- Every phase domain time of round `r` is at or before the round action `S.a r`. -/
theorem domain_le_a (S : Setup V) (r : Round) (p : Phase) :
    domain S.E S.hc r p ≤ S.a r := by
  have hd : domain S.E S.hc r p
      = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + p.domainOffset * S.E.Δ := rfl
  have ha : S.a r = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + 6 * S.E.Δ := rfl
  rw [hd, ha]
  refine Int.add_le_add_left ?_ _
  refine Int.mul_le_mul_of_nonneg_right ?_ S.E.Δ_pos.le
  cases p <;> simp only [Phase.domainOffset] <;> norm_num


/-- If `v`'s read before `S.a r` has the completed round-`r` phase-`p` result `root`, the
    action-time checkpoint read has the same result. -/
theorem frame_phase_checkpoint_eq (S : Setup V) (rho : NamedRun V)
    (v : V) (r : Round) (p : Phase) (root : Option (Block V))
    (hbase : phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho (S.a r) v).cache
        (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.toHealing r) p = some root) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
      (checkpoint S rho v r).st.core.toHealing r) p = some root := by
  set before := NamedRun.stateBeforeTime S rho (S.a r) v with hbefore
  have hclipped := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).2.2
  have hraw : phaseResult (cacheAtRound before.cache r) p = some root := by
    rw [← hbase, Proofs.ModelProperties.readFrame_phase, Proofs.ModelProperties.toHealing_F,
      ← phase_clip, hclipped]
  have hsome : phaseResult (cacheAtRound before.cache r) p ≠ none := by
    rw [hraw]; exact Option.some_ne_none _
  have hprep : phaseResult (cacheAtRound (NamedActionReads.preparedCache S before (S.a r)) r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    have hsome' : phaseResult (cacheAtRound (alignRound before.cache
        (S.hc.round_of (S.E.slotOf (S.a r)))) r) p ≠ none := by
      rw [Proofs.HealingLemmas.round_of_slotOf_a S r, cacheAtRound_align_self]; exact hsome
    rw [Proofs.ModelProperties.preparedCache_phase_of_align S before (S.a r) r p hsome',
      Proofs.HealingLemmas.round_of_slotOf_a S r, cacheAtRound_align_self]
  have key : phaseResult (cacheAtRound before.cache r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    conv_lhs => rw [← hclipped]
    exact phase_clip _ _ _ _
  rw [hraw] at key
  rw [show checkpoint S rho v r = NamedActionReads.confirmationReadFrom S before (S.a r) from rfl,
    Proofs.ModelProperties.readFrame_phase, Proofs.ModelProperties.toHealing_F,
    Proofs.ModelProperties.confirmationReadFrom_st_core,
    Proofs.ModelProperties.confirmationReadFrom_cache, hprep, hraw]
  exact (clip_result_advance before.st.core.F before.st.core.F
    (Proofs.ModelProperties.Preceq_self _) (some root)).trans key.symm

#print axioms a_lt_opening_succ
#print axioms frame_phase_checkpoint_eq

end DecoupledConsensusModel.Proofs.FrameForward

end
