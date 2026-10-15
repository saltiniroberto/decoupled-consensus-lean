module
public import Proofs.Vocabulary.Protocol.Grades.Inclusions
public import Proofs.Vocabulary.Protocol.Duties.Inputs.LayerAHistoryIndices
public import Proofs.Vocabulary.Protocol.ChainState.FinalityCertificates
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import Proofs.Vocabulary.ModelProperties.readFrame
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.NamedActionReads_preparedCache
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Block algebra -/

/-- A result of `pickUnique?` passes its test. -/
private theorem pick_property {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    {x : α} (h : pickUnique? T p = some x) : p x = true := by
  unfold pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact Finset.choose_property _ _ hex
  · exact absurd h (by simp)

/-- `deepest?` of a set is a descendant of every member compatible with it. -/
private theorem preceq_deepest_of_compatible {T : Finset (Block V)} {G P : Block V}
    (hG : Block.deepest? T = some G) (hP : P ∈ T)
    (hcomp : Block.compatible P G = true) : Block.Preceq P G := by
  rcases (show Block.Preceq P G ∨ Block.Preceq G P by
    simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hcomp) with hPG | hGP
  · exact hPG
  · have hdeep : Block.isDeepestIn T G = true := pick_property hG
    simp only [Block.isDeepestIn, decide_eq_true_eq] at hdeep
    have hno : Block.deeper P G = false := hdeep P hP
    simp only [Block.deeper, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hno
    have hle : P.depth ≤ G.depth := hno.1
    have heq := Block.preceq_eq_of_depth_le hGP hle
    subst heq
    exact Block.preceq_self _

/-- Two comparable blocks of the same depth are equal. -/
private theorem eq_of_compatible_depth {A B : Block V}
    (hcomp : Block.compatible A B = true) (h : A.depth = B.depth) : A = B := by
  rcases (show Block.Preceq A B ∨ Block.Preceq B A by
    simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hcomp) with hAB | hBA
  · exact Block.preceq_eq_of_depth_le hAB (le_of_eq h.symm)
  · exact (Block.preceq_eq_of_depth_le hBA (le_of_eq h)).symm

/-- The `deepest?` of a nonempty chain is `some`. -/
private theorem deepest_some_of_chain {T : Finset (Block V)} {P : Block V}
    (hP : P ∈ T) (hchain : ∀ A ∈ T, ∀ B ∈ T, Block.compatible A B = true) :
    ∃ G, Block.deepest? T = some G := by
  obtain ⟨M, hM, hmax⟩ := T.exists_max_image (fun B : Block V => B.depth) ⟨P, hP⟩
  have hMdeep : Block.isDeepestIn T M = true := by
    simp only [Block.isDeepestIn, decide_eq_true_eq]
    intro C hC
    simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
      decide_eq_false_iff_not, not_lt, decide_eq_true_eq]
    refine ⟨hmax C hC, ?_⟩
    intro hdepth
    have hCM : C = M := eq_of_compatible_depth (hchain C hC M hM) hdepth.symm
    subst hCM
    simp
  have huniq : ∃! a, a ∈ T ∧ Block.isDeepestIn T a = true := by
    refine ⟨M, ⟨hM, hMdeep⟩, ?_⟩
    rintro a ⟨haT, hadeep⟩
    simp only [Block.isDeepestIn, decide_eq_true_eq] at hadeep
    have hno : Block.deeper M a = false := hadeep M hM
    simp only [Block.deeper, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hno
    exact eq_of_compatible_depth (hchain a haT M hM)
      (Nat.le_antisymm (hmax a haT) hno.1)
  refine ⟨T.choose (fun a => Block.isDeepestIn T a = true) huniq, ?_⟩
  unfold Block.deepest? pickUnique?
  rw [dif_pos huniq]

/-- Every tree member `P` that is an ancestor of `root` is an ancestor of the active prefix of
    `root`, which therefore exists. -/
theorem activePrefix_covers {tree : Finset (Block V)} {root P : Block V}
    (hPT : P ∈ tree) (hPr : Block.Preceq P root) :
    ∃ G, activePrefix tree root = some G ∧ Block.Preceq P G := by
  set T := tree.filter (fun B => Block.preceq B root = true) with hT
  have hmem : P ∈ T := Finset.mem_filter.mpr ⟨hPT, hPr⟩
  have hchain : ∀ A ∈ T, ∀ B ∈ T, Block.compatible A B = true := by
    intro A hA B hB
    exact Block.compatible_of_preceq_common (Finset.mem_filter.mp hA).2
      (Finset.mem_filter.mp hB).2
  obtain ⟨G, hG⟩ := deepest_some_of_chain hmem hchain
  refine ⟨G, hG, ?_⟩
  have hGmem : G ∈ T := Proofs.Engine.deepest?_mem hG
  exact preceq_deepest_of_compatible hG hmem (hchain P hmem G hGmem)


/-! ## The SG anchor and the FG root -/

/-- The SG anchor is a descendant of the FG root. -/
theorem fg_root_preceq_anchor (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (g1 : Option (Option (Block V))) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (DecoupledConsensusModel.Protocol.anchor E hc st r g1) := by
  rcases g1 with _ | g
  · exact Block.preceq_self _
  rcases g with _ | root
  · exact Block.preceq_self _
  show Block.Preceq (Protocol.get_fg_root st.toFG)
    ((activePrefix (Protocol.get_filtered_block_tree st.toFG) root).getD
      (Protocol.get_fg_root st.toFG))
  cases hA : activePrefix (Protocol.get_filtered_block_tree st.toFG) root with
  | none => exact Block.preceq_self _
  | some A =>
    exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (NamedProposalParent.activePrefix_mem _ root A hA)

#print axioms activePrefix_covers

/-! ## The stable output -/


/-- A block `P` that is an ancestor of `latest_stable` and compatible with `Σ.F` is an ancestor of
    `get_stable`. -/
theorem preceq_get_stable (st : Protocol.Store V) {P : Block V}
    (hlat : Block.Preceq P st.latest_stable)
    (hF : Block.compatible P st.F = true) :
    Block.Preceq P (Protocol.get_stable st) := by
  unfold Protocol.get_stable
  split
  · exact hlat
  · rename_i hno
    rcases (show Block.Preceq P st.F ∨ Block.Preceq st.F P by
      simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hF) with hPF | hFP
    · exact hPF
    · exact absurd (Block.preceq_trans hFP hlat) hno


#print axioms preceq_get_stable


/-! ### Round openings -/

/-- The G1 domain time of a round is its opening. -/
theorem domain_g1_eq_opening (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 = opening S.E S.hc r := by
  simp only [domain, Phase.domainOffset]
  ring


/-! ## The prepared read -/

private theorem ip_clip_compatible (g F : Block V) :
    Block.compatible (clipGrade g F) F = true := by
  induction g with
  | genesis => simp [clipGrade, Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · assumption
    · exact ih

private theorem ip_compatible_ancestors {A B C D : Block V}
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D)
    (hBD : Block.compatible B D = true) : Block.compatible A C = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hBD
  rcases hBD with hBD | hDB
  · exact Block.compatible_of_preceq_common (Block.preceq_trans hAB hBD) hCD
  · exact Block.compatible_of_preceq_common hAB (Block.preceq_trans hCD hDB)

private theorem ip_clip_after_advance (B F G : Block V) (hFG : Block.Preceq F G) :
    clipGrade (clipGrade B F) G = clipGrade B G := by
  apply Block.preceq_antisymm
  · apply (q10_retained_prefix B G _ (ip_clip_compatible (clipGrade B F) G)).mpr
    exact Block.preceq_trans (q10_clip_preceq (clipGrade B F) G) (q10_clip_preceq B F)
  · apply (q10_retained_prefix (clipGrade B F) G _ (ip_clip_compatible B G)).mpr
    apply (q10_retained_prefix B F _ ?_).mpr
    · exact q10_clip_preceq B G
    · exact ip_compatible_ancestors (Block.preceq_self _) hFG (ip_clip_compatible B G)

private theorem ip_clip_result_advance (F G : Block V) (hFG : Block.Preceq F G)
    (x : Option (Option (Block V))) : clipResult G (clipResult F x) = clipResult G x := by
  cases x with
  | none => rfl
  | some root =>
    cases root with
    | none => rfl
    | some B =>
      simp only [clipResult, Option.map_some]
      exact congrArg (fun C => some (some C)) (ip_clip_after_advance B F G hFG)

private theorem ip_phase_clip_frame (F : Block V) (f : Frame V) (p : Phase) :
    phaseResult (clipFrame F f) p = clipResult F (phaseResult f p) := by
  cases p <;> rfl

private theorem ip_cacheAtRound_clip (F : Block V) (c : Cache V) (r : Round) :
    cacheAtRound (clipCache F c) r = clipFrame F (cacheAtRound c r) := by
  unfold cacheAtRound clipCache
  split_ifs <;> rfl

private theorem ip_phase_clip (F : Block V) (c : Cache V) (r : Round) (p : Phase) :
    phaseResult (cacheAtRound (clipCache F c) r) p =
      clipResult F (phaseResult (cacheAtRound c r) p) := by
  rw [ip_cacheAtRound_clip, ip_phase_clip_frame]

private theorem ip_cacheAtRound_align_self (c : Cache V) (r : Round) :
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

/-- The confirmation read at time `u` keeps every completed phase result of `u`'s own clock round
    from the read before `u`. -/
theorem frame_phase_prepared_eq (S : Setup V) (rho : NamedRun V) (v : V) (r : Round)
    (p : Phase) (u : Time) (hround : S.hc.round_of (S.E.slotOf u) = r)
    (root : Option (Block V))
    (hbase : phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho u v).cache
        (NamedRun.stateBeforeTime S rho u v).st.core.toHealing r) p = some root) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame (confirmationReadAt S rho v u).cache
      (confirmationReadAt S rho v u).st.core.toHealing r) p = some root := by
  set before := NamedRun.stateBeforeTime S rho u v with hbefore
  have hclipped := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho u v).2.2
  have hraw : phaseResult (cacheAtRound before.cache r) p = some root := by
    rw [← hbase, Proofs.ModelProperties.readFrame_phase, Proofs.ModelProperties.toHealing_F,
      ← ip_phase_clip, hclipped]
  have hsome : phaseResult (cacheAtRound before.cache r) p ≠ none := by
    rw [hraw]; exact Option.some_ne_none _
  have hprep : phaseResult (cacheAtRound (NamedActionReads.preparedCache S before u) r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    have hsome' : phaseResult (cacheAtRound (alignRound before.cache
        (S.hc.round_of (S.E.slotOf u))) r) p ≠ none := by
      rw [hround, ip_cacheAtRound_align_self]; exact hsome
    rw [Proofs.ModelProperties.preparedCache_phase_of_align S before u r p hsome', hround,
      ip_cacheAtRound_align_self]
  have key : phaseResult (cacheAtRound before.cache r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    conv_lhs => rw [← hclipped]
    exact ip_phase_clip _ _ _ _
  rw [hraw] at key
  rw [show confirmationReadAt S rho v u = NamedActionReads.confirmationReadFrom S before u from rfl,
    Proofs.ModelProperties.readFrame_phase, Proofs.ModelProperties.toHealing_F,
    Proofs.ModelProperties.confirmationReadFrom_st_core,
    Proofs.ModelProperties.confirmationReadFrom_cache, hprep, hraw]
  exact (ip_clip_result_advance before.st.core.F before.st.core.F
    (Proofs.ModelProperties.Preceq_self _) (some root)).trans key.symm

#print axioms frame_phase_prepared_eq


end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
