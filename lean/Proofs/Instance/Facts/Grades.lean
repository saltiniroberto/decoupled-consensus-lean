import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Instance.NoRaise.GradesDue
import Proofs.Instance.Equalities.ForkChoiceImages
import Proofs.Instance.Equalities.GradesImages
import Proofs.Instance.Equalities.ContractImages

/-!
# The grades facts at `Model.specDraft`

Proofs of fields of `GradesFacts` and `GradesRunFacts` at `Model.specDraft`, with the equalities
between its grade members and those of `Model.vocabulary` that the proofs rewrite with.
-/

set_option autoImplicit false

/-! ## Blocks and their `Block.toSpec` forms -/

namespace SpecDraftRecord.GradesLocal

open Spec

variable {V : Type} [DecidableEq V]

/-- `Block.toSpec` is injective. -/
theorem blockToSpec_inj (A B : DecoupledConsensusModel.Block V) :
    Block.toSpec A = Block.toSpec B ↔ A = B :=
  ⟨fun h => by simpa using congrArg Block.toProof h, fun h => h ▸ rfl⟩

omit [DecidableEq V] in
/-- `Block.toSpec` keeps the depth. -/
theorem toSpec_depth (B : DecoupledConsensusModel.Block V) : (Block.toSpec B).depth = B.depth := by
  rw [← Block.toProof_depth, Block.toProof_toSpec]

/-- `Block.toSpec A` is an ancestor of `Block.toSpec B`, or equal to it, exactly when `A` is an
    ancestor of `B` or equal to it. -/
theorem toSpec_ancestorEq (A B : DecoupledConsensusModel.Block V) :
    (Block.toSpec A).ancestorEq (Block.toSpec B) = DecoupledConsensusModel.Block.preceq A B := by
  induction B with
  | genesis =>
      show (Block.toSpec A).ancestorEq Block.genesis = _
      rw [Block.ancestorEq, DecoupledConsensusModel.Block.preceq]
      have e : (Block.genesis : Block V) = Block.toSpec DecoupledConsensusModel.Block.genesis := rfl
      rw [e]
      simp only [blockToSpec_inj]
  | node p s r votes support ats proposer ih =>
      have e : Block.toSpec (DecoupledConsensusModel.Block.node p s r votes support ats proposer) =
          Block.node (Block.toSpec p) s (BlockId.toSpec r) (votes.map GoldfishVote.toSpec)
            (support.map GoldfishVote.toSpec) (ats.map Attestation.toSpec) proposer := rfl
      rw [e, Block.ancestorEq, ← e, DecoupledConsensusModel.Block.preceq, ih]
      simp only [blockToSpec_inj]

/-- `Block.toSpec A` and `Block.toSpec B` are compatible exactly when `A` and `B` are. -/
theorem toSpec_compatible (A B : DecoupledConsensusModel.Block V) :
    (Block.toSpec A).compatible (Block.toSpec B) = DecoupledConsensusModel.Block.compatible A B := by
  simp only [Block.compatible, DecoupledConsensusModel.Block.compatible, toSpec_ancestorEq]

/-- Mapping each block of `X` by `Block.toSpec` and back by `Block.toProof` gives `X`. -/
theorem image_toProof_map_toSpec (X : Finset (DecoupledConsensusModel.Block V)) :
    (X.map ForkChoiceGrades.blockToSpecEmb).image Block.toProof = X := by
  ext B
  simp [ForkChoiceGrades.blockToSpecEmb]

/-- The deepest block of the `Block.toSpec` forms of `X`, mapped back by `Block.toProof`, is the
    deepest block of `X`. -/
theorem deepest?_map_toSpec (X : Finset (DecoupledConsensusModel.Block V)) :
    (Block.deepest? (X.map ForkChoiceGrades.blockToSpecEmb)).map Block.toProof =
      DecoupledConsensusModel.Block.deepest? X := by
  have hinj : Set.InjOn (Block.toProof (V := V))
      (↑(X.map ForkChoiceGrades.blockToSpecEmb) : Set (Block V)) := by
    intro a ha b hb h
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, ForkChoiceGrades.blockToSpecEmb,
      Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨a', _, rfl⟩ := ha
    obtain ⟨b', _, rfl⟩ := hb
    simp only [Block.toProof_toSpec] at h
    rw [h]
  have h := Block.toProof_deepest?_of_injOn _ hinj
  rw [image_toProof_map_toSpec] at h
  exact h.symm

omit [DecidableEq V] in
/-- `chain_up n` at `Block.toSpec B` is the list of `Block.toSpec` forms of `chain_up n B`. -/
theorem toSpec_chain_up (n : Nat) (B : DecoupledConsensusModel.Block V) :
    Protocol.chain_up n (Block.toSpec B) =
      (DecoupledConsensusModel.Protocol.chain_up n B).map Block.toSpec := by
  induction n generalizing B with
  | zero => simp [DecoupledConsensusModel.Protocol.chain_up, Protocol.chain_up]
  | succ n ih =>
    cases B with
    | genesis =>
      simp [DecoupledConsensusModel.Protocol.chain_up, Protocol.chain_up, Block.toSpec,
        DecoupledConsensusModel.Block.parent?, Block.parent?, Id.run, Option.value, pure]
    | node p s r votes support ats proposer =>
      simp [DecoupledConsensusModel.Protocol.chain_up, Protocol.chain_up, Block.toSpec,
        DecoupledConsensusModel.Block.parent?, Block.parent?, Id.run, ih, Option.value, pure]

omit [DecidableEq V] in
/-- `chain_of` at `Block.toSpec B` is the list of `Block.toSpec` forms of `chain_of B`. -/
theorem toSpec_chain_of (B : DecoupledConsensusModel.Block V) :
    Protocol.chain_of (Block.toSpec B) =
      (DecoupledConsensusModel.Protocol.chain_of B).map Block.toSpec := by
  rw [Protocol.chain_of, toSpec_depth, toSpec_chain_up, DecoupledConsensusModel.Protocol.chain_of]

/-- The genesis block is an ancestor of every block `B`, or `B` itself. -/
theorem genesis_ancestorEq (B : Block V) : Block.ancestorEq .genesis B = true := by
  induction B with
  | genesis => simp [Block.ancestorEq]
  | node p s root gv gsv ats v ih => simp [Block.ancestorEq, ih]

/-- The deepest ancestor of `g`, or `g` itself, compatible with `F`, by recursion on `g`'s parent. -/
def clipBlock (g F : Block V) : Block V :=
  match g with
  | .genesis => .genesis
  | .node p s root gv gsv ats v =>
      if Block.compatible (.node p s root gv gsv ats v) F then
        .node p s root gv gsv ats v
      else clipBlock p F

/-- The loop of `deepest_compatible_ancestor`, run over at least `g.depth + 1` indices from
    `(none, g)`, ends in `(some x, x)` with `x = clipBlock g F`. -/
theorem dca_loop_eq (F : Block V) (l : List Nat) (g : Block V) (hl : g.depth + 1 ≤ l.length) :
    (forIn (m := Id) l ((none : Option (Block V)), g) fun _ (s : Option (Block V) × Block V) =>
        if s.2.compatible F = true then pure (ForInStep.done (some s.2, s.2))
        else pure (ForInStep.yield (none, s.2.parent))) =
      (some (clipBlock g F), clipBlock g F) := by
  induction l generalizing g with
  | nil => simp at hl
  | cons x l ih =>
    rw [List.forIn_cons]
    cases g with
    | genesis =>
      have hc : (Block.genesis : Block V).compatible F = true := by
        simp [Block.compatible, genesis_ancestorEq]
      simp only [hc, if_true]
      rfl
    | node p s root gv gsv ats v =>
      by_cases hc : (Block.node p s root gv gsv ats v).compatible F = true
      · simp only [hc, if_true]
        simp only [clipBlock, hc, if_true]
        rfl
      · have hl' : p.depth + 1 ≤ l.length := by
          simp [Block.depth] at hl; omega
        have hpar : (Block.node p s root gv gsv ats v).parent = p := rfl
        simp only [hc, Bool.false_eq_true, if_false, hpar]
        show forIn l (none, p) _ = _
        rw [ih p hl']
        simp only [clipBlock, hc, Bool.false_eq_true, if_false]

/-- `deepest_compatible_ancestor g F = clipBlock g F`. -/
theorem deepest_compatible_ancestor_eq (g F : Block V) :
    Protocol.deepest_compatible_ancestor g F = clipBlock g F := by
  unfold Protocol.deepest_compatible_ancestor
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [dca_loop_eq F _ g (by simp [Std.Legacy.Range.size])]
  rfl

/-- `clipBlock` at the `Block.toSpec` forms of `g` and `F` is the form of `clipGrade g F`. -/
theorem clipBlock_toSpec (g F : DecoupledConsensusModel.Block V) :
    clipBlock (Block.toSpec g) (Block.toSpec F) =
      Block.toSpec (DecoupledConsensusModel.Protocol.clipGrade g F) := by
  induction g with
  | genesis =>
      rw [DecoupledConsensusModel.Protocol.clipGrade]
      rfl
  | node p s r votes support ats proposer ih =>
      have e : Block.toSpec (DecoupledConsensusModel.Block.node p s r votes support ats proposer) =
          Block.node (Block.toSpec p) s (BlockId.toSpec r) (votes.map GoldfishVote.toSpec)
            (support.map GoldfishVote.toSpec) (ats.map Attestation.toSpec) proposer := rfl
      rw [e, clipBlock, ← e, toSpec_compatible, DecoupledConsensusModel.Protocol.clipGrade]
      split_ifs
      · rfl
      · exact ih

end SpecDraftRecord.GradesLocal

namespace SpecDraftRecord.GradesFacts

open DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## Members equal to `Model.vocabulary`'s -/

/-- `Model.specDraft`'s `opening_slot` equals `Model.vocabulary`'s: both are `r * R`. -/
theorem eq_opening_slot :
    (Model.specDraft (V := V)).opening_slot = (Model.vocabulary (V := V)).opening_slot := by
  funext hc r
  show r * hc.R = hc.opening_slot r
  unfold DecoupledConsensusModel.Protocol.HealConfig.opening_slot
  rfl

/-- `Model.specDraft`'s `round_of` equals `Model.vocabulary`'s: both are `s / R`. -/
theorem eq_round_of :
    (Model.specDraft (V := V)).round_of = (Model.vocabulary (V := V)).round_of := by
  funext hc s
  show s / hc.R = hc.round_of s
  unfold DecoupledConsensusModel.Protocol.HealConfig.round_of
  rfl

/-- `Model.specDraft`'s `opening` equals `Model.vocabulary`'s. -/
theorem eq_opening :
    (Model.specDraft (V := V)).opening = (Model.vocabulary (V := V)).opening := by
  funext E hc r
  show (Spec.Config.toSpec E hc unreadHeightConfig).opening r =
    DecoupledConsensusModel.Protocol.opening E hc r
  rw [toProof_opening E hc unreadHeightConfig]

/-- `Model.specDraft`'s `a` equals `Model.vocabulary`'s: both are `4Δ · (r · R) + 6Δ`. -/
theorem eq_a :
    (Model.specDraft (V := V)).a = (Model.vocabulary (V := V)).a := by
  funext hc d r
  show 4 * d * ((r * hc.R : Nat) : DecoupledConsensusModel.Time) + 6 * d = hc.a d r
  unfold DecoupledConsensusModel.Protocol.HealConfig.a
    DecoupledConsensusModel.Protocol.HealConfig.opening_slot DecoupledConsensusModel.slotStart
  rfl

/-- `Model.specDraft`'s `early` equals `Model.vocabulary`'s. -/
theorem eq_early :
    (Model.specDraft (V := V)).early = (Model.vocabulary (V := V)).early := by
  funext E hc r p
  show (Spec.Config.toSpec E hc unreadHeightConfig).early r
      (Spec.Protocol.Phase.toSpec p) = DecoupledConsensusModel.Protocol.early E hc r p
  rw [← toProof_early E hc unreadHeightConfig, Spec.Protocol.Phase.toProof_toSpec]

/-- `Model.specDraft`'s `proposal_time` equals `Model.vocabulary`'s. -/
theorem eq_proposal_time :
    (Model.specDraft (V := V)).proposal_time = (Model.vocabulary (V := V)).proposal_time := by
  funext E s
  exact (toProof_proposal_time E unreadHealConfig unreadHeightConfig s).symm

/-- `Model.specDraft`'s `late` equals `Model.vocabulary`'s. -/
theorem eq_late :
    (Model.specDraft (V := V)).late = (Model.vocabulary (V := V)).late := by
  funext E hc r p
  show (Spec.Config.toSpec E hc unreadHeightConfig).opening r +
      Member.lateOffset p * (Spec.Config.toSpec E hc unreadHeightConfig).Δ =
    DecoupledConsensusModel.Protocol.late E hc r p
  rw [← toProof_opening E hc unreadHeightConfig]
  unfold DecoupledConsensusModel.Protocol.late
  cases p <;>
    simp only [Member.lateOffset, DecoupledConsensusModel.Protocol.Phase.lateOffset] <;> rfl

/-- `Model.specDraft`'s `domain` equals `Model.vocabulary`'s. -/
theorem eq_domain :
    (Model.specDraft (V := V)).domain = (Model.vocabulary (V := V)).domain := by
  funext E hc r p
  show (Spec.Config.toSpec E hc unreadHeightConfig).opening r +
      Member.domainOffset p * (Spec.Config.toSpec E hc unreadHeightConfig).Δ =
    DecoupledConsensusModel.Protocol.domain E hc r p
  rw [← toProof_opening E hc unreadHeightConfig]
  unfold DecoupledConsensusModel.Protocol.domain
  cases p <;>
    simp only [Member.domainOffset, DecoupledConsensusModel.Protocol.Phase.domainOffset] <;> rfl

/-- `Model.specDraft`'s `clipGrade` equals `Model.vocabulary`'s. -/
theorem eq_clipGrade :
    (Model.specDraft (V := V)).clipGrade = (Model.vocabulary (V := V)).clipGrade := by
  funext g F
  show (Spec.Protocol.deepest_compatible_ancestor (Spec.Block.toSpec g)
      (Spec.Block.toSpec F)).toProof = DecoupledConsensusModel.Protocol.clipGrade g F
  rw [GradesLocal.deepest_compatible_ancestor_eq, GradesLocal.clipBlock_toSpec,
    Spec.Block.toProof_toSpec]

/-- `Model.specDraft`'s `chain_of` equals `Model.vocabulary`'s. -/
theorem eq_chain_of :
    (Model.specDraft (V := V)).chain_of = (Model.vocabulary (V := V)).chain_of := by
  funext B
  show (Spec.Protocol.chain_of (Spec.Block.toSpec B)).map
      Spec.Block.toProof = DecoupledConsensusModel.Protocol.chain_of B
  rw [← toProof_chain_of, Spec.Block.toProof_toSpec]

/-- `Model.specDraft`'s `activePrefix` equals `Model.vocabulary`'s. -/
theorem eq_activePrefix :
    (Model.specDraft (V := V)).activePrefix = (Model.vocabulary (V := V)).activePrefix := by
  funext tree root
  show (Spec.Protocol.activePrefix (tree.map ForkChoiceGrades.blockToSpecEmb)
      (Spec.Block.toSpec root)).map Spec.Block.toProof =
    DecoupledConsensusModel.Protocol.activePrefix tree root
  unfold Spec.Protocol.activePrefix DecoupledConsensusModel.Protocol.activePrefix
  have hset : (tree.map ForkChoiceGrades.blockToSpecEmb).filter
        (fun B => B.ancestorEq (Spec.Block.toSpec root) = true) =
      (tree.filter (fun B => DecoupledConsensusModel.Block.preceq B root = true)).map
        ForkChoiceGrades.blockToSpecEmb := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_map, ForkChoiceGrades.blockToSpecEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨a, ⟨ha, by rwa [GradesLocal.toSpec_ancestorEq] at h⟩, rfl⟩
    · rintro ⟨a, ⟨ha, h⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, by rwa [GradesLocal.toSpec_ancestorEq]⟩
  rw [hset, GradesLocal.deepest?_map_toSpec]

/-- `Model.specDraft`'s `clipResult` equals `Model.vocabulary`'s. -/
theorem eq_clipResult :
    (Model.specDraft (V := V)).clipResult = (Model.vocabulary (V := V)).clipResult := by
  funext F result
  show (Spec.Protocol.make_result_compatible_with (Spec.Block.toSpec F)
      (Spec.GradeResult.toSpec result)).toProof =
    DecoupledConsensusModel.Protocol.clipResult F result
  have hc : ∀ B : DecoupledConsensusModel.Block V,
      (Spec.Protocol.deepest_compatible_ancestor (Spec.Block.toSpec B)
        (Spec.Block.toSpec F)).toProof = DecoupledConsensusModel.Protocol.clipGrade B F :=
    fun B => congrFun (congrFun (eq_clipGrade (V := V)) B) F
  rcases result with _ | _ | B
  · simp [Spec.Protocol.make_result_compatible_with, Id.run,
      Spec.GradeResult.toSpec, DecoupledConsensusModel.Protocol.clipResult]
    rfl
  · simp [Spec.Protocol.make_result_compatible_with, Id.run,
      Spec.GradeResult.toSpec, DecoupledConsensusModel.Protocol.clipResult,
      Spec.GradeResult.block]
    rfl
  · simp only [Spec.Protocol.make_result_compatible_with, Id.run,
      Spec.GradeResult.toSpec, DecoupledConsensusModel.Protocol.clipResult,
      Option.map_some]
    simp only [Spec.GradeResult.block, ne_eq, reduceCtorEq, not_false_eq_true,
      dite_true, Option.value, Option.get_some]
    show some (some (Spec.Protocol.deepest_compatible_ancestor
      (Spec.Block.toSpec B) (Spec.Block.toSpec F)).toProof) = _
    rw [hc]

/-- `Model.specDraft`'s `token` equals `Model.vocabulary`'s. -/
theorem eq_token :
    (Model.specDraft (V := V)).token = (Model.vocabulary (V := V)).token := by
  funext u
  show (Spec.Protocol.token (Spec.Protocol.SGVote.toSpec u)).toProof =
    DecoupledConsensusModel.Protocol.token u
  rw [← toProof_token, Spec.Protocol.SGVote.toProof_toSpec]

/-- `Model.specDraft`'s `deepest_clear` equals `Model.vocabulary`'s. -/
theorem eq_deepest_clear :
    (Model.specDraft (V := V)).deepest_clear = (Model.vocabulary (V := V)).deepest_clear := by
  funext floor C test
  show (Spec.Protocol.deepest_clear
      ((floor.map Spec.Block.toSpec).getD .genesis) (Spec.Block.toSpec C)
      (fun B => test B.toProof)).map Spec.Block.toProof =
    DecoupledConsensusModel.Protocol.deepest_clear floor C test
  unfold Spec.Protocol.deepest_clear DecoupledConsensusModel.Protocol.deepest_clear
  have hset : (Spec.Protocol.chain_of (Spec.Block.toSpec C)).toFinset.filter
        (fun B => (((floor.map Spec.Block.toSpec).getD .genesis).ancestorEq B &&
          test B.toProof) = true) =
      ((DecoupledConsensusModel.Protocol.chain_of C).toFinset.filter (fun B =>
        floor.elim true (fun anchor => DecoupledConsensusModel.Block.preceq anchor B) = true ∧
          test B = true)).map ForkChoiceGrades.blockToSpecEmb := by
    rw [GradesLocal.toSpec_chain_of]
    ext B
    simp only [Finset.mem_filter, Finset.mem_map, List.mem_toFinset, List.mem_map,
      ForkChoiceGrades.blockToSpecEmb, Function.Embedding.coeFn_mk, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hf, ht⟩
      refine ⟨a, ⟨ha, ?_, by simpa using ht⟩, rfl⟩
      cases floor with
      | none => rfl
      | some A => simpa [GradesLocal.toSpec_ancestorEq] using hf
    · rintro ⟨a, ⟨ha, hf, ht⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ?_, by simpa using ht⟩
      cases floor with
      | none => exact GradesLocal.genesis_ancestorEq _
      | some A => simpa [GradesLocal.toSpec_ancestorEq] using hf
  rw [hset, GradesLocal.deepest?_map_toSpec]

/-- `Model.specDraft`'s `CleanFrom` holds exactly when `Model.vocabulary`'s does. -/
theorem eq_CleanFrom {Key : Type}
    (raw : Finset (DecoupledConsensusModel.Protocol.Token Key)) (k : Nat) :
    (Model.specDraft (V := V)).CleanFrom raw k ↔ (Model.vocabulary (V := V)).CleanFrom raw k := by
  show Spec.Protocol.CleanFrom (raw.map ForkChoiceGrades.tokenToSpecEmb) k ↔
    DecoupledConsensusModel.Protocol.CleanFrom raw k
  simp only [Spec.Protocol.CleanFrom, DecoupledConsensusModel.Protocol.CleanFrom,
    Finset.forall_mem_map]
  exact Iff.rfl

/-! ## Members read through `toProof` -/

/-- `Model.specDraftBase`'s `sgVote` equals `Model.vocabulary`'s. -/
theorem eq_sgVote_base :
    (Model.specDraftBase (V := V)).sgVote = (Model.vocabulary (V := V)).sgVote := by
  funext a
  show (Spec.Protocol.sgVote (Spec.Attestation.toSpec a)).toProof =
    DecoupledConsensusModel.Protocol.sgVote a
  rw [← toProof_sgVote, Spec.Attestation.toProof_toSpec]

/-- The grade-1 result of `fr` is the grade-1 result of `Spec.RoundGrades.toProof fr`. -/
theorem sd_frame_g1 (fr : (Model.specDraft (V := V)).Frame) :
    Model.Frame.g1 fr =
      Model.Frame.g1 (M := Model.vocabulary (V := V)) (Spec.RoundGrades.toProof fr) :=
  rfl

/-- The grade-2 result of `fr` is the grade-2 result of `Spec.RoundGrades.toProof fr`. -/
theorem sd_frame_g2 (fr : (Model.specDraft (V := V)).Frame) :
    Model.Frame.g2 fr =
      Model.Frame.g2 (M := Model.vocabulary (V := V)) (Spec.RoundGrades.toProof fr) :=
  rfl

/-- `Model.specDraft`'s `phaseResult fr p` is the result of phase `p` in
    `Spec.RoundGrades.toProof fr`. -/
theorem sd_phaseResult (fr : (Model.specDraft (V := V)).Frame)
    (p : DecoupledConsensusModel.Protocol.Phase) :
    (Model.specDraft (V := V)).phaseResult fr p =
      (Model.vocabulary (V := V)).phaseResult (Spec.RoundGrades.toProof fr) p := by
  show (Spec.Protocol.phaseResult fr (Spec.Protocol.Phase.toSpec p)).toProof =
    DecoupledConsensusModel.Protocol.phaseResult (Spec.RoundGrades.toProof fr) p
  rw [← toProof_phaseResult, Spec.Protocol.Phase.toProof_toSpec]

/-- The image under `toProof` of the grades of round `r` saved in `c` is the grades of round `r`
    saved in the image of `c`. -/
theorem sd_cacheAtRound (c : (Model.specDraft (V := V)).Cache) (r : DecoupledConsensusModel.Round) :
    Spec.RoundGrades.toProof ((Model.specDraft (V := V)).cacheAtRound c r) =
      (Model.vocabulary (V := V)).cacheAtRound (Spec.SavedGrades.toProof c) r :=
  (toProof_cacheAtRound c r).symm

end SpecDraftRecord.GradesFacts

namespace SpecDraftRecord.NoRaise

/-! ## What the grades update computes -/

open Spec Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Each of the six results of an answer `st'` of `update_grades` at time `t` is computed exactly
    when it is computed in the store's saved grades brought to `t`'s round, or it is one of the
    three results the routine computes and `t` is its time. -/
theorem update_grades_pending_iff {C : Config} {P : Provisional V} {st st' : Store V} {t : Time}
    (h : update_grades C P st t = .ok st') :
    (st'.saved_grades.current.g0 ≠ .pending ↔
        (advance_to_round st.saved_grades (roundAt C t)).current.g0 ≠ .pending ∨
          t = C.opening (roundAt C t) + C.Δ) ∧
    (st'.saved_grades.current.g1 ≠ .pending ↔
        (advance_to_round st.saved_grades (roundAt C t)).current.g1 ≠ .pending ∨
          t = C.opening (roundAt C t)) ∧
    (st'.saved_grades.current.g2 ≠ .pending ↔
        (advance_to_round st.saved_grades (roundAt C t)).current.g2 ≠ .pending) ∧
    (st'.saved_grades.next.g0 ≠ .pending ↔
        (advance_to_round st.saved_grades (roundAt C t)).next.g0 ≠ .pending) ∧
    (st'.saved_grades.next.g1 ≠ .pending ↔
        (advance_to_round st.saved_grades (roundAt C t)).next.g1 ≠ .pending) ∧
    (st'.saved_grades.next.g2 ≠ .pending ↔
        (advance_to_round st.saved_grades (roundAt C t)).next.g2 ≠ .pending ∨
          t = C.opening (roundAt C t + 1) - C.Δ) := by
  simp only [update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := DRE.ok_of_bind h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    simp only [make_saved_grades_compatible_with, make_round_grades_compatible_with,
      make_result_compatible_with_ne_pending_iff, ne_eq, reduceCtorEq, not_false_eq_true,
      implies_true, true_or, or_true, iff_true] <;>
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at * <;>
    tauto


omit [Fintype V] in
/-- If round `r`'s result for `q` is computed in `c`, and `c.round ≤ ρ ≤ r`, it is still computed in
    `advance_to_round c ρ`. -/
theorem srg_advance_ne_pending {c : SavedGrades V} {ρ r : Round} {q : Phase}
    (h1 : c.round ≤ ρ) (h2 : ρ ≤ r)
    (h : phaseResult (saved_round_grades c r) q ≠ .pending) :
    phaseResult (saved_round_grades (advance_to_round c ρ) r) q ≠ .pending := by
  simp only [advance_to_round, saved_round_grades] at h ⊢
  split_ifs at h ⊢ <;> (try simp only at *) <;>
    first
      | exact h
      | (exfalso; (try simp only [Spec.Round] at *); omega)
      | (exfalso; apply h; cases q <;> rfl)
      | (subst_vars; exact h)

omit [Fintype V] in
/-- A result of round `r` computed in `advance_to_round c ρ` was computed in `c`. -/
theorem srg_advance_ne_pending_rev {c : SavedGrades V} {ρ r : Round} {q : Phase}
    (h : phaseResult (saved_round_grades (advance_to_round c ρ) r) q ≠ .pending) :
    phaseResult (saved_round_grades c r) q ≠ .pending := by
  simp only [advance_to_round, saved_round_grades] at h ⊢
  split_ifs at h ⊢ <;> (try simp only at *) <;>
    first
      | exact h
      | (exfalso; (try simp only [Spec.Round] at *); omega)
      | (exfalso; apply h; cases q <;> rfl)
      | (subst_vars; exact h)

end SpecDraftRecord.NoRaise

/-! ## The fields of `GradesFacts` -/

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

set_option linter.unusedVariables false

open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Engine
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)
open DecoupledConsensusModel.Proofs.HealingLemmas
open Execution (Setup)
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open Execution
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (HeightConfig)
open Protocol (own_lock)
open Internal.HealingSurface
open Proofs.HealingLemmas
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedConfirmationMembership
open Protocol
open Execution Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Execution Internal.NamedOutageEntry DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)
open Internal Execution Internal.PhaseGrades DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)
open DecoupledConsensusModel.Proofs.NamedProposalParent
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)
open scoped DC
open SpecDraftRecord.GradesFacts

/-- The field `early_g2_le_opening` of `GradesFacts` at `Model.specDraft`: a round's G2 early cutoff
    comes no later than the instant the round opens. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_le_opening : ∀ (S : Setup V) (r : Round),
    (Model.specDraft (V := V)).early S.E S.hc r .g2 ≤ (Model.specDraft (V := V)).opening S.E S.hc r := by
  simp only [eq_opening, eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_le_opening

/-- The field `action_succ_eq_add_rounds` of `GradesFacts` at `Model.specDraft`: round `r + 1`'s
    action instant is `4 * S.hc.R * S.E.Δ` after round `r`'s. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_action_succ_eq_add_rounds : ∀ (S : Setup V) (r : Round),
    Restated.Vocabulary.Execution.Setup.a (Model.specDraft (V := V)) S (r + 1) =
      Restated.Vocabulary.Execution.Setup.a (Model.specDraft (V := V)) S r + 4 * (S.hc.R : Int) * S.E.Δ := by
  simp only [Restated.Vocabulary.Execution.Setup.a, eq_a]
  exact (Model.vocabulary_facts_grades (V := V)).action_succ_eq_add_rounds

/-- The field `domain_le_a` of `GradesFacts` at `Model.specDraft`: the instant at which round `r`'s
    grade `p` is computed is at or before round `r`'s action instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_le_a : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    (Model.specDraft (V := V)).domain S.E S.hc r p ≤ (Model.specDraft (V := V)).a S.hc S.E.Δ r := by
  simp only [eq_a, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_le_a

/-- The field `attestWindow_prev_inPhase` of `GradesFacts` at `Model.specDraft`: if
    `tGAT + 8RΔ ≤ tE' ≤ opening r₀ < tE` and `1 ≤ r₀`, then the window
    `[a (r₀ − 1) − wAttest, a (r₀ − 1)]` lies inside `[tGAT, tE]`, and its end is at or before
    `opening (r₀ + 1)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_attestWindow_prev_inPhase : ∀ (S : Setup V) (tGAT tE tE' : Int) {r₀ : Nat}
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE') (hr1 : 1 ≤ r₀)
    (hr' : tE' ≤ (Model.specDraft (V := V)).opening S.E S.hc r₀) (hrE : (Model.specDraft (V := V)).opening S.E S.hc r₀ < tE),
    tGAT ≤ ((Model.specDraft (V := V)).a S.hc S.E.Δ (r₀ - 1)) - wAttest S ∧
      ((Model.specDraft (V := V)).a S.hc S.E.Δ (r₀ - 1)) ≤ tE ∧
      ((Model.specDraft (V := V)).a S.hc S.E.Δ (r₀ - 1)) ≤ (Model.specDraft (V := V)).opening S.E S.hc (r₀ + 1) := by
  simp only [eq_opening, eq_a]
  exact (Model.vocabulary_facts_grades (V := V)).attestWindow_prev_inPhase

/-- The field `le_opening_add_toNat` of `GradesFacts` at `Model.specDraft`: round `r + tE.toNat`
    opens at or after `tE`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_le_opening_add_toNat : ∀ (S : Setup V) (r : Nat) (tE : Int),
    tE ≤ (Model.specDraft (V := V)).opening S.E S.hc (r + tE.toNat) := by
  simp only [eq_opening]
  exact (Model.vocabulary_facts_grades (V := V)).le_opening_add_toNat

/-- The field `domain_add_five_delta_le_action` of `GradesFacts` at `Model.specDraft`: for every
    phase `p`, round `r`'s domain instant for `p`, plus five delays, is at or before round `r`'s
    action instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_add_five_delta_le_action : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    (Model.specDraft (V := V)).domain S.E S.hc r p + 5 * S.E.Δ ≤ (Model.specDraft (V := V)).a S.hc S.E.Δ r := by
  simp only [eq_a, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_add_five_delta_le_action

/-- The field `supports_transport_with_cap` of `GradesFacts` at `Model.specDraft`: if the source
    tokens are nested early in late in raw, the target early tokens are among the target late
    tokens, every source early token covering `B` reaches the target early tokens or a target raw
    equivocation at its round, every target late token comes back as a source late token or a source
    raw equivocation at its round, and every target raw equivocation comes back as a source one,
    then source support for `B` is target support for `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_supports_transport_with_cap : ∀ {Key Blk : Type} (covers : Key → Blk → Prop)
    {se sl sr te tl tr : Finset (Token Key)} {B : Blk}
    (hSourceLate : se ⊆ sl) (hSourceRaw : sl ⊆ sr) (hTargetLate : te ⊆ tl)
    (hForward : ∀ u ∈ se, covers u.key B → u ∈ te ∨ DecoupledConsensusModel.Protocol.EquivocationAt tr u.round)
    (hLateBack : ∀ x ∈ tl, x ∈ sl ∨ DecoupledConsensusModel.Protocol.EquivocationAt sr x.round)
    (hEqBack : ∀ k, DecoupledConsensusModel.Protocol.EquivocationAt tr k → DecoupledConsensusModel.Protocol.EquivocationAt sr k)
    (h : (Model.specDraft (V := V)).Supports covers se sl sr B), (Model.specDraft (V := V)).Supports covers te tl tr B := by
  exact (Model.vocabulary_facts_grades (V := V)).supports_transport_with_cap

/-- The field `opposition_back_with_cap` of `GradesFacts` at `Model.specDraft`: if the source early
    tokens are among the source late tokens, every source early token covering `B` reaches the
    target early tokens or a target raw equivocation at its round, every target late token comes
    back as a source late token or a source raw equivocation at its round, and every target raw
    equivocation comes back as a source one, then target opposition to `B` is source opposition to
    `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposition_back_with_cap : ∀ {Key Blk : Type} (covers : Key → Blk → Prop)
    {se sl sr te tl tr : Finset (Token Key)} {B : Blk}
    (hSourceLate : se ⊆ sl)
    (hForward : ∀ u ∈ se, covers u.key B → u ∈ te ∨ DecoupledConsensusModel.Protocol.EquivocationAt tr u.round)
    (hLateBack : ∀ x ∈ tl, x ∈ sl ∨ DecoupledConsensusModel.Protocol.EquivocationAt sr x.round)
    (hEqBack : ∀ k, DecoupledConsensusModel.Protocol.EquivocationAt tr k → DecoupledConsensusModel.Protocol.EquivocationAt sr k)
    (h : (Model.specDraft (V := V)).Opposes covers te tl tr B), (Model.specDraft (V := V)).Opposes covers se sl sr B := by
  exact (Model.vocabulary_facts_grades (V := V)).opposition_back_with_cap

/-- The field `early_g2_eq` of `GradesFacts` at `Model.specDraft`: the early cutoff of grade 2 of
    round `r` is `11Δ` before round `r`'s action instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_eq : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g2 = (Model.specDraft (V := V)).a S.hc S.E.Δ r - 11 * S.E.Δ := by
  simp only [eq_a, eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_eq

/-- The field `action_add_delta_le_next_Γ_neg1` of `GradesFacts` at `Model.specDraft`: one delay
    after the action instant of round `r` is at or before the earliest grade cutoff of round
    `r + 1`, one delay before the start of that round's opening slot. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_action_add_delta_le_next_Γ_neg1 : ∀ (S : Setup V) (r : Round),
    (Model.specDraft (V := V)).a S.hc S.E.Δ r + S.E.Δ ≤ slotStart S.E.Δ ((Model.specDraft (V := V)).opening_slot S.hc (r + 1)) - S.E.Δ := by
  simp only [eq_opening_slot, eq_a]
  exact (Model.vocabulary_facts_grades (V := V)).action_add_delta_le_next_Γ_neg1

/-- The field `gammaNeg1_eq_domain_g2_succ` of `GradesFacts` at `Model.specDraft`: the earliest
    grade cutoff of round `r + 1`, one delay before the start of its opening slot, is the G2 domain
    instant of round `r + 1`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gammaNeg1_eq_domain_g2_succ : ∀ (S : Setup V) (r : Round),
    slotStart S.E.Δ ((Model.specDraft (V := V)).opening_slot S.hc (r + 1)) - S.E.Δ = (Model.specDraft (V := V)).domain S.E S.hc (r + 1) .g2 := by
  simp only [eq_opening_slot, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).gammaNeg1_eq_domain_g2_succ

/-- The field `action_delta_le_early` of `GradesFacts` at `Model.specDraft`: with at least three
    slots per round, one delay after the action instant of round `q` is at or before the G2 early
    cutoff of any later round `r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_action_delta_le_early : ∀ (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R) (hqr : q < r),
    (Model.specDraft (V := V)).a S.hc S.E.Δ q + S.E.Δ ≤ (Model.specDraft (V := V)).early S.E S.hc r .g2 := by
  simp only [eq_a, eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).action_delta_le_early

/-- The field `a_add_rounds` of `GradesFacts` at `Model.specDraft`: the action instant of round
    `r + k` is the action instant of round `r` plus `k` round lengths of `4Δ·R` each. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_a_add_rounds : ∀ (S : Setup V) (r k : Round), (Model.specDraft (V := V)).a S.hc S.E.Δ (r + k) = (Model.specDraft (V := V)).a S.hc S.E.Δ r + 4 * S.E.Δ * ((S.hc.R * k : Nat) : Time) := by
  simp only [eq_a]
  exact (Model.vocabulary_facts_grades (V := V)).a_add_rounds

/-- The field `deepest_clear_isSome_of_mem` of `GradesFacts` at `Model.specDraft`: if `floor` is
    absent or an ancestor of `B` (or `B` itself), `B` is on the chain of `C`, and `B` passes `test`,
    then the deepest clear ancestor of `C` from `floor` with the test `test` exists. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_deepest_clear_isSome_of_mem : ∀ {floor : Option (DecoupledConsensusModel.Block V)} {C B : DecoupledConsensusModel.Block V} {test : DecoupledConsensusModel.Block V → Bool}, (floor.elim True fun a ↦ a.preceq B = Bool.true) → B ∈ (Model.specDraft (V := V)).chain_of C → test B = Bool.true → ((Model.specDraft (V := V)).deepest_clear floor C test).isSome = Bool.true := by
  simp only [eq_chain_of, eq_deepest_clear]
  exact (Model.vocabulary_facts_grades (V := V)).deepest_clear_isSome_of_mem

/-- The field `gradeView_toHealing_clock` of `GradesFacts` at `Model.specDraft`: the grade view of
    the healing view of `st` with its clock set to `t` and its slot set to `s` is the grade view of
    the healing view of `st`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeView_toHealing_clock : ∀ (st : (Model.specDraft (V := V)).S) (t : DecoupledConsensusModel.Time) (s : DecoupledConsensusModel.Slot), ((Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_t_s st t s))) = ((Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing st)) := by
  intro st t s
  rfl

/-- The field `q10_supports_of_not_opposes` of `GradesFacts` at `Model.specDraft`: for every cover
    test `c`, if the early tokens `e` are among the late tokens `l` and `e` is not empty, then the
    tokens `e`, `l` and `raw` either oppose `B` under `c` or support `B` under `c`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_supports_of_not_opposes : ∀ {Key : Type} {Blk : Type} (c : Key → Blk → Prop) {e l raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, e ⊆ l → e.Nonempty → ¬(Model.specDraft (V := V)).Opposes c e l raw B → (Model.specDraft (V := V)).Supports c e l raw B := by
  exact (Model.vocabulary_facts_grades (V := V)).q10_supports_of_not_opposes

/-- The field `opposes_congr` of `GradesFacts` at `Model.specDraft`: if the cover tests `c` and `c'`
    agree on `B` for the key of every late token, then tokens that oppose `B` under `c` oppose it
    under `c'`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposes_congr : ∀ {Key : Type} {Blk : Type} (c c' : Key → Blk → Prop) {e l raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, (∀ x ∈ l, c x.key B ↔ c' x.key B) → (Model.specDraft (V := V)).Opposes c e l raw B → (Model.specDraft (V := V)).Opposes c' e l raw B := by
  exact (Model.vocabulary_facts_grades (V := V)).opposes_congr

/-- The field `supports_congr` of `GradesFacts` at `Model.specDraft`: if the early tokens are among
    the late tokens, and the cover tests `c` and `c'` agree on `B` for the key of every late token,
    then tokens that support `B` under `c` support it under `c'`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_supports_congr : ∀ {Key : Type} {Blk : Type} (c c' : Key → Blk → Prop) {e l raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, e ⊆ l → (∀ x ∈ l, c x.key B ↔ c' x.key B) → (Model.specDraft (V := V)).Supports c e l raw B → (Model.specDraft (V := V)).Supports c' e l raw B := by
  exact (Model.vocabulary_facts_grades (V := V)).supports_congr

/-- The field `alignRound_round` of `GradesFacts` at `Model.specDraft`: after
    `Protocol.alignRound c r₀`, the cache's round is `r₀`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_alignRound_round : ∀ (c : (Model.specDraft (V := V)).Cache) (r₀ : DecoupledConsensusModel.Round), ((Model.specDraft (V := V)).alignRound c r₀).round = r₀ := by
  intro c r₀
  show (Spec.Protocol.advance_to_round c r₀).round = r₀
  unfold Spec.Protocol.advance_to_round
  split_ifs with h
  · exact h.symm
  · rfl
  · rfl

/-- The field `cleanFrom_intro` of `GradesFacts` at `Model.specDraft`: if any two tokens `x` and `y`
    of `raw` with `k ≤ x.round` and the same round carry the same key, then `raw` is clean from
    round `k` on. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_cleanFrom_intro : ∀ {Key : Type} {raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {k : ℕ}, (∀ x ∈ raw, ∀ y ∈ raw, k ≤ x.round → x.round = y.round → x.key = y.key) → (Model.specDraft (V := V)).CleanFrom raw k := by
  simp only [eq_CleanFrom]
  exact (Model.vocabulary_facts_grades (V := V)).cleanFrom_intro

/-- The field `clear_of_g0` of `GradesFacts` at `Model.specDraft`: if the grade-0 entry of the frame
    `frame` is the root `root`, then the test of `frame` at the block `B` answers whether `B` and
    `root` lie on one chain. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_clear_of_g0 : ∀ {frame : (Model.specDraft (V := V)).Frame} {root : DecoupledConsensusModel.Block V}, frame.g0 = Option.some (Option.some root) → ∀ (B : DecoupledConsensusModel.Block V), (Model.specDraft (V := V)).clear frame B = B.compatible root := by
  intro (fr : Spec.RoundGrades V) root h B
  exact (Model.vocabulary_facts_grades (V := V)).clear_of_g0 (frame := fr.toProof) h B

/-- The field `clear_of_g0_some_none` of `GradesFacts` at `Model.specDraft`: if the frame's grade-0
    entry is a completed phase with no root, then every block `B` clears the frame. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_clear_of_g0_some_none : ∀ {frame : (Model.specDraft (V := V)).Frame}, frame.g0 = Option.some Option.none → ∀ (B : DecoupledConsensusModel.Block V), (Model.specDraft (V := V)).clear frame B = Bool.true := by
  intro (fr : Spec.RoundGrades V) h B
  exact (Model.vocabulary_facts_grades (V := V)).clear_of_g0_some_none (frame := fr.toProof) h B

/-- The field `compatible_of_clear` of `GradesFacts` at `Model.specDraft`: if the block `B` passes
    the test of the frame `frame`, and `frame`'s grade-0 entry is the completed root `root`, then
    `B` and `root` lie on one chain. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_compatible_of_clear : ∀ {frame : (Model.specDraft (V := V)).Frame} {B root : DecoupledConsensusModel.Block V}, (Model.specDraft (V := V)).clear frame B = Bool.true → frame.g0 = Option.some (Option.some root) → B.compatible root = Bool.true := by
  intro (fr : Spec.RoundGrades V) B root hc h
  exact (Model.vocabulary_facts_grades (V := V)).compatible_of_clear (frame := fr.toProof) hc h

/-- The field `key_eq_of_cleanFrom` of `GradesFacts` at `Model.specDraft`: if `raw` is clean from
    round `k` on, and the tokens `x` and `y` of `raw` have the same round, at least `k`, then they
    carry the same key. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_key_eq_of_cleanFrom : ∀ {Key : Type} {raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {k : ℕ}, (Model.specDraft (V := V)).CleanFrom raw k → ∀ x ∈ raw, ∀ y ∈ raw, k ≤ x.round → x.round = y.round → x.key = y.key := by
  simp only [eq_CleanFrom]
  exact (Model.vocabulary_facts_grades (V := V)).key_eq_of_cleanFrom

/-- The field `opening_slot_add_mk` of `GradesFacts` at `Model.specDraft`: the opening slot of round
    `r + k` is the opening slot of round `r` plus `k` times the round length `R`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_add_mk : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (r k : DecoupledConsensusModel.Round), ((Model.specDraft (V := V)).opening_slot hc (r + k)) = ((Model.specDraft (V := V)).opening_slot hc r) + k * hc.R := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_add_mk

/-- The field `opening_slot_succ_mk` of `GradesFacts` at `Model.specDraft`: round `r + 1` opens at
    the opening slot of round `r` plus `R`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_succ_mk : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round), ((Model.specDraft (V := V)).opening_slot hc (r + 1)) = ((Model.specDraft (V := V)).opening_slot hc r) + hc.R := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_succ_mk

/-- The field `opening_slot_zero_mk` of `GradesFacts` at `Model.specDraft`: the opening slot of
    round `0` is slot `0`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_zero_mk : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig), ((Model.specDraft (V := V)).opening_slot hc 0) = 0 := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_zero_mk

/-- The field `opposes_cases` of `GradesFacts` at `Model.specDraft`: if the tokens oppose `B`, then
    either some late token, of a round at least every early token's, does not cover `B`, or two raw
    tokens of one round, at least every early token's, carry different keys. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposes_cases : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, (Model.specDraft (V := V)).Opposes covers early late raw B → (∃ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) ∧ ¬covers x.key B) ∨ ∃ x ∈ raw, ∃ y ∈ raw, (∀ u ∈ early, u.round ≤ x.round) ∧ x.round = y.round ∧ x.key ≠ y.key := by
  exact (Model.vocabulary_facts_grades (V := V)).opposes_cases

/-- The field `opposes_of_late` of `GradesFacts` at `Model.specDraft`: if the token `x` is among the
    late tokens, its round is at least every early token's, and `x`'s key does not cover `B`, then
    the tokens oppose `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposes_of_late : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, ∀ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) → ¬covers x.key B → (Model.specDraft (V := V)).Opposes covers early late raw B := by
  exact (Model.vocabulary_facts_grades (V := V)).opposes_of_late

/-- The field `supports_elim` of `GradesFacts` at `Model.specDraft`: if the tokens support `B`, then
    some early token `u` has the largest round among the early tokens, covers `B`, the raw tokens
    are clean from `u`'s round on, and every late token of a round larger than `u`'s covers `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_supports_elim : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, (Model.specDraft (V := V)).Supports covers early late raw B → ∃ u ∈ early, (∀ x ∈ early, x.round ≤ u.round) ∧ covers u.key B ∧ (Model.specDraft (V := V)).CleanFrom raw u.round ∧ ∀ x ∈ late, u.round < x.round → covers x.key B := by
  simp only [eq_CleanFrom]
  exact (Model.vocabulary_facts_grades (V := V)).supports_elim

/-- The field `supports_intro` of `GradesFacts` at `Model.specDraft`: if the token `u` is among the
    early tokens, has the largest round among them, covers `B`, the raw tokens are clean from `u`'s
    round on, and every late token of a round larger than `u`'s covers `B`, then the tokens support
    `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_supports_intro : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, ∀ u ∈ early, (∀ x ∈ early, x.round ≤ u.round) → covers u.key B → (Model.specDraft (V := V)).CleanFrom raw u.round → (∀ x ∈ late, u.round < x.round → covers x.key B) → (Model.specDraft (V := V)).Supports covers early late raw B := by
  simp only [eq_CleanFrom]
  exact (Model.vocabulary_facts_grades (V := V)).supports_intro

/-- The field `deepest_clear_preceq` of `GradesFacts` at `Model.specDraft`: if the deepest clear
    ancestor of `C` from the optional block `floor` with the test `test` is `B`, then `B` is an
    ancestor of `C` or `C` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_deepest_clear_preceq : ∀ {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool} (h : (Model.specDraft (V := V)).deepest_clear floor C test = some B), Block.preceq B C = true := by
  simp only [eq_deepest_clear]
  exact (Model.vocabulary_facts_grades (V := V)).deepest_clear_preceq

/-- The field `early_g2_le_early_g0` of `GradesFacts` at `Model.specDraft`: for every environment
    `E`, configuration `hc` and round `r`, round `r`'s grade-2 early cutoff is at or before its
    grade-0 early cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_le_early_g0 : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round), (Model.specDraft (V := V)).early E hc r .g2 ≤ (Model.specDraft (V := V)).early E hc r .g0 := by
  simp only [eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_le_early_g0

/-- The field `early_g2_le_early_g1` of `GradesFacts` at `Model.specDraft`: for every environment
    `E`, configuration `hc` and round `r`, round `r`'s grade-2 early cutoff is at or before its
    grade-1 early cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_le_early_g1 : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round), (Model.specDraft (V := V)).early E hc r .g2 ≤ (Model.specDraft (V := V)).early E hc r .g1 := by
  simp only [eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_le_early_g1

/-- The field `early_le_late` of `GradesFacts` at `Model.specDraft`: for every round `r` and phase
    `p`, round `r`'s early cutoff of `p` is at or before its late cutoff of `p`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_le_late : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase), (Model.specDraft (V := V)).early E hc r p ≤ (Model.specDraft (V := V)).late E hc r p := by
  simp only [eq_early, eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).early_le_late

/-- The field `ActionRound_round_of_opening_succ` of `GradesFacts` at `Model.specDraft`: for every
    round `r`, the slot after round `r`'s opening slot belongs to round `r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_ActionRound_round_of_opening_succ : ∀ (hc : HealConfig) (r : Round), ((Model.specDraft (V := V)).round_of hc (((Model.specDraft (V := V)).opening_slot hc r) + 1)) = r := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).ActionRound_round_of_opening_succ

/-- The field `HealingLemmas_round_of_opening_succ` of `GradesFacts` at `Model.specDraft`: for every
    round `r`, the slot after round `r`'s opening slot belongs to round `r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_HealingLemmas_round_of_opening_succ : ∀ (hc : HealConfig) (r : Round), ((Model.specDraft (V := V)).round_of hc (((Model.specDraft (V := V)).opening_slot hc r) + 1)) = r := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).HealingLemmas_round_of_opening_succ

/-- The field `deepest_clear_eq_tip` of `GradesFacts` at `Model.specDraft`: if `C` is a descendant
    of the optional block `floor` or that block itself (when `floor` is some block), and `C` passes
    `test`, then the deepest clear ancestor of `C` from `floor` with the test `test` is `C`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_deepest_clear_eq_tip : ∀ {floor : Option (Block V)} {C : Block V} {test : Block V → Bool} (hfloor : floor.elim True (fun a => Block.preceq a C = true)) (htest : test C = true), (Model.specDraft (V := V)).deepest_clear floor C test = some C := by
  simp only [eq_deepest_clear]
  exact (Model.vocabulary_facts_grades (V := V)).deepest_clear_eq_tip

/-- The field `lastInteriorSlot_before_opening` of `GradesFacts` at `Model.specDraft`: for a
    positive round `q`, with `r` the round `q − 1` and `s` the slot before round `q`'s opening slot:
    the slot after round `r`'s opening slot is at or before `s`, `s` is before round `r + 1`'s
    opening slot, and `s + 1` is round `q`'s opening slot. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_lastInteriorSlot_before_opening : ∀ (hc : Protocol.HealConfig) {q : Round} (hq : 0 < q),
    let r := q - 1
    let s := (Model.specDraft (V := V)).opening_slot hc q - 1
    (Model.specDraft (V := V)).opening_slot hc r + 1 ≤ s ∧
      s < (Model.specDraft (V := V)).opening_slot hc (r + 1) ∧
      s + 1 = (Model.specDraft (V := V)).opening_slot hc q := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).lastInteriorSlot_before_opening

/-- The field `opening_slot_succ_eq` of `GradesFacts` at `Model.specDraft`: for every round `q`,
    round `q + 1`'s opening slot is round `q`'s opening slot plus `R` slots. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_succ_eq : ∀ (hc : Protocol.HealConfig) (q : Round), ((Model.specDraft (V := V)).opening_slot hc (q + 1)) = ((Model.specDraft (V := V)).opening_slot hc q) + hc.R := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_succ_eq

/-- The field `round_of_eq_of_opening_succ_le_of_lt_next_opening` of `GradesFacts` at
    `Model.specDraft`: every slot `k` at or after the slot after round `q`'s opening slot, and
    before round `q + 1`'s opening slot, belongs to round `q`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_eq_of_opening_succ_le_of_lt_next_opening : ∀ (hc : Protocol.HealConfig) {q k : Nat} (hlo : ((Model.specDraft (V := V)).opening_slot hc q) + 1 ≤ k) (hhi : k < ((Model.specDraft (V := V)).opening_slot hc (q + 1))), ((Model.specDraft (V := V)).round_of hc k) = q := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_eq_of_opening_succ_le_of_lt_next_opening

/-- The field `round_of_opening_slot_eq` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    round `r`'s opening slot belongs to round `r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_opening_slot_eq : ∀ (hc : Protocol.HealConfig) (r : Round), ((Model.specDraft (V := V)).round_of hc (((Model.specDraft (V := V)).opening_slot hc r))) = r := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_opening_slot_eq

/-- The field `round_of_opening_slot_eq_schedule` of `GradesFacts` at `Model.specDraft`: for every
    round `q`, round `q`'s opening slot belongs to round `q`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_opening_slot_eq_schedule : ∀ (hc : Protocol.HealConfig) (q : Round), ((Model.specDraft (V := V)).round_of hc (((Model.specDraft (V := V)).opening_slot hc q))) = q := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_opening_slot_eq_schedule

/-- The field `deepest_clear_Preceq` of `GradesFacts` at `Model.specDraft`: if the deepest block of
    `C`'s chain that descends from the optional block `floor` and passes `test` is `B`, then `B` is
    an ancestor of `C` or `C` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_deepest_clear_Preceq : ∀ {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool} (h : (Model.specDraft (V := V)).deepest_clear floor C test = some B), Block.Preceq B C := by
  simp only [eq_deepest_clear]
  exact (Model.vocabulary_facts_grades (V := V)).deepest_clear_Preceq

/-- The field `deepest_clear_floor_Preceq` of `GradesFacts` at `Model.specDraft`: if the deepest
    block of `C`'s chain that descends from the block `A` and passes `test` is `B`, then `A` is an
    ancestor of `B` or `B` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_deepest_clear_floor_Preceq : ∀ {A C B : Block V} {test : Block V → Bool} (h : (Model.specDraft (V := V)).deepest_clear (some A) C test = some B), Block.Preceq A B := by
  simp only [eq_deepest_clear]
  exact (Model.vocabulary_facts_grades (V := V)).deepest_clear_floor_Preceq

/-- The field `deepest_clear_test` of `GradesFacts` at `Model.specDraft`: if the deepest block of
    `C`'s chain that descends from the optional block `floor` and passes `test` is `B`, then
    `test B` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_deepest_clear_test : ∀ {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool} (h : (Model.specDraft (V := V)).deepest_clear floor C test = some B), test B = true := by
  simp only [eq_deepest_clear]
  exact (Model.vocabulary_facts_grades (V := V)).deepest_clear_test

/-- The field `ModelProperties_gradeView_T` of `GradesFacts` at `Model.specDraftBase`: the block
    tree of the grade view of `st` is the block tree of `st`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraftBase_ModelProperties_gradeView_T : ∀ (st : (Model.specDraftBase (V := V)).HS), ((Model.specDraftBase (V := V)).gradeView st).T = st.toFG.toSG.toGoldfishStore.T := by
  intro st
  exact (SpecDraftRecord.toProof_gs_T (st : Spec.Store V)).symm

/-- The field `ModelProperties_gradeView_T` of `GradesFacts` at `Model.specDraft`: the block tree of
    the grade view of `st` is the block tree of `st`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_ModelProperties_gradeView_T : ∀ (st : (Model.specDraft (V := V)).HS), ((Model.specDraft (V := V)).gradeView st).T = st.toFG.toSG.toGoldfishStore.T :=
  fun st => specDraftBase_ModelProperties_gradeView_T st.val

/-- The field `ModelProperties_phaseResult_g2` of `GradesFacts` at `Model.specDraft`: the result of
    the frame `f` for the grade-2 phase is `f`'s grade-2 result. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_ModelProperties_phaseResult_g2 : ∀ (f : (Model.specDraft (V := V)).Frame), (Model.specDraft (V := V)).phaseResult f .g2 = f.g2 := by
  intro f
  rfl

/-- The field `activePrefix_covers` of `GradesFacts` at `Model.specDraft`: if `P` is in `tree` and
    is an ancestor of `root` or `root` itself, then the active prefix of `root` in `tree` is some
    block `G`, and `P` is an ancestor of `G` or `G` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_activePrefix_covers : ∀ {tree : Finset (Block V)} {root P : Block V} (hPT : P ∈ tree) (hPr : Block.Preceq P root), ∃ G, (Model.specDraft (V := V)).activePrefix tree root = some G ∧ Block.Preceq P G := by
  simp only [eq_activePrefix]
  exact (Model.vocabulary_facts_grades (V := V)).activePrefix_covers

/-- The field `early_le_domain` of `GradesFacts` at `Model.specDraft`: for every round `q`, round
    `q`'s grade-2 early cutoff is at or before its grade-2 domain instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_le_domain : ∀ (S : Setup V) (q : Round), (Model.specDraft (V := V)).early S.E S.hc q .g2 ≤ (Model.specDraft (V := V)).domain S.E S.hc q .g2 := by
  simp only [eq_early, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).early_le_domain

/-- The field `NamedOutageClosure_opening_mono` of `GradesFacts` at `Model.specDraft`: if the round
    `q` is at or before the round `r`, round `q` opens at or before round `r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_NamedOutageClosure_opening_mono : ∀ (S : Setup V) {q r : Round} (h : q ≤ r), (Model.specDraft (V := V)).opening S.E S.hc q ≤ (Model.specDraft (V := V)).opening S.E S.hc r := by
  simp only [eq_opening]
  exact (Model.vocabulary_facts_grades (V := V)).NamedOutageClosure_opening_mono

/-- The field `q10_clip_preceq` of `GradesFacts` at `Model.specDraft`: the clip of `g` at `F` is an
    ancestor of `g` or `g` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_clip_preceq : ∀ (g F : Block V), Block.Preceq ((Model.specDraft (V := V)).clipGrade g F) g := by
  simp only [eq_clipGrade]
  exact (Model.vocabulary_facts_grades (V := V)).q10_clip_preceq

/-- The field `q10_domain_g2_lt_domain_g1` of `GradesFacts` at `Model.specDraft`: for every round
    `r`, round `r`'s grade-2 domain instant is strictly before its grade-1 domain instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_domain_g2_lt_domain_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).domain S.E S.hc r .g2 < (Model.specDraft (V := V)).domain S.E S.hc r .g1 := by
  simp only [eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).q10_domain_g2_lt_domain_g1

/-- The field `q10_early_g1_le_domain_g2` of `GradesFacts` at `Model.specDraft`: for every round
    `r`, round `r`'s grade-1 early cutoff is at or before its grade-2 domain instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_early_g1_le_domain_g2 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g1 ≤ (Model.specDraft (V := V)).domain S.E S.hc r .g2 := by
  simp only [eq_early, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).q10_early_g1_le_domain_g2

/-- The field `q10_early_g1_public` of `GradesFacts` at `Model.specDraft`: for a positive round `r`,
    round `r`'s grade-1 early cutoff is a whole number of delays `S.E.Δ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_early_g1_public : ∀ (S : Setup V) (r : Round) (hr : 0 < r), PublicTime S ((Model.specDraft (V := V)).early S.E S.hc r .g1) := by
  simp only [eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).q10_early_g1_public

/-- The field `q10_early_g2_le_early_g1` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    round `r`'s grade-2 early cutoff is at or before its grade-1 early cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_early_g2_le_early_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g2 ≤ (Model.specDraft (V := V)).early S.E S.hc r .g1 := by
  simp only [eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).q10_early_g2_le_early_g1

/-- The field `q10_early_le_late` of `GradesFacts` at `Model.specDraft`: for every round `r` and
    phase `p`, round `r`'s early cutoff of `p` is at or before its late cutoff of `p`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_early_le_late : ∀ (S : Setup V) (r : Round) (p : Phase), (Model.specDraft (V := V)).early S.E S.hc r p ≤ (Model.specDraft (V := V)).late S.E S.hc r p := by
  simp only [eq_early, eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).q10_early_le_late

/-- The field `q10_late_g1_le_domain_g2` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    round `r`'s grade-1 late cutoff is at or before its grade-2 domain instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_late_g1_le_domain_g2 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).late S.E S.hc r .g1 ≤ (Model.specDraft (V := V)).domain S.E S.hc r .g2 := by
  simp only [eq_late, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).q10_late_g1_le_domain_g2

/-- The field `q10_late_g1_public` of `GradesFacts` at `Model.specDraft`: for a positive round `r`,
    round `r`'s grade-1 late cutoff is a whole number of delays `S.E.Δ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_late_g1_public : ∀ (S : Setup V) (r : Round) (hr : 0 < r), PublicTime S ((Model.specDraft (V := V)).late S.E S.hc r .g1) := by
  simp only [eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).q10_late_g1_public

/-- The field `q10_retained_prefix` of `GradesFacts` at `Model.specDraft`: if `B` lies on one chain
    with `F`, then `B` is an ancestor of the clip of `g` at `F` or that block itself exactly when
    `B` is an ancestor of `g` or `g` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_retained_prefix : ∀ (g F B : Block V) (hBF : Block.compatible B F = true), Block.Preceq B ((Model.specDraft (V := V)).clipGrade g F) ↔ Block.Preceq B g := by
  simp only [eq_clipGrade]
  exact (Model.vocabulary_facts_grades (V := V)).q10_retained_prefix

/-- The field `domain_g2_le_domain_g1` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    round `r`'s grade-2 domain instant is at or before its grade-1 domain instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_g2_le_domain_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).domain S.E S.hc r .g2 ≤ (Model.specDraft (V := V)).domain S.E S.hc r .g1 := by
  simp only [eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_g2_le_domain_g1

/-- The field `early_g1_le_domain_g1` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    round `r`'s grade-1 early cutoff is at or before its grade-1 domain instant. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g1_le_domain_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g1 ≤ (Model.specDraft (V := V)).domain S.E S.hc r .g1 := by
  simp only [eq_early, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).early_g1_le_domain_g1

/-- The field `early_g1_le_late_g1` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    round `r`'s grade-1 early cutoff is at or before its grade-1 late cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g1_le_late_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g1 ≤ (Model.specDraft (V := V)).late S.E S.hc r .g1 := by
  simp only [eq_early, eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).early_g1_le_late_g1

/-- The field `early_g2_le_late_g2` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    round `r`'s grade-2 early cutoff is at or before its grade-2 late cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_le_late_g2 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g2 ≤ (Model.specDraft (V := V)).late S.E S.hc r .g2 := by
  simp only [eq_early, eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_le_late_g2

/-- The field `early_g2_public` of `GradesFacts` at `Model.specDraft`: for a positive round `s`,
    round `s`'s grade-2 early cutoff is a whole number of delays `S.E.Δ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_public : ∀ (S : Setup V) (s : Round) (hs : 0 < s), PublicTime S ((Model.specDraft (V := V)).early S.E S.hc s .g2) := by
  simp only [eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_public

/-- The field `activePrefix_mem` of `GradesFacts` at `Model.specDraft`: if the active prefix of
    `root` in `tree` is `B`, then `B` is in `tree`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_activePrefix_mem : ∀ (tree : Finset (Block V)) (root B : Block V) (h : (Model.specDraft (V := V)).activePrefix tree root = some B), B ∈ tree := by
  simp only [eq_activePrefix]
  exact (Model.vocabulary_facts_grades (V := V)).activePrefix_mem

/-- The field `lo_le_domain_of_window_start` of `GradesFacts` at `Model.specDraft`: for `0 < r` and
    `lo ≤ opening (r - η_SG)`, `lo ≤ domain r p` for every phase `p`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_lo_le_domain_of_window_start : ∀ (S : Setup V) {r : Round} (hr : 0 < r) {lo : Time} (hlo : lo ≤ (Model.specDraft (V := V)).opening S.E S.hc (r - S.hc.η_SG)) (p : Phase), lo ≤ (Model.specDraft (V := V)).domain S.E S.hc r p := by
  simp only [eq_opening, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).lo_le_domain_of_window_start

/-- The field `lo_le_early_g2_of_window_start` of `GradesFacts` at `Model.specDraft`: for `0 < r`
    and `lo ≤ opening (r - η_SG)`, `lo ≤ early r g2`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_lo_le_early_g2_of_window_start : ∀ (S : Setup V) {r : Round} (hr : 0 < r) {lo : Time} (hlo : lo ≤ (Model.specDraft (V := V)).opening S.E S.hc (r - S.hc.η_SG)), lo ≤ (Model.specDraft (V := V)).early S.E S.hc r .g2 := by
  simp only [eq_opening, eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).lo_le_early_g2_of_window_start

/-- The field `opening_add_le_of_lt` of `GradesFacts` at `Model.specDraft`: if `q < r`, then
    `opening q + 8 * Δ ≤ opening r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_add_le_of_lt : ∀ (S : Setup V) {q r : Round} (h : q < r), (Model.specDraft (V := V)).opening S.E S.hc q + 8 * S.E.Δ ≤ (Model.specDraft (V := V)).opening S.E S.hc r := by
  simp only [eq_opening]
  exact (Model.vocabulary_facts_grades (V := V)).opening_add_le_of_lt

/-- The field `activePrefix_preceq` of `GradesFacts` at `Model.specDraft`: the deepest active block
    on a root's own chain is an ancestor of that root. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_activePrefix_preceq : ∀ {tree : Finset (Block V)} {root B : Block V} (h : (Model.specDraft (V := V)).activePrefix tree root = some B), Block.preceq B root = true := by
  simp only [eq_activePrefix]
  exact (Model.vocabulary_facts_grades (V := V)).activePrefix_preceq

/-- The field `clipCache_round` of `GradesFacts` at `Model.specDraft`: clipping a cache to `F`
    leaves its round. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_clipCache_round : ∀ (F : Block V) (c : (Model.specDraft (V := V)).Cache), ((Model.specDraft (V := V)).clipCache F c).round = c.round := by
  intro F c
  rfl

/-- The field `clipResult_some_map_clipGrade` of `GradesFacts` at `Model.specDraft`: the clip at `F`
    of the completed phase result whose root is `o` clipped at `F` is that same completed result. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_clipResult_some_map_clipGrade : ∀ (F : Block V) (o : Option (Block V)), (Model.specDraft (V := V)).clipResult F (some (o.map (fun B => (Model.specDraft (V := V)).clipGrade B F)))
    = some (o.map (fun B => (Model.specDraft (V := V)).clipGrade B F)) := by
  simp only [eq_clipGrade, eq_clipResult]
  exact (Model.vocabulary_facts_grades (V := V)).clipResult_some_map_clipGrade

/-- The field `domain_g2_le_domain_l67` of `GradesFacts` at `Model.specDraft`:
    `domain q .g2 ≤ domain q p` for every phase `p`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_g2_le_domain_l67 : ∀ (S : Setup V) (q : Round) (p : Phase), (Model.specDraft (V := V)).domain S.E S.hc q .g2 ≤
    (Model.specDraft (V := V)).domain S.E S.hc q p := by
  simp only [eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_g2_le_domain_l67

/-- The field `domain_le_domain_g0` of `GradesFacts` at `Model.specDraft`:
    `domain r p ≤ domain r .g0` for every phase `p`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_le_domain_g0 : ∀ (S : Setup V) (r : Round) (p : Phase), (Model.specDraft (V := V)).domain S.E S.hc r p ≤ (Model.specDraft (V := V)).domain S.E S.hc r .g0 := by
  simp only [eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_le_domain_g0

/-- The field `early_add_two_delta_le_domain` of `GradesFacts` at `Model.specDraft`: for every round
    `r` and phase `p`, the early cutoff plus two delays is at or before the domain instant. The
    early offsets are `−3`, `−4`, `−5` and the domain offsets `1`, `0`, `−1`, in units of `Δ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_add_two_delta_le_domain : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase), (Model.specDraft (V := V)).early S.E S.hc r p + 2 * S.E.Δ ≤ (Model.specDraft (V := V)).domain S.E S.hc r p := by
  simp only [eq_early, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).early_add_two_delta_le_domain

/-- The field `early_g2_lt_domain` of `GradesFacts` at `Model.specDraft`: a round's G2 early cutoff
    comes strictly before the instant at which any of its phases is read. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_lt_domain : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase), (Model.specDraft (V := V)).early S.E S.hc r .g2 < (Model.specDraft (V := V)).domain S.E S.hc r p := by
  simp only [eq_early, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_lt_domain

/-- The field `exists_round_of_slot` of `GradesFacts` at `Model.specDraft`: for every slot `s` at or
    after round `r`'s third slot there is a `k` such that `s` is at or after round `(r + k)`'s third
    slot and at or before the slot after round `(r + k + 1)`'s opening slot. The slot is typed `Nat`
    (`Slot` is an `abbrev` for it) because `omega` does not read hypotheses stated at `Slot`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_round_of_slot : ∀ (hc : Protocol.HealConfig) (r : Round) {s : Nat} (hs : ((Model.specDraft (V := V)).opening_slot hc r) + 2 ≤ s), ∃ k : Nat, ((Model.specDraft (V := V)).opening_slot hc (r + k)) + 2 ≤ s ∧ s ≤ ((Model.specDraft (V := V)).opening_slot hc (r + k + 1)) + 1 := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).exists_round_of_slot

/-- The field `firstInterior_lt_nextOpening_l86e` of `GradesFacts` at `Model.specDraft`:
    `opening_slot r + 1 < opening_slot (r + 1)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_firstInterior_lt_nextOpening_l86e : ∀ (S : Setup V) (r : Round), ((Model.specDraft (V := V)).opening_slot S.hc r) + 1 < ((Model.specDraft (V := V)).opening_slot S.hc (r + 1)) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).firstInterior_lt_nextOpening_l86e

/-- The field `Sts_gradeView_T` of `GradesFacts` at `Model.specDraft`: the tree of the grade view
    read from a store's healing view is that store's tree. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_gradeView_T : ∀ (st : (Model.specDraft (V := V)).S), ((Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing st)).T = st.T := by
  intro st
  rfl

/-- The field `gradeView_sg_votes` of `GradesFacts` at `Model.specDraftBase`: the SG votes of round
    `r` in the grade view of a store's healing view are the SG votes `Protocol.sgVote` of the
    attestations `st.sg_pool r` of that store. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraftBase_gradeView_sg_votes : ∀ (st : (Model.specDraftBase (V := V)).S) (r : Round), ((Model.specDraftBase (V := V)).gradeView ((Model.specDraftBase (V := V)).toHealing st)).sg_votes r = (((Model.specDraftBase (V := V)).store_sg_pool st r)).image (Model.specDraftBase (V := V)).sgVote := by
  intro st r
  have h := (Model.vocabulary_facts_grades (V := V)).gradeView_sg_votes (Spec.Store.toProof st) r
  rw [eq_sgVote_base]
  show (Spec.Store.sg_votes st r).map Spec.Protocol.SGVote.toProofEmb =
    ((Spec.Store.sg_pool st r).image Spec.Attestation.toProof).image _
  rw [← SpecDraftRecord.toProof_gv_sg_votes, ← SpecDraftRecord.toProof_store_sg_pool]
  exact h

/-- The field `gradeView_sg_votes` of `GradesFacts` at `Model.specDraft`: the SG votes of round `r`
    in the grade view of a store's healing view are the SG votes `Protocol.sgVote` of the
    attestations `st.sg_pool r` of that store. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeView_sg_votes : ∀ (st : (Model.specDraft (V := V)).S) (r : Round), ((Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing st)).sg_votes r = (((Model.specDraft (V := V)).store_sg_pool st r)).image (Model.specDraft (V := V)).sgVote :=
  fun st r => specDraftBase_gradeView_sg_votes st.val r

/-- The field `gradeView_timestamp_sg_vote` of `GradesFacts` at `Model.specDraft`: the SG vote
    timestamp map of the grade view read from a store's healing view is that store's SG vote
    timestamp map. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeView_timestamp_sg_vote : ∀ (st : (Model.specDraft (V := V)).S), ((Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing st)).timestamp_sg_vote = st.timestamp_sg_vote := by
  intro st
  rfl

/-- The field `gradeView_tree` of `GradesFacts` at `Model.specDraft`: the filtered tree of the grade
    view read from the healing store `hs` is `Protocol.get_filtered_block_tree` of `hs`'s
    fork-choice view. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeView_tree : ∀ (hs : (Model.specDraft (V := V)).HS), ((Model.specDraft (V := V)).gradeView hs).tree = (Model.specDraft (V := V)).get_filtered_block_tree hs.toFG := by
  intro hs
  rfl

/-- The field `late_le_domain` of `GradesFacts` at `Model.specDraft`: `late r p ≤ domain r p`: the
    late offsets are `−3Δ`, `−2Δ`, `−Δ` and the domain offsets `Δ`, `0`, `−Δ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_late_le_domain : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase), (Model.specDraft (V := V)).late S.E S.hc r p ≤ (Model.specDraft (V := V)).domain S.E S.hc r p := by
  simp only [eq_late, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).late_le_domain

/-- The field `le_opening_round_of_sub_two` of `GradesFacts` at `Model.specDraft`:
    `sEnd ≤ opening_slot (round_of (sEnd − 2) + 1) + 1`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_le_opening_round_of_sub_two : ∀ (hc : Protocol.HealConfig) (sEnd : Nat), sEnd ≤ ((Model.specDraft (V := V)).opening_slot hc (((Model.specDraft (V := V)).round_of hc (sEnd - 2)) + 1)) + 1 := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).le_opening_round_of_sub_two

/-- The field `le_opening_slot_far` of `GradesFacts` at `Model.specDraft`:
    `s ≤ (r + 1 + s + 1) · R`, since `R ≥ 1`. The slot is typed `Nat` because `omega` does not read
    hypotheses stated at `Slot`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_le_opening_slot_far : ∀ (hc : Protocol.HealConfig) (r s : Nat), s ≤ ((Model.specDraft (V := V)).opening_slot hc (r + 1 + s + 1)) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).le_opening_slot_far

/-- The field `le_round_of_sub_two` of `GradesFacts` at `Model.specDraft`: if
    `opening_slot ρ + 2 ≤ sEnd`, then `ρ ≤ round_of (sEnd − 2)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_le_round_of_sub_two : ∀ (hc : Protocol.HealConfig) {ρ : Nat} {sEnd : Nat} (h : ((Model.specDraft (V := V)).opening_slot hc ρ) + 2 ≤ sEnd), ρ ≤ ((Model.specDraft (V := V)).round_of hc (sEnd - 2)) := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).le_round_of_sub_two

/-- The field `lt_opening_slot_round_of_succ` of `GradesFacts` at `Model.specDraft`: `s` is before
    the opening slot of the round after the round of `s`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_lt_opening_slot_round_of_succ : ∀ (hc : Protocol.HealConfig) (s : Slot), s < ((Model.specDraft (V := V)).opening_slot hc (((Model.specDraft (V := V)).round_of hc s) + 1)) := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).lt_opening_slot_round_of_succ

/-- The field `openingSlot_pos_l58` of `GradesFacts` at `Model.specDraft`: if `0 < q`, then
    `0 < opening_slot q`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_openingSlot_pos_l58 : ∀ (S : Setup V) {q : Round} (hq : 0 < q), 0 < ((Model.specDraft (V := V)).opening_slot S.hc q) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).openingSlot_pos_l58

/-- The field `openingSlot_pred_pos_l58` of `GradesFacts` at `Model.specDraft`: if `0 < q`, then
    `0 < opening_slot q − 1`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_openingSlot_pred_pos_l58 : ∀ (S : Setup V) {q : Round} (hq : 0 < q), 0 < ((Model.specDraft (V := V)).opening_slot S.hc q) - 1 := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).openingSlot_pred_pos_l58

/-- The field `openingSlots_l86f` of `GradesFacts` at `Model.specDraft`: if the progress deadline
    `D` satisfies `D + 2 ≤ m`, then with `start` the opening slot of `m` and `d = start − 1`:
    `opening_slot D + 1 ≤ d`, `opening_slot D + 2 ≤ start`, `opening_slot (m − 1) + 1 ≤ d`, `0 < d`,
    `d + 1 = start`, `m − 2 + 1 = m − 1`, `m − 1 + 1 = m`, `D ≤ m − 2` and `opening_slot D + 2 ≤ d`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_openingSlots_l86f : ∀ (S : Setup V) {D m : Round} (hm : D + 2 ≤ m), ((Model.specDraft (V := V)).opening_slot S.hc D) + 1 ≤ ((Model.specDraft (V := V)).opening_slot S.hc m) - 1 ∧
    ((Model.specDraft (V := V)).opening_slot S.hc D) + 2 ≤ ((Model.specDraft (V := V)).opening_slot S.hc m) ∧
    ((Model.specDraft (V := V)).opening_slot S.hc (m - 1)) + 1 ≤ ((Model.specDraft (V := V)).opening_slot S.hc m) - 1 ∧
    0 < ((Model.specDraft (V := V)).opening_slot S.hc m) - 1 ∧
    ((Model.specDraft (V := V)).opening_slot S.hc m) - 1 + 1 = ((Model.specDraft (V := V)).opening_slot S.hc m) ∧
    m - 2 + 1 = m - 1 ∧ m - 1 + 1 = m ∧ D ≤ m - 2 ∧
    ((Model.specDraft (V := V)).opening_slot S.hc D) + 2 ≤ ((Model.specDraft (V := V)).opening_slot S.hc m) - 1 := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).openingSlots_l86f

/-- The field `opening_eq_of_delta_eq` of `GradesFacts` at `Model.specDraft`: if the environments
    `E` and `E'` have the same delay `Δ`, then round `r` opens at the same instant in both. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_eq_of_delta_eq : ∀ {E E' : Env V} (h : E.Δ = E'.Δ) (hc : Protocol.HealConfig) (r : Round), (Model.specDraft (V := V)).opening E hc r = (Model.specDraft (V := V)).opening E' hc r := by
  simp only [eq_opening]
  exact (Model.vocabulary_facts_grades (V := V)).opening_eq_of_delta_eq

/-- The field `Sts_opening_mono` of `GradesFacts` at `Model.specDraft`: for `r ≤ r'`, round `r`
    opens at or before round `r'`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_opening_mono : ∀ (S : Setup V) {r r' : Round} (h : r ≤ r'), (Model.specDraft (V := V)).opening S.E S.hc r ≤ (Model.specDraft (V := V)).opening S.E S.hc r' := by
  simp only [eq_opening]
  exact (Model.vocabulary_facts_grades (V := V)).Sts_opening_mono

/-- The field `opening_slot_add` of `GradesFacts` at `Model.specDraft`: the opening slot of round
    `r + k` is the opening slot of round `r` plus `k` times the round length `R`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_add : ∀ (hc : Protocol.HealConfig) (r k : Round), ((Model.specDraft (V := V)).opening_slot hc (r + k)) = ((Model.specDraft (V := V)).opening_slot hc r) + k * hc.R := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_add

/-- The field `opening_slot_le_of_le` of `GradesFacts` at `Model.specDraft`: if round `r` is at most
    round `r'`, then round `r` opens no later than round `r'`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_le_of_le : ∀ (hc : Protocol.HealConfig) {r r' : Round} (h : r ≤ r'), ((Model.specDraft (V := V)).opening_slot hc r) ≤ ((Model.specDraft (V := V)).opening_slot hc r') := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_le_of_le

/-- The field `opening_slot_le_of_le_round_of` of `GradesFacts` at `Model.specDraft`: if round `r`
    is at or before the round of slot `s`, then the opening slot of `r` is at or before `s`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_le_of_le_round_of : ∀ (hc : Protocol.HealConfig) {r : Round} {s : Slot} (h : r ≤ ((Model.specDraft (V := V)).round_of hc s)), ((Model.specDraft (V := V)).opening_slot hc r) ≤ s := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_le_of_le_round_of

/-- The field `opening_slot_mono` of `GradesFacts` at `Model.specDraft`: a later round opens later. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_mono : ∀ (S : Setup V) {r r' : Round} (h : r ≤ r'), ((Model.specDraft (V := V)).opening_slot S.hc r) ≤ ((Model.specDraft (V := V)).opening_slot S.hc r') := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_mono

/-- The field `opening_slot_pos` of `GradesFacts` at `Model.specDraft`: every round after round `0`
    opens at a slot after slot `0`, because a round is at least three slots long. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_pos : ∀ (S : Setup V) {r : Round} (hr : 0 < r), 0 < ((Model.specDraft (V := V)).opening_slot S.hc r) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_pos

/-- The field `opening_slot_pos_of_round_pos` of `GradesFacts` at `Model.specDraft`: if the round
    `r` is positive, then the opening slot of round `r` is positive. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_pos_of_round_pos : ∀ (hc : Protocol.HealConfig) {r : Round} (h : 0 < r), 0 < ((Model.specDraft (V := V)).opening_slot hc r) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_pos_of_round_pos

/-- The field `opening_slot_round_of_le_slot` of `GradesFacts` at `Model.specDraft`: the opening
    slot of the round of `s` is at or before `s`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_round_of_le_slot : ∀ (hc : Protocol.HealConfig) (s : Slot), ((Model.specDraft (V := V)).opening_slot hc (((Model.specDraft (V := V)).round_of hc s))) ≤ s := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_round_of_le_slot

/-- The field `opening_slot_succ` of `GradesFacts` at `Model.specDraft`: round `r + 1` opens at the
    opening slot of round `r` plus `R`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_succ : ∀ (hc : Protocol.HealConfig) (r : Round), ((Model.specDraft (V := V)).opening_slot hc (r + 1)) = ((Model.specDraft (V := V)).opening_slot hc r) + hc.R := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_succ

/-- The field `opening_slot_succ_le_l78` of `GradesFacts` at `Model.specDraft`:
    `opening_slot a + 1 ≤ opening_slot (a + 1)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_succ_le_l78 : ∀ (S : Setup V) (a : Round), ((Model.specDraft (V := V)).opening_slot S.hc a) + 1 ≤ ((Model.specDraft (V := V)).opening_slot S.hc (a + 1)) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_succ_le_l78

/-- The field `opening_slot_succ_lt_l78` of `GradesFacts` at `Model.specDraft`:
    `opening_slot r + 1 < opening_slot (r + 1)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_succ_lt_l78 : ∀ (S : Setup V) (r : Round), ((Model.specDraft (V := V)).opening_slot S.hc r) + 1 < ((Model.specDraft (V := V)).opening_slot S.hc (r + 1)) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_succ_lt_l78

/-- The field `opening_slot_succ_lt_l88` of `GradesFacts` at `Model.specDraft`:
    `o_(c + 1) + 1 ≤ o_(c + 2)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_slot_succ_lt_l88 : ∀ (S : Setup V) (c : Round), ((Model.specDraft (V := V)).opening_slot S.hc (c + 1)) + 1 ≤ ((Model.specDraft (V := V)).opening_slot S.hc (c + 2)) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).opening_slot_succ_lt_l88

/-- The field `phaseResult_g0` of `GradesFacts` at `Model.specDraft`: a frame's phase result at the
    phase `g0` is its grade-0 field. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_g0 : ∀ (f : (Model.specDraft (V := V)).Frame), (Model.specDraft (V := V)).phaseResult f .g0 = f.g0 := by
  intro f
  rfl

/-- The field `phaseResult_g1` of `GradesFacts` at `Model.specDraft`: a frame's phase result at the
    phase `g1` is its grade-1 field. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_g1 : ∀ (f : (Model.specDraft (V := V)).Frame), (Model.specDraft (V := V)).phaseResult f .g1 = f.g1 := by
  intro f
  rfl

/-- The field `Sts_phaseResult_g2` of `GradesFacts` at `Model.specDraft`: a frame's phase result at
    the phase `g2` is its grade-2 field. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_phaseResult_g2 : ∀ (f : (Model.specDraft (V := V)).Frame), (Model.specDraft (V := V)).phaseResult f .g2 = f.g2 := by
  intro f
  rfl

/-- The field `plusTwo_slot_le_nextOpening_l53` of `GradesFacts` at `Model.specDraft`:
    `opening_slot q + 2 ≤ opening_slot (q + 1)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_plusTwo_slot_le_nextOpening_l53 : ∀ (S : Setup V) (q : Round), ((Model.specDraft (V := V)).opening_slot S.hc q) + 2 ≤ ((Model.specDraft (V := V)).opening_slot S.hc (q + 1)) := by
  simp only [eq_opening_slot]
  exact (Model.vocabulary_facts_grades (V := V)).plusTwo_slot_le_nextOpening_l53

/-- The field `preceq_clipGrade` of `GradesFacts` at `Model.specDraft`: if `X` is an ancestor of `g`
    or `g` itself, and `X` lies on one chain with `F`, then `X` is an ancestor of
    `Protocol.clipGrade g F` or that block itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_clipGrade : ∀ {X F : Block V} (hXF : Block.compatible X F = true), ∀ g : Block V, Block.Preceq X g → Block.Preceq X ((Model.specDraft (V := V)).clipGrade g F) := by
  simp only [eq_clipGrade]
  exact (Model.vocabulary_facts_grades (V := V)).preceq_clipGrade

/-- The field `preceq_deepest_clear` of `GradesFacts` at `Model.specDraft`: if `B` is an ancestor of
    `C` or `C` itself, `floor` is an ancestor of `B` or `B` itself, and `B` passes the test, then
    `deepest_clear` from the block `floor` to `C` with that test returns a block `D`, and `B` is an
    ancestor of `D` or `D` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_deepest_clear : ∀ {floor C B : Block V} {test : Block V → Bool} (hBC : Block.Preceq B C) (hfloor : Block.Preceq floor B) (htest : test B = true), ∃ D : Block V, (Model.specDraft (V := V)).deepest_clear (some floor) C test = some D ∧ Block.Preceq B D := by
  simp only [eq_deepest_clear]
  exact (Model.vocabulary_facts_grades (V := V)).preceq_deepest_clear

/-- The field `preceq_of_activePrefix_eq_some` of `GradesFacts` at `Model.specDraft`: if the active
    prefix of `root` in `tree` is `L`, then `L` is an ancestor of `root` or `root` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_of_activePrefix_eq_some : ∀ {tree : Finset (Block V)} {root L : Block V} (h : (Model.specDraft (V := V)).activePrefix tree root = some L), Block.Preceq L root := by
  simp only [eq_activePrefix]
  exact (Model.vocabulary_facts_grades (V := V)).preceq_of_activePrefix_eq_some

/-- The field `round_of_mono` of `GradesFacts` at `Model.specDraft`: if slot `s` is at or before
    slot `s'`, the round of `s` is at or before the round of `s'`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_mono : ∀ (hc : Protocol.HealConfig) {s s' : Slot} (h : s ≤ s'), ((Model.specDraft (V := V)).round_of hc s) ≤ ((Model.specDraft (V := V)).round_of hc s') := by
  simp only [eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_mono

/-- The field `round_of_mono_sts` of `GradesFacts` at `Model.specDraft`: a later slot belongs to a
    round at or after an earlier slot's round. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_mono_sts : ∀ (hc : Protocol.HealConfig) {s_0 s_1 : Slot} (h : s_0 ≤ s_1), ((Model.specDraft (V := V)).round_of hc s_0) ≤ ((Model.specDraft (V := V)).round_of hc s_1) := by
  simp only [eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_mono_sts

/-- The field `round_of_opening_slot_add` of `GradesFacts` at `Model.specDraft`: the slot `j` places
    after round `ρ`'s opening slot, with `j < R`, is in round `ρ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_opening_slot_add : ∀ (hc : Protocol.HealConfig) (ρ : Round) {j : Nat} (hj : j < hc.R), ((Model.specDraft (V := V)).round_of hc (((Model.specDraft (V := V)).opening_slot hc ρ) + j)) = ρ := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_opening_slot_add

/-- The field `round_of_sub_two_lt` of `GradesFacts` at `Model.specDraft`: if `0 < ρ` and
    `sEnd ≤ opening_slot ρ + 1`, then `round_of (sEnd − 2) < ρ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_sub_two_lt : ∀ (hc : Protocol.HealConfig) {ρ : Nat} {sEnd : Nat} (hρ : 0 < ρ) (h : sEnd ≤ ((Model.specDraft (V := V)).opening_slot hc ρ) + 1), ((Model.specDraft (V := V)).round_of hc (sEnd - 2)) < ρ := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_sub_two_lt

/-- The field `slot_round_bounds_l86e` of `GradesFacts` at `Model.specDraft`:
    `opening_slot (round_of s) ≤ s < opening_slot (round_of s + 1)`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_slot_round_bounds_l86e : ∀ (S : Setup V) (s : Slot), ((Model.specDraft (V := V)).opening_slot S.hc (((Model.specDraft (V := V)).round_of S.hc s))) ≤ s ∧
    s < ((Model.specDraft (V := V)).opening_slot S.hc (((Model.specDraft (V := V)).round_of S.hc s) + 1)) := by
  simp only [eq_opening_slot, eq_round_of]
  exact (Model.vocabulary_facts_grades (V := V)).slot_round_bounds_l86e

/-- The field `token_key` of `GradesFacts` at `Model.specDraft`: the key of the token of the
    attestation `y` is the root `y` names as confirmed. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_token_key : ∀ (y : Protocol.SGVote V), ((Model.specDraft (V := V)).token y).key = y.confirmed := by
  simp only [eq_token]
  exact (Model.vocabulary_facts_grades (V := V)).token_key

/-- The field `token_round` of `GradesFacts` at `Model.specDraft`: the round of the token of the
    attestation `y` is `y`'s round. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_token_round : ∀ (y : Protocol.SGVote V), ((Model.specDraft (V := V)).token y).round = y.round := by
  simp only [eq_token]
  exact (Model.vocabulary_facts_grades (V := V)).token_round

/-! ## The field of `GradesRunFacts` -/

/-- The field `phaseResult_initial_some` of `GradesRunFacts` at `Model.specDraft`: if the cache of
    `v`'s initial node state holds a result for round `r` and phase `p`, then `r` is `0`. -/
theorem _root_.SpecDraftRecord.GradesRunFacts.specDraft_phaseResult_initial_some :
    ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
      (x : Framework.StsMultisetLog.AtomicExec (Record.protocolOf (Model.specDraft (V := V)) S)
        Sched)
      (v : V) {r : Round} {p : Protocol.Phase} {o : Option (Block V)}
      (h : (Model.specDraft (V := V)).phaseResult
        ((Model.specDraft (V := V)).cacheAtRound (x[0][v].st).cache r) p = some o), r = 0 := by
  intro S Sched x v r p o h
  rw [Record.st_zero] at h
  change (Spec.Protocol.phaseResult
      (Spec.Protocol.saved_round_grades Spec.Protocol.initial_saved_grades r)
      (Spec.Protocol.Phase.toSpec p)).toProof =
    some o at h
  unfold Spec.Protocol.saved_round_grades at h
  split_ifs at h with h0 h1
  · exact h0
  · cases p <;> simp [Spec.Protocol.initial_saved_grades,
      Spec.Protocol.phaseResult, Spec.Protocol.pending_round_grades,
      Spec.Protocol.Phase.toSpec] at h
  · cases p <;> simp [Spec.Protocol.phaseResult,
      Spec.Protocol.pending_round_grades, Spec.Protocol.Phase.toSpec] at h

/-- The field `domain_le_action` of `GradesFacts` at `Model.specDraft`: the instant at which round
    `r`'s phase `p` freezes its grade is at or before round `r`'s action instant
    `Model.specDraft.a S.hc S.E.Δ r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_le_action : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    (Model.specDraft (V := V)).domain S.E S.hc r p ≤ (Model.specDraft (V := V)).a S.hc S.E.Δ r := by
  simp only [eq_a, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_le_action

/-- The field `healA_succ_round` of `GradesFacts` at `Model.specDraft`: the action instant of round
    `r + 1` is the action instant of round `r` plus the round length `4ΔR`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_healA_succ_round : ∀ (hc : Protocol.HealConfig) (Δ : Int) (r : Round),
    (Model.specDraft (V := V)).a hc Δ (r + 1) = (Model.specDraft (V := V)).a hc Δ r + 4 * Δ * (hc.R : Int) := by
  simp only [eq_a]
  exact (Model.vocabulary_facts_grades (V := V)).healA_succ_round

/-- The field `opening_add` of `GradesFacts` at `Model.specDraft`: the opening instant of round
    `r + k` is the opening instant of round `r` plus `k` times the round length `4ΔR`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_add : ∀ (E : Env V) (hc : Protocol.HealConfig) (r k : Round),
    (Model.specDraft (V := V)).opening E hc (r + k) = (Model.specDraft (V := V)).opening E hc r + (k : Int) * (4 * E.Δ * (hc.R : Int)) := by
  simp only [eq_opening]
  exact (Model.vocabulary_facts_grades (V := V)).opening_add

/-- The field `opening_eq_proposal_time` of `GradesFacts` at `Model.specDraft`: the opening instant
    of round `r` is the proposal instant of round `r`'s opening slot. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_eq_proposal_time : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round), (Model.specDraft (V := V)).opening E hc r = (Model.specDraft (V := V)).proposal_time E ((Model.specDraft (V := V)).opening_slot hc r) := by
  simp only [eq_opening_slot, eq_opening, eq_proposal_time]
  exact (Model.vocabulary_facts_grades (V := V)).opening_eq_proposal_time

/-- The field `early_g2_add_delta_le_early_g1` of `GradesFacts` at `Model.specDraft`: for every
    round `r`, `early r .g2 + Δ ≤ early r .g1`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g2_add_delta_le_early_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g2 + S.E.Δ ≤ (Model.specDraft (V := V)).early S.E S.hc r .g1 := by
  simp only [eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).early_g2_add_delta_le_early_g1

/-- The field `early_g1_add_delta_le_early_g0` of `GradesFacts` at `Model.specDraft`: for every
    round `r`, `early r .g1 + Δ ≤ early r .g0`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_early_g1_add_delta_le_early_g0 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).early S.E S.hc r .g1 + S.E.Δ ≤ (Model.specDraft (V := V)).early S.E S.hc r .g0 := by
  simp only [eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).early_g1_add_delta_le_early_g0

/-- The field `late_g1_add_delta_le_late_g2` of `GradesFacts` at `Model.specDraft`: for every round
    `r`, `late r .g1 + Δ ≤ late r .g2`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_late_g1_add_delta_le_late_g2 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).late S.E S.hc r .g1 + S.E.Δ ≤ (Model.specDraft (V := V)).late S.E S.hc r .g2 := by
  simp only [eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).late_g1_add_delta_le_late_g2

/-- The field `late_g0_add_delta_le_late_g1` of `GradesFacts` at `Model.specDraft`: for every round
    `r`, `late r .g0 + Δ ≤ late r .g1`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_late_g0_add_delta_le_late_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).late S.E S.hc r .g0 + S.E.Δ ≤ (Model.specDraft (V := V)).late S.E S.hc r .g1 := by
  simp only [eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).late_g0_add_delta_le_late_g1

/-- The field `opening_sub_five_delta_le_early_g2` of `GradesFacts` at `Model.specDraft`: for every
    round `r`, `opening r − 5Δ ≤ early r .g2`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opening_sub_five_delta_le_early_g2 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).opening S.E S.hc r - 5 * S.E.Δ ≤ (Model.specDraft (V := V)).early S.E S.hc r .g2 := by
  simp only [eq_opening, eq_early]
  exact (Model.vocabulary_facts_grades (V := V)).opening_sub_five_delta_le_early_g2

/-- The field `late_g1_add_delta_lt_opening` of `GradesFacts` at `Model.specDraft`: for every round
    `r`, `late r .g1 + Δ < opening r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_late_g1_add_delta_lt_opening : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).late S.E S.hc r .g1 + S.E.Δ < (Model.specDraft (V := V)).opening S.E S.hc r := by
  simp only [eq_opening, eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).late_g1_add_delta_lt_opening

/-- The field `opposes_of_raw` of `GradesFacts` at `Model.specDraft`: if `x` and `y` are raw tokens
    of one round, at least every early token's, with different keys, the tokens oppose `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposes_of_raw : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk} (x : DecoupledConsensusModel.Protocol.Token Key), x ∈ raw → ∀ (y : DecoupledConsensusModel.Protocol.Token Key), y ∈ raw → (∀ u ∈ early, u.round ≤ x.round) → x.round = y.round → x.key ≠ y.key → (Model.specDraft (V := V)).Opposes covers early late raw B := by
  exact (Model.vocabulary_facts_grades (V := V)).opposes_of_raw

/-- The field `round_of_slotOf_domain` of `GradesFacts` at `Model.specDraft`: for a positive round
    `r` and every phase `p`, `r` is the round of the slot of `Model.specDraft.domain S.E S.hc r p`,
    or that round plus one. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_round_of_slotOf_domain : ∀ (S : Setup V) {r : Round} (hr : 0 < r) (p : Protocol.Phase),
    r = (Model.specDraft (V := V)).round_of S.hc (S.E.slotOf ((Model.specDraft (V := V)).domain S.E S.hc r p)) ∨
    r = (Model.specDraft (V := V)).round_of S.hc (S.E.slotOf ((Model.specDraft (V := V)).domain S.E S.hc r p)) + 1 := by
  simp only [eq_round_of, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).round_of_slotOf_domain

/-- The field `publicTime_domain` of `GradesFacts` at `Model.specDraft`: for a positive round `r`
    and every phase `p`, `Model.specDraft.domain S.E S.hc r p` is a public instant of `S` (a natural
    multiple of the delay `S.E.Δ`). -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_publicTime_domain : ∀ (S : Setup V) {r : Round} (hr : 0 < r) (p : Protocol.Phase),
    PublicTime S ((Model.specDraft (V := V)).domain S.E S.hc r p) := by
  simp only [eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).publicTime_domain

/-- The field `late_g0_public` of `GradesFacts` at `Model.specDraft`: for every positive round `s`,
    the late G0 cutoff of `s` is a whole number of `S.E.Δ`s. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_late_g0_public : ∀ (S : Setup V) (s : Round) (hs : 0 < s), PublicTime S ((Model.specDraft (V := V)).late S.E S.hc s .g0) := by
  simp only [eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).late_g0_public

/-- The field `q10_domain_g2_le_late_g2` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    the domain instant of `r`'s G2 phase is at or before `r`'s late G2 cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_domain_g2_le_late_g2 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).domain S.E S.hc r .g2 ≤ (Model.specDraft (V := V)).late S.E S.hc r .g2 := by
  simp only [eq_late, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).q10_domain_g2_le_late_g2

/-- The field `action_add_three_delta_le_late_succ` of `GradesFacts` at `Model.specDraft`: for every
    round `r` and phase `p`, round `r`'s action instant plus three delays is at or before the late
    cutoff of phase `p` of round `r + 1`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_action_add_three_delta_le_late_succ : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    (Model.specDraft (V := V)).a S.hc S.E.Δ r + 3 * S.E.Δ ≤ (Model.specDraft (V := V)).late S.E S.hc (r + 1) p := by
  simp only [eq_a, eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).action_add_three_delta_le_late_succ

/-- The field `domain_g2_add_delta_le_domain_g1` of `GradesFacts` at `Model.specDraft`: for every
    round `r`, `domain r .g2 + Δ ≤ domain r .g1`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_g2_add_delta_le_domain_g1 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).domain S.E S.hc r .g2 + S.E.Δ ≤ (Model.specDraft (V := V)).domain S.E S.hc r .g1 := by
  simp only [eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_g2_add_delta_le_domain_g1

/-- The field `domain_g1_add_delta_le_domain_g0` of `GradesFacts` at `Model.specDraft`: for every
    round `r`, `domain r .g1 + Δ ≤ domain r .g0`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_g1_add_delta_le_domain_g0 : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).domain S.E S.hc r .g1 + S.E.Δ ≤ (Model.specDraft (V := V)).domain S.E S.hc r .g0 := by
  simp only [eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_g1_add_delta_le_domain_g0

/-- The field `Sts_domain_g1_eq_opening` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    `domain r .g1 = opening r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_domain_g1_eq_opening : ∀ (S : Setup V) (r : Round), (Model.specDraft (V := V)).domain S.E S.hc r .g1 = (Model.specDraft (V := V)).opening S.E S.hc r := by
  simp only [eq_opening, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).Sts_domain_g1_eq_opening

/-- The field `domain_g0_eq_opening` of `GradesFacts` at `Model.specDraft`: for every round `r`,
    `domain r .g0 = opening r + Δ`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_domain_g0_eq_opening : ∀ (S : Setup V) (r : Round),
    (Model.specDraft (V := V)).domain S.E S.hc r .g0 = (Model.specDraft (V := V)).opening S.E S.hc r + S.E.Δ := by
  simp only [eq_opening, eq_domain]
  exact (Model.vocabulary_facts_grades (V := V)).domain_g0_eq_opening

/-- The field `allPhasesCutoff_eq_early_g0` of `GradesFacts` at `Model.specDraft`: for every round
    `q`, the late grade-0 cutoff of `q` is its early grade-0 cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_allPhasesCutoff_eq_early_g0 : ∀ (S : Setup V) (q : Round),
    (Model.specDraft (V := V)).late S.E S.hc q .g0 = (Model.specDraft (V := V)).early S.E S.hc q .g0 := by
  simp only [eq_early, eq_late]
  exact (Model.vocabulary_facts_grades (V := V)).allPhasesCutoff_eq_early_g0

/-- The field `clear_of_g0_ne` of `GradesFacts` at `Model.specDraft`: if the grade-0 entry of the
    frame `frame` is no completed root, every block `B` clears `frame`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_clear_of_g0_ne : ∀ {frame : (Model.specDraft (V := V)).Frame}, (∀ root : DecoupledConsensusModel.Block V, frame.g0 ≠ Option.some (Option.some root)) → ∀ (B : DecoupledConsensusModel.Block V), (Model.specDraft (V := V)).clear frame B = Bool.true := by
  intro (fr : Spec.RoundGrades V) h B
  exact (Model.vocabulary_facts_grades (V := V)).clear_of_g0_ne (frame := fr.toProof) h B

/-- `clipResultImage F g` is pending exactly when `g` is. -/
theorem _root_.SpecDraftRecord.GradesFacts.clipResultImage_eq_pending
    (F : Block V) (g : Spec.GradeResult V) :
    SpecDraftRecord.clipResultImage F g = .pending ↔ g = .pending := by
  rcases g with _ | _ | G
  · simp [SpecDraftRecord.clipResultImage, Id.run]; rfl
  · simp [SpecDraftRecord.clipResultImage, Id.run, Spec.GradeResult.block]
  · simp [SpecDraftRecord.clipResultImage, Id.run, Spec.GradeResult.block,
      Option.value]

/-- The field `phaseResult_clipCache_ne_none` of `GradesFacts` at `Model.specDraft`: if the cache
    `c` holds a result for round `r` and phase `p`, so does `c` clipped to `F`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_clipCache_ne_none : ∀ (F : Block V) (c : (Model.specDraft (V := V)).Cache) (r : Round) (p : Protocol.Phase),
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p ≠ none →
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).clipCache F c) r) p ≠ none := by
  intro F c r p h
  change (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades c r)
    (Spec.Protocol.Phase.toSpec p)).toProof ≠ none at h
  show (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    (SpecDraftRecord.Member.clipCache F c) r)
    (Spec.Protocol.Phase.toSpec p)).toProof ≠ none
  rw [Ne, Spec.GradeResult.toProof_eq_none] at h ⊢
  have hm := SpecDraftRecord.GradesFacts.clipResultImage_eq_pending F
  unfold Spec.Protocol.saved_round_grades at h ⊢
  simp only [SpecDraftRecord.Member.clipCache] at ⊢
  split_ifs at h ⊢ <;>
    cases p <;>
    simp_all [Spec.Protocol.phaseResult, SpecDraftRecord.Member.clipFrame,
      Spec.Protocol.Phase.toSpec]

section GradesTransports

set_option linter.unusedSimpArgs false

open SpecDraftRecord.GradesImages

/-! ## Grade views and their images under `toProof` -/

/-- The blocks of the grade view `gv` are the blocks of the grade view of its image
    `gv.val.toProof`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_gv_T (gv : (Model.specDraft (V := V)).GV) :
    gv.T = Model.GV.T (M := Model.vocabulary (V := V)) gv.val.toProof.toHealing.gradeView := by
  show SpecDraftRecord.Member.gv_T gv.val = gv.val.toProof.toHealing.gradeView.T
  exact (SpecDraftRecord.toProof_gv_T gv.val).symm

/-- The block stamps of the grade view `gv` are those of the grade view of its image
    `gv.val.toProof`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_gv_timestamp_block
    (gv : (Model.specDraft (V := V)).GV) :
    gv.timestamp_block =
      Model.GV.timestamp_block (M := Model.vocabulary (V := V))
        gv.val.toProof.toHealing.gradeView := by
  funext B
  exact (SpecDraftRecord.GradesImages.toProof_gv_timestamp_block gv.val B).symm

/-- The SG votes of the grade view `gv` are those of the grade view of its image `gv.val.toProof`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_gv_sg_votes (gv : (Model.specDraft (V := V)).GV) :
    gv.sg_votes =
      Model.GV.sg_votes (M := Model.vocabulary (V := V)) gv.val.toProof.toHealing.gradeView := by
  funext r
  exact (SpecDraftRecord.toProof_gv_sg_votes gv.val r).symm

/-- The SG vote stamps of the grade view `gv` are those of the grade view of its image
    `gv.val.toProof`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_gv_timestamp_sg_vote
    (gv : (Model.specDraft (V := V)).GV) :
    gv.timestamp_sg_vote =
      Model.GV.timestamp_sg_vote (M := Model.vocabulary (V := V))
        gv.val.toProof.toHealing.gradeView := by
  funext u
  exact (SpecDraftRecord.toProof_gv_timestamp_sg_vote gv.val u).symm

/-- `Model.specDraft`'s `latest_window` equals `Model.vocabulary`'s. -/
theorem _root_.SpecDraftRecord.GradesFacts.eq_latest_window :
    (Model.specDraft (V := V)).latest_window = (Model.vocabulary (V := V)).latest_window := by
  funext η r
  exact (SpecDraftRecord.toProof_latest_window η r).symm

/-- `Model.specDraft`'s `Supports` is the support test on tokens it is defined as. -/
theorem _root_.SpecDraftRecord.GradesFacts.eq_Supports {Key Target : Type}
    (covers : Key → Target → Prop)
    (early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)) (B : Target) :
    (Model.specDraft (V := V)).Supports covers early late raw B ↔
      (Model.vocabulary (V := V)).Supports covers early late raw B :=
  Iff.rfl

/-- `Model.specDraft`'s `Opposes` is the opposition test on tokens it is defined as. -/
theorem _root_.SpecDraftRecord.GradesFacts.eq_Opposes {Key Target : Type}
    (covers : Key → Target → Prop)
    (early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)) (B : Target) :
    (Model.specDraft (V := V)).Opposes covers early late raw B ↔
      (Model.vocabulary (V := V)).Opposes covers early late raw B :=
  Iff.rfl

/-- `Model.specDraft`'s `head_covers` equals `Model.vocabulary`'s on every tree `T`, block `B` and key
    `H`. -/
theorem _root_.SpecDraftRecord.GradesFacts.eq_head_covers
    (T : Finset (DecoupledConsensusModel.Block V)) (B : DecoupledConsensusModel.Block V)
    (H : Option DecoupledConsensusModel.BlockId) :
    (Model.specDraft (V := V)).head_covers T B H = (Model.vocabulary (V := V)).head_covers T B H := by
  show SpecDraftRecord.successOutcomes (SpecDraftRecord.orVocabulary
    (Spec.Protocol.head_covers (T.map SpecDraftRecord.ForkChoiceGrades.blockToSpecEmb)
      (Spec.Block.toSpec B) (H.map Spec.BlockId.toSpec))
    (DecoupledConsensusModel.Protocol.head_covers T B H)) =
      pure (DecoupledConsensusModel.Protocol.head_covers T B H)
  cases h : Spec.Protocol.head_covers
      (T.map SpecDraftRecord.ForkChoiceGrades.blockToSpecEmb) (Spec.Block.toSpec B)
      (H.map Spec.BlockId.toSpec) with
  | error e => rfl
  | ok b =>
    suffices hb : b = DecoupledConsensusModel.Protocol.head_covers T B H by
      subst hb; rfl
    cases H with
    | none =>
      have h' : (Except.ok false : DC.DRE Bool) = .ok b := h
      cases h'
      simp [DecoupledConsensusModel.Protocol.head_covers]
    | some x =>
      simp only [Spec.Protocol.head_covers, Option.map_some, ne_eq, reduceCtorEq,
        not_false_eq_true, dite_true, Option.value, Option.get_some] at h
      rw [SpecDraftRecord.ForkChoiceImages.find?_map T _ (fun _ => rfl) x] at h
      cases hf : DecoupledConsensusModel.Block.find? T x with
      | none =>
        rw [hf] at h
        cases h
      | some X =>
        rw [hf] at h
        have h' : (Except.ok ((Spec.Block.toSpec B).ancestorEq
            (Spec.Block.toSpec X)) : DC.DRE Bool) = .ok b := h
        cases h'
        simp only [DecoupledConsensusModel.Protocol.head_covers, hf]
        exact Spec.Block.toSpec_ancestorEq B X

/-- `sd_rw` rewrites the grade members of `Model.specDraft` at a store, and the readers of its grade
    view, into their values at the store's image under `toProof`; `sd_rw at *` also rewrites every
    hypothesis. -/
local syntax "sd_rw" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| sd_rw $[$loc]?) =>
    `(tactic| simp only [specDraft_rawInputs_eq, specDraft_bodyReady_eq,
        specDraft_interpretedInputs_eq, specDraft_rawView_eq, specDraft_readyView_eq,
        specDraft_localCovers_eq, specDraft_positive_eq, specDraft_opposing_eq,
        specDraft_gradeBool_eq, specDraft_freezeRoot_eq, sd_gv_T, sd_gv_timestamp_block,
        sd_gv_sg_votes, sd_gv_timestamp_sg_vote, eq_token, eq_early, eq_late, eq_opening,
        eq_domain, eq_round_of, eq_latest_window, eq_Supports, eq_Opposes, eq_head_covers] $[$loc]?)

/-! ### The anchor of a store, read at its own filtered tree -/

omit [Fintype V] [Inhabited V] in
/-- The fork-choice root of a store is an ancestor of, or equal to, every block of its filtered
    tree. -/
theorem _root_.SpecDraftRecord.GradesFacts.draft_fg_root_ancestorEq_of_mem_filtered
    {st : Spec.Store V} {B : Spec.Block V}
    (h : B ∈ Spec.Protocol.get_filtered_block_tree st) :
    (Spec.Protocol.get_fg_root st).ancestorEq B = true := by
  simp only [Spec.Protocol.get_filtered_block_tree,
    Spec.Protocol.get_filtered_block_tree_from, Id.run, pure, Finset.mem_filter] at h
  exact h.2

/-- The fork-choice root of a store `st` of `Model.specDraft` is an ancestor of, or equal to, every
    block of its filtered tree. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_fg_root_preceq_of_mem_filtered
    {st : (Model.specDraft (V := V)).FGS} {B : DecoupledConsensusModel.Block V}
    (h : B ∈ (Model.specDraft (V := V)).get_filtered_block_tree st) :
    DecoupledConsensusModel.Block.Preceq ((Model.specDraft (V := V)).get_fg_root st) B := by
  change B ∈ (Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st.val)).image
    Spec.Block.toProof at h
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp h
  exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
    (Spec.Block.toProof_preceq_of_ancestorEq _ _
      (draft_fg_root_ancestorEq_of_mem_filtered hX))

/-- On a store `st` of `Model.specDraft`, the SG root at the block standing for `R`, mapped by
    `toProof`, is the deepest block of the filtered tree that is an ancestor of `R`, or the
    fork-choice root when there is none. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_get_sg_root_some (st : (Model.specDraft (V := V)).HS)
    (R : DecoupledConsensusModel.Block V) :
    (Spec.Protocol.get_sg_root (Spec.Store.ofImage st.val) (some (st.val.blockOfImage R))).toProof =
      (DecoupledConsensusModel.Protocol.activePrefix
        ((Model.specDraft (V := V)).get_filtered_block_tree st) R).getD
        ((Model.specDraft (V := V)).get_fg_root st) := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  have hA := Spec.Protocol.activePrefix_blockOfImage (Spec.Store.ofImage st.val) hT.injOn_toProof hpar
    (SpecDraftRecord.GradesImages.filtered_subset (Spec.Store.ofImage st.val)) R
  rw [Spec.Store.blockOfImage_ofImage] at hA
  show _ = (DecoupledConsensusModel.Protocol.activePrefix
    (SpecDraftRecord.Member.get_filtered_block_tree st.val) R).getD
      (SpecDraftRecord.Member.get_fg_root st.val)
  unfold SpecDraftRecord.Member.get_filtered_block_tree SpecDraftRecord.Member.get_fg_root
  rw [← hA]
  simp only [Spec.Protocol.get_sg_root, Spec.Protocol.active_prefix, Id.run,
    ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
  split
  · next h =>
    have h' : Spec.Protocol.activePrefix
        (Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st.val)) (st.val.blockOfImage R) =
          none := h
    rw [h']
    rfl
  · next h =>
    have h' : Spec.Protocol.activePrefix
        (Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st.val)) (st.val.blockOfImage R) ≠
          none := h
    obtain ⟨A, hA'⟩ := Option.ne_none_iff_exists'.mp h'
    simp only [hA', Option.map_some, Option.getD_some]
    rfl

/-- `Model.specDraft`'s anchor at a store `st` and a grade-1 result with the block `R` is the
    deepest block of the filtered tree that is an ancestor of `R`, or the fork-choice root when
    there is none. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_anchor_some (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS)
    (r : Round) (R : DecoupledConsensusModel.Block V) :
    (Model.specDraft (V := V)).anchor E hc st r (some (some R)) =
      pure ((DecoupledConsensusModel.Protocol.activePrefix
        ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) R).getD
        ((Model.specDraft (V := V)).get_fg_root st.toFG)) := by
  have h := sd_get_sg_root_some st R
  show SpecDraftRecord.successOutcomes (Except.ok (Spec.Protocol.get_sg_root
    (Spec.Store.ofImage st.val) (some (st.val.blockOfImage R))).toProof) = _
  rw [h]
  rfl

/-- `Model.specDraft`'s anchor at a store `st` and a grade-1 result with no block, pending or
    computed empty, is the fork-choice root. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_anchor_of_ne (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS)
    (r : Round) (g1 : Option (Option (DecoupledConsensusModel.Block V)))
    (h : ∀ R, g1 ≠ some (some R)) :
    (Model.specDraft (V := V)).anchor E hc st r g1 =
      pure ((Model.specDraft (V := V)).get_fg_root st.toFG) := by
  rcases g1 with _ | _ | R
  · rfl
  · rfl
  · exact absurd rfl (h R)


/-! ### The grade-2 candidate of a store -/

omit [Fintype V] [Inhabited V] in
/-- If `active_prefix st g` is `some X`, then `g` names a block `G`, `X` is in the filtered tree of
    `st`, and `X` is an ancestor of `G` or `G` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.draft_active_prefix_some {st : Spec.Store V}
    {g : Option (Spec.Block V)} {X : Spec.Block V}
    (h : Spec.Protocol.active_prefix st g = some X) :
    ∃ G, g = some G ∧ X ∈ Spec.Protocol.get_filtered_block_tree st ∧
      X.ancestorEq G = true := by
  cases g with
  | none => cases h
  | some G =>
    refine ⟨G, rfl, ?_⟩
    simp only [Spec.Protocol.active_prefix, Id.run, pure, ne_eq, reduceCtorEq,
      not_false_eq_true, dite_true, Option.value, Option.get_some] at h
    simp only [Spec.Protocol.activePrefix, Spec.Block.deepest?] at h
    unfold Spec.pickUnique? at h
    split at h
    · rename_i hex
      rw [← Option.some.inj h]
      exact Finset.mem_filter.mp (Finset.choose_mem _ _ hex)
    · cases h

/-- An outcome `some Q` of `Model.specDraft`'s grade-2 candidate of the round grades `fr` at a store
    `st` is a block of the filtered tree that is an ancestor of the grade-2 block of `fr`, or that
    block itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_grade2Block_some {st : (Model.specDraft (V := V)).HS}
    {fr : Spec.RoundGrades V} {o : Option (DecoupledConsensusModel.Block V)}
    (ho : (Model.specDraft (V := V)).grade2Block st fr ⇢ o) {Q : DecoupledConsensusModel.Block V}
    (hQ : o = some Q) :
    ∃ R, Model.Frame.g2 (M := Model.specDraft (V := V)) fr = some (some R) ∧
      Q ∈ (Model.specDraft (V := V)).get_filtered_block_tree st.toFG ∧
      DecoupledConsensusModel.Block.Preceq Q R := by
  have hfill : ∀ g : Spec.GradeResult V, ∃ G, SpecDraftRecord.fillResult g = .computed G ∧
      (∀ X, G = some X → g = .computed (some X)) := by
    rintro (_ | G)
    · exact ⟨none, rfl, fun _ h => nomatch h⟩
    · exact ⟨G, rfl, fun _ h => h ▸ rfl⟩
  obtain ⟨G0, h0, -⟩ := hfill (st.val.roundGradesOfImage fr).g0
  obtain ⟨G1, h1, -⟩ := hfill (st.val.roundGradesOfImage fr).g1
  obtain ⟨G2, h2, h2'⟩ := hfill (st.val.roundGradesOfImage fr).g2
  have hfr : SpecDraftRecord.fillRound (st.val.roundGradesOfImage fr) =
      ⟨.computed G0, .computed G1, .computed G2⟩ := by
    simp only [SpecDraftRecord.fillRound, h0, h1, h2]
  have ho' : Except.map (Option.map Spec.Block.toProof)
      (Spec.Protocol.grade2Block (Spec.Store.ofImage st.val)
        (SpecDraftRecord.fillRound (st.val.roundGradesOfImage fr))) = .ok o :=
    (SpecDraftRecord.returns_successOutcomes _ _).mp ho
  rw [hfr] at ho'
  change Except.ok ((Spec.Protocol.active_prefix (Spec.Store.ofImage st.val) G2).map
    Spec.Block.toProof) = Except.ok o at ho'
  have ho'' := Except.ok.inj ho'
  subst hQ
  cases hY : Spec.Protocol.active_prefix (Spec.Store.ofImage st.val) G2 with
  | none =>
    rw [hY] at ho''
    cases ho''
  | some Y =>
    rw [hY] at ho''
    obtain ⟨X, rfl, hYm, hYX⟩ := draft_active_prefix_some hY
    refine ⟨X.toProof, ?_, ?_, ?_⟩
    · show fr.g2.toProof = _
      have hX : st.val.resultOfImage fr.g2 = .computed (some X) := h2' X rfl
      rcases hr : fr.g2 with _ | _ | Z <;> rw [hr] at hX <;>
        simp [Spec.Store.resultOfImage] at hX
      rw [← hX]
      simp
    · rw [← Option.some.inj ho'']
      exact Finset.mem_image_of_mem _ hYm
    · rw [← Option.some.inj ho'']
      exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
        (Spec.Block.toProof_preceq_of_ancestorEq _ _ hYX)


/-! ### The SG vote of a store -/

/-- The confirmed block of a store `st` of `Model.specDraft` is `st.val.live_confirmed.toProof`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_live_confirmed (st : (Model.specDraft (V := V)).HS) :
    st.toFG.toSG.toGoldfishStore.live_confirmed = st.val.live_confirmed.toProof := by
  show SpecDraftRecord.Member.gs_live_confirmed st.val = _
  unfold SpecDraftRecord.Member.gs_live_confirmed
  exact SpecDraftRecord.toProof_gs_live_confirmed st.val

omit [Fintype V] [Inhabited V] in
/-- `Block.deepest? T = some D` puts `D` in `T`. -/
theorem _root_.SpecDraftRecord.GradesFacts.draft_deepest?_mem {T : Finset (Spec.Block V)}
    {D : Spec.Block V} (h : Spec.Block.deepest? T = some D) : D ∈ T := by
  unfold Spec.Block.deepest? Spec.pickUnique? at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact Finset.choose_mem _ _ hex
  · cases h

/-- On a store `st` of `Model.specDraft`, when the clearing walk of `Model.specDraft` from the
    anchor of `g` finds no block, the spec's walk from the block standing for that anchor finds none
    either. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_deepest_clear_none (st : (Model.specDraft (V := V)).HS)
    (g : DecoupledConsensusModel.Protocol.GradeRead V)
    (h : (Model.specDraft (V := V)).deepest_clear (some g.anchor)
      st.toFG.toSG.toGoldfishStore.live_confirmed g.clear = none) :
    Spec.Protocol.deepest_clear (st.val.blockOfImage g.anchor)
      (Spec.Store.ofImage st.val).live_confirmed (fun B => g.clear B.toProof) = none := by
  have hlc : (Spec.Store.ofImage st.val).live_confirmed.toProof = st.val.live_confirmed.toProof := by
    rw [Spec.Store.ofImage_live_confirmed, Spec.Store.toProof_blockOfImage]
  rw [eq_deepest_clear, sd_live_confirmed, ← hlc] at h
  change DecoupledConsensusModel.Protocol.deepest_clear (some g.anchor)
    (Spec.Store.ofImage st.val).live_confirmed.toProof g.clear = none at h
  cases hD : Spec.Protocol.deepest_clear (st.val.blockOfImage g.anchor)
      (Spec.Store.ofImage st.val).live_confirmed (fun B => g.clear B.toProof) with
  | none => rfl
  | some D =>
    exfalso
    unfold Spec.Protocol.deepest_clear at hD
    have hm := Finset.mem_filter.mp (draft_deepest?_mem hD)
    rw [Bool.and_eq_true] at hm
    obtain ⟨hc, ha, ht⟩ := And.intro hm.1 hm.2
    have hmem : D.toProof ∈ (DecoupledConsensusModel.Protocol.chain_of
        (Spec.Store.ofImage st.val).live_confirmed.toProof).toFinset.filter (fun B =>
          (some g.anchor).elim true (fun anchor => DecoupledConsensusModel.Block.preceq anchor B) =
            true ∧ g.clear B = true) := by
      refine Finset.mem_filter.mpr ⟨?_, ?_, ht⟩
      · rw [SpecDraftRecord.toProof_chain_of, List.mem_toFinset]
        exact List.mem_map_of_mem (List.mem_toFinset.mp hc)
      · have := Spec.Block.toProof_preceq_of_ancestorEq _ _ ha
        rwa [Spec.Store.toProof_blockOfImage] at this
    have hs := DecoupledConsensusModel.Proofs.HealingSurface.deepest?_isSome_of_chain
      (C := (Spec.Store.ofImage st.val).live_confirmed.toProof)
      (fun X hX => DecoupledConsensusModel.Proofs.Engine.mem_chain_of_preceq
        (List.mem_toFinset.mp (Finset.mem_filter.mp hX).1)) ⟨_, hmem⟩
    unfold DecoupledConsensusModel.Protocol.deepest_clear at h
    rw [h] at hs
    exact Bool.false_ne_true hs

/-- `Model.specDraft`'s SG vote at a store `st` and a grade read `g`, when the spec's clearing walk
    finds a block `D`: the image of `D`, an ancestor of the confirmed block of `st` and a descendant
    of the anchor of `g`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_currentSGVote_some (st : (Model.specDraft (V := V)).HS)
    (g : DecoupledConsensusModel.Protocol.GradeRead V) {D : Spec.Block V}
    (hD : Spec.Protocol.deepest_clear (st.val.blockOfImage g.anchor)
      (Spec.Store.ofImage st.val).live_confirmed (fun B => g.clear B.toProof) = some D) :
    (Model.specDraft (V := V)).currentSGVote st g = D.toProof ∧
      DecoupledConsensusModel.Block.Preceq D.toProof st.toFG.toSG.toGoldfishStore.live_confirmed ∧
      DecoupledConsensusModel.Block.Preceq g.anchor D.toProof := by
  have hm := Finset.mem_filter.mp (draft_deepest?_mem hD)
  rw [Bool.and_eq_true] at hm
  refine ⟨?_, ?_, ?_⟩
  · show (Spec.Protocol.currentSGVote (Spec.Store.ofImage st.val)
      (SpecDraftRecord.ForkChoiceGrades.gradeReadOfImage st.val g)).toProof = _
    simp only [Spec.Protocol.currentSGVote, Id.run,
      SpecDraftRecord.ForkChoiceGrades.gradeReadOfImage]
    have hv : ∀ (o : Option (Spec.Block V)) (ho : o ≠ none), o = some D →
        o.value ho = D := by
      rintro _ _ rfl
      rfl
    rw [dif_pos (by rw [hD]; exact Option.some_ne_none D)]
    exact congrArg Spec.Block.toProof (hv _ _ hD)
  · rw [sd_live_confirmed]
    have hc := List.mem_toFinset.mp hm.1
    have := DecoupledConsensusModel.Proofs.Engine.mem_chain_of_preceq
      (C := (Spec.Store.ofImage st.val).live_confirmed.toProof)
      (by rw [SpecDraftRecord.toProof_chain_of]; exact List.mem_map_of_mem hc)
    rw [Spec.Store.ofImage_live_confirmed, Spec.Store.toProof_blockOfImage] at this
    exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp this
  · have := Spec.Block.toProof_preceq_of_ancestorEq _ _ hm.2.1
    rw [Spec.Store.toProof_blockOfImage] at this
    exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp this

/-- `Model.specDraft`'s SG vote at a store `st` and a grade read `g`, when the spec's clearing walk
    finds no block: the grade-2 candidate of `g` if any, else the fork-choice root when `g`'s raw
    grade-2 test holds, else the anchor of `g`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_currentSGVote_none (st : (Model.specDraft (V := V)).HS)
    (g : DecoupledConsensusModel.Protocol.GradeRead V)
    (hB : Spec.Protocol.deepest_clear (st.val.blockOfImage g.anchor)
      (Spec.Store.ofImage st.val).live_confirmed (fun B => g.clear B.toProof) = none) :
    (∀ Q, g.Q2 = some Q → (Model.specDraft (V := V)).currentSGVote st g = Q) ∧
      (g.Q2 = none → g.rawG2 →
        (Model.specDraft (V := V)).currentSGVote st g = (Model.specDraft (V := V)).get_fg_root st.toFG) ∧
      (g.Q2 = none → ¬ g.rawG2 → (Model.specDraft (V := V)).currentSGVote st g = g.anchor) := by
  have e : (Model.specDraft (V := V)).currentSGVote st g = (Spec.Protocol.currentSGVote
      (Spec.Store.ofImage st.val) (SpecDraftRecord.ForkChoiceGrades.gradeReadOfImage st.val g)).toProof := rfl
  refine ⟨fun Q hQ => ?_, fun hQ hr => ?_, fun hQ hr => ?_⟩ <;> rw [e] <;>
    simp only [Spec.Protocol.currentSGVote, Id.run,
      SpecDraftRecord.ForkChoiceGrades.gradeReadOfImage, hB, hQ, ne_eq, not_true_eq_false,
      Option.map_some, Option.map_none, reduceCtorEq, not_false_eq_true, dite_true, dite_false,
      ite_true, ite_false, Option.value, Option.get_some]
  · exact Spec.Store.toProof_blockOfImage _ _
  · simp only [hr, decide_true, ite_true]
    rfl
  · simp only [hr, decide_false]
    exact Spec.Store.toProof_blockOfImage _ _

/-! ### Grade reads that need no equality -/

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- If `Except.map f e` answers `b`, then `e` answers some `a` with `b = f a`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_except_map_ok {α β : Type} {f : α → β}
    {e : DC.DRE α} {b : β} (h : Except.map f e = .ok b) : ∃ a, e = .ok a ∧ b = f a := by
  cases e with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, (Except.ok.inj h).symm⟩

omit [Fintype V] [Inhabited V] in
/-- The grade-2 candidate of a grade read off a store is a block of the store's tree. -/
theorem _root_.SpecDraftRecord.GradesFacts.draft_round_grade_read_Q2_mem
    {st : Spec.Store V} {r : Round} {G : Spec.Protocol.GradeRead V}
    (h : Spec.Protocol.round_grade_read st r = .ok G) {Y : Spec.Block V}
    (hY : G.Q2 = some Y) : Y ∈ st.T := by
  unfold Spec.Protocol.round_grade_read at h
  obtain ⟨A, -, h⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok h
  obtain ⟨Q2, hQ2, h⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok h
  obtain ⟨G0, -, h⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok h
  obtain ⟨raw, -, h⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok h
  have e := Except.ok.inj h
  subst e
  unfold Spec.Protocol.grade2Block at hQ2
  obtain ⟨Gs, -, hQ2⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok hQ2
  have e2 : Spec.Protocol.active_prefix st Gs.G2 = Q2 := Except.ok.inj hQ2
  rw [← e2] at hY
  obtain ⟨_, _, hm, -⟩ := draft_active_prefix_some hY
  exact SpecDraftRecord.GradesImages.filtered_subset st hm


omit [Fintype V] [Inhabited V] in
/-- When the confirmation candidate of a store `S` is a block `Y`, the stable root of the store's
    round, read from the same saved grades, is `Y`. -/
theorem _root_.SpecDraftRecord.GradesFacts.draft_stable_root_of_candidate (C : Spec.Config)
    (S : Spec.Store V) {Y : Spec.Block V}
    (ho : Spec.Protocol.confirmation_candidate C S = .ok (some Y)) {B : Spec.Block V}
    (hB : Spec.Protocol.round_stable_root S (C.round_of S.s) = .ok B) : B = Y := by
  unfold Spec.Protocol.confirmation_candidate at ho
  unfold Spec.Protocol.round_stable_root at hB
  dsimp only at hB
  obtain ⟨G2, hG2, ho⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok ho
  obtain ⟨G2', hG2', hB⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok hB
  have e : G2 = G2' := by
    change (match (Spec.Protocol.make_round_grades_compatible_with S.F
        (Spec.Protocol.saved_round_grades S.saved_grades (C.round_of S.s))).g2 with
      | .pending => (throw DC.Error.error : DC.DRE (Option (Spec.Block V)))
      | .computed G => pure G) = Except.ok G2 at hG2
    change (match (Spec.Protocol.make_round_grades_compatible_with S.F
        (Spec.Protocol.saved_round_grades S.saved_grades (C.round_of S.s))).g2 with
      | .pending => (throw DC.Error.error : DC.DRE (Option (Spec.Block V)))
      | .computed G => pure G) = Except.ok G2' at hG2'
    exact Except.ok.inj (hG2.symm.trans hG2')
  subst e
  have ho' : Spec.Protocol.active_prefix S G2 = some Y := Except.ok.inj ho
  have hB' : Spec.Protocol.stable_root S G2 = B := Except.ok.inj hB
  rw [← hB']
  simp only [Spec.Protocol.stable_root, Id.run, ho', ne_eq, reduceCtorEq,
    not_false_eq_true, dite_true, Option.value, Option.get_some]
  rfl

/-- The field `bodyReady_eq_false_of_find_none` of `GradesFacts` at `Model.specDraft`: if the SG
    vote `u` names the head `root` and the grade view `gv`'s tree has no block with that root, then
    every outcome of the body condition of `gv` for `u` is `false`, at every finalized block `F` and
    every cutoff `cutoff`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_bodyReady_eq_false_of_find_none :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : DecoupledConsensusModel.Block V) (cutoff : DecoupledConsensusModel.Time) (u : DecoupledConsensusModel.Protocol.SGVote V) {root : DecoupledConsensusModel.BlockId}, u.confirmed = Option.some root → DecoupledConsensusModel.Block.find? gv.T root = Option.none → ∀ b : Bool, (Model.specDraft (V := V)).bodyReady gv F cutoff u ⇢ b → b = Bool.false := by
  intro gv F cutoff u root h1 h2 b hb
  rw [specDraft_bodyReady_eq] at hb
  rw [sd_gv_T] at h2
  exact (Model.vocabulary_facts_grades
      (V := V)).bodyReady_eq_false_of_find_none _ F cutoff u h1 h2 b hb


/-- The field `bodyReady_of_confirmed_none` of `GradesFacts` at `Model.specDraft`: if the SG vote
    `u` confirms no root, then every outcome of the body condition of `u` at the grade view `gv`
    against `F` before `cutoff` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_bodyReady_of_confirmed_none :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V}, u.confirmed = Option.none → ∀ b : Bool, (Model.specDraft (V := V)).bodyReady gv F cutoff u ⇢ b → b = Bool.true := by
  intro gv F cutoff u h1 b hb
  rw [specDraft_bodyReady_eq] at hb
  exact (Model.vocabulary_facts_grades (V := V)).bodyReady_of_confirmed_none h1 b hb


/-- The field `bodyReady_of_find` of `GradesFacts` at `Model.specDraft`: if the SG vote `u` names
    the root `root`, `root` resolves in the tree of the grade view `gv` to the block `H`, `gv`
    stamps `H` before `cutoff`, and `H` is compatible with the finalized block `F`, then every
    outcome of the body condition of `gv` for `u` at `cutoff` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_bodyReady_of_find :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V} {root : DecoupledConsensusModel.BlockId} {H : DecoupledConsensusModel.Block V}, u.confirmed = Option.some root → DecoupledConsensusModel.Block.find? gv.T root = Option.some H → DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true → H.compatible F = Bool.true → ∀ b : Bool, (Model.specDraft (V := V)).bodyReady gv F cutoff u ⇢ b → b = Bool.true := by
  intro gv F cutoff u root H h1 h2 h3 h4 b hb
  rw [specDraft_bodyReady_eq] at hb
  rw [sd_gv_T] at h2
  rw [sd_gv_timestamp_block] at h3
  exact (Model.vocabulary_facts_grades (V := V)).bodyReady_of_find
      (gv := gv.val.toProof.toHealing.gradeView) h1 h2 h3 h4 b hb


/-- The field `bodyReady_of_head` of `GradesFacts` at `Model.specDraft`: for an attestation naming a
    head that the grade view's processed tree resolves to a block stamped before the cutoff and
    compatible with the reader's finalized block, every outcome of the body condition is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_bodyReady_of_head :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : DecoupledConsensusModel.Block V) (cutoff : ℤ) (u : DecoupledConsensusModel.Protocol.SGVote V) {root : DecoupledConsensusModel.BlockId} {H : DecoupledConsensusModel.Block V}, u.confirmed = Option.some root → DecoupledConsensusModel.Block.find? gv.T root = Option.some H → DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true → H.compatible F = Bool.true → ∀ b : Bool, (Model.specDraft (V := V)).bodyReady gv F cutoff u ⇢ b → b = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).bodyReady_of_head
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `bodyReady_of_no_head` of `GradesFacts` at `Model.specDraft`: for an attestation whose
    `confirmed` field is empty, every outcome of the body condition of every grade view at every
    cutoff is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_bodyReady_of_no_head :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : DecoupledConsensusModel.Block V) (cutoff : ℤ) (u : DecoupledConsensusModel.Protocol.SGVote V), u.confirmed = Option.none → ∀ b : Bool, (Model.specDraft (V := V)).bodyReady gv F cutoff u ⇢ b → b = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).bodyReady_of_no_head
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `bodyReady_parts` of `GradesFacts` at `Model.specDraft`: if an outcome `b` of the body
    condition of the SG vote `u` at the grade view `gv` against `F` before `cutoff` is `true`, and
    `u` confirms the root `root`, then `gv`'s tree finds a block `H` at `root`, `gv` stamped `H`
    before `cutoff`, and `H` is compatible with `F`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_bodyReady_parts :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V} {root : DecoupledConsensusModel.BlockId} (b : Bool), (Model.specDraft (V := V)).bodyReady gv F cutoff u ⇢ b → b = Bool.true → u.confirmed = Option.some root → ∃ H, DecoupledConsensusModel.Block.find? gv.T root = Option.some H ∧ DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true ∧ H.compatible F = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).bodyReady_parts
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `exists_find_of_bodyReady` of `GradesFacts` at `Model.specDraft`: if the SG vote `u`
    names the root `root` and an outcome `b` of the body condition of the grade view `gv` at
    `cutoff` against `F` for `u` is `true`, then `root` resolves in the tree of `gv` to some block
    `H`, `gv` stamps `H` before `cutoff`, and `H` is compatible with `F`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_find_of_bodyReady :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V} {root : DecoupledConsensusModel.BlockId}, u.confirmed = Option.some root → ∀ b : Bool, (Model.specDraft (V := V)).bodyReady gv F cutoff u ⇢ b → b = Bool.true → ∃ H, DecoupledConsensusModel.Block.find? gv.T root = Option.some H ∧ DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true ∧ H.compatible F = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).exists_find_of_bodyReady
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `mem_interpretedInputs_iff` of `GradesFacts` at `Model.specDraft`: for every outcome
    `I` of `v`'s interpreted inputs of the round-`r` grade of `gv` at the cutoff `c`, every outcome
    `R` of `v`'s raw inputs there and every outcome `b` of the body condition of the attestation `y`
    at `gv`, `F` and `c`, `y` is in `I` exactly when it is in `R` and `b` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_interpretedInputs_iff :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : DecoupledConsensusModel.Block V} {η r : DecoupledConsensusModel.Round} {c : DecoupledConsensusModel.Time} {v : V} {y : DecoupledConsensusModel.Protocol.SGVote V}
    (I : Finset (DecoupledConsensusModel.Protocol.SGVote V)) (hI : (Model.specDraft (V := V)).interpretedInputs gv F η r c v ⇢ I)
    (R : Finset (DecoupledConsensusModel.Protocol.SGVote V)) (hR : (Model.specDraft (V := V)).rawInputs gv η r c v ⇢ R)
    (b : Bool) (hb : (Model.specDraft (V := V)).bodyReady gv F c y ⇢ b),
    y ∈ I ↔ y ∈ R ∧ b = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).mem_interpretedInputs_iff
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `rawInputs_mono` of `GradesFacts` at `Model.specDraft`: if the cutoff `c` is at or
    before the cutoff `d`, every raw input of `sender` in an outcome `X` of the raw inputs of the
    grade view `gv` for round `r` and window length `eta` at `c` is also in every outcome `Y` of the
    raw inputs at `d`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_rawInputs_mono :
    ∀ (gv : (Model.specDraft (V := V)).GV) (eta r : Round) {c d : Time} (hcd : c ≤ d) (sender : V)
    (X : Finset (Protocol.SGVote V)), (Model.specDraft (V := V)).rawInputs gv eta r c sender ⇢ X →
    ∀ Y : Finset (Protocol.SGVote V), (Model.specDraft (V := V)).rawInputs gv eta r d sender ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).rawInputs_mono
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `rawView_mono` of `GradesFacts` at `Model.specDraft`: if the cutoff `c` is at or
    before the cutoff `d`, every token of an outcome `X` of `v`'s raw view of the grade view `gv`
    for round `r` and window length `eta` at `c` is also in every outcome `Y` of it at `d`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_rawView_mono :
    ∀ (gv : (Model.specDraft (V := V)).GV) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), (Model.specDraft (V := V)).rawView gv eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), (Model.specDraft (V := V)).rawView gv eta r d v ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).rawView_mono
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `readyView_mono` of `GradesFacts` at `Model.specDraft`: if the cutoff `c` is at or
    before the cutoff `d`, every token of an outcome `X` of `v`'s ready view of the grade view `gv`
    with the finalized block `F`, for round `r` and window length `eta`, at `c` is also in every
    outcome `Y` of it at `d`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readyView_mono :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), (Model.specDraft (V := V)).readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), (Model.specDraft (V := V)).readyView gv F eta r d v ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).readyView_mono
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `readyView_subset_rawView` of `GradesFacts` at `Model.specDraft`: every outcome `X` of
    `v`'s ready view of the grade view `gv` with the finalized block `F`, for round `r`, window
    length `eta` and cutoff `c`, is contained in every outcome `Y` of `v`'s raw view of `gv` for the
    same round, window length and cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readyView_subset_rawView :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (eta r : Round) (c : Time) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), (Model.specDraft (V := V)).readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), (Model.specDraft (V := V)).rawView gv eta r c v ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).readyView_subset_rawView
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `phaseGrade_of_honestPositiveSupport` of `GradesFacts` at `Model.specDraft`: for a
    choice `pos` of one outcome per validator of the support test for `C` and a choice `opp` of one
    outcome per validator of the opposition test for `C`, in the grade view `gv` with the cutoffs
    `ea` and `la`: if the validators outside `Hon` weigh strictly less than `Hon`, `pos` is `true`
    at every member of `Hon`, and every validator at which `opp` is `true` is outside `Hon`, then
    every outcome of the grade test of `gv` for `C` with those cutoffs is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseGrade_of_honestPositiveSupport :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (Hon : Finset V) (eta r : Round) (ea la : Time) (C : Block V)
    (pos : V → Bool) (hpos : ∀ v, (Model.specDraft (V := V)).positive gv F eta r ea la v C ⇢ pos v)
    (opp : V → Bool) (hopp : ∀ v, (Model.specDraft (V := V)).opposing gv F eta r ea la v C ⇢ opp v)
    (hmajority : E.electorate.weightOf (Finset.univ \ Hon) <
    E.electorate.weightOf Hon) (hpositive : ∀ v ∈ Hon,
    pos v = true) (hopposing : ∀ v,
    opp v = true →
    v ∉ Hon) (g : Bool) (hg : (Model.specDraft (V := V)).gradeBool E gv F eta r ea la C ⇢ g), g = true := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).phaseGrade_of_honestPositiveSupport (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `q10_freeze_of_graded` of `GradesFacts` at `Model.specDraft`: if `e ≤ l`, `B` is in
    the tree of the grade view `gv`, and an outcome `b` of the grade test of `gv` for `B` with the
    cutoffs `e` and `l` is `true`, then every outcome `fr` of the frozen root of `gv` with those
    cutoffs is some block `raw`, and `B` is an ancestor of `raw` or `raw` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_freeze_of_graded :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (eta r : Round) {e l : Time} (hel : e ≤ l) {B : Block V} (hmem : B ∈ gv.T) (b : Bool) (hb : (Model.specDraft (V := V)).gradeBool E gv F eta r e l B ⇢ b) (hgrade : b = true) (fr : Option (Block V)) (hfr : (Model.specDraft (V := V)).freezeRoot E gv F eta r e l ⇢ fr), ∃ raw : Block V, fr = some raw ∧ Block.Preceq B raw := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).q10_freeze_of_graded (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `q10_gradeBool_transport` of `GradesFacts` at `Model.specDraft`: take two grade views,
    `gva` with the finalized block `Fa` and the cutoffs `ea`, `la`, and `gvb` with the finalized
    block `Fb` and the cutoffs `eb`, `lb`, whose chosen ready and raw views satisfy the seven
    inclusions `hea_la` to `hrb_ra`; if every token of `Rea w` whose key `cva` says covers `B` is in
    `Reb w`, every key that `cva` says covers `B` is one `cvb` says covers it, and an outcome `ga`
    of the grade test of `gva` for `B` is `true`, then every outcome of the grade test of `gvb` for
    `B` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_gradeBool_transport :
    ∀ (E : Env V) (gva gvb : (Model.specDraft (V := V)).GV) (Fa Fb : Block V) (eta r : Round) (ea la eb lb : Time) (B : Block V)
    (Rea : V → Finset (Protocol.Token (Option BlockId))) (hRea : ∀ w, (Model.specDraft (V := V)).readyView gva Fa eta r ea w ⇢ Rea w)
    (Rla : V → Finset (Protocol.Token (Option BlockId))) (hRla : ∀ w, (Model.specDraft (V := V)).readyView gva Fa eta r la w ⇢ Rla w)
    (Wa : V → Finset (Protocol.Token (Option BlockId))) (hWa : ∀ w, (Model.specDraft (V := V)).rawView gva eta r la w ⇢ Wa w)
    (Reb : V → Finset (Protocol.Token (Option BlockId))) (hReb : ∀ w, (Model.specDraft (V := V)).readyView gvb Fb eta r eb w ⇢ Reb w)
    (Rlb : V → Finset (Protocol.Token (Option BlockId))) (hRlb : ∀ w, (Model.specDraft (V := V)).readyView gvb Fb eta r lb w ⇢ Rlb w)
    (Wb : V → Finset (Protocol.Token (Option BlockId))) (hWb : ∀ w, (Model.specDraft (V := V)).rawView gvb eta r lb w ⇢ Wb w)
    (cva : Option BlockId → Bool) (hcva : ∀ k, (Model.specDraft (V := V)).localCovers gva k B ⇢ cva k)
    (cvb : Option BlockId → Bool) (hcvb : ∀ k, (Model.specDraft (V := V)).localCovers gvb k B ⇢ cvb k)
    (hea_la : ∀ w, Rea w ⊆ Rla w) (hla_ra : ∀ w, Rla w ⊆ Wa w) (heb_lb : ∀ w, Reb w ⊆ Rlb w) (hlb_rb : ∀ w, Rlb w ⊆ Wb w) (heb_la : ∀ w, Reb w ⊆ Rla w) (hlb_la : ∀ w, Rlb w ⊆ Rla w) (hrb_ra : ∀ w, Wb w ⊆ Wa w) (hkeep : ∀ w, ∀ u ∈ Rea w,
    cva u.key = true → u ∈ Reb w) (hcov : ∀ k, cva k = true → cvb k = true) (ga : Bool) (hga : (Model.specDraft (V := V)).gradeBool E gva Fa eta r ea la B ⇢ ga) (hgrade : ga = true) (gb : Bool) (hgb : (Model.specDraft (V := V)).gradeBool E gvb Fb eta r eb lb B ⇢ gb), gb = true := by
  intro E gva gvb
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).q10_gradeBool_transport (E := E)
      (gva := gva.val.toProof.toHealing.gradeView) (gvb := gvb.val.toProof.toHealing.gradeView)


/-- The field `q10_graded_compatible` of `GradesFacts` at `Model.specDraft`: if `e ≤ l` and an
    outcome of the grade test of the grade view `gv` with the cutoffs `e` and `l` is `true` for `B`
    and one is `true` for `B'`, then `B` and `B'` lie on one chain. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_graded_compatible :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (eta r : Round) {e l : Time} (hel : e ≤ l) {B B' : Block V} (b : Bool) (hb : (Model.specDraft (V := V)).gradeBool E gv F eta r e l B ⇢ b) (hB : b = true) (b' : Bool) (hb' : (Model.specDraft (V := V)).gradeBool E gv F eta r e l B' ⇢ b') (hB' : b' = true), Block.compatible B B' = true := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).q10_graded_compatible (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `q10_interpreted_cut` of `GradesFacts` at `Model.specDraft`: if the cutoff `c` is at
    or before the cutoff `d`, every interpreted input of `sender` in an outcome `X` of the
    interpreted inputs of the grade view `gv` with the finalized block `F`, for round `r` and window
    length `eta`, at `c` is also in every outcome `Y` of them at `d`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_interpreted_cut :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (eta r : Round) {c d : Time} (hcd : c ≤ d) (sender : V)
    (X : Finset (Protocol.SGVote V)), (Model.specDraft (V := V)).interpretedInputs gv F eta r c sender ⇢ X →
    ∀ Y : Finset (Protocol.SGVote V), (Model.specDraft (V := V)).interpretedInputs gv F eta r d sender ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).q10_interpreted_cut
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `q10_rawView_cut` of `GradesFacts` at `Model.specDraft`: if the cutoff `c` is at or
    before the cutoff `d`, every token of an outcome `X` of `v`'s raw view of the grade view `gv`
    for round `r` and window length `eta` at `c` is also in every outcome `Y` of it at `d`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_rawView_cut :
    ∀ (gv : (Model.specDraft (V := V)).GV) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), (Model.specDraft (V := V)).rawView gv eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), (Model.specDraft (V := V)).rawView gv eta r d v ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).q10_rawView_cut
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `q10_readyView_cut` of `GradesFacts` at `Model.specDraft`: if the cutoff `c` is at or
    before the cutoff `d`, every token of an outcome `X` of `v`'s ready view of the grade view `gv`
    with the finalized block `F`, for round `r` and window length `eta`, at `c` is also in every
    outcome `Y` of it at `d`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_readyView_cut :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), (Model.specDraft (V := V)).readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), (Model.specDraft (V := V)).readyView gv F eta r d v ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).q10_readyView_cut
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `q10_ready_subset_raw` of `GradesFacts` at `Model.specDraft`: every outcome `X` of
    `v`'s ready view of the grade view `gv` with the finalized block `F`, for round `r`, window
    length `eta` and cutoff `c`, is contained in every outcome `Y` of `v`'s raw view of `gv` for the
    same round, window length and cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_q10_ready_subset_raw :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (eta r : Round) (c : Time) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), (Model.specDraft (V := V)).readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), (Model.specDraft (V := V)).rawView gv eta r c v ⇢ Y → X ⊆ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).q10_ready_subset_raw
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `exists_find_of_localCovers` of `GradesFacts` at `Model.specDraft`: if an outcome `b`
    of the cover test of the key `some root` for `B` in the grade view `gv` is `true`, then `root`
    resolves in the tree of `gv` to some block `H`, and `B` is an ancestor of `H` or `H` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_find_of_localCovers :
    ∀ {gv : (Model.specDraft (V := V)).GV} {root : BlockId} {B : Block V} (b : Bool) (hb : (Model.specDraft (V := V)).localCovers gv (some root) B ⇢ b) (hcov : b = true), ∃ H : Block V, Block.find? gv.T root = some H ∧ Block.Preceq B H := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).exists_find_of_localCovers
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `Sts_exists_mem_T_preceq_of_gradeBool` of `GradesFacts` at `Model.specDraft`: if an
    outcome `b` of the grade test of the grade view `gv` for `B` is `true`, then `gv.T` holds a
    descendant of `B` or `B` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_exists_mem_T_preceq_of_gradeBool :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V) (b : Bool) (hb : (Model.specDraft (V := V)).gradeBool E gv F η r early late B ⇢ b) (h : b = true), ∃ H ∈ gv.T, Block.Preceq B H := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).Sts_exists_mem_T_preceq_of_gradeBool (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `find_of_mem_readyView` of `GradesFacts` at `Model.specDraft`: if the token `tok` is
    in an outcome `X` of `v`'s ready view of the grade view `gv` for round `r` at the cutoff `c`
    (with the finalized block `F`), and `tok` names the root `root`, then `root` resolves in `gv`'s
    tree to some block. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_find_of_mem_readyView :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (c : Time) (v : V) {tok : Protocol.Token (Option BlockId)} {root : BlockId} (X : Finset (Protocol.Token (Option BlockId))) (hX : (Model.specDraft (V := V)).readyView gv F η r c v ⇢ X) (htok : tok ∈ X) (hkey : tok.key = some root), ∃ H : Block V, Block.find? gv.T root = some H := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).find_of_mem_readyView
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `gradeBool_eq_false_of_weight_le` of `GradesFacts` at `Model.specDraft`: for a choice
    `pos` of one outcome per validator of the support test for `B` and a choice `opp` of one outcome
    per validator of the opposition test for `B` in the grade view, if the validators at which `pos`
    is `true` weigh at most as much as those at which `opp` is `true`, then every outcome of the
    grade test of the view for `B` is `false`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeBool_eq_false_of_weight_le :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V)
    (pos : V → Bool) (hpos : ∀ u, (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ pos u)
    (opp : V → Bool) (hopp : ∀ u, (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ opp u) (h : E.electorate.weightOf
    (Finset.univ.filter fun u => pos u = true)
    ≤ E.electorate.weightOf
    (Finset.univ.filter fun u => opp u = true)) (g : Bool) (hg : (Model.specDraft (V := V)).gradeBool E gv F η r early late B ⇢ g), g = false := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).gradeBool_eq_false_of_weight_le (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `gradeBool_of_freezeRoot_eq_some` of `GradesFacts` at `Model.specDraft`: if an outcome
    of the frozen root of the grade view `gv` with finalized block `F`, at round `r` with cutoffs
    `early` and `late`, is `some D`, then every outcome of the grade test `Protocol.gradeBool` for
    `D` with the same arguments is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeBool_of_freezeRoot_eq_some :
    ∀ {E : Env V} {gv : (Model.specDraft (V := V)).GV} {F : Block V} {η r : Round} {early late : Time} {D : Block V} (fr : Option (Block V)) (hfr : (Model.specDraft (V := V)).freezeRoot E gv F η r early late ⇢ fr) (h : fr = some D) (g : Bool), (Model.specDraft (V := V)).gradeBool E gv F η r early late D ⇢ g → g = true := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).gradeBool_of_freezeRoot_eq_some (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `gradeBool_of_subsets` of `GradesFacts` at `Model.specDraft`: for choices of one
    outcome per validator of the opposition tests (`opp'` for `B'` in `gv'`, `opp` for `B` in `gv`)
    and of the support tests (`pos` for `B` in `gv`, `pos'` for `B'` in `gv'`): if an outcome of the
    local grade of `B` in the grade view `gv` (finalized block `F`, cutoffs `early` and `late`) is
    `true`, every sender at which `opp'` is `true` is one at which `opp` is `true`, and every sender
    at which `pos` is `true` is one at which `pos'` is `true`, then every outcome of the local grade
    of `B'` in `gv'` (finalized block `F'`, cutoffs `early'` and `late'`) is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeBool_of_subsets :
    ∀ (E : Env V) {gv gv' : (Model.specDraft (V := V)).GV} {F F' : Block V} {η r : Round} {early late early' late' : Time} {B B' : Block V}
    (opp' : V → Bool) (hopp' : ∀ u, (Model.specDraft (V := V)).opposing gv' F' η r early' late' u B' ⇢ opp' u)
    (opp : V → Bool) (hopp'' : ∀ u, (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ opp u)
    (pos : V → Bool) (hpos' : ∀ u, (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ pos u)
    (pos' : V → Bool) (hpos'' : ∀ u, (Model.specDraft (V := V)).positive gv' F' η r early' late' u B' ⇢ pos' u)
    (hopp : (Finset.univ.filter fun u => opp' u = true) ⊆
    Finset.univ.filter fun u => opp u = true) (hpos : (Finset.univ.filter fun u => pos u = true) ⊆
    Finset.univ.filter fun u => pos' u = true) (g : Bool) (hg : (Model.specDraft (V := V)).gradeBool E gv F η r early late B ⇢ g) (h : g = true) (g' : Bool), (Model.specDraft (V := V)).gradeBool E gv' F' η r early' late' B' ⇢ g' → g' = true := by
  intro E gv gv'
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).gradeBool_of_subsets (E := E)
      (gv := gv.val.toProof.toHealing.gradeView) (gv' := gv'.val.toProof.toHealing.gradeView)


/-- The field `gradeBool_of_supporters` of `GradesFacts` at `Model.specDraft`: for a choice `pos` of
    one outcome per validator of the support test for `B` and a choice `W` of one outcome per
    validator of the raw view at the late cutoff: if the early cutoff is at or before the late one,
    `pos` is `true` at every member of `H`, and the validators whose chosen raw view is non-empty
    and that are not in `H` weigh strictly less than `H`, then every outcome of the grade test of
    the view for `B` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeBool_of_supporters :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V) (H : Finset V)
    (pos : V → Bool) (hpos' : ∀ u, (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ pos u)
    (W : V → Finset (Protocol.Token (Option BlockId))) (hW : ∀ u, (Model.specDraft (V := V)).rawView gv η r late u ⇢ W u)
    (hel : early ≤ late) (hpos : ∀ u ∈ H, pos u = true) (hw : E.electorate.weightOf
    ((Finset.univ.filter fun u => (W u).Nonempty) \ H)
    < E.electorate.weightOf H) (g : Bool), (Model.specDraft (V := V)).gradeBool E gv F η r early late B ⇢ g → g = true := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).gradeBool_of_supporters (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `gradeBool_of_weight_lt` of `GradesFacts` at `Model.specDraft`: for a choice `opp` of
    one outcome per validator of the opposition test for `B` and a choice `pos` of one outcome per
    validator of the support test for `B` in the grade view, if the validators at which `opp` is
    `true` weigh strictly less than those at which `pos` is `true`, then every outcome of the grade
    test of the view for `B` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeBool_of_weight_lt :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V)
    (opp : V → Bool) (hopp : ∀ u, (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ opp u)
    (pos : V → Bool) (hpos : ∀ u, (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ pos u) (h : E.electorate.weightOf
    (Finset.univ.filter fun u => opp u = true)
    < E.electorate.weightOf
    (Finset.univ.filter fun u => pos u = true)) (g : Bool) (hg : (Model.specDraft (V := V)).gradeBool E gv F η r early late B ⇢ g), g = true := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).gradeBool_of_weight_lt (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `gradeBool_round_zero` of `GradesFacts` at `Model.specDraft`: whatever the electorate,
    grade view, finalized block, window length and cutoffs, every outcome of the grade test of round
    `0` is false for every block `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeBool_round_zero :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η : Round) (early late : Time) (B : Block V) (g : Bool), (Model.specDraft (V := V)).gradeBool E gv F η 0 early late B ⇢ g → g = false := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).gradeBool_round_zero (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `localCovers_none` of `GradesFacts` at `Model.specDraft`: in any grade view `gv`,
    every outcome of the cover test of the empty key for a block `B` is `false`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_localCovers_none :
    ∀ (gv : (Model.specDraft (V := V)).GV) (B : Block V) (b : Bool), (Model.specDraft (V := V)).localCovers gv none B ⇢ b → b = false := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).localCovers_none
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `localCovers_of_find` of `GradesFacts` at `Model.specDraft`: if the root `root`
    resolves in the tree of the grade view `gv` to the block `H`, and `B` is an ancestor of `H` or
    `H` itself, then every outcome of the cover test of the key `some root` for `B` in `gv` is
    `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_localCovers_of_find :
    ∀ {gv : (Model.specDraft (V := V)).GV} {root : BlockId} {B H : Block V} (hfind : Block.find? gv.T root = some H) (hBH : Block.Preceq B H) (b : Bool), (Model.specDraft (V := V)).localCovers gv (some root) B ⇢ b → b = true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).localCovers_of_find
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `localCovers_some_iff_of_find` of `GradesFacts` at `Model.specDraft`: if the key `key`
    resolves in the grade view `gv`'s tree to the block `H`, then every outcome `b` of the cover
    test of `key` for `B` in `gv` is `true` exactly when `B` is an ancestor of `H` or `H` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_localCovers_some_iff_of_find :
    ∀ {gv : (Model.specDraft (V := V)).GV} {key : BlockId} {B H : Block V} (hfind : Block.find? gv.T key = some H) (b : Bool) (hb : (Model.specDraft (V := V)).localCovers gv (some key) B ⇢ b), b = true ↔ Block.Preceq B H := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).localCovers_some_iff_of_find
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `mem_T_of_freezeRoot_eq_some` of `GradesFacts` at `Model.specDraft`: if an outcome of
    the frozen root of the grade view `gv` is `some D`, then `D` is in the tree of `gv`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_T_of_freezeRoot_eq_some :
    ∀ {E : Env V} {gv : (Model.specDraft (V := V)).GV} {F : Block V} {η r : Round} {early late : Time} {D : Block V} (fr : Option (Block V)) (hfr : (Model.specDraft (V := V)).freezeRoot E gv F η r early late ⇢ fr) (h : fr = some D), D ∈ gv.T := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).mem_T_of_freezeRoot_eq_some (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `opposing_cases` of `GradesFacts` at `Model.specDraft`: if an outcome `o` of the
    opposition test of `u` for `B` in the grade view is `true`, then for every outcome `Re`, `Rl` of
    `u`'s early and late ready views, every outcome `W` of `u`'s raw view at the late cutoff, and
    every choice `cov` of one outcome per key of the cover test of `B` in `gv`: either some token
    `x` of `Rl`, of a round at least that of every token of `Re`, has a key that `cov` does not say
    covers `B`; or two tokens `x`, `y` of `W`, `x` of a round at least that of every token of `Re`,
    have the same round and different keys. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposing_cases :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (o : Bool) (ho : (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ o) (h : o = true)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : (Model.specDraft (V := V)).rawView gv η r late u ⇢ W)
    (cov : Option BlockId → Bool) (hcov : ∀ k, (Model.specDraft (V := V)).localCovers gv k B ⇢ cov k), (∃ x ∈ Rl,
    (∀ y ∈ Re, y.round ≤ x.round) ∧
    ¬ cov x.key = true) ∨
    ∃ x ∈ W, ∃ y ∈ W,
    (∀ z ∈ Re, z.round ≤ x.round) ∧
    x.round = y.round ∧ x.key ≠ y.key := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).opposing_cases
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `opposing_false_of_positive` of `GradesFacts` at `Model.specDraft`: if `early ≤ late`
    and an outcome `p` of the support test of `u` for `B` in the grade view is `true`, then every
    outcome of the opposition test of `u` for `B` there is `false`. The early witness is then a raw
    token at the late cutoff, so its clean condition excludes both a late ready token of its round
    not covering `B` and two raw tokens of one round from its round on with different keys; a late
    token of a larger round covers `B` by the last condition. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposing_false_of_positive :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (hel : early ≤ late) (p : Bool) (hp : (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ p) (h : p = true) (o : Bool), (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ o → o = false := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).opposing_false_of_positive
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `opposing_of_positive_not_compatible` of `GradesFacts` at `Model.specDraft`: if the
    early cutoff is at or before the late one, an outcome `p` of the support test of `u` for `B` in
    the grade view is `true`, and `B'` is not on one chain with `B`, then every outcome of the
    opposition test of `u` for `B'` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposing_of_positive_not_compatible :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (u : V) {B B' : Block V} (hel : early ≤ late) (hBB' : ¬ Block.Compatible B B') (p : Bool) (hp : (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ p) (h : p = true) (o : Bool), (Model.specDraft (V := V)).opposing gv F η r early late u B' ⇢ o → o = true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).opposing_of_positive_not_compatible
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `preceq_freezeRoot` of `GradesFacts` at `Model.specDraft`: for a choice `g` of one
    outcome per block of the grade test: if `X` is in the view's tree and `g X` is `true`, and every
    two blocks of the tree at which `g` is `true` lie on one chain, then every outcome of the frozen
    root is some block `D` and `X` is an ancestor of `D` or `D` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_freezeRoot :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) {X : Block V}
    (g : Block V → Bool) (hg : ∀ B, (Model.specDraft (V := V)).gradeBool E gv F η r early late B ⇢ g B)
    (hXT : X ∈ gv.T) (hX : g X = true) (hcmp : ∀ D ∈ gv.T, ∀ D' ∈ gv.T, g D = true →
    g D' = true → Block.compatible D D' = true) (fr : Option (Block V)), (Model.specDraft (V := V)).freezeRoot E gv F η r early late ⇢ fr → ∃ D : Block V, fr = some D ∧ Block.Preceq X D := by
  intro E gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).preceq_freezeRoot (E := E)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `preceq_of_localCovers_of_find` of `GradesFacts` at `Model.specDraft`: if an outcome
    `b` of the cover test of the key `some root` for the block `B` in the grade view `gv` is `true`,
    and `root` resolves in `gv`'s tree to the block `H`, then `B` is an ancestor of `H` or `H`
    itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_of_localCovers_of_find :
    ∀ {gv : (Model.specDraft (V := V)).GV} {root : BlockId} {B H : Block V} (b : Bool) (hb : (Model.specDraft (V := V)).localCovers gv (some root) B ⇢ b) (hcov : b = true) (hfind : Block.find? gv.T root = some H), Block.Preceq B H := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).preceq_of_localCovers_of_find
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `val_index_of_mem_rawInputs` of `GradesFacts` at `Model.specDraft`: every attestation
    in an outcome `X` of `sender`'s raw inputs to the round-`r` grade of `gv` at the cutoff is
    signed by `sender`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_val_index_of_mem_rawInputs :
    ∀ {gv : (Model.specDraft (V := V)).GV} {eta r : Round} {cutoff : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : (Model.specDraft (V := V)).rawInputs gv eta r cutoff sender ⇢ X) (hu : u ∈ X), u.val_index = sender := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).val_index_of_mem_rawInputs
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `exists_rawInputs_of_mem_rawView` of `GradesFacts` at `Model.specDraft`: if the token
    `tok` is in an outcome `X` of `v`'s raw view of the round-`r` grade of the grade view `gv` at
    the cutoff `c`, then for every outcome `Y` of `v`'s raw inputs to that grade at that cutoff,
    `tok` is the token of some attestation in `Y`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_rawInputs_of_mem_rawView :
    ∀ {gv : (Model.specDraft (V := V)).GV} {η r : DecoupledConsensusModel.Round} {c : DecoupledConsensusModel.Time} {v : V} {tok : DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId)} (X : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).rawView gv η r c v ⇢ X → tok ∈ X → ∀ Y : Finset (DecoupledConsensusModel.Protocol.SGVote V), (Model.specDraft (V := V)).rawInputs gv η r c v ⇢ Y → ∃ y ∈ Y, (Model.specDraft (V := V)).token y = tok := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).exists_rawInputs_of_mem_rawView
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `opposes_of_opposing` of `GradesFacts` at `Model.specDraft`: if an outcome `o` of the
    opposition test of the sender `u` for `B` in the grade view `gv` is `true`, then for every
    choice `cov` of one outcome per key and block of the cover test of `gv`, and every outcome `Re`,
    `Rl`, `W` of `u`'s ready tokens at `early`, its ready tokens at `late` and its raw tokens at
    `late`, those tokens oppose `B`, where a key covers a block when `cov` says `true` for them. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposes_of_opposing :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : DecoupledConsensusModel.Block V} {η r : DecoupledConsensusModel.Round} {early late : DecoupledConsensusModel.Time} {u : V} {B : DecoupledConsensusModel.Block V} (o : Bool), (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ o → o = Bool.true →
    ∀ (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, (Model.specDraft (V := V)).localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).rawView gv η r late u ⇢ W →
    (Model.specDraft (V := V)).Opposes (fun k b ↦ cov k b = Bool.true) Re Rl W B := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).opposes_of_opposing
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `opposing_of_Opposes` of `GradesFacts` at `Model.specDraft`: for a choice `cov` of one
    outcome per key and block of the cover test of `gv`, and outcomes `Re`, `Rl`, `W` of `u`'s early
    ready view, late ready view and late raw view, if `Protocol.Opposes` holds of `B` for `Re`,
    `Rl`, `W` with "`cov` says `true`" as the cover test, then every outcome of the opposition test
    of `u` for `B` in the grade view is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposing_of_Opposes :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : DecoupledConsensusModel.Block V) (η r : DecoupledConsensusModel.Round) (early late : DecoupledConsensusModel.Time) (u : V) (B : DecoupledConsensusModel.Block V)
    (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, (Model.specDraft (V := V)).localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).rawView gv η r late u ⇢ W →
    (Model.specDraft (V := V)).Opposes (fun k b ↦ cov k b = Bool.true) Re Rl W B → ∀ o : Bool, (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ o → o = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).opposing_of_Opposes
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `positive_of_Supports` of `GradesFacts` at `Model.specDraft`: for a choice `cov` of
    one outcome per key and block of the cover test of `gv`, and outcomes `Re`, `Rl`, `W` of `u`'s
    early ready view, late ready view and late raw view, if `Protocol.Supports` holds of `B` for
    `Re`, `Rl`, `W` with "`cov` says `true`" as the cover test, then every outcome of the support
    test of `u` for `B` in the grade view is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_positive_of_Supports :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : DecoupledConsensusModel.Block V) (η r : DecoupledConsensusModel.Round) (early late : DecoupledConsensusModel.Time) (u : V) (B : DecoupledConsensusModel.Block V)
    (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, (Model.specDraft (V := V)).localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).rawView gv η r late u ⇢ W →
    (Model.specDraft (V := V)).Supports (fun k b ↦ cov k b = Bool.true) Re Rl W B → ∀ p : Bool, (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ p → p = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).positive_of_Supports
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `supports_of_positive` of `GradesFacts` at `Model.specDraft`: if an outcome `p` of the
    support test of the sender `u` for `B` in the grade view `gv` is `true`, then for every choice
    `cov` of one outcome per key and block of the cover test of `gv`, and every outcome `Re`, `Rl`,
    `W` of `u`'s ready tokens at `early`, its ready tokens at `late` and its raw tokens at `late`,
    those tokens support `B`, where a key covers a block when `cov` says `true` for them. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_supports_of_positive :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : DecoupledConsensusModel.Block V} {η r : DecoupledConsensusModel.Round} {early late : DecoupledConsensusModel.Time} {u : V} {B : DecoupledConsensusModel.Block V} (p : Bool), (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ p → p = Bool.true →
    ∀ (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, (Model.specDraft (V := V)).localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), (Model.specDraft (V := V)).rawView gv η r late u ⇢ W →
    (Model.specDraft (V := V)).Supports (fun k b ↦ cov k b = Bool.true) Re Rl W B := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).supports_of_positive
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `rawInputs_mem_window` of `GradesFacts` at `Model.specDraft`: the only attestations an
    outcome `X` of a round-`r` grade's raw inputs of `v` holds are the ones `v`'s store holds for a
    round of `latest_window η r`, signed by that sender and recorded before the cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_rawInputs_mem_window :
    ∀ (gv : (Model.specDraft (V := V)).GV) (eta r : DecoupledConsensusModel.Round) (cutoff : ℤ) (sender : V) {u : DecoupledConsensusModel.Protocol.SGVote V} (X : Finset (DecoupledConsensusModel.Protocol.SGVote V)), (Model.specDraft (V := V)).rawInputs gv eta r cutoff sender ⇢ X → u ∈ X → (∃ k ∈ (Model.specDraft (V := V)).latest_window eta r, u ∈ gv.sg_votes k) ∧ u.val_index = sender ∧ DecoupledConsensusModel.occurrenceBefore (gv.timestamp_sg_vote u) cutoff = Bool.true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).rawInputs_mem_window
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `token_mem_readyView` of `GradesFacts` at `Model.specDraft`: if the attestation `y` is
    in an outcome `X` of `v`'s raw inputs to the round-`r` grade of the grade view `gv` at the
    cutoff `c`, and an outcome `b` of the body condition of `y` at `gv`, the finalized block `F` and
    `c` is `true`, then the token of `y` is in every outcome `Y` of `v`'s ready view at that cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_token_mem_readyView :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : DecoupledConsensusModel.Block V) (η r : DecoupledConsensusModel.Round) (c : DecoupledConsensusModel.Time) (v : V) {y : DecoupledConsensusModel.Protocol.SGVote V} (X : Finset (DecoupledConsensusModel.Protocol.SGVote V)), (Model.specDraft (V := V)).rawInputs gv η r c v ⇢ X → y ∈ X → ∀ b : Bool, (Model.specDraft (V := V)).bodyReady gv F c y ⇢ b → b = Bool.true → ∀ Y : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId)), (Model.specDraft (V := V)).readyView gv F η r c v ⇢ Y → (Model.specDraft (V := V)).token y ∈ Y := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).token_mem_readyView
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `compatible_of_gradeBool_phase` of `GradesFacts` at `Model.specDraft`: if an outcome
    of the grade test of the grade view `gv` for round `r` with the cutoffs of the phase `p` is
    `true` for `B` and one is `true` for `B'`, then `B` and `B'` are one an ancestor of the other. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_compatible_of_gradeBool_phase :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (r : Round) (p : Protocol.Phase) {B B' : Block V} (b : Bool) (hb : (Model.specDraft (V := V)).gradeBool E gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p)
    ((Model.specDraft (V := V)).late E hc r p) B ⇢ b) (hB : b = true) (b' : Bool) (hb' : (Model.specDraft (V := V)).gradeBool E gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p)
    ((Model.specDraft (V := V)).late E hc r p) B' ⇢ b') (hB' : b' = true), Block.compatible B B' = true := by
  intro E hc gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).compatible_of_gradeBool_phase (E := E) (hc := hc)
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `exists_window_of_mem_rawInputs` of `GradesFacts` at `Model.specDraft`: if `u` is in
    an outcome `X` of `sender`'s raw inputs read from the grade view `gv` for round `r` with the
    window length `eta` and the cutoff `cutoff`, then `u` is an SG vote `gv` holds for some round
    `k` of the latest window of `eta` rounds before `r`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_window_of_mem_rawInputs :
    ∀ {gv : (Model.specDraft (V := V)).GV} {eta r : Round} {cutoff : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : (Model.specDraft (V := V)).rawInputs gv eta r cutoff sender ⇢ X) (hu : u ∈ X), ∃ k, k ∈ (Model.specDraft (V := V)).latest_window eta r ∧ u ∈ gv.sg_votes k := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).exists_window_of_mem_rawInputs
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `lo_le_of_rawInputs_l53` of `GradesFacts` at `Model.specDraft`: if
    `lo ≤ opening (r − η_SG)`, `opening r − 5Δ ≤ c`, and some `u` is in an outcome `X` of the raw
    inputs of round `r` for some sender at some cutoff, then `lo ≤ c`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_lo_le_of_rawInputs_l53 :
    ∀ (S : Setup V) {lo : Int} {r : Round} {c : Time} (hlow : lo ≤ (Model.specDraft (V := V)).opening S.E S.hc (r - S.hc.η_SG)) (hc : (Model.specDraft (V := V)).opening S.E S.hc r - 5 * S.E.Δ ≤ c) {gv : (Model.specDraft (V := V)).GV} {c' : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : (Model.specDraft (V := V)).rawInputs gv S.hc.η_SG r c' sender ⇢ X) (hraw : u ∈ X), lo ≤ c := by
  intro S lo r c hlow hc gv
  sd_rw at *
  exact (Model.vocabulary_facts_grades (V := V)).lo_le_of_rawInputs_l53 (S := S) (lo := lo) (r := r)
      (c := c) (hlow := hlow) (hc := hc) (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `mem_rawInputs_of_occurrenceBefore` of `GradesFacts` at `Model.specDraft`: if the
    grade view `gv` holds the attestation `u` among its SG votes of round `k`, `k` is one of the
    rounds `latest_window eta r` reads, `u` is signed by `sender`, and the stamp `gv` gives `u`
    occurs before `cutoff`, then `u` is in every outcome of `sender`'s raw inputs to the round-`r`
    grade at that cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_rawInputs_of_occurrenceBefore :
    ∀ (gv : (Model.specDraft (V := V)).GV) (eta r k : Round) (cutoff : Time) (sender : V) {u : Protocol.SGVote V} (hk : k ∈ (Model.specDraft (V := V)).latest_window eta r) (hu : u ∈ gv.sg_votes k) (hidx : u.val_index = sender) (hocc : occurrenceBefore (gv.timestamp_sg_vote u) cutoff = true) (X : Finset (Protocol.SGVote V)), (Model.specDraft (V := V)).rawInputs gv eta r cutoff sender ⇢ X → u ∈ X := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).mem_rawInputs_of_occurrenceBefore
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `mem_rawInputs_of_stamp` of `GradesFacts` at `Model.specDraft`: if the grade view `gv`
    holds the attestation `u` among its SG votes of round `k`, `k` is one of the rounds
    `latest_window eta r` reads, `u` is signed by `sender`, and `gv` stamps `u` at an instant
    strictly before `cutoff`, then `u` is in every outcome of `sender`'s raw inputs to the round-`r`
    grade at that cutoff. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_rawInputs_of_stamp :
    ∀ (gv : (Model.specDraft (V := V)).GV) (eta r k : Round) (cutoff : Time) (sender : V) {u : Protocol.SGVote V} (hk : k ∈ (Model.specDraft (V := V)).latest_window eta r) (hu : u ∈ gv.sg_votes k) (hidx : u.val_index = sender) {stamp : Time} (hts : gv.timestamp_sg_vote u = some (stamp : Stamp)) (hlt : stamp < cutoff) (X : Finset (Protocol.SGVote V)), (Model.specDraft (V := V)).rawInputs gv eta r cutoff sender ⇢ X → u ∈ X := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).mem_rawInputs_of_stamp
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `mem_rawView_iff` of `GradesFacts` at `Model.specDraft`: for every outcome `X` of
    `v`'s raw view of the grade view `gv` for round `r` at the cutoff `c` and every outcome `Y` of
    `v`'s raw inputs to that grade at that cutoff, a token is in `X` exactly when it is the token
    (round and named root) of an attestation in `Y`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_rawView_iff :
    ∀ (gv : (Model.specDraft (V := V)).GV) (η r : Round) (c : Time) (v : V) (tok : Protocol.Token (Option BlockId))
    (X : Finset (Protocol.Token (Option BlockId))) (hX : (Model.specDraft (V := V)).rawView gv η r c v ⇢ X)
    (Y : Finset (Protocol.SGVote V)) (hY : (Model.specDraft (V := V)).rawInputs gv η r c v ⇢ Y), tok ∈ X ↔
    ∃ y ∈ Y, (Model.specDraft (V := V)).token y = tok := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).mem_rawView_iff
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `mem_readyView_iff` of `GradesFacts` at `Model.specDraft`: for every outcome `X` of
    `v`'s ready view of the round-`r` grade of `gv` at the cutoff `c` and every outcome `Y` of `v`'s
    interpreted inputs there, a token is in `X` exactly when it is the token of some attestation in
    `Y`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_readyView_iff :
    ∀ {gv : (Model.specDraft (V := V)).GV} {F : Block V} {η r : Round} {c : Time} {v : V} {tok : Protocol.Token (Option BlockId)}
    (X : Finset (Protocol.Token (Option BlockId))) (hX : (Model.specDraft (V := V)).readyView gv F η r c v ⇢ X)
    (Y : Finset (Protocol.SGVote V)) (hY : (Model.specDraft (V := V)).interpretedInputs gv F η r c v ⇢ Y), tok ∈ X ↔
    ∃ y ∈ Y, (Model.specDraft (V := V)).token y = tok := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).mem_readyView_iff
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `mem_sg_votes_of_mem_rawInputs` of `GradesFacts` at `Model.specDraft`: if `u` is in an
    outcome `X` of the raw inputs of `sender` in the grade view `gv`, for the window `eta` before
    round `r` and the cutoff `cutoff`, then some round `k` of that window has `u` among `gv`'s SG
    votes of round `k`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_sg_votes_of_mem_rawInputs :
    ∀ {gv : (Model.specDraft (V := V)).GV} {eta r : Round} {cutoff : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : (Model.specDraft (V := V)).rawInputs gv eta r cutoff sender ⇢ X) (hu : u ∈ X), ∃ k ∈ (Model.specDraft (V := V)).latest_window eta r, u ∈ gv.sg_votes k := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).mem_sg_votes_of_mem_rawInputs
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `exists_honest_max_positive_supporter_of_relativeGrade` of `GradesFacts` at
    `Model.specDraft`: if, for every choice `ins` of interpreted inputs at the early cutoff, the
    weight outside `Hon` is less than the weight of the members of `Hon` with a nonempty chosen
    input, and an outcome `g` of the grade test of `B` at phase `p` of round `r` is `true`, then
    some member `v` of `Hon` has an outcome `I` of its interpreted inputs at the early cutoff and an
    input `u ∈ I` whose confirmed root resolves in the view's tree to a block `head` of which `B` is
    an ancestor, every outcome of `v`'s support test for `B` is `true`, and every input of `I` has a
    round at most `u`'s. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_honest_max_positive_supporter_of_relativeGrade :
    ∀ (E : Env V) (hc : Protocol.HealConfig)
    {gv : (Model.specDraft (V := V)).GV} {F : Block V} {Hon : Finset V} {r : Round} {B : Block V} {p : Protocol.Phase},
    (∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, (Model.specDraft (V := V)).interpretedInputs gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p) v ⇢ ins v) →
      E.electorate.weightOf (Finset.univ \ Hon) <
        E.electorate.weightOf (Hon.filter fun v => (ins v).Nonempty)) →
    ∀ g : Bool, (Model.specDraft (V := V)).gradeBool E gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p) ((Model.specDraft (V := V)).late E hc r p) B ⇢ g →
    g = true →
    ∃ v ∈ Hon, ∃ I : Finset (Protocol.SGVote V),
      (Model.specDraft (V := V)).interpretedInputs gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p) v ⇢ I ∧
      ∃ u ∈ I, ∃ head : Block V, u.confirmed = some head.root ∧
        Block.find? gv.T head.root = some head ∧ head ∈ gv.T ∧ Block.Preceq B head ∧
        (∀ b : Bool, (Model.specDraft (V := V)).positive gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p) ((Model.specDraft (V := V)).late E hc r p) v B ⇢ b →
          b = true) ∧
        ∀ x ∈ I, x.round ≤ u.round := by
  intro E hc gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).exists_honest_max_positive_supporter_of_relativeGrade
      (E := E) (hc := hc) (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `exists_head_of_head_covers` of `GradesFacts` at `Model.specDraft`: if an outcome `b`
    of the cover test of the optional root `H` for `B` in the tree `T` is `true`, then `H` is some
    root `root` that resolves in `T` to a block `head` of `T`, and `B` is an ancestor of `head` or
    `head` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_head_of_head_covers :
    ∀ {T : Finset (Block V)} {B : Block V} {H : Option BlockId} (b : Bool) (hb : (Model.specDraft (V := V)).head_covers T B H ⇢ b) (h : b = true), ∃ (root : BlockId) (head : Block V), H = some root ∧
    Block.find? T root = some head ∧ head ∈ T ∧ Block.preceq B head = true := by
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).exists_head_of_head_covers


/-- The field `conditions_of_opposing` of `GradesFacts` at `Model.specDraft`: if an outcome `o` of
    the opposition test of `u` for `B` in the grade view is `true`, then for every outcome `Re`,
    `Rl` of `u`'s early and late ready views, every outcome `W` of `u`'s raw view at the late
    cutoff, and every choice `cov` of one outcome per key of the cover test of `B` over `gv`'s tree:
    either some token `x` of `Rl` has a round at least that of every token of `Re` and `cov` does
    not say that `x`'s key covers `B`, or two tokens `x` and `y` of `W` have the same round, at
    least that of every token of `Re`, and different keys. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_conditions_of_opposing :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (o : Bool) (ho : (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ o) (h : o = true)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : (Model.specDraft (V := V)).rawView gv η r late u ⇢ W)
    (cov : Option BlockId → Bool) (hcov : ∀ k, (Model.specDraft (V := V)).head_covers gv.T B k ⇢ cov k), (∃ x ∈ Rl,
    (∀ y ∈ Re, y.round ≤ x.round) ∧
    ¬ cov x.key = true) ∨
    ∃ x ∈ W, ∃ y ∈ W,
    (∀ z ∈ Re, z.round ≤ x.round) ∧
    x.round = y.round ∧ x.key ≠ y.key := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).conditions_of_opposing
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `conditions_of_positive` of `GradesFacts` at `Model.specDraft`: if an outcome `p` of
    the support test of `u` for `B` in the grade view is `true`, then for every outcome `Re`, `Rl`
    of `u`'s early and late ready views, every outcome `W` of `u`'s raw view at the late cutoff, and
    every choice `cov` of one outcome per key of the cover test of `B` over `gv`'s tree: some token
    `u₀` of `Re` has the largest round in it, `cov` says its key covers `B`, no two tokens of `W` of
    one round at least its own have different keys, and `cov` says the key of every token of `Rl` of
    a larger round covers `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_conditions_of_positive :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (p : Bool) (hp : (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ p) (h : p = true)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : (Model.specDraft (V := V)).rawView gv η r late u ⇢ W)
    (cov : Option BlockId → Bool) (hcov : ∀ k, (Model.specDraft (V := V)).head_covers gv.T B k ⇢ cov k), ∃ u₀ ∈ Re,
    (∀ x ∈ Re, x.round ≤ u₀.round) ∧
    cov u₀.key = true ∧
    (∀ x ∈ W, ∀ y ∈ W,
    u₀.round ≤ x.round → x.round = y.round → x.key = y.key) ∧
    (∀ x ∈ Rl, u₀.round < x.round →
    cov x.key = true) := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).conditions_of_positive
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `exists_find_of_head_covers` of `GradesFacts` at `Model.specDraft`: if an outcome `b`
    of the cover test of the root `root` for `X` in the tree `T` is `true`, then `root` resolves in
    `T` to some block `H`, and `X` is an ancestor of `H` or `H` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_exists_find_of_head_covers :
    ∀ {T : Finset (Block V)} {X : Block V} {root : BlockId} (b : Bool) (hb : (Model.specDraft (V := V)).head_covers T X (some root) ⇢ b) (h : b = true), ∃ H : Block V, Block.find? T root = some H ∧ Block.Preceq X H := by
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).exists_find_of_head_covers


/-- The field `head_covers_of_find` of `GradesFacts` at `Model.specDraft`: if the root `root`
    resolves in the tree `T` to the block `H`, and `X` is an ancestor of `H` or `H` itself, then
    every outcome of the cover test of `root` for `X` in `T` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_head_covers_of_find :
    ∀ {T : Finset (Block V)} {X H : Block V} {root : BlockId} (hfind : Block.find? T root = some H) (hXH : Block.Preceq X H) (b : Bool), (Model.specDraft (V := V)).head_covers T X (some root) ⇢ b → b = true := by
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).head_covers_of_find


/-- The field `localCovers_eq_true_iff` of `GradesFacts` at `Model.specDraft`: for every outcome `b`
    of the cover test of the key `k` for the block `B` in the grade view `gv` and every outcome `b'`
    of the head cover test of `k` for `B` over `gv`'s tree, `b` is `true` exactly when `b'` is
    `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_localCovers_eq_true_iff :
    ∀ (gv : (Model.specDraft (V := V)).GV) (k : Option BlockId) (B : Block V) (b : Bool), (Model.specDraft (V := V)).localCovers gv k B ⇢ b → ∀ b' : Bool, (Model.specDraft (V := V)).head_covers gv.T B k ⇢ b' → (b = true ↔ b' = true) := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).localCovers_eq_true_iff
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `opposing_of_late_not_covers` of `GradesFacts` at `Model.specDraft`: if the token `x`
    is in an outcome `Rl` of `u`'s ready view at the cutoff `late`, every token of an outcome `Re`
    of `u`'s ready view at the cutoff `early` has a round at most `x`'s round, and an outcome `b` of
    the cover test of `x`'s key for `B` in `gv`'s tree is not `true`, then every outcome of the
    opposition test of `u` for `B` is `true`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_opposing_of_late_not_covers :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) {x : Protocol.Token (Option BlockId)}
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl) (hx : x ∈ Rl)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re) (hle : ∀ y ∈ Re, y.round ≤ x.round)
    (b : Bool) (hb : (Model.specDraft (V := V)).head_covers gv.T B x.key ⇢ b) (hnot : ¬ b = true) (o : Bool), (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ o → o = true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).opposing_of_late_not_covers
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `positive_of_conditions` of `GradesFacts` at `Model.specDraft`: for outcomes `Re`,
    `W`, `Rl` of `u`'s early ready view, raw view at the late cutoff and late ready view, and a
    choice `cov` of one outcome per key of the cover test of `B` in `gv.T`: every outcome of the
    support test of `u` for `B` in the grade view is `true` if some attestation token `u₀` of `u` is
    in `Re`, every token of `Re` has round at most `u₀`'s, `cov` says `u₀`'s confirmed key covers
    `B`, no two tokens of `W` of one round at least `u₀`'s round carry different keys, and `cov`
    says the key of every token of `Rl` of a round larger than `u₀`'s covers `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_positive_of_conditions :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (u₀ : Protocol.Token (Option BlockId))
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : (Model.specDraft (V := V)).readyView gv F η r early u ⇢ Re)
    (hmem : u₀ ∈ Re) (hlatest : ∀ x ∈ Re, x.round ≤ u₀.round)
    (cov : Option BlockId → Bool) (hcov' : ∀ k, (Model.specDraft (V := V)).head_covers gv.T B k ⇢ cov k)
    (hcov : cov u₀.key = true)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : (Model.specDraft (V := V)).rawView gv η r late u ⇢ W)
    (hclean : ∀ x ∈ W, ∀ y ∈ W,
    u₀.round ≤ x.round → x.round = y.round → x.key = y.key)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : (Model.specDraft (V := V)).readyView gv F η r late u ⇢ Rl)
    (hlater : ∀ x ∈ Rl, u₀.round < x.round →
    cov x.key = true) (p : Bool), (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ p → p = true := by
  intro gv
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).positive_of_conditions
      (gv := gv.val.toProof.toHealing.gradeView)


/-- The field `preceq_of_head_covers_of_find` of `GradesFacts` at `Model.specDraft`: if an outcome
    `b` of the cover test of `root` for `X` in the tree `T` is `true` and `root` resolves in `T` to
    the block `H`, then `X` is an ancestor of `H` or `H` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_of_head_covers_of_find :
    ∀ {T : Finset (Block V)} {X H : Block V} {root : BlockId} (b : Bool) (hb : (Model.specDraft (V := V)).head_covers T X (some root) ⇢ b) (h : b = true) (hfind : Block.find? T root = some H), Block.Preceq X H := by
  sd_rw
  exact (Model.vocabulary_facts_grades (V := V)).preceq_of_head_covers_of_find


/-- The field `Sts_anchor_cases` of `GradesFacts` at `Model.specDraft`: every outcome `A` of
    `Protocol.anchor` at a grade-1 result `g1` is the store's fork-choice root, or `g1` is a
    completed grade-1 root and `A` is an ancestor of it. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_anchor_cases :
    ∀ (S : DecoupledConsensusModel.Execution.Setup V) (stH : (Model.specDraft (V := V)).HS) (r₁ : DecoupledConsensusModel.Round) (g1 : Option (Option (DecoupledConsensusModel.Block V))) (A : DecoupledConsensusModel.Block V), (Model.specDraft (V := V)).anchor S.E S.hc stH r₁ g1 ⇢ A → A = (Model.specDraft (V := V)).get_fg_root stH.toFG ∨ ∃ root, g1 = Option.some (Option.some root) ∧ A.Preceq root := by
  intro S stH r₁ g1 A hA
  rcases g1 with _ | _ | R
  · rw [sd_anchor_of_ne _ _ _ _ _ (by simp), returns_pure] at hA
    exact Or.inl hA
  · rw [sd_anchor_of_ne _ _ _ _ _ (by simp), returns_pure] at hA
    exact Or.inl hA
  · rw [sd_anchor_some, returns_pure] at hA
    cases hp : DecoupledConsensusModel.Protocol.activePrefix
        ((Model.specDraft (V := V)).get_filtered_block_tree stH.toFG) R with
    | none =>
      rw [hp] at hA
      exact Or.inl hA
    | some X =>
      rw [hp] at hA
      subst hA
      exact Or.inr ⟨R, rfl, DecoupledConsensusModel.Sts.preceq_of_activePrefix_eq_some hp⟩


/-- The field `anchor_compatible` of `GradesFacts` at `Model.specDraft`: every outcome `A` of the
    block the grade frame anchors a round at lies on one chain with `T` whenever every grade-1 root
    the frame holds does, and so does the store's fork-choice root. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_anchor_compatible :
    ∀ (S : DecoupledConsensusModel.Execution.Setup V) {stH : (Model.specDraft (V := V)).HS} {T : DecoupledConsensusModel.Block V} {r₁ : DecoupledConsensusModel.Round} {g1 : Option (Option (DecoupledConsensusModel.Block V))}, (∀ (root : DecoupledConsensusModel.Block V), g1 = Option.some (Option.some root) → root.compatible T = Bool.true) → ((Model.specDraft (V := V)).get_fg_root stH.toFG).compatible T = Bool.true → ∀ A : DecoupledConsensusModel.Block V, (Model.specDraft (V := V)).anchor S.E S.hc stH r₁ g1 ⇢ A → A.compatible T = Bool.true := by
  intro S stH T r₁ g1 hroot hfg A hA
  rcases specDraft_Sts_anchor_cases S stH r₁ g1 A hA with rfl | ⟨root, hg, hpre⟩
  · exact hfg
  · exact DecoupledConsensusModel.Protocol.compatible_of_preceq_of_compatible hpre (hroot root hg)


/-- The field `anchor_cases` of `GradesFacts` at `Model.specDraft`: every outcome `a` of the anchor
    read from the grade-1 result `g1` is the store's FG root, or `g1` holds a root `root` whose
    active prefix in the store's filtered tree is a block `A`, and `a` is `A`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_anchor_cases :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) (g1 : Option (Option (Block V)))
    (a : Block V), (Model.specDraft (V := V)).anchor E hc st r g1 ⇢ a → a = (Model.specDraft (V := V)).get_fg_root st.toFG ∨
    ∃ root A, g1 = some (some root) ∧
    (Model.specDraft (V := V)).activePrefix
    ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) root = some A ∧
    a = A := by
  intro E hc st r g1 a ha
  rcases g1 with _ | _ | R
  · rw [sd_anchor_of_ne _ _ _ _ _ (by simp), returns_pure] at ha
    exact Or.inl ha
  · rw [sd_anchor_of_ne _ _ _ _ _ (by simp), returns_pure] at ha
    exact Or.inl ha
  · rw [sd_anchor_some, returns_pure] at ha
    rw [eq_activePrefix]
    cases hp : DecoupledConsensusModel.Protocol.activePrefix
        ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) R with
    | none =>
      rw [hp] at ha
      exact Or.inl ha
    | some X =>
      rw [hp] at ha
      exact Or.inr ⟨R, X, rfl, hp, ha⟩


/-- The field `anchor_eq_of_filtered_fg_root` of `GradesFacts` at `Model.specDraft`: if two stores
    have the same filtered tree and the same FG root, the anchor read from the same grade-1 result
    at the first store can return `x` exactly when the anchor at the second store can return `x`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_anchor_eq_of_filtered_fg_root :
    ∀ (E : Env V) (hc : Protocol.HealConfig) {st st' : (Model.specDraft (V := V)).HS} (r : Round) (g1 : Option (Option (Block V))) (htree : (Model.specDraft (V := V)).get_filtered_block_tree st.toFG =
    (Model.specDraft (V := V)).get_filtered_block_tree st'.toFG) (hroot : (Model.specDraft (V := V)).get_fg_root st.toFG = (Model.specDraft (V := V)).get_fg_root st'.toFG) (x : Block V), (Model.specDraft (V := V)).anchor E hc st r g1 ⇢ x ↔
    (Model.specDraft (V := V)).anchor E hc st' r g1 ⇢ x := by
  intro E hc st st' r g1 htree hroot x
  rcases g1 with _ | _ | R
  · rw [sd_anchor_of_ne _ _ _ _ _ (by simp), sd_anchor_of_ne _ _ _ _ _ (by simp), hroot]
  · rw [sd_anchor_of_ne _ _ _ _ _ (by simp), sd_anchor_of_ne _ _ _ _ _ (by simp), hroot]
  · rw [sd_anchor_some, sd_anchor_some, htree, hroot]


/-- The field `anchor_of_activePrefix` of `GradesFacts` at `Model.specDraft`: if the grade-1 result
    is the completed root `root`, and the active prefix of `root` in the store's filtered block tree
    is `A`, then every outcome `a` of the anchor is `A`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_anchor_of_activePrefix :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {root A : Block V} (h : (Model.specDraft (V := V)).activePrefix ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) root = some A) (a : Block V), (Model.specDraft (V := V)).anchor E hc st r (some (some root)) ⇢ a → a = A := by
  intro E hc st r root A h a ha
  rw [sd_anchor_some, returns_pure] at ha
  rw [eq_activePrefix] at h
  have h' : DecoupledConsensusModel.Protocol.activePrefix
      ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) root = some A := h
  rw [ha, h']
  rfl


/-- The field `preceq_anchor_of_fgRoot` of `GradesFacts` at `Model.specDraft`: if `P` is an ancestor
    of the store's fork-choice root or that block itself, then `P` is an ancestor of every outcome
    `a` of the anchor of round `r` or `a` itself, whatever the frame's grade-1 result. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_anchor_of_fgRoot :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) (g1 : Option (Option (Block V))) {P : Block V} (hP : Block.Preceq P ((Model.specDraft (V := V)).get_fg_root st.toFG)) (a : Block V), (Model.specDraft (V := V)).anchor E hc st r g1 ⇢ a → Block.Preceq P a := by
  intro E hc st r g1 P hP a ha
  rcases specDraft_anchor_cases E hc st r g1 a ha with rfl | ⟨root, A, -, hA, rfl⟩
  · exact hP
  · rw [eq_activePrefix] at hA
    have hm := DecoupledConsensusModel.Sts.mem_of_activePrefix_eq_some hA
    exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      (DecoupledConsensusModel.Block.preceq_trans
        (DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hP)
        (DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
          (sd_fg_root_preceq_of_mem_filtered hm)))


/-- The field `preceq_anchor_of_g1` of `GradesFacts` at `Model.specDraft`: if `P` is in the store's
    filtered tree and is an ancestor of `e` or `e` itself, then `P` is an ancestor of every outcome
    `a` of the anchor of round `r` at the grade-1 result `e`, or `a` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_anchor_of_g1 :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {P e : Block V} (hPt : P ∈ (Model.specDraft (V := V)).get_filtered_block_tree st.toFG) (hPe : Block.Preceq P e) (a : Block V), (Model.specDraft (V := V)).anchor E hc st r (some (some e)) ⇢ a → Block.Preceq P a := by
  intro E hc st r P e hPt hPe' a ha
  have hPe := DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hPe'
  rw [sd_anchor_some, returns_pure] at ha
  subst ha
  have hPm : P ∈ ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG).filter
      (fun B => DecoupledConsensusModel.Block.preceq B e = true) := Finset.mem_filter.2 ⟨hPt, hPe⟩
  have hchain : ∀ Y ∈ ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG).filter
      (fun B => DecoupledConsensusModel.Block.preceq B e = true),
      DecoupledConsensusModel.Block.preceq Y e = true :=
    fun Y hY => (Finset.mem_filter.1 hY).2
  cases hp : DecoupledConsensusModel.Protocol.activePrefix
      ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) e with
  | none =>
    exfalso
    unfold DecoupledConsensusModel.Protocol.activePrefix at hp
    have hs := DecoupledConsensusModel.Proofs.HealingSurface.deepest?_isSome_of_chain hchain ⟨P, hPm⟩
    rw [hp] at hs
    exact Bool.false_ne_true hs
  | some G =>
    simp only [Option.getD_some]
    unfold DecoupledConsensusModel.Protocol.activePrefix at hp
    have hGm := Finset.mem_filter.1 (DecoupledConsensusModel.Proofs.Engine.deepest?_mem hp)
    exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      (DecoupledConsensusModel.Proofs.HealingLemmas.deepest?_dominates hp hPm
        (DecoupledConsensusModel.Block.compatible_of_preceq_common hPe hGm.2))


/-- The field `grade2Block_some` of `GradesFacts` at `Model.specDraft`: if an outcome of the grade-2
    block the frame `frame` gives the store `st` is `some Q`, then the frame's grade-2 result is a
    completed root `clipped`, and `Q` is an ancestor of `clipped` or `clipped` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_grade2Block_some :
    ∀ {st : (Model.specDraft (V := V)).HS} {frame : (Model.specDraft (V := V)).Frame} {Q : Block V} (o : Option (Block V)) (ho : (Model.specDraft (V := V)).grade2Block st frame ⇢ o) (h : o = some Q), ∃ clipped : Block V, frame.g2 = some (some clipped) ∧ Block.Preceq Q clipped := by
  intro st frame Q o ho h
  obtain ⟨R, hR, -, hQR⟩ := sd_grade2Block_some ho h
  exact ⟨R, hR, hQR⟩

/-- If the results `r` and `r'` have the same image under `GradeResult.toProof`, then
    `st.resultOfImage r = st.resultOfImage r'`. -/
theorem _root_.SpecDraftRecord.GradesFacts.resultOfImage_eq_of_toProof
    (st : Spec.Store V) {r r' : Spec.GradeResult V} (h : r.toProof = r'.toProof) :
    st.resultOfImage r = st.resultOfImage r' := by
  cases r with
  | pending =>
    cases r' with
    | pending => rfl
    | computed G' => simp [Spec.GradeResult.toProof] at h
  | computed G =>
    cases r' with
    | pending => simp [Spec.GradeResult.toProof] at h
    | computed G' =>
      simp only [Spec.GradeResult.toProof, Option.some.injEq] at h
      simp only [Spec.Store.resultOfImage]
      congr 1
      have h' := congrArg (Option.map st.blockOfImage) h
      simp only [Option.map_map] at h'
      exact h'

/-- The field `grade2Block_eq_of_phases` of `GradesFacts` at `Model.specDraft`: if the frames
    `frame` and `frame'` have the same grade-0, grade-1 and grade-2 results, then on every store
    `st` the grade-2 block of the two frames has the same outcomes. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_grade2Block_eq_of_phases :
    ∀ {st : (Model.specDraft (V := V)).HS} {frame frame' : (Model.specDraft (V := V)).Frame},
      frame.g0 = frame'.g0 → frame.g1 = frame'.g1 → frame.g2 = frame'.g2 →
      ∀ o, (Model.specDraft (V := V)).grade2Block st frame ⇢ o ↔
        (Model.specDraft (V := V)).grade2Block st frame' ⇢ o := by
  intro st f f' h0 h1 h2 o
  have e0 : Spec.GradeResult.toProof (Spec.RoundGrades.g0 f) =
      Spec.GradeResult.toProof (Spec.RoundGrades.g0 f') := h0
  have e1 : Spec.GradeResult.toProof (Spec.RoundGrades.g1 f) =
      Spec.GradeResult.toProof (Spec.RoundGrades.g1 f') := h1
  have e2 : Spec.GradeResult.toProof (Spec.RoundGrades.g2 f) =
      Spec.GradeResult.toProof (Spec.RoundGrades.g2 f') := h2
  have hf : st.val.roundGradesOfImage f = st.val.roundGradesOfImage f' := by
    simp only [Spec.Store.roundGradesOfImage]
    rw [SpecDraftRecord.GradesFacts.resultOfImage_eq_of_toProof st.val e0,
      SpecDraftRecord.GradesFacts.resultOfImage_eq_of_toProof st.val e1,
      SpecDraftRecord.GradesFacts.resultOfImage_eq_of_toProof st.val e2]
  change SpecDraftRecord.Member.grade2Block st.val f ⇢ o ↔
    SpecDraftRecord.Member.grade2Block st.val f' ⇢ o
  unfold SpecDraftRecord.Member.grade2Block
  rw [hf]


/-- The field `grade2Block_preceq_root` of `GradesFacts` at `Model.specDraft`: if an outcome of
    `Protocol.grade2Block stH frame` is `some Q`, the frame's grade-2 entry is a block `root` and
    `Q` is an ancestor of it. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_grade2Block_preceq_root :
    ∀ {stH : (Model.specDraft (V := V)).HS} {frame : (Model.specDraft (V := V)).Frame} {Q : Block V} (o : Option (Block V)) (ho : (Model.specDraft (V := V)).grade2Block stH frame ⇢ o) (hQ : o = some Q), ∃ root : Block V, frame.g2 = some (some root) ∧ Block.Preceq Q root := by
  intro stH frame Q o ho hQ
  obtain ⟨R, hR, -, hQR⟩ := sd_grade2Block_some ho hQ
  exact ⟨R, hR, hQR⟩


/-- The field `mem_filtered_of_grade2Block` of `GradesFacts` at `Model.specDraft`: if an outcome of
    the grade-2 block the frame `frame` gives the store `st` is `some Q`, then `Q` is in `st`'s
    filtered tree. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_mem_filtered_of_grade2Block :
    ∀ {st : (Model.specDraft (V := V)).HS} {frame : (Model.specDraft (V := V)).Frame} {Q : Block V} (o : Option (Block V)) (ho : (Model.specDraft (V := V)).grade2Block st frame ⇢ o) (h : o = some Q), Q ∈ (Model.specDraft (V := V)).get_filtered_block_tree st.toFG := by
  intro st frame Q o ho h
  exact (sd_grade2Block_some ho h).choose_spec.2.1


/-- The field `Q2_compatible` of `GradesFacts` at `Model.specDraft`: a grade-2 candidate `Q` that an
    outcome of the frame's grade-2 block offers lies on one chain with `T` whenever the grade-2 root
    it was computed from does. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Q2_compatible :
    ∀ {stH : (Model.specDraft (V := V)).HS} {T : Block V} {frame : (Model.specDraft (V := V)).Frame} (hg2 : ∀ root : Block V, frame.g2 = some (some root) → Block.compatible root T = true) {Q : Block V} (o : Option (Block V)) (ho : (Model.specDraft (V := V)).grade2Block stH frame ⇢ o) (hQ : o = some Q), Block.compatible Q T = true := by
  intro stH T frame hg2 Q o ho hQ
  obtain ⟨R, hR, -, hQR⟩ := sd_grade2Block_some ho hQ
  exact DecoupledConsensusModel.Protocol.compatible_of_preceq_of_compatible hQR (hg2 R hR)


/-- The field `fgRoot_preceq_grade2Block` of `GradesFacts` at `Model.specDraft`: if an outcome of
    the frame's grade-2 block at the store `st` is `some q`, then the store's fork-choice root is an
    ancestor of `q` or `q` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_fgRoot_preceq_grade2Block :
    ∀ {st : (Model.specDraft (V := V)).HS} {frame : (Model.specDraft (V := V)).Frame} {q : Block V} (o : Option (Block V)) (ho : (Model.specDraft (V := V)).grade2Block st frame ⇢ o) (h : o = some q), Block.Preceq ((Model.specDraft (V := V)).get_fg_root st.toFG) q := by
  intro st frame q o ho h
  obtain ⟨-, -, hm, -⟩ := sd_grade2Block_some ho h
  exact sd_fg_root_preceq_of_mem_filtered hm


/-- The field `Sts_currentSGVote_of_Q2` of `GradesFacts` at `Model.specDraft`: if the clearing walk
    from the anchor finds no block on the store's confirmed chain and the grade read offers the
    grade-2 candidate `Q`, the SG walk returns `Q`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_currentSGVote_of_Q2 :
    ∀ {stH : (Model.specDraft (V := V)).HS} {grades : DecoupledConsensusModel.Protocol.GradeRead V} {Q : DecoupledConsensusModel.Block V}, (Model.specDraft (V := V)).deepest_clear (Option.some grades.anchor) stH.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = Option.none → grades.Q2 = Option.some Q → (Model.specDraft (V := V)).currentSGVote stH grades = Q := by
  intro stH grades Q h hQ
  exact (sd_currentSGVote_none stH grades (sd_deepest_clear_none stH grades h)).1 Q hQ


/-- The field `currentSGVote_of_Q2` of `GradesFacts` at `Model.specDraft`: if no block on the
    store's live confirmed chain descends from the read's anchor and passes the read's clearance
    test, and the read's grade-2 candidate is `Q`, the selected SG vote is `Q`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_currentSGVote_of_Q2 :
    ∀ {st : (Model.specDraft (V := V)).HS} {grades : Protocol.GradeRead V} {Q : Block V} (h : (Model.specDraft (V := V)).deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = none) (hQ : grades.Q2 = some Q), (Model.specDraft (V := V)).currentSGVote st grades = Q := by
  intro st grades Q h hQ
  exact (sd_currentSGVote_none st grades (sd_deepest_clear_none st grades h)).1 Q hQ


/-- The field `currentSGVote_of_none_none` of `GradesFacts` at `Model.specDraft`: if the clearing
    walk finds no block and the grade read offers no grade-2 candidate, the SG walk returns the
    block the store's fork-choice walk starts from, or the grade read's anchor. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_currentSGVote_of_none_none :
    ∀ {stH : (Model.specDraft (V := V)).HS} {grades : DecoupledConsensusModel.Protocol.GradeRead V}, (Model.specDraft (V := V)).deepest_clear (Option.some grades.anchor) stH.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = Option.none → grades.Q2 = Option.none → (Model.specDraft (V := V)).currentSGVote stH grades = (Model.specDraft (V := V)).get_fg_root stH.toFG ∨ (Model.specDraft (V := V)).currentSGVote stH grades = grades.anchor := by
  intro stH grades h hQ
  have k := sd_currentSGVote_none stH grades (sd_deepest_clear_none stH grades h)
  by_cases hr : grades.rawG2
  · exact Or.inl (k.2.1 hQ hr)
  · exact Or.inr (k.2.2 hQ hr)


/-- The field `currentSGVote_of_not_rawG2` of `GradesFacts` at `Model.specDraft`: if no block on the
    store's live confirmed chain descends from the read's anchor and passes the read's clearance
    test, the read has no grade-2 candidate, and the read reports no raw grade-2 result, the
    selected SG vote is the read's anchor. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_currentSGVote_of_not_rawG2 :
    ∀ {st : (Model.specDraft (V := V)).HS} {grades : Protocol.GradeRead V} (h : (Model.specDraft (V := V)).deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = none) (hQ : grades.Q2 = none) (hraw : ¬ grades.rawG2), (Model.specDraft (V := V)).currentSGVote st grades = grades.anchor := by
  intro st grades h hQ hraw
  exact (sd_currentSGVote_none st grades (sd_deepest_clear_none st grades h)).2.2 hQ hraw


/-- The field `currentSGVote_of_rawG2` of `GradesFacts` at `Model.specDraft`: if no block on the
    store's live confirmed chain descends from the read's anchor and passes the read's clearance
    test, the read has no grade-2 candidate, and the read reports a raw grade-2 result, the selected
    SG vote is the FG root of the store. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_currentSGVote_of_rawG2 :
    ∀ {st : (Model.specDraft (V := V)).HS} {grades : Protocol.GradeRead V} (h : (Model.specDraft (V := V)).deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = none) (hQ : grades.Q2 = none) (hraw : grades.rawG2), (Model.specDraft (V := V)).currentSGVote st grades = (Model.specDraft (V := V)).get_fg_root st.toFG := by
  intro st grades h hQ hraw
  exact (sd_currentSGVote_none st grades (sd_deepest_clear_none st grades h)).2.1 hQ hraw


/-- The field `sgVote_compatible` of `GradesFacts` at `Model.specDraft`: the SG walk's output lies
    on one chain with `T` whenever the store's confirmed block lies on one chain with `T`, every
    grade-2 candidate the frame offers lies on one chain with `T`, and so do the frame's anchor
    block and the store's fork-choice root. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_sgVote_compatible :
    ∀ {stH : (Model.specDraft (V := V)).HS} {grades : DecoupledConsensusModel.Protocol.GradeRead V} {T : DecoupledConsensusModel.Block V}, stH.toFG.toSG.toGoldfishStore.live_confirmed.compatible T = Bool.true → (∀ (Q : DecoupledConsensusModel.Block V), grades.Q2 = Option.some Q → Q.compatible T = Bool.true) → grades.anchor.compatible T = Bool.true → ((Model.specDraft (V := V)).get_fg_root stH.toFG).compatible T = Bool.true → ((Model.specDraft (V := V)).currentSGVote stH grades).compatible T = Bool.true := by
  intro stH grades T hC hQ hA hfg
  cases hD : Spec.Protocol.deepest_clear (stH.val.blockOfImage grades.anchor)
      (Spec.Store.ofImage stH.val).live_confirmed (fun B => grades.clear B.toProof) with
  | some D =>
    obtain ⟨e, hDC, -⟩ := sd_currentSGVote_some stH grades hD
    rw [e]
    exact DecoupledConsensusModel.Protocol.compatible_of_preceq_of_compatible hDC hC
  | none =>
    have k := sd_currentSGVote_none stH grades hD
    cases hq : grades.Q2 with
    | some Q =>
      rw [k.1 Q hq]
      exact hQ Q hq
    | none =>
      by_cases hr : grades.rawG2
      · rw [k.2.1 hq hr]
        exact hfg
      · rw [k.2.2 hq hr]
        exact hA


/-- The field `preceq_currentSGVote_of_cases` of `GradesFacts` at `Model.specDraft`: if `P` is an
    ancestor of the read's anchor, an ancestor of the read's grade-2 block whenever there is one,
    and an ancestor of the store's fork-choice root when there is none, then `P` is an ancestor of
    the SG vote `currentSGVote st grades` or that block itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_currentSGVote_of_cases :
    ∀ {st : (Model.specDraft (V := V)).HS} {grades : Protocol.GradeRead V} {P : Block V} (hA : Block.Preceq P grades.anchor) (hQ : ∀ q : Block V, grades.Q2 = some q → Block.Preceq P q) (hR : grades.Q2 = none → Block.Preceq P ((Model.specDraft (V := V)).get_fg_root st.toFG)), Block.Preceq P ((Model.specDraft (V := V)).currentSGVote st grades) := by
  intro st grades P hA hQ hR
  cases hD : Spec.Protocol.deepest_clear (st.val.blockOfImage grades.anchor)
      (Spec.Store.ofImage st.val).live_confirmed (fun B => grades.clear B.toProof) with
  | some D =>
    obtain ⟨e, -, hAD⟩ := sd_currentSGVote_some st grades hD
    rw [e]
    exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      (DecoupledConsensusModel.Block.preceq_trans
        (DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hA)
        (DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hAD))
  | none =>
    have k := sd_currentSGVote_none st grades hD
    cases hq : grades.Q2 with
    | some Q =>
      rw [k.1 Q hq]
      exact hQ Q hq
    | none =>
      by_cases hr : grades.rawG2
      · rw [k.2.1 hq hr]
        exact hR hq
      · rw [k.2.2 hq hr]
        exact hA


/-- The field `gradeView_timestamp_block` of `GradesFacts` at `Model.specDraft`: the block timestamp
    map of the grade view read from a store's healing view is that store's block timestamp map. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_gradeView_timestamp_block :
    ∀ (st : (Model.specDraft (V := V)).S), ((Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing st)).timestamp_block = st.timestamp_block := by
  intro st
  rfl


/-- The field `ModelProperties_exists_mem_T_preceq_of_gradeBool` of `GradesFacts` at
    `Model.specDraft`: if an outcome `b` of the local grade of `Q` at the healing store `st` is
    `true`, then some block `H` of `st`'s tree has `Q` as an ancestor or is `Q` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_ModelProperties_exists_mem_T_preceq_of_gradeBool :
    ∀ (E : Env V) (st : (Model.specDraft (V := V)).HS) (F : Block V) (eta r : Round) (early late : Time) {Q : Block V} (b : Bool) (hb : (Model.specDraft (V := V)).gradeBool E ((Model.specDraft (V := V)).gradeView st) F eta r early late Q ⇢ b) (h : b = true), ∃ H ∈ st.toFG.toSG.toGoldfishStore.T, Block.Preceq Q H := by
  intro E st F eta r early late Q b hb h
  have := specDraft_Sts_exists_mem_T_preceq_of_gradeBool E ((Model.specDraft (V := V)).gradeView st)
    F eta r early late Q b hb h
  rwa [specDraft_ModelProperties_gradeView_T] at this


/-- The field `frameStableRoot_exists` of `GradesFacts` at `Model.specDraft`: for every cache `c`,
    store `st` and round `r`, every outcome `x` of the stable root `frameStableRoot c E hc st r` is
    `some G` for some block `G`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_frameStableRoot_exists :
    ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) (x : Option (Block V)), (Model.specDraft (V := V)).frameStableRoot c E hc st r ⇢ x → ∃ G : Block V, x = some G := by
  intro c E hc st r x hx
  obtain ⟨B, -, rfl⟩ := sd_except_map_ok ((SpecDraftRecord.returns_successOutcomes _ _).mp hx)
  exact ⟨_, rfl⟩


/-- The field `runtime_Q2_mem` of `GradesFacts` at `Model.specDraft`: if an outcome `g` of the grade
    read that the frame contract of the cache `cache` gives at the healing store `st` for round `r`
    has the grade-2 candidate `B`, then `B` is in `st`'s tree. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_runtime_Q2_mem :
    ∀ (cache : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) (B : Block V) (g : Protocol.GradeRead V) (hg : ((Model.specDraft (V := V)).frameContract cache).read E hc st r ⇢ g) (h : g.Q2 = some B), B ∈ st.toFG.toSG.toGoldfishStore.T := by
  intro cache E hc st r B g hg h
  obtain ⟨G, hG, rfl⟩ := sd_except_map_ok ((SpecDraftRecord.returns_successOutcomes _ _).mp hg)
  change G.Q2.map Spec.Block.toProof = some B at h
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.mp h
  show Y.toProof ∈ SpecDraftRecord.Member.gs_T st.val
  unfold SpecDraftRecord.Member.gs_T
  rw [SpecDraftRecord.toProof_gs_T]
  exact Finset.mem_image_of_mem _ (draft_round_grade_read_Q2_mem hG hY)


/-- The field `frameSGCandidate_stableRoot` of `GradesFacts` at `Model.specDraft`: if an outcome of
    the frame contract's select candidate of the cache `c` at the store `st` and any slot is
    `some G`, then every outcome of the stable root of `c` at `st` for the round of `st`'s slot is
    `some G`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_frameSGCandidate_stableRoot :
    ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (slot : Slot) {G : Block V} (o : Option (Block V)) (ho : (Model.specDraft (V := V)).frameSGCandidate c E hc ((Model.specDraft (V := V)).toHealing st) slot ⇢ o) (h : o = some G) (x : Option (Block V)), (Model.specDraft (V := V)).frameStableRoot c E hc ((Model.specDraft (V := V)).toHealing st) (((Model.specDraft (V := V)).round_of hc st.s)) ⇢ x → x = some G := by
  intro c E hc st slot G o ho h x hx
  subst h
  obtain ⟨o', ho1, ho2⟩ := sd_except_map_ok ((SpecDraftRecord.returns_successOutcomes _ _).mp ho)
  obtain ⟨B, hB1, rfl⟩ := sd_except_map_ok ((SpecDraftRecord.returns_successOutcomes _ _).mp hx)
  obtain ⟨Y, rfl, rfl⟩ := Option.map_eq_some_iff.mp ho2.symm
  have hr : (Model.specDraft (V := V)).round_of hc st.s =
      (Spec.Config.toSpec E hc SpecDraftRecord.unreadHeightConfig).round_of
        ((Model.specDraft (V := V)).toHealing st).val.s := rfl
  rw [hr] at hB1
  rw [draft_stable_root_of_candidate _ _ ho1 hB1]


/-- The field `onPhaseTick_round` of `GradesFacts` at `Model.specDraft`: every outcome `c'` of the
    cache a phase tick at `t` leaves has the round of `t`'s slot as its round. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_onPhaseTick_round :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache) (c' : (Model.specDraft (V := V)).Cache), (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c' → c'.round = ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) := by
  intro E hc st t c c' hc'
  obtain ⟨S, hS, rfl⟩ := sd_except_map_ok ((SpecDraftRecord.returns_successOutcomes _ _).mp hc')
  have h := (SpecDraftRecord.NoRaise.update_grades_results hS).1
  show S.saved_grades.round = _
  rw [h, eq_round_of]
  simp only [SpecDraftRecord.NoRaise.roundAt, Spec.Config.round_of,
    Spec.Config.toSpec_slotOf, Spec.Config.toSpec_R]
  show _ = DecoupledConsensusModel.Protocol.HealConfig.round_of hc (E.slotOf t)
  unfold DecoupledConsensusModel.Protocol.HealConfig.round_of
  rfl

/-! ## The frame read through the tree, the grade-2 candidate, the phase tick -/

section MembersTwo

open SpecDraftRecord.GradesFacts

/-- A store `st` of `Model.specDraft` meets three conditions on its tree: no two tree blocks have
    one image, the tree holds the parent of each of its blocks, and the finalized block is a tree
    block. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_tree_hyps (st : (Model.specDraft (V := V)).HS) :
    Set.InjOn (Spec.Block.toProof (V := V))
        (↑st.val.T : Set (Spec.Block V)) ∧
      SpecDraftRecord.NoRaise.ParentClosed st.val.T ∧ st.val.F ∈ st.val.T :=
  ⟨SpecDraftRecord.NoRaise.DistinctRoots.injOn_toProof st.property.2.1, st.property.2.2.1,
    st.property.2.2.2⟩

/-- The finalized block of a store `st` of `Model.specDraft` is the finalized block of its image
    under `toProof`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_F_ok (st : (Model.specDraft (V := V)).HS) :
    Model.FGS.F (Model.HS.toFG st) =
      Model.FGS.F (Model.HS.toFG (M := Model.vocabulary (V := V))
        (Spec.Store.toProof st.val).toHealing) :=
  (SpecDraftRecord.toProof_fg_F st.val).symm

/-- The image of the grades of round `r` read by `readFrame` from `c` against `st` is the grades of
    round `r` read from the image of `c` against the image of `st`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_readFrame (c : (Model.specDraft (V := V)).Cache)
    (st : (Model.specDraft (V := V)).HS) (r : DecoupledConsensusModel.Round) :
    Spec.RoundGrades.toProof ((Model.specDraft (V := V)).readFrame c st r) =
      (Model.vocabulary (V := V)).readFrame (Spec.SavedGrades.toProof c)
        (Spec.Store.toProof st.val).toHealing r := by
  obtain ⟨hinj, hpar, hF⟩ := sd_tree_hyps st
  exact SpecDraftRecord.GradesImages.toProof_readFrame_ofImage st.val hinj hpar hF c r

/-- The field `readFrame_g2` of `GradesFacts` at `Model.specDraft`: the grade-2 result of the
    round-`r` frame read from the cache `c` at `st` is the grade-2 result of `c`'s frame for round
    `r`, clipped to `st`'s finalized block. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_g2 : ∀ (c : (Model.specDraft (V := V)).Cache) (st : (Model.specDraft (V := V)).HS) (r : Round), ((Model.specDraft (V := V)).readFrame c st r).g2 =
    (Model.specDraft (V := V)).clipResult st.toFG.F
    ((Model.specDraft (V := V)).cacheAtRound c r).g2 := by
  intro c st r
  rw [sd_frame_g2, sd_readFrame, eq_clipResult, sd_frame_g2, sd_cacheAtRound, sd_F_ok]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_g2 (Spec.SavedGrades.toProof c)
    (Spec.Store.toProof st.val).toHealing r

/-- The field `readFrame_phase` of `GradesFacts` at `Model.specDraft`: for every phase `p`, the
    result for `p` of the round-`r` frame read from the cache `c` at `st` is the result for `p` of
    `c`'s frame for round `r`, clipped to `st`'s finalized block. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_phase : ∀ (c : (Model.specDraft (V := V)).Cache) (st : (Model.specDraft (V := V)).HS) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase), (Model.specDraft (V := V)).phaseResult
    ((Model.specDraft (V := V)).readFrame c st r) p =
    (Model.specDraft (V := V)).clipResult st.toFG.F
    ((Model.specDraft (V := V)).phaseResult
    ((Model.specDraft (V := V)).cacheAtRound c r) p) := by
  intro c st r p
  rw [sd_phaseResult, sd_readFrame, eq_clipResult, sd_phaseResult, sd_cacheAtRound, sd_F_ok]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_phase (Spec.SavedGrades.toProof c)
    (Spec.Store.toProof st.val).toHealing r p

/-- The field `readFrame_g1_of_cache` of `GradesFacts` at `Model.specDraft`: if the cache `c` holds
    the grade-1 root `e` for round `r`, the round-`r` frame read from `c` at the store `st` holds
    `Protocol.clipGrade e st.F` as its grade-1 root. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_g1_of_cache : ∀ {c : (Model.specDraft (V := V)).Cache} {st : (Model.specDraft (V := V)).HS} {r : Round} {e : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) .g1 = some (some e)), ((Model.specDraft (V := V)).readFrame c st r).g1 = some (some ((Model.specDraft (V := V)).clipGrade e st.toFG.F)) := by
  intro c st r e h
  rw [sd_phaseResult, sd_cacheAtRound] at h
  rw [sd_frame_g1, sd_readFrame, eq_clipGrade, sd_F_ok]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_g1_of_cache (st := (Spec.Store.toProof st.val).toHealing) h

/-- The field `readFrame_g1_provenance` of `GradesFacts` at `Model.specDraft`: if the round-`r`
    frame read from the cache `c` at the store `st` holds the grade-1 root `root`, then the cache's
    own round-`r` frame holds a grade-1 root `root₀` of which `root` is an ancestor. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_g1_provenance : ∀ (c : (Model.specDraft (V := V)).Cache) (st : (Model.specDraft (V := V)).HS) (r : Round) {root : Block V} (h : ((Model.specDraft (V := V)).readFrame c st r).g1 = some (some root)), ∃ root₀ : Block V,
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) .g1 = some (some root₀) ∧
    Block.Preceq root root₀ := by
  intro c st r root h
  rw [sd_frame_g1, sd_readFrame] at h
  simp only [sd_phaseResult, sd_cacheAtRound]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_g1_provenance (Spec.SavedGrades.toProof c)
    (Spec.Store.toProof st.val).toHealing r h

/-- The field `readFrame_g2_of_cache` of `GradesFacts` at `Model.specDraft`: if the cache `c` holds
    the grade-2 root `e` for round `r`, the round-`r` frame read from `c` at the store `st` holds
    `Protocol.clipGrade e st.F` as its grade-2 root. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_g2_of_cache : ∀ {c : (Model.specDraft (V := V)).Cache} {st : (Model.specDraft (V := V)).HS} {r : Round} {e : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) .g2 = some (some e)), ((Model.specDraft (V := V)).readFrame c st r).g2 = some (some ((Model.specDraft (V := V)).clipGrade e st.toFG.F)) := by
  intro c st r e h
  rw [sd_phaseResult, sd_cacheAtRound] at h
  rw [sd_frame_g2, sd_readFrame, eq_clipGrade, sd_F_ok]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_g2_of_cache (st := (Spec.Store.toProof st.val).toHealing) h

/-- The field `readFrame_g2_provenance` of `GradesFacts` at `Model.specDraft`: if the round-`r`
    frame read from the cache `c` at the store `st` holds the grade-2 root `root`, then the cache's
    own round-`r` frame holds a grade-2 root `root₀` of which `root` is an ancestor. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_g2_provenance : ∀ (c : (Model.specDraft (V := V)).Cache) (st : (Model.specDraft (V := V)).HS) (r : Round) {root : Block V} (h : ((Model.specDraft (V := V)).readFrame c st r).g2 = some (some root)), ∃ root₀ : Block V,
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) .g2 = some (some root₀) ∧
    Block.Preceq root root₀ := by
  intro c st r root h
  rw [sd_frame_g2, sd_readFrame] at h
  simp only [sd_phaseResult, sd_cacheAtRound]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_g2_provenance (Spec.SavedGrades.toProof c)
    (Spec.Store.toProof st.val).toHealing r h

/-- The field `readFrame_phase_of_cache` of `GradesFacts` at `Model.specDraft`: if the cache `c`
    holds the root `e` for round `r` and the phase `p`, the round-`r` frame read from `c` at the
    store `st` holds `Protocol.clipGrade e st.F` for that phase. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_phase_of_cache : ∀ {c : (Model.specDraft (V := V)).Cache} {st : (Model.specDraft (V := V)).HS} {r : Round} {p : Protocol.Phase} {e : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some (some e)), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).readFrame c st r) p
    = some (some ((Model.specDraft (V := V)).clipGrade e st.toFG.F)) := by
  intro c st r p e h
  rw [sd_phaseResult, sd_cacheAtRound] at h
  rw [sd_phaseResult, sd_readFrame, eq_clipGrade, sd_F_ok]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_phase_of_cache (st := (Spec.Store.toProof st.val).toHealing) h

/-- The field `readFrame_phase_provenance` of `GradesFacts` at `Model.specDraft`: if the round-`r`
    frame read from the cache `c` at the store `st` holds the root `root` for the phase `p`, then
    the cache's own round-`r` frame holds a root `root₀` for `p`, and `root` is an ancestor of
    `root₀` or `root₀` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_readFrame_phase_provenance : ∀ (c : (Model.specDraft (V := V)).Cache) (st : (Model.specDraft (V := V)).HS) (r : Round) {p : Protocol.Phase} {root : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).readFrame c st r) p = some (some root)), ∃ root₀ : Block V,
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some (some root₀) ∧
    Block.Preceq root root₀ := by
  intro c st r p root h
  rw [sd_phaseResult, sd_readFrame] at h
  simp only [sd_phaseResult, sd_cacheAtRound]
  exact (Model.vocabulary_facts_grades (V := V)).readFrame_phase_provenance (Spec.SavedGrades.toProof c)
    (Spec.Store.toProof st.val).toHealing r h

/-- The outcomes of `Model.specDraft`'s `grade2Block` at a store `st` and round grades `fr`: the
    deepest block of the filtered tree that is an ancestor of `fr`'s grade-2 block, if any. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_grade2Block_iff {st : (Model.specDraft (V := V)).HS}
    {fr : Spec.RoundGrades V} {o : Option (DecoupledConsensusModel.Block V)} :
    (Model.specDraft (V := V)).grade2Block st fr ⇢ o ↔
      o = ((Model.Frame.g2 (M := Model.specDraft (V := V)) fr).bind id).bind
        (DecoupledConsensusModel.Protocol.activePrefix
          ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG)) := by
  obtain ⟨hinj, hpar, hF⟩ := sd_tree_hyps st
  have hfill : ∀ g : Spec.GradeResult V, ∃ G, SpecDraftRecord.fillResult g = .computed G :=
    by rintro (_ | G) <;> exact ⟨_, rfl⟩
  obtain ⟨G0, h0⟩ := hfill (st.val.roundGradesOfImage fr).g0
  obtain ⟨G1, h1⟩ := hfill (st.val.roundGradesOfImage fr).g1
  have h2 : SpecDraftRecord.fillResult (st.val.roundGradesOfImage fr).g2 =
      .computed (((Model.Frame.g2 (M := Model.specDraft (V := V)) fr).bind id).map
        st.val.blockOfImage) := by
    show SpecDraftRecord.fillResult (st.val.resultOfImage fr.g2) =
      .computed ((fr.g2.toProof.bind id).map _)
    rcases fr.g2 with _ | _ | X <;> rfl
  have hfr : SpecDraftRecord.fillRound (st.val.roundGradesOfImage fr) =
      ⟨.computed G0, .computed G1, .computed
        (((Model.Frame.g2 (M := Model.specDraft (V := V)) fr).bind id).map st.val.blockOfImage)⟩ := by
    simp only [SpecDraftRecord.fillRound, h0, h1, h2]
  have he : Except.map (Option.map Spec.Block.toProof)
      (Spec.Protocol.grade2Block (Spec.Store.ofImage st.val)
        (SpecDraftRecord.fillRound (st.val.roundGradesOfImage fr))) =
      .ok (((Model.Frame.g2 (M := Model.specDraft (V := V)) fr).bind id).bind
        (DecoupledConsensusModel.Protocol.activePrefix
          ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG))) := by
    rw [hfr]
    change Except.ok ((Spec.Protocol.active_prefix (Spec.Store.ofImage st.val) _).map
      Spec.Block.toProof) = _
    congr 1
    rcases ((Model.Frame.g2 (M := Model.specDraft (V := V)) fr).bind id) with _ | x
    · rfl
    · exact Spec.Protocol.activePrefix_blockOfImage (Spec.Store.ofImage st.val) hinj hpar
        (SpecDraftRecord.GradesImages.filtered_subset (Spec.Store.ofImage st.val)) x
  show Returns (SpecDraftRecord.successOutcomes (Except.map (Option.map Spec.Block.toProof)
      (Spec.Protocol.grade2Block (Spec.Store.ofImage st.val)
        (SpecDraftRecord.fillRound (st.val.roundGradesOfImage fr))))) o ↔ _
  rw [SpecDraftRecord.returns_successOutcomes, he]
  constructor
  · intro h; exact (Except.ok.inj h).symm
  · intro h; rw [h]

/-- The field `grade2Block_eq_of_filtered_eq` of `GradesFacts` at `Model.specDraft`: two stores with
    the same filtered tree have the same outcomes of the grade-2 candidate of a frame. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_grade2Block_eq_of_filtered_eq : ∀ {st st' : (Model.specDraft (V := V)).HS} (frame : (Model.specDraft (V := V)).Frame) (h : (Model.specDraft (V := V)).get_filtered_block_tree st.toFG = (Model.specDraft (V := V)).get_filtered_block_tree st'.toFG) (x : Option (Block V)), (Model.specDraft (V := V)).grade2Block st frame ⇢ x ↔ (Model.specDraft (V := V)).grade2Block st' frame ⇢ x := by
  intro st st' frame h x
  rw [sd_grade2Block_iff, sd_grade2Block_iff, h]

/-- The field `preceq_grade2Block_of_g2` of `GradesFacts` at `Model.specDraft`: if the frame holds a
    grade-0 result, a grade-1 result and the grade-2 root `e`, and `P` is in the filtered tree and
    is an ancestor of `e` or `e` itself, then the grade-2 candidate is some `q`, and `P` is an
    ancestor of `q` or `q` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_grade2Block_of_g2 : ∀ {st : (Model.specDraft (V := V)).HS} {frame : (Model.specDraft (V := V)).Frame} {o₀ o₁ : Option (Block V)} {P e : Block V} (h₀ : frame.g0 = some o₀) (h₁ : frame.g1 = some o₁) (h₂ : frame.g2 = some (some e)) (hPt : P ∈ (Model.specDraft (V := V)).get_filtered_block_tree st.toFG) (hPe : Block.Preceq P e) (o : Option (Block V)), (Model.specDraft (V := V)).grade2Block st frame ⇢ o → ∃ q : Block V, o = some q ∧ Block.Preceq P q := by
  intro st frame o₀ o₁ P e h₀ h₁ h₂ hPt hPe o ho
  rw [sd_grade2Block_iff, h₂] at ho
  simp only [Option.bind_some, id_eq] at ho
  subst ho
  have hPe' := Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hPe
  have hPm : P ∈ ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG).filter
      (fun B => Block.preceq B e = true) := Finset.mem_filter.2 ⟨hPt, hPe'⟩
  have hchain : ∀ Y ∈ ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG).filter
      (fun B => Block.preceq B e = true), Block.preceq Y e = true :=
    fun Y hY => (Finset.mem_filter.1 hY).2
  cases hp : DecoupledConsensusModel.Protocol.activePrefix
      ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) e with
  | none =>
      exfalso
      unfold DecoupledConsensusModel.Protocol.activePrefix at hp
      have hs := Proofs.HealingSurface.deepest?_isSome_of_chain hchain ⟨P, hPm⟩
      rw [hp] at hs
      exact Bool.false_ne_true hs
  | some G =>
      refine ⟨G, rfl, ?_⟩
      unfold DecoupledConsensusModel.Protocol.activePrefix at hp
      have hGm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem hp)
      have hd := Proofs.HealingLemmas.deepest?_dominates hp hPm
        (Block.compatible_of_preceq_common hPe' hGm.2)
      first
        | exact hd
        | exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hd

/-- Replacing the saved grades of `st` does not change the anchor of a result. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_anchor_with_saved_grades (st : Spec.Store V)
    (x : Spec.SavedGrades V) (g : Spec.GradeResult V) :
    Spec.Protocol.anchor { st with saved_grades := x } g =
      Spec.Protocol.anchor st g := rfl

/-- The anchor at the grade-1 result of the frame `readFrame` reads from `c` is the anchor computed
    on the store with its saved grades read through the tree, brought to round `r` and filled. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_anchor_readFrame (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (c : Spec.SavedGrades V)
    (st : (Model.specDraft (V := V)).HS) (r : Round) :
    (Model.specDraft (V := V)).anchor E hc st r ((Model.specDraft (V := V)).readFrame c st r).g1 =
      SpecDraftRecord.successOutcomes (Except.map Spec.Block.toProof
        (Spec.Protocol.anchor { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) }
          (Spec.Protocol.round_grades { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r).g1)) := by
  obtain ⟨hinj, hpar, hF⟩ := sd_tree_hyps st
  rw [SpecDraftRecord.GradesImages.round_grades_ofImage_eq_fillRound_readFrame st.property,
    sd_anchor_with_saved_grades]
  show SpecDraftRecord.successOutcomes (Except.map Spec.Block.toProof
    (Spec.Protocol.anchor (Spec.Store.ofImage st.val) (SpecDraftRecord.fillResult
      (SpecDraftRecord.ForkChoiceGrades.gradeResultOfImage st.val
        (SpecDraftRecord.Member.readFrame c st.val r).g1.toProof)))) = _
  rw [(SpecDraftRecord.GradesImages.gradeResultOfImage_readFrame st.val hinj hpar hF c r).2.1]
  rfl

/-- An outcome `g` of the member `frameGradeRead` at round `r` is made of the anchor, the grade-2
    candidate and the grade-0 test computed on the store with its saved grades read through the
    tree, brought to round `r` and filled. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_read_parts {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : (Model.specDraft (V := V)).HS} {r : Round}
    {g : DecoupledConsensusModel.Protocol.GradeRead V}
    (hg : (Model.specDraft (V := V)).frameGradeRead c E hc st r ⇢ g) :
    ∃ A Q2, Spec.Protocol.anchor { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) }
          (Spec.Protocol.round_grades { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r).g1 = .ok A ∧
      Spec.Protocol.grade2Block { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) }
          (Spec.Protocol.round_grades { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r) = .ok Q2 ∧
      g.anchor = A.toProof ∧ g.Q2 = Q2.map Spec.Block.toProof ∧
      g.clear = SpecDraftRecord.Member.clear (Spec.Protocol.round_grades { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r) := by
  have hg' := (SpecDraftRecord.returns_successOutcomes _ _).1 hg
  cases hr : Spec.Protocol.round_grade_read { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r with
  | error e =>
    rw [hr] at hg'
    cases hg'
  | ok gr =>
    rw [hr] at hg'
    simp only [Except.map, Except.ok.injEq] at hg'
    subst hg'
    simp only [Spec.Protocol.round_grade_read] at hr
    obtain ⟨A, hA, hr⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok hr
    obtain ⟨Q2, hQ, hr⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok hr
    obtain ⟨G0, -, hr⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok hr
    obtain ⟨raw, -, hr⟩ := SpecDraftRecord.NoRaise.DRE.of_bind_ok hr
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    exact ⟨A, Q2, hA, hQ, rfl, rfl, rfl⟩

/-- Filling the round grades `fr` does not change the member `clear`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_clear_fillRound (fr : Spec.RoundGrades V) :
    SpecDraftRecord.Member.clear (SpecDraftRecord.fillRound fr) = SpecDraftRecord.Member.clear fr := by
  funext B
  rcases fr with ⟨a0, a1, a2⟩
  rcases a0 with _ | _ | _ <;>
    simp [SpecDraftRecord.Member.clear, DecoupledConsensusModel.Protocol.clear,
      SpecDraftRecord.fillRound, SpecDraftRecord.fillResult, Spec.RoundGrades.toProof]

/-- The field `frameGradeRead_anchor` of `GradesFacts` at `Model.specDraft`: for every outcome `g`
    of the frame grade read of `c` at `st` and `r`, and every outcome `a` of the anchor at the
    grade-1 result of the round-`r` frame read from `c` at `st`, the anchor of `g` is `a`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_frameGradeRead_anchor : ∀ (c : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : DecoupledConsensusModel.Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, (Model.specDraft (V := V)).frameGradeRead c E hc st r ⇢ g → ∀ a : DecoupledConsensusModel.Block V, (Model.specDraft (V := V)).anchor E hc st r ((Model.specDraft (V := V)).readFrame c st r).g1 ⇢ a → g.anchor = a := by
  intro c E hc st r g hg a ha
  obtain ⟨A, Q2, hA, -, hgA, -, -⟩ := sd_read_parts (c := c) hg
  rw [sd_anchor_readFrame] at ha
  have ha' := (SpecDraftRecord.returns_successOutcomes _ _).1 ha
  rw [hA] at ha'
  simp only [Except.map, Except.ok.injEq] at ha'
  rw [hgA, ha']

/-- The field `frameGradeRead_clear` of `GradesFacts` at `Model.specDraft`: the grade-0 test of
    every outcome of the frame grade read of `c` at `st` and `r` is the test of the round-`r` frame
    read from `c` at `st`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_frameGradeRead_clear : ∀ (c : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : DecoupledConsensusModel.Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, (Model.specDraft (V := V)).frameGradeRead c E hc st r ⇢ g → g.clear = (Model.specDraft (V := V)).clear ((Model.specDraft (V := V)).readFrame c st r) := by
  intro c E hc st r g hg
  obtain ⟨A, Q2, -, -, -, -, hgc⟩ := sd_read_parts (c := c) hg
  rw [hgc, SpecDraftRecord.GradesImages.round_grades_ofImage_eq_fillRound_readFrame st.property,
    sd_clear_fillRound]
  rfl

/-- The outcomes of `Model.specDraft`'s `frameStableRoot` at a store `st`: the deepest block of the
    filtered tree that is an ancestor of the grade-2 block of the frame `readFrame c st r`, or the
    fork-choice root when there is none. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_frameStableRoot_iff {c : Spec.SavedGrades V}
    {E : Env V} {hc : Protocol.HealConfig} {st : (Model.specDraft (V := V)).HS} {r : Round}
    {x : Option (DecoupledConsensusModel.Block V)} :
    (Model.specDraft (V := V)).frameStableRoot c E hc st r ⇢ x ↔
      x = some ((((Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st r)).bind id).bind
        (DecoupledConsensusModel.Protocol.activePrefix ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG))).getD
          ((Model.specDraft (V := V)).get_fg_root st.toFG)) := by
  obtain ⟨hinj, hpar, hF⟩ := sd_tree_hyps st
  have hR := (SpecDraftRecord.GradesImages.gradeResultOfImage_readFrame st.val hinj hpar hF c r).2.2
  have hg2 : (Spec.Protocol.round_grades { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r).g2 =
      .computed (((Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st r)).bind id).map
        st.val.blockOfImage) := by
    rw [SpecDraftRecord.GradesImages.round_grades_ofImage_eq_fillRound_readFrame st.property]
    show SpecDraftRecord.fillResult (SpecDraftRecord.Member.readFrame c st.val r).g2 = _
    rw [← hR, SpecDraftRecord.GradesImages.fill_gradeResultOfImage]
    rfl
  have he : Except.map (fun B => some B.toProof) (Spec.Protocol.round_stable_root { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r) =
      .ok (some ((((Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st r)).bind id).bind
        (DecoupledConsensusModel.Protocol.activePrefix ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG))).getD
          ((Model.specDraft (V := V)).get_fg_root st.toFG))) := by
    simp only [Spec.Protocol.round_stable_root]
    rw [hg2]
    show Except.ok (some (Spec.Protocol.stable_root (Spec.Store.ofImage st.val) _).toProof) = _
    congr 2
    have key : ∀ u : Option (DecoupledConsensusModel.Block V),
        (Spec.Protocol.active_prefix (Spec.Store.ofImage st.val) (u.map st.val.blockOfImage)).map
          Spec.Block.toProof =
        u.bind (DecoupledConsensusModel.Protocol.activePrefix ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG)) := by
      rintro (_ | y)
      · rfl
      · exact Spec.Protocol.activePrefix_blockOfImage (Spec.Store.ofImage st.val) hinj hpar
          (SpecDraftRecord.GradesImages.filtered_subset (Spec.Store.ofImage st.val)) y
    rw [← key]
    simp only [Spec.Protocol.stable_root, Id.run, ne_eq]
    cases hA : Spec.Protocol.active_prefix (Spec.Store.ofImage st.val)
        (((Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st r)).bind id).map st.val.blockOfImage) with
    | none => rfl
    | some A => rfl
  show Returns (SpecDraftRecord.successOutcomes (Except.map (fun B => some B.toProof)
      (Spec.Protocol.round_stable_root { Spec.Store.ofImage st.val with saved_grades := SpecDraftRecord.fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) r) } r))) x ↔ _
  rw [SpecDraftRecord.returns_successOutcomes, he]
  constructor
  · intro h; exact (Except.ok.inj h).symm
  · intro h; rw [h]

/-- The field `frameStableRoot_cases` of `GradesFacts` at `Model.specDraft`: every stable root `G`
    of round `r` through `c` is the fork-choice root, or an ancestor of the frame's grade-2 root. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_frameStableRoot_cases : ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {G : Block V} (x : Option (Block V)) (hx : (Model.specDraft (V := V)).frameStableRoot c E hc st r ⇢ x) (h : x = some G), G = (Model.specDraft (V := V)).get_fg_root st.toFG ∨
    ∃ root : Block V, ((Model.specDraft (V := V)).readFrame c st r).g2 = some (some root) ∧
    Block.Preceq G root := by
  intro c E hc st r G x hx h
  rw [sd_frameStableRoot_iff, h] at hx
  have hG := Option.some.inj hx
  rcases hu : (Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st r)) with _ | _ | e
  · rw [hu] at hG; left; exact hG
  · rw [hu] at hG; left; exact hG
  · rw [hu] at hG
    simp only [Option.bind_some, id_eq] at hG
    cases hp : DecoupledConsensusModel.Protocol.activePrefix
        ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) e with
    | none => rw [hp] at hG; left; exact hG
    | some Y =>
      rw [hp] at hG
      simp only [Option.getD_some] at hG
      right
      refine ⟨e, rfl, ?_⟩
      unfold DecoupledConsensusModel.Protocol.activePrefix at hp
      have hYm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem hp)
      rw [hG]
      exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hYm.2

/-- The field `preceq_frameStableRoot` of `GradesFacts` at `Model.specDraft`: if the frame's grade-2
    root is `e`, `X ⪯ e`, and `X` is a filtered block or an ancestor of the fork-choice root, then
    `X` is an ancestor of every stable root of round `r` through `c`, or that root itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_preceq_frameStableRoot : ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {X e G : Block V} (he : ((Model.specDraft (V := V)).readFrame c st r).g2 = some (some e)) (hXe : Block.Preceq X e) (hX : X ∈ (Model.specDraft (V := V)).get_filtered_block_tree st.toFG ∨
    Block.Preceq X ((Model.specDraft (V := V)).get_fg_root st.toFG)) (x : Option (Block V)) (hx : (Model.specDraft (V := V)).frameStableRoot c E hc st r ⇢ x) (hG : x = some G), Block.Preceq X G := by
  intro c E hc st r X e G he hXe hX x hx hG
  rw [sd_frameStableRoot_iff, hG] at hx
  have hG' := Option.some.inj hx
  have he' : Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st r) = some (some e) := he
  rw [he'] at hG'
  simp only [Option.bind_some, id_eq] at hG'
  have hXe' := Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hXe
  cases hp : DecoupledConsensusModel.Protocol.activePrefix
      ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) e with
  | none =>
    rw [hp] at hG'
    simp only [Option.getD_none] at hG'
    rcases hX with hXt | hXf
    · exfalso
      have hPm : X ∈ ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG).filter
          (fun B => Block.preceq B e = true) := Finset.mem_filter.2 ⟨hXt, hXe'⟩
      have hchain : ∀ Y ∈ ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG).filter
          (fun B => Block.preceq B e = true), Block.preceq Y e = true :=
        fun Y hY => (Finset.mem_filter.1 hY).2
      unfold DecoupledConsensusModel.Protocol.activePrefix at hp
      have hs := Proofs.HealingSurface.deepest?_isSome_of_chain hchain ⟨X, hPm⟩
      rw [hp] at hs
      exact Bool.false_ne_true hs
    · rw [hG']; exact hXf
  | some Y =>
    rw [hp] at hG'
    simp only [Option.getD_some] at hG'
    rw [hG']
    unfold DecoupledConsensusModel.Protocol.activePrefix at hp
    have hYm := Finset.mem_filter.1 (Proofs.Engine.deepest?_mem hp)
    rcases hX with hXt | hXf
    · have hPm : X ∈ ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG).filter
          (fun B => Block.preceq B e = true) := Finset.mem_filter.2 ⟨hXt, hXe'⟩
      have hd := Proofs.HealingLemmas.deepest?_dominates hp hPm
        (Block.compatible_of_preceq_common hXe' hYm.2)
      first
        | exact hd
        | exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hd
    · exact Proofs.ModelProperties.Preceq_trans hXf
        (sd_fg_root_preceq_of_mem_filtered (st := st.toFG) hYm.1)

/-- The field `frameStableRoot_of_grade2Block` of `GradesFacts` at `Model.specDraft`: if two stores
    have the same finalized block and the same filtered tree, and the grade-2 candidate of the frame
    read at `st'` is `Q`, then every stable root of round `r` through `c` at `st` is `Q`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_frameStableRoot_of_grade2Block : ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st st' : (Model.specDraft (V := V)).HS) (r : Round) (hF : st'.toFG.F = st.toFG.F) (htree : (Model.specDraft (V := V)).get_filtered_block_tree st'.toFG = (Model.specDraft (V := V)).get_filtered_block_tree st.toFG) {Q : Block V} (o : Option (Block V)) (ho : (Model.specDraft (V := V)).grade2Block st' ((Model.specDraft (V := V)).readFrame c st' r) ⇢ o) (h : o = some Q) (x : Option (Block V)), (Model.specDraft (V := V)).frameStableRoot c E hc st r ⇢ x → x = some Q := by
  intro c E hc st st' r hF htree Q o ho h x hx
  rw [sd_grade2Block_iff, h, htree] at ho
  have hg : Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st' r) =
      Model.Frame.g2 (M := (Model.specDraft (V := V))) ((Model.specDraft (V := V)).readFrame c st r) := by
    rw [specDraft_readFrame_g2, specDraft_readFrame_g2, hF]
  rw [hg] at ho
  rw [sd_frameStableRoot_iff] at hx
  rw [hx, ← ho]
  rfl

/-- An outcome `c'` of the member `onPhaseTick` is the saved grades `update_grades` writes on the
    store with its saved grades replaced by `c`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_onPhaseTick_ok {E : DecoupledConsensusModel.Env V}
    {hc : DecoupledConsensusModel.Protocol.HealConfig} {st : (Model.specDraft (V := V)).HS} {t : Int}
    {c c' : (Model.specDraft (V := V)).Cache} (hc' : (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c') :
    ∃ S : Spec.Store V,
      Spec.Protocol.update_grades
        (Spec.Config.toSpec E hc SpecDraftRecord.unreadHeightConfig)
        (Spec.Provisional.toSpec E) { st.val with saved_grades := c } t = .ok S ∧
      c' = S.saved_grades ∧
      SpecDraftRecord.NoRaise.roundAt
        (Spec.Config.toSpec E hc SpecDraftRecord.unreadHeightConfig) t =
          (Model.specDraft (V := V)).round_of hc (E.slotOf t) := by
  obtain ⟨S, hS, rfl⟩ := sd_except_map_ok ((SpecDraftRecord.returns_successOutcomes _ _).mp hc')
  refine ⟨S, hS, rfl, ?_⟩
  rw [eq_round_of]
  simp only [SpecDraftRecord.NoRaise.roundAt, Spec.Config.round_of,
    Spec.Config.toSpec_slotOf, Spec.Config.toSpec_R]
  show _ = DecoupledConsensusModel.Protocol.HealConfig.round_of hc (E.slotOf t)
  unfold DecoupledConsensusModel.Protocol.HealConfig.round_of
  rfl

/-- `Model.specDraft`'s `phaseResult fr p` is not `none` exactly when the result of phase `p` in
    `fr` is not pending. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_phaseResult_ne_none (fr : Spec.RoundGrades V)
    (p : DecoupledConsensusModel.Protocol.Phase) :
    (Model.specDraft (V := V)).phaseResult fr p ≠ none ↔
      Spec.Protocol.phaseResult fr (Spec.Protocol.Phase.toSpec p) ≠ .pending := by
  show (Spec.Protocol.phaseResult fr _).toProof ≠ none ↔ _
  rw [ne_eq, Spec.GradeResult.toProof_eq_none]

/-- The field `phaseResult_onPhaseTick_ne_none_of_le` of `GradesFacts` at `Model.specDraft`: if the
    cache's round is at most the round of `t`, which is at most `r`, a result of round `r` the cache
    holds is still held by every outcome of the phase tick at `t`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_onPhaseTick_ne_none_of_le : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS)
    (t : Time) (c : (Model.specDraft (V := V)).Cache) (r : Round) (p : Protocol.Phase),
    c.round ≤ (Model.specDraft (V := V)).round_of hc (E.slotOf t) → (Model.specDraft (V := V)).round_of hc (E.slotOf t) ≤ r →
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p ≠ none →
    ∀ c' : (Model.specDraft (V := V)).Cache, (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c' →
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p ≠ none := by
  intro E hc st t c r p h1 h2 h c' hc'
  obtain ⟨S, hS, rfl, hρ⟩ := sd_onPhaseTick_ok hc'
  rw [sd_phaseResult_ne_none] at h ⊢
  rw [← hρ] at h1 h2
  have ha := SpecDraftRecord.NoRaise.srg_advance_ne_pending
    (c := c) (q := Spec.Protocol.Phase.toSpec p) h1 h2 h
  have k := SpecDraftRecord.NoRaise.update_grades_pending_iff hS
  have kr := (SpecDraftRecord.NoRaise.update_grades_results hS).1
  change Spec.Protocol.phaseResult
    (Spec.Protocol.saved_round_grades S.saved_grades r) _ ≠ _
  change Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    (Spec.Protocol.advance_to_round c _) r) _ ≠ _ at ha
  unfold Spec.Protocol.saved_round_grades at ha ⊢
  rw [kr]
  rw [SpecDraftRecord.NoRaise.advance_to_round_round] at ha
  split_ifs at ha ⊢ <;>
    rcases p with _ | _ | _ <;>
    simp only [Spec.Protocol.phaseResult, Spec.Protocol.Phase.toSpec,
      reduceCtorEq, if_true, if_false] at ha ⊢ <;>
    first
      | exact k.1.2 (Or.inl ha) | exact k.2.1.2 (Or.inl ha) | exact k.2.2.1.2 ha
      | exact k.2.2.2.1.2 ha | exact k.2.2.2.2.1.2 ha | exact k.2.2.2.2.2.2 (Or.inl ha)
      | exact absurd ha (by simp [Spec.Protocol.pending_round_grades])

/-- The field `phaseResult_onPhaseTick_some_domain_or_kept` of `GradesFacts` at `Model.specDraft`: a
    result an outcome of the phase tick at `t` holds for round `r` and phase `p` was computed at
    `t = domain r p`, or the cache already held it. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_onPhaseTick_some_domain_or_kept : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache) {r : Round} {p : Protocol.Phase} {o : Option (Block V)} (c' : (Model.specDraft (V := V)).Cache) (hc' : (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c') (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p
    = some o), t = (Model.specDraft (V := V)).domain E hc r p ∨
    ∃ o', (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some o' := by
  intro E hc st t c r p o c' hc' h
  obtain ⟨S, hS, rfl, hρ⟩ := sd_onPhaseTick_ok hc'
  have hne : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound S.saved_grades r) p ≠ none := by
    rw [h]; exact Option.some_ne_none o
  suffices hs : t = (Model.specDraft (V := V)).domain E hc r p ∨ (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p ≠ none by
    rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Option.ne_none_iff_exists'.mp hs)
  rw [sd_phaseResult_ne_none] at hne ⊢
  have k := SpecDraftRecord.NoRaise.update_grades_pending_iff hS
  have kr := (SpecDraftRecord.NoRaise.update_grades_results hS).1
  have back := fun h' => SpecDraftRecord.NoRaise.srg_advance_ne_pending_rev
    (c := c) (ρ := SpecDraftRecord.NoRaise.roundAt
      (Spec.Config.toSpec E hc SpecDraftRecord.unreadHeightConfig) t)
    (r := r) (q := Spec.Protocol.Phase.toSpec p) h'
  change Spec.Protocol.phaseResult
    (Spec.Protocol.saved_round_grades S.saved_grades r) _ ≠ _ at hne
  have key : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
      (Spec.Protocol.advance_to_round c (SpecDraftRecord.NoRaise.roundAt
        (Spec.Config.toSpec E hc SpecDraftRecord.unreadHeightConfig) t)) r)
        (Spec.Protocol.Phase.toSpec p) ≠ .pending ∨
      t = SpecDraftRecord.Member.domain E hc r p := by
    unfold Spec.Protocol.saved_round_grades at hne ⊢
    rw [kr] at hne
    rw [SpecDraftRecord.NoRaise.advance_to_round_round]
    split_ifs at hne ⊢ <;> rcases p with _ | _ | _ <;>
      simp only [Spec.Protocol.phaseResult, Spec.Protocol.Phase.toSpec,
        reduceCtorEq, if_true, if_false] at hne ⊢ <;>
      first
        | exact Or.inl (k.2.2.1.1 hne)
        | exact Or.inl (k.2.2.2.1.1 hne)
        | exact Or.inl (k.2.2.2.2.1.1 hne)
        | (rcases k.1.1 hne with h' | h'
           · exact Or.inl h'
           · right; subst_vars
             simp only [SpecDraftRecord.Member.domain, SpecDraftRecord.Member.domainOffset, one_mul]
             exact h')
        | (rcases k.2.1.1 hne with h' | h'
           · exact Or.inl h'
           · right; subst_vars
             simp only [SpecDraftRecord.Member.domain, SpecDraftRecord.Member.domainOffset, zero_mul,
               add_zero]
             exact h')
        | (rcases k.2.2.2.2.2.1 hne with h' | h'
           · exact Or.inl h'
           · right; subst_vars
             simp only [SpecDraftRecord.Member.domain, SpecDraftRecord.Member.domainOffset,
               neg_one_mul, ← sub_eq_add_neg]
             exact h')
        | exact absurd hne (by simp [Spec.Protocol.pending_round_grades])
  rcases key with h' | h'
  · exact Or.inr (back h')
  · exact Or.inl h'

/-- The field `phaseResult_onPhaseTick_some_cases` of `GradesFacts` at `Model.specDraft`: a result
    an outcome of the phase tick at `t` holds for round `r` and phase `p` is of `t`'s round, or was
    computed at `domain r p`, or the cache already held it. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_onPhaseTick_some_cases : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache) {r : Round} {p : Protocol.Phase} {o : Option (Block V)} (c' : (Model.specDraft (V := V)).Cache) (hc' : (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c') (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p
    = some o), r = ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) ∨ t = (Model.specDraft (V := V)).domain E hc r p ∨
    ∃ o', (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some o' := by
  intro E hc st t c r p o c' hc' h
  exact Or.inr (specDraft_phaseResult_onPhaseTick_some_domain_or_kept E hc st t c c' hc' h)


omit [Fintype V] [Inhabited V] in
/-- The image under `toProof` of the genesis block is compatible with every block `F`. -/
theorem _root_.SpecDraftRecord.GradesFacts.genesis_compatible_image (F : DecoupledConsensusModel.Block V) :
    DecoupledConsensusModel.Block.compatible
      (Spec.Block.genesis : Spec.Block V).toProof F = true := by
  show DecoupledConsensusModel.Block.compatible .genesis F = true
  unfold DecoupledConsensusModel.Block.compatible
  have : DecoupledConsensusModel.Block.preceq .genesis F = true := by
    induction F with
    | genesis => simp [DecoupledConsensusModel.Block.preceq]
    | node p s r v sv a pr ih =>
      simp only [DecoupledConsensusModel.Block.preceq, Bool.or_eq_true]
      exact Or.inr ih
  rw [this]; rfl

omit [Fintype V] [Inhabited V] in
/-- The loop of `clipBlockImage F`, started at the block `g` and given at least `g.depth + 1` steps,
    stops at a block whose image is `clipGrade g.toProof F`. -/
theorem _root_.SpecDraftRecord.GradesFacts.clipBlockImage_loop (F : DecoupledConsensusModel.Block V)
    (l : List Nat) (g : Spec.Block V) (hl : g.depth + 1 ≤ l.length) :
    ∃ W : Spec.Block V,
      (forIn (m := Id) l ((none : Option (Spec.Block V)), g)
        fun _ (s : Option (Spec.Block V) × Spec.Block V) =>
        if DecoupledConsensusModel.Block.compatible s.2.toProof F = true then
          pure (ForInStep.done (some s.2, s.2))
        else pure (ForInStep.yield (none, s.2.parent))) = (some W, W) ∧
      W.toProof = DecoupledConsensusModel.Protocol.clipGrade g.toProof F := by
  induction l generalizing g with
  | nil => simp at hl
  | cons x l ih =>
    rw [List.forIn_cons]
    cases g with
    | genesis =>
      simp only [genesis_compatible_image F, if_true]
      refine ⟨.genesis, rfl, ?_⟩
      show DecoupledConsensusModel.Block.genesis = DecoupledConsensusModel.Protocol.clipGrade .genesis F
      rw [DecoupledConsensusModel.Protocol.clipGrade]
    | node p s r votes support ats proposer =>
      have hn : (Spec.Block.node p s r votes support ats proposer).toProof =
          .node p.toProof s r.toProof (votes.map Spec.GoldfishVote.toProof)
            (support.map Spec.GoldfishVote.toProof)
            (ats.map Spec.Attestation.toProof) proposer := rfl
      by_cases h : DecoupledConsensusModel.Block.compatible
          (Spec.Block.node p s r votes support ats proposer).toProof F = true
      · simp only [h, if_true]
        refine ⟨_, rfl, ?_⟩
        rw [hn] at h ⊢
        rw [DecoupledConsensusModel.Protocol.clipGrade, if_pos h]
      · have hl' : p.depth + 1 ≤ l.length := by
          simp [Spec.Block.depth] at hl; omega
        simp only [h, Bool.false_eq_true, if_false]
        obtain ⟨W, hW, hWp⟩ := ih p hl'
        refine ⟨W, hW, ?_⟩
        rw [hWp, hn]
        rw [hn] at h
        rw [DecoupledConsensusModel.Protocol.clipGrade, if_neg h]

omit [Fintype V] [Inhabited V] in
/-- The image of `clipBlockImage F g` is `clipGrade g.toProof F`. -/
theorem _root_.SpecDraftRecord.GradesFacts.toProof_clipBlockImage (F : DecoupledConsensusModel.Block V)
    (g : Spec.Block V) :
    (SpecDraftRecord.clipBlockImage F g).toProof = DecoupledConsensusModel.Protocol.clipGrade g.toProof F := by
  obtain ⟨W, hW, hWp⟩ := clipBlockImage_loop F
    (List.range' 0 (Std.Legacy.Range.size [:g.depth + 1]) 1) g (by simp [Std.Legacy.Range.size])
  unfold SpecDraftRecord.clipBlockImage
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [hW]
  exact hWp

omit [Fintype V] [Inhabited V] in
/-- The image of `clipResultImage F g` is `clipResult F g.toProof`. -/
theorem _root_.SpecDraftRecord.GradesFacts.toProof_clipResultImage (F : DecoupledConsensusModel.Block V)
    (g : Spec.GradeResult V) :
    (SpecDraftRecord.clipResultImage F g).toProof =
      DecoupledConsensusModel.Protocol.clipResult F g.toProof := by
  rcases g with _ | _ | X
  · simp [SpecDraftRecord.clipResultImage, DecoupledConsensusModel.Protocol.clipResult, Id.run]
    rfl
  · simp [SpecDraftRecord.clipResultImage, DecoupledConsensusModel.Protocol.clipResult, Id.run,
      Spec.GradeResult.block]
    rfl
  · show some (some (SpecDraftRecord.clipBlockImage F X).toProof) = _
    rw [toProof_clipBlockImage]
    simp [DecoupledConsensusModel.Protocol.clipResult]

/-- The image of the saved grades `c` clipped to `F` by `Model.specDraft`'s `clipCache` is the image
    of `c` clipped to `F`. -/
theorem _root_.SpecDraftRecord.GradesFacts.sd_clipCache (F : DecoupledConsensusModel.Block V)
    (c : (Model.specDraft (V := V)).Cache) :
    Spec.SavedGrades.toProof ((Model.specDraft (V := V)).clipCache F c) =
      (Model.vocabulary (V := V)).clipCache F (Spec.SavedGrades.toProof c) := by
  show (⟨c.round, (SpecDraftRecord.Member.clipFrame F c.current).toProof,
    (SpecDraftRecord.Member.clipFrame F c.next).toProof⟩ : DecoupledConsensusModel.Protocol.Cache V) =
    DecoupledConsensusModel.Protocol.clipCache F ⟨c.round, c.current.toProof, c.next.toProof⟩
  simp only [SpecDraftRecord.Member.clipFrame, Spec.RoundGrades.toProof,
    toProof_clipResultImage, DecoupledConsensusModel.Protocol.clipCache,
    DecoupledConsensusModel.Protocol.clipFrame]

/-- The field `phaseResult_clipCache` of `GradesFacts` at `Model.specDraft`: if the cache `c`
    clipped to `F` holds the root `root` for round `r₁` and phase `p`, then `c` holds a root `root₀`
    for them of which `root` is an ancestor, or `root₀` itself. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_clipCache : ∀ {F : Block V} {c : (Model.specDraft (V := V)).Cache} {r₁ : Round} {p : Protocol.Phase} {root : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).clipCache F c) r₁) p
    = some (some root)), ∃ root₀ : Block V,
    (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r₁) p = some (some root₀) ∧
    Block.Preceq root root₀ := by
  intro F c r₁ p root h
  rw [sd_phaseResult, sd_cacheAtRound, sd_clipCache] at h
  simp only [sd_phaseResult, sd_cacheAtRound]
  exact (Model.vocabulary_facts_grades (V := V)).phaseResult_clipCache h

/-- The field `phaseResult_clipCache_isSome` of `GradesFacts` at `Model.specDraft`: if the cache `c`
    clipped to `F` holds a result for round `r` and phase `p`, so does `c`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_clipCache_isSome : ∀ {F : Block V} {c : (Model.specDraft (V := V)).Cache} {r : Round} {p : Protocol.Phase} {o : Option (Block V)} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).clipCache F c) r) p = some o), ∃ o', (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some o' := by
  intro F c r p o h
  rw [sd_phaseResult, sd_cacheAtRound, sd_clipCache] at h
  simp only [sd_phaseResult, sd_cacheAtRound]
  exact (Model.vocabulary_facts_grades (V := V)).phaseResult_clipCache_isSome h

/-- The field `phaseResult_clipCache_some` of `GradesFacts` at `Model.specDraft`: if the cache `c`
    holds the root `e` for round `r` and phase `p`, then `c` clipped to `F` holds `clipGrade e F`
    for them. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_clipCache_some : ∀ {F : Block V} {c : (Model.specDraft (V := V)).Cache} {r : Round} {p : Protocol.Phase} {e : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some (some e)), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).clipCache F c) r) p
    = some (some ((Model.specDraft (V := V)).clipGrade e F)) := by
  intro F c r p e h
  rw [sd_phaseResult, sd_cacheAtRound] at h
  rw [sd_phaseResult, sd_cacheAtRound, sd_clipCache, eq_clipGrade]
  exact (Model.vocabulary_facts_grades (V := V)).phaseResult_clipCache_some h

end MembersTwo

section MembersThree

/-! ### The vote fields -/

/-- The field `Sts_currentSGVote_of_deepest_clear` of `GradesFacts` at `Model.specDraft`: if the
    clearing walk from the grade read's anchor along the store's confirmed chain finds `D`, the SG
    vote is `D`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_Sts_currentSGVote_of_deepest_clear : ∀ {st : (Model.specDraft (V := V)).HS} {grades : Protocol.GradeRead V} {D : Block V} (h : (Model.specDraft (V := V)).deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = some D), (Model.specDraft (V := V)).currentSGVote st grades = D := by
  intro st grades D h
  rw [eq_deepest_clear, sd_live_confirmed] at h
  exact SpecDraftRecord.GradesImages.member_currentSGVote_of_deepest_clear st grades h

/-- The field `ModelProperties_currentSGVote_of_deepest_clear` of `GradesFacts` at
    `Model.specDraft`: if the clearing walk from the grade read's anchor along the store's confirmed
    chain finds `B`, the SG vote is `B`. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_ModelProperties_currentSGVote_of_deepest_clear : ∀ {st : (Model.specDraft (V := V)).HS} {grades : Protocol.GradeRead V} {B : Block V} (h : (Model.specDraft (V := V)).deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = some B), (Model.specDraft (V := V)).currentSGVote st grades = B :=
  fun h => SpecDraftRecord.GradesFacts.specDraft_Sts_currentSGVote_of_deepest_clear h

/-- The field `get_head_with_eq_fork_choice` of `GradesFacts` at `Model.specDraft`: for every
    outcome `R` of the SG root at the store's round, the head is an outcome `X` exactly when `X` is
    an outcome of the Goldfish fork choice from `R` through the filtered tree. -/
theorem _root_.SpecDraftRecord.GradesFacts.specDraft_get_head_with_eq_fork_choice : ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (R : Block V), (Model.specDraft (V := V)).get_sg_root_with contract E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ R →
    ∀ X : Block V, (Model.specDraft (V := V)).get_head_with contract E hc st votes support s ⇢ X ↔
    (Model.specDraft (V := V)).goldfish_fork_choice E st.toFG.σ st.toFG.h_max st.toFG.toSG.toGoldfishStore.T st.toFG.toSG.toGoldfishStore.s
    R
    ((Model.specDraft (V := V)).get_filtered_block_tree st.toFG) votes support s ⇢ X := by
  intro c E hc st votes support s R hR X
  have hr : (Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc SpecDraftRecord.unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.specDraft, SpecDraftRecord.Member.gs_s, SpecDraftRecord.Member.toHealing,
      SpecDraftRecord.Member.toFG, SpecDraftRecord.Member.toSG,
      SpecDraftRecord.Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      SpecDraftRecord.toProof_gs_s, SpecDraftRecord.Member.round_of]
    rfl
  have hR' : Returns (SpecDraftRecord.Member.get_sg_root_with c E hc st.val
      ((Spec.Config.toSpec E hc SpecDraftRecord.unreadHeightConfig).round_of st.val.s)) R := by
    rw [← hr]; exact hR
  have e1 := SpecDraftRecord.ContractImages.member_get_head_with_eq_layer st c E hc votes support s
  have e := SpecDraftRecord.ContractImages.member_get_head_in_tree_with_layer_eq st c E hc
    (SpecDraftRecord.Member.get_filtered_block_tree st.val) votes support s hR'
  rw [SpecDraftRecord.ForkChoiceImages.specDraft_goldfish_fork_choice_eq]
  show Returns (SpecDraftRecord.Member.get_head_with c E hc st.val votes support s) X ↔ _
  rw [e1, e]
  simp only [Model.vocabulary, returns_pure]
  have hT : st.toFG.toSG.toGoldfishStore.T = st.val.T.image Spec.Block.toProof := by
    simp only [Model.GS.T, Model.specDraft, SpecDraftRecord.Member.gs_T, SpecDraftRecord.Member.toFG,
      SpecDraftRecord.Member.toSG, SpecDraftRecord.Member.toGoldfishStore, Model.HS.toFG,
      Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq, SpecDraftRecord.toProof_gs_T]
  have hQ : (Model.specDraft (V := V)).get_filtered_block_tree st.toFG =
      SpecDraftRecord.Member.get_filtered_block_tree st.val := rfl
  have hσ : (fun C => Spec.Protocol.ChainState.toProof (st.toFG.σ C)) =
      (fun C => (st.val.σ (st.val.blockOfImage C)).toProof) := rfl
  have hm : st.toFG.h_max = st.val.h_max := rfl
  have hs : st.toFG.toSG.toGoldfishStore.s = st.val.s := by
    simp only [Model.GS.s, Model.specDraft, SpecDraftRecord.Member.gs_s, SpecDraftRecord.Member.toFG,
      SpecDraftRecord.Member.toSG, SpecDraftRecord.Member.toGoldfishStore, Model.HS.toFG,
      Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq, SpecDraftRecord.toProof_gs_s]
  rw [hT, hQ, hσ, hm, hs]

end MembersThree

end GradesTransports

end DecoupledConsensusModel.Sts.Record
