import Proofs.Instance.Members.Base
import Proofs.Instance.NoRaise.Kit
import Proofs.Instance.Members.DutiesNode
import Proofs.Instance.Members.ForkChoiceGrades
import Proofs.Instance.Members.ChainStateToHandlers

/-!
# The filled members agree with the spec's routines

The members of the instance that read grades run the spec's routines on the store
`{ st with saved_grades := fill c }`. For each such routine, this file proves that when it answers
on `{ st with saved_grades := c }`, it answers the same on the filled store; a routine that returns
a store returns the same store with its saved grades `fill c`.
-/

set_option autoImplicit false

namespace SpecDraftRecord

open Spec
open scoped Spec DC

/-! ## Agreement of grade results -/

section Agreement

variable {V : Type}

/-- The grade result `g'` equals `g` whenever `g` is not pending. -/
def ResultAgrees (g g' : GradeResult V) : Prop := g ≠ .pending → g' = g

/-- Each of the three results `g0`, `g1`, `g2` of `grades'` agrees with the same result of `grades`. -/
def RoundAgrees (grades grades' : RoundGrades V) : Prop :=
  ResultAgrees grades.g0 grades'.g0 ∧ ResultAgrees grades.g1 grades'.g1 ∧
    ResultAgrees grades.g2 grades'.g2

/-- The filled result agrees with the result. -/
theorem resultAgrees_fillResult (g : GradeResult V) : ResultAgrees g (fillResult g) :=
  fun h => fillResult_of_ne_pending h

/-- A result agrees with itself. -/
theorem resultAgrees_refl (g : GradeResult V) : ResultAgrees g g := fun _ => rfl

/-- A round's grades agree with themselves. -/
theorem roundAgrees_refl (grades : RoundGrades V) : RoundAgrees grades grades :=
  ⟨resultAgrees_refl _, resultAgrees_refl _, resultAgrees_refl _⟩

/-- The filled round grades agree with the round grades. -/
theorem roundAgrees_fillRound (grades : RoundGrades V) :
    RoundAgrees grades (fillRound grades) :=
  ⟨resultAgrees_fillResult _, resultAgrees_fillResult _, resultAgrees_fillResult _⟩

/-- If the raising read of the grade result `g` answers `G`, the read of every result agreeing with
    `g` answers `G`. -/
theorem read_of_resultAgrees {g g' : GradeResult V} (hg : ResultAgrees g g')
    {G : Option (Block V)} (h : (g : DC.DRE (Option (Block V))) = .ok G) :
    (g' : DC.DRE (Option (Block V))) = .ok G := by
  cases g with
  | pending => cases h
  | computed G₀ => rw [hg (by simp)]; exact h

/-- The result of one phase agrees when the round's grades agree. -/
theorem resultAgrees_phaseResult {grades grades' : RoundGrades V}
    (h : RoundAgrees grades grades') (p : Protocol.Phase) :
    ResultAgrees (Protocol.phaseResult grades p) (Protocol.phaseResult grades' p) := by
  unfold Protocol.phaseResult
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- On every round `r`, the grades read from `fill c` agree with the grades read from `c`. -/
theorem roundAgrees_saved_round_grades_fill (c : SavedGrades V) (r : Round) :
    RoundAgrees (Protocol.saved_round_grades c r) (Protocol.saved_round_grades (fill c) r) := by
  by_cases h0 : r = c.round
  · rw [saved_round_grades_fill c (Or.inl h0)]
    exact roundAgrees_fillRound _
  by_cases h1 : r = c.round + 1
  · rw [saved_round_grades_fill c (Or.inr h1)]
    exact roundAgrees_fillRound _
  rw [saved_round_grades_fill_of_ne c h0 h1]
  unfold Protocol.saved_round_grades
  simp only [h0, h1, if_false]
  exact roundAgrees_refl _

variable [DecidableEq V]

/-- Making two agreeing results compatible with a block `F` keeps them agreeing. -/
theorem resultAgrees_make_result_compatible_with (F : Block V) {g g' : GradeResult V}
    (h : ResultAgrees g g') :
    ResultAgrees (Protocol.make_result_compatible_with F g)
      (Protocol.make_result_compatible_with F g') := by
  intro hne
  have : g ≠ .pending := by
    rintro rfl
    exact hne rfl
  rw [h this]

/-- Making two agreeing round grades compatible with a block `F` keeps them agreeing. -/
theorem roundAgrees_make_round_grades_compatible_with (F : Block V)
    {grades grades' : RoundGrades V} (h : RoundAgrees grades grades') :
    RoundAgrees (Protocol.make_round_grades_compatible_with F grades)
      (Protocol.make_round_grades_compatible_with F grades') :=
  ⟨resultAgrees_make_result_compatible_with F h.1,
    resultAgrees_make_result_compatible_with F h.2.1,
    resultAgrees_make_result_compatible_with F h.2.2⟩

/-- On every round `r`, the grades `round_grades` reads on `{ st with saved_grades := fill c }`
    agree with those it reads on `{ st with saved_grades := c }`. -/
theorem roundAgrees_round_grades_fill (st : Store V) (c : SavedGrades V) (r : Round) :
    RoundAgrees (Protocol.round_grades { st with saved_grades := c } r)
      (Protocol.round_grades { st with saved_grades := fill c } r) :=
  roundAgrees_make_round_grades_compatible_with st.F (roundAgrees_saved_round_grades_fill c r)

end Agreement

/-! ## Binds that keep their answers -/

namespace Fill

/-- A bind in `DRE` keeps an answer when each part does: if `x'` answers whatever `x` answers, and
    `f' a` answers `v'` whenever `f a` answers `v`, then `x' >>= f'` answers `v'` whenever `x >>= f`
    answers `v`. -/
theorem DRE.bind_agree {α β : Type} {x x' : DC.DRE α} {f f' : α → DC.DRE β} {v v' : β}
    (hx : ∀ a, x = .ok a → x' = .ok a) (hf : ∀ a, f a = .ok v → f' a = .ok v')
    (h : (x >>= f) = .ok v) : (x' >>= f') = .ok v' := by
  obtain ⟨a, ha, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [hx a ha, NoRaise.DRE.bind_ok]
  exact hf a h

/-- A bind in `DREB` keeps an answer when each part does, from the list `l` of the objects sent
    before it. -/
theorem DREB.bind_agree {V α β : Type} {x x' : DREB V α} {f f' : α → DREB V β}
    {l l'' : List (NamedObject V)} {w w' : β}
    (hx : ∀ a l', x.run l = .ok (a, l') → x'.run l = .ok (a, l'))
    (hf : ∀ a l', (f a).run l' = .ok (w, l'') → (f' a).run l' = .ok (w', l''))
    (h : (x >>= f).run l = .ok (w, l'')) : (x' >>= f').run l = .ok (w', l'') := by
  rw [StateT.run_bind] at h ⊢
  obtain ⟨⟨a, l'⟩, ha, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [hx a l' ha, NoRaise.DRE.bind_ok]
  exact hf a l' h

/-- A routine of `DRE` lifted into `DREB` keeps an answer when the routine does. -/
theorem DREB.liftM_agree {V α : Type} {x x' : DC.DRE α} (hx : ∀ a, x = .ok a → x' = .ok a)
    {l : List (NamedObject V)} {a : α} {l' : List (NamedObject V)}
    (h : (liftM x : DREB V α).run l = .ok (a, l')) :
    (liftM x' : DREB V α).run l = .ok (a, l') := by
  cases x with
  | error e => cases h
  | ok b =>
    rw [hx b rfl]
    exact h

/-- If `pure a` in `DREB` answers `w` from `l` with the list `l'`, then `w = a` and `l' = l`. -/
theorem DREB.pure_run_eq {V α : Type} {a w : α} {l l' : List (NamedObject V)}
    (h : (pure a : DREB V α).run l = .ok (w, l')) : w = a ∧ l' = l := by
  have h' : (Except.ok (a, l) : DC.DRE (α × List (NamedObject V))) = .ok (w, l') := h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h'
  exact ⟨h'.1.symm, h'.2.symm⟩

/-- `pure a` in `DREB` answers `a` from `l` and sends nothing. -/
theorem DREB.pure_run {V α : Type} (a : α) (l : List (NamedObject V)) :
    (pure a : DREB V α).run l = .ok (a, l) := rfl

end Fill

open Fill

/-! ## The routines that read grades and return no store -/

section Readers

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- `computed_grades` keeps its answer on agreeing round grades. -/
theorem computed_grades_of_roundAgrees {grades grades' : RoundGrades V}
    (hg : RoundAgrees grades grades') {G : Protocol.ComputedGrades V}
    (h : Protocol.computed_grades grades = .ok G) :
    Protocol.computed_grades grades' = .ok G := by
  simp only [Protocol.computed_grades] at h ⊢
  obtain ⟨a2, h2, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨a1, h1, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨a0, h0, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [read_of_resultAgrees hg.2.2 h2, NoRaise.DRE.bind_ok, read_of_resultAgrees hg.2.1 h1,
    NoRaise.DRE.bind_ok, read_of_resultAgrees hg.1 h0, NoRaise.DRE.bind_ok]
  exact h

omit [DecidableEq V] in
/-- `rawG2` keeps its answer on agreeing round grades. -/
theorem rawG2_of_roundAgrees {grades grades' : RoundGrades V}
    (hg : RoundAgrees grades grades') {b : Bool}
    (h : Protocol.rawG2 grades = .ok b) : Protocol.rawG2 grades' = .ok b := by
  simp only [Protocol.rawG2] at h ⊢
  obtain ⟨a2, h2, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [read_of_resultAgrees hg.2.2 h2, NoRaise.DRE.bind_ok]
  exact h

variable [Fintype V]

omit [Fintype V] in
/-- `anchor` keeps its answer on an agreeing grade-1 result, on stores that differ only in their
    saved grades. -/
theorem anchor_agree (st : Store V) (x y : SavedGrades V) {g g' : GradeResult V}
    (hg : ResultAgrees g g') {A : Block V}
    (h : Protocol.anchor { st with saved_grades := x } g = .ok A) :
    Protocol.anchor { st with saved_grades := y } g' = .ok A := by
  simp only [Protocol.anchor] at h ⊢
  obtain ⟨a, ha, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [read_of_resultAgrees hg ha, NoRaise.DRE.bind_ok]
  exact h

omit [Fintype V] in
/-- `grade2Block` keeps its answer on agreeing round grades, on stores that differ only in their
    saved grades. -/
theorem grade2Block_agree (st : Store V) (x y : SavedGrades V)
    {grades grades' : RoundGrades V} (hg : RoundAgrees grades grades') {Q : Option (Block V)}
    (h : Protocol.grade2Block { st with saved_grades := x } grades = .ok Q) :
    Protocol.grade2Block { st with saved_grades := y } grades' = .ok Q := by
  simp only [Protocol.grade2Block] at h ⊢
  obtain ⟨a, ha, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [computed_grades_of_roundAgrees hg ha, NoRaise.DRE.bind_ok]
  exact h

omit [Fintype V] in
/-- If `round_stable_root` answers `B` on `{ st with saved_grades := c }`, it answers `B` on
    `{ st with saved_grades := fill c }`. -/
theorem round_stable_root_fill_ok (st : Store V) (c : SavedGrades V) (r : Round) {B : Block V}
    (h : Protocol.round_stable_root { st with saved_grades := c } r = .ok B) :
    Protocol.round_stable_root { st with saved_grades := fill c } r = .ok B := by
  have hg := roundAgrees_round_grades_fill st c r
  simp only [Protocol.round_stable_root] at h ⊢
  obtain ⟨a, ha, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [read_of_resultAgrees hg.2.2 ha, NoRaise.DRE.bind_ok]
  exact h

omit [Fintype V] in
/-- If `grade2_block_with` answers `Q` on `{ st with saved_grades := c }`, it answers `Q` on
    `{ st with saved_grades := fill c }`. -/
theorem grade2_block_with_fill_ok (st : Store V) (c : SavedGrades V) (r : Round)
    {Q : Option (Block V)}
    (h : Protocol.grade2_block_with { st with saved_grades := c } r = .ok Q) :
    Protocol.grade2_block_with { st with saved_grades := fill c } r = .ok Q :=
  grade2Block_agree st c (fill c) (roundAgrees_round_grades_fill st c r) h

omit [Fintype V] in
/-- If `round_grade_read` answers `G` on `{ st with saved_grades := c }`, it answers `G` on
    `{ st with saved_grades := fill c }`. -/
theorem round_grade_read_fill_ok (st : Store V) (c : SavedGrades V) (r : Round)
    {G : Protocol.GradeRead V}
    (h : Protocol.round_grade_read { st with saved_grades := c } r = .ok G) :
    Protocol.round_grade_read { st with saved_grades := fill c } r = .ok G := by
  have hg := roundAgrees_round_grades_fill st c r
  simp only [Protocol.round_grade_read] at h ⊢
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨Q, hQ, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨G0, hG0, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨raw, hraw, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [anchor_agree st c (fill c) hg.2.1 hA, NoRaise.DRE.bind_ok,
    grade2Block_agree st c (fill c) hg hQ, NoRaise.DRE.bind_ok,
    read_of_resultAgrees hg.1 hG0, NoRaise.DRE.bind_ok,
    rawG2_of_roundAgrees hg hraw, NoRaise.DRE.bind_ok]
  exact h

omit [Fintype V] in
/-- If `fg_source_with` answers `q` on `{ st with saved_grades := c }`, it answers `q` on
    `{ st with saved_grades := fill c }`. -/
theorem fg_source_with_fill_ok (st : Store V) (c : SavedGrades V) (r : Round)
    (A_G2 : Option (Block V)) {q : Option (Block V)}
    (h : Protocol.fg_source_with { st with saved_grades := c } r A_G2 = .ok q) :
    Protocol.fg_source_with { st with saved_grades := fill c } r A_G2 = .ok q := by
  have hg := roundAgrees_round_grades_fill st c r
  simp only [Protocol.fg_source_with] at h ⊢
  split_ifs at h ⊢
  · obtain ⟨a, ha, h⟩ := NoRaise.DRE.of_bind_ok h
    rw [read_of_resultAgrees hg.1 ha, NoRaise.DRE.bind_ok]
    exact h
  · exact h

omit [Fintype V] in
/-- If `get_sg_vote_with` answers `B` on `{ st with saved_grades := c }`, it answers `B` on
    `{ st with saved_grades := fill c }`. -/
theorem get_sg_vote_with_fill_ok (st : Store V) (c : SavedGrades V) (r : Round)
    (A_G2 : Option (Block V)) {B : Block V}
    (h : Protocol.get_sg_vote_with { st with saved_grades := c } r A_G2 = .ok B) :
    Protocol.get_sg_vote_with { st with saved_grades := fill c } r A_G2 = .ok B := by
  simp only [Protocol.get_sg_vote_with] at h ⊢
  obtain ⟨G, hG, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [round_grade_read_fill_ok st c r hG, NoRaise.DRE.bind_ok]
  exact h

variable (C : Config)

omit [Fintype V] in
/-- If the saved grade of phase `p` of the store's round answers `G` on
    `{ st with saved_grades := c }`, it answers `G` on `{ st with saved_grades := fill c }`. -/
theorem grade_fill_ok (st : Store V) (c : SavedGrades V) (p : Protocol.Phase)
    {G : Option (Block V)}
    (h : Store.grade C { st with saved_grades := c } p = .ok G) :
    Store.grade C { st with saved_grades := fill c } p = .ok G := by
  have hag := roundAgrees_make_round_grades_compatible_with st.F
    (roundAgrees_saved_round_grades_fill c (C.round_of st.s))
  simp only [Store.grade] at h ⊢
  exact read_of_resultAgrees (resultAgrees_phaseResult hag p) h

omit [Fintype V] in
/-- If `get_sg_root_with` answers `B` on `{ st with saved_grades := c }`, it answers `B` on
    `{ st with saved_grades := fill c }`. -/
theorem get_sg_root_with_fill_ok (st : Store V) (c : SavedGrades V) {B : Block V}
    (h : Protocol.get_sg_root_with C { st with saved_grades := c } = .ok B) :
    Protocol.get_sg_root_with C { st with saved_grades := fill c } = .ok B := by
  simp only [Protocol.get_sg_root_with] at h ⊢
  obtain ⟨a, ha, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [show Store.G1 C { st with saved_grades := fill c } = .ok a from
    grade_fill_ok C st c .g1 ha]
  exact h

omit [Fintype V] in
/-- If `confirmation_candidate` answers `Q` on `{ st with saved_grades := c }`, it answers `Q` on
    `{ st with saved_grades := fill c }`. -/
theorem confirmation_candidate_fill_ok (st : Store V) (c : SavedGrades V)
    {Q : Option (Block V)}
    (h : Protocol.confirmation_candidate C { st with saved_grades := c } = .ok Q) :
    Protocol.confirmation_candidate C { st with saved_grades := fill c } = .ok Q := by
  simp only [Protocol.confirmation_candidate] at h ⊢
  obtain ⟨a, ha, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [show Store.G2 C { st with saved_grades := fill c } = .ok a from
    grade_fill_ok C st c .g2 ha, NoRaise.DRE.bind_ok]
  exact h

/-- If `get_head_in_tree_with_layer` answers `H` on `{ st with saved_grades := c }`, it answers `H`
    on `{ st with saved_grades := fill c }`. -/
theorem get_head_in_tree_with_layer_fill_ok (st : Store V) (c : SavedGrades V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    {H : Block V}
    (h : Protocol.get_head_in_tree_with_layer C { st with saved_grades := c } tree votes
      support_votes s = .ok H) :
    Protocol.get_head_in_tree_with_layer C { st with saved_grades := fill c } tree votes
      support_votes s = .ok H := by
  simp only [Protocol.get_head_in_tree_with_layer] at h ⊢
  exact DRE.bind_agree (fun _ ha => get_sg_root_with_fill_ok C st c ha) (fun _ h => h) h

/-- If `get_head_with` answers `H` on `{ st with saved_grades := c }`, it answers `H` on
    `{ st with saved_grades := fill c }`. -/
theorem get_head_with_fill_ok (st : Store V) (c : SavedGrades V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) {H : Block V}
    (h : Protocol.get_head_with C { st with saved_grades := c } votes support_votes s =
      .ok H) :
    Protocol.get_head_with C { st with saved_grades := fill c } votes support_votes s =
      .ok H :=
  get_head_in_tree_with_layer_fill_ok C st c _ votes support_votes s h

/-- If `get_fg_vote_with` answers `out` on `{ st with saved_grades := c }`, it answers `out` on
    `{ st with saved_grades := fill c }`. -/
theorem get_fg_vote_with_fill_ok (st : Store V) (c : SavedGrades V) (r : Round)
    (A_G2 : Option (Block V))
    {out : Option (Height × BlockId × Bool) × Height × BlockId × Height}
    (h : Protocol.get_fg_vote_with C { st with saved_grades := c } r A_G2 = .ok out) :
    Protocol.get_fg_vote_with C { st with saved_grades := fill c } r A_G2 = .ok out := by
  simp only [Protocol.get_fg_vote_with] at h ⊢
  refine DRE.bind_agree (fun _ ha => ha) (fun _ h => ?_) h
  refine DRE.bind_agree (fun _ ha => get_head_with_fill_ok C st c _ _ _ ha) (fun _ h => ?_) h
  exact DRE.bind_agree (fun _ ha => fg_source_with_fill_ok st c r A_G2 ha) (fun _ h => h) h

/-- If `attestation_input` answers `input` on `{ st with saved_grades := c }`, it answers `input` on
    `{ st with saved_grades := fill c }`. -/
theorem attestation_input_fill_ok (v : V) (st : Store V) (c : SavedGrades V)
    {input : Protocol.AttestationInput V}
    (h : Protocol.attestation_input C v { st with saved_grades := c } = .ok input) :
    Protocol.attestation_input C v { st with saved_grades := fill c } = .ok input := by
  simp only [Protocol.attestation_input] at h ⊢
  refine DRE.bind_agree (fun _ ha => grade2_block_with_fill_ok st c _ ha) (fun A_G2 h => ?_) h
  refine DRE.bind_agree (fun _ ha => get_fg_vote_with_fill_ok C st c _ A_G2 ha)
    (fun fv h => ?_) h
  obtain ⟨fields, h_j, J, h_F⟩ := fv
  exact DRE.bind_agree (fun _ ha => get_sg_vote_with_fill_ok st c _ A_G2 ha) (fun _ h => h) h

/-- If `build_attestation` answers `out` on `{ st with saved_grades := c }`, it answers `out` on
    `{ st with saved_grades := fill c }`. -/
theorem build_attestation_fill_ok (v : V) (st : Store V) (c : SavedGrades V)
    (sh : SigningHistory) {out : SigningHistory × Attestation V}
    (h : Protocol.build_attestation C v { st with saved_grades := c } sh = .ok out) :
    Protocol.build_attestation C v { st with saved_grades := fill c } sh = .ok out := by
  simp only [Protocol.build_attestation] at h ⊢
  exact DRE.bind_agree (fun _ ha => attestation_input_fill_ok C v st c ha) (fun _ h => h) h

/-- If `proposal_input` answers `input` on `{ st with saved_grades := c }`, it answers `input` on
    `{ st with saved_grades := fill c }`. -/
theorem proposal_input_fill_ok (X : External V) (v : V) (st : Store V) (c : SavedGrades V)
    {input : Protocol.ProposalInput V}
    (h : Protocol.proposal_input C X v { st with saved_grades := c } = .ok input) :
    Protocol.proposal_input C X v { st with saved_grades := fill c } = .ok input := by
  simp only [Protocol.proposal_input] at h ⊢
  refine DRE.bind_agree (fun _ ha => ha) (fun _ h => ?_) h
  exact DRE.bind_agree (fun _ ha => get_head_with_fill_ok C st c _ _ _ ha) (fun _ h => h) h

/-- If `build_proposal` answers `B` on `{ st with saved_grades := c }`, it answers `B` on
    `{ st with saved_grades := fill c }`. -/
theorem build_proposal_fill_ok (X : External V) (v : V) (st : Store V) (c : SavedGrades V)
    {B : Block V}
    (h : Protocol.build_proposal C X v { st with saved_grades := c } = .ok B) :
    Protocol.build_proposal C X v { st with saved_grades := fill c } = .ok B := by
  simp only [Protocol.build_proposal] at h ⊢
  refine DRE.bind_agree (fun _ ha => proposal_input_fill_ok C X v st c ha) (fun _ h => ?_) h
  exact DRE.bind_agree (fun _ ha => ha) (fun _ h => h) h

end Readers

/-! ## The store writes commute with replacing the saved grades -/

section Writers

variable {V : Type} [DecidableEq V] [Fintype V] (C : Config) (P : Provisional V)

private theorem getElem_fun {α β : Type} (f : α → β) (a : α) : f[a] = f a := rfl

omit [Fintype V] in
/-- Admitting an attestation commutes with replacing the saved grades. -/
theorem admit_attestation_with_saved_grades (st : Store V) (x : SavedGrades V)
    (row : Attestation V) :
    Protocol.admit_attestation C { st with saved_grades := x } row =
      { Protocol.admit_attestation C st row with saved_grades := x } := by
  have hadm : Protocol.attestation_admissible C { st with saved_grades := x } row =
      Protocol.attestation_admissible C st row := rfl
  simp only [Protocol.admit_attestation, Id.run, pure, hadm]
  split_ifs <;> rfl

omit [Fintype V] in
/-- Admitting a list of attestations commutes with replacing the saved grades. -/
theorem admit_attestations_with_saved_grades (st : Store V) (x : SavedGrades V)
    (rows : List (Attestation V)) :
    Protocol.admit_attestations C { st with saved_grades := x } rows =
      { Protocol.admit_attestations C st rows with saved_grades := x } := by
  simp only [Protocol.admit_attestations, Id.run, List.forIn_pure_yield_eq_foldl]
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.foldl_cons]
    rw [admit_attestation_with_saved_grades, ih]

/-- Admitting a Goldfish vote commutes with replacing the saved grades. -/
theorem on_goldfish_vote_checked_with_saved_grades (st : Store V) (x : SavedGrades V)
    (vote : GoldfishVote V) :
    Protocol.on_goldfish_vote_checked P { st with saved_grades := x } vote =
      { Protocol.on_goldfish_vote_checked P st vote with saved_grades := x } := by
  have hpool : ∀ s, Store.pool { st with saved_grades := x } s = st.pool s := fun _ => rfl
  simp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote, Id.run, pure,
    getElem_fun, hpool]
  split_ifs <;> rfl

omit [Fintype V] in
/-- Updating the finality fields commutes with replacing the saved grades. -/
theorem update_finality_with_saved_grades (st : Store V) (x : SavedGrades V) (B : Block V) :
    Protocol.update_finality { st with saved_grades := x } B =
      { Protocol.update_finality st B with saved_grades := x } := by
  simp only [Protocol.update_finality, Id.run, pure, getElem_fun]
  split_ifs <;> rfl

/-- Admitting a block commutes with replacing the saved grades. -/
theorem on_block_with_saved_grades (st : Store V) (x : SavedGrades V) (B : Block V) :
    Protocol.on_block C P { st with saved_grades := x } B =
      { Protocol.on_block C P st B with saved_grades := x } := by
  have hfold : ∀ (votes : List (GoldfishVote V)) (y : Store V),
      votes.foldl (fun b a => Protocol.on_goldfish_vote_checked P b a)
          { y with saved_grades := x } =
        { votes.foldl (fun b a => Protocol.on_goldfish_vote_checked P b a) y with
          saved_grades := x } := by
    intro votes
    induction votes with
    | nil => intro y; rfl
    | cons vote votes ih =>
      intro y
      simp only [List.foldl_cons]
      rw [on_goldfish_vote_checked_with_saved_grades, ih]
  have hadm : Protocol.block_admissible C P { st with saved_grades := x } B =
      Protocol.block_admissible C P st B := rfl
  simp only [Protocol.on_block, Id.run, pure, hadm]
  split_ifs
  · simp only [Protocol.add_block, Id.run, getElem_fun, List.forIn_pure_yield_eq_foldl,
      pure_bind]
    simp only [pure]
    rw [← admit_attestations_with_saved_grades, ← update_finality_with_saved_grades, ← hfold]
  · rfl

/-! ## The duties that return a store -/

/-- If `propose_block`, run from `l`, answers the store `out` and the list `l'` on
    `{ st with saved_grades := c }`, it answers `{ out with saved_grades := fill c }` and `l'` on
    `{ st with saved_grades := fill c }`. -/
theorem propose_block_fill_ok (X : External V) (v : V) (st : Store V) (c : SavedGrades V)
    (l : List (NamedObject V)) {out : Store V} {l' : List (NamedObject V)}
    (h : (Protocol.propose_block C P X v { st with saved_grades := c }).run l =
      .ok (out, l')) :
    (Protocol.propose_block C P X v { st with saved_grades := fill c }).run l =
      .ok ({ out with saved_grades := fill c }, l') := by
  simp only [Protocol.propose_block] at h ⊢
  refine DREB.bind_agree
    (fun _ _ ha => DREB.liftM_agree (fun _ hb => build_proposal_fill_ok C X v st c hb) ha)
    (fun B _ h => ?_) h
  refine DREB.bind_agree (fun _ _ ha => ha) (fun _ _ h => ?_) h
  obtain ⟨rfl, rfl⟩ := DREB.pure_run_eq h
  rw [on_block_with_saved_grades C P st (fill c) B, on_block_with_saved_grades C P st c B]
  exact DREB.pure_run _ _

/-- If `attest`, run from `l`, answers `out` and the list `l'` on `{ st with saved_grades := c }`,
    it answers `({ out.1 with saved_grades := fill c }, out.2)` and `l'` on
    `{ st with saved_grades := fill c }`. -/
theorem attest_fill_ok (v : V) (st : Store V) (c : SavedGrades V)
    (sh : SigningHistory) (l : List (NamedObject V)) {out : Store V × SigningHistory}
    {l' : List (NamedObject V)}
    (h : (Protocol.attest C v { st with saved_grades := c } sh).run l = .ok (out, l')) :
    (Protocol.attest C v { st with saved_grades := fill c } sh).run l =
      .ok (({ out.1 with saved_grades := fill c }, out.2), l') := by
  simp only [Protocol.attest] at h ⊢
  refine DREB.bind_agree
    (fun _ _ ha => DREB.liftM_agree (fun _ hb => build_attestation_fill_ok C v st c sh hb) ha)
    (fun r _ h => ?_) h
  refine DREB.bind_agree (fun _ _ ha => ha) (fun _ _ h => ?_) h
  obtain ⟨rfl, rfl⟩ := DREB.pure_run_eq h
  rw [admit_attestation_with_saved_grades C st (fill c) r.2,
    admit_attestation_with_saved_grades C st c r.2]
  exact DREB.pure_run _ _

/-- If `goldfish_vote`, run from `l`, answers the store `out` and the list `l'` on
    `{ st with saved_grades := c }`, it answers `{ out with saved_grades := fill c }` and `l'` on
    `{ st with saved_grades := fill c }`. -/
theorem goldfish_vote_fill_ok (v : V) (st : Store V) (c : SavedGrades V)
    (l : List (NamedObject V)) {out : Store V} {l' : List (NamedObject V)}
    (h : (Protocol.goldfish_vote C P v { st with saved_grades := c }).run l = .ok (out, l')) :
    (Protocol.goldfish_vote C P v { st with saved_grades := fill c }).run l =
      .ok ({ out with saved_grades := fill c }, l') := by
  simp only [Protocol.goldfish_vote] at h ⊢
  refine DREB.bind_agree (fun _ _ ha => ha) (fun _ _ h => ?_) h
  refine DREB.bind_agree (fun _ _ ha => ha) (fun _ _ h => ?_) h
  refine DREB.bind_agree (fun _ _ ha => ha) (fun _ _ h => ?_) h
  refine DREB.bind_agree
    (fun _ _ ha => DREB.liftM_agree
      (fun _ hb => get_head_in_tree_with_layer_fill_ok C st c _ _ _ _ hb) ha)
    (fun _ _ h => ?_) h
  split_ifs at h ⊢
  · refine DREB.bind_agree (fun _ _ ha => ha) (fun _ _ h => ?_) h
    obtain ⟨rfl, rfl⟩ := DREB.pure_run_eq h
    rw [on_goldfish_vote_checked_with_saved_grades P st (fill c),
      on_goldfish_vote_checked_with_saved_grades P st c]
    exact DREB.pure_run _ _
  · obtain ⟨rfl, rfl⟩ := DREB.pure_run_eq h
    exact DREB.pure_run _ _

/-- If `update_confirmation` answers the store `out` on `{ st with saved_grades := c }`, it answers
    `{ out with saved_grades := fill c }` on `{ st with saved_grades := fill c }`. -/
theorem update_confirmation_fill_ok (st : Store V) (c : SavedGrades V) (s : Slot)
    {out : Store V}
    (h : Protocol.update_confirmation C { st with saved_grades := c } s = .ok out) :
    Protocol.update_confirmation C { st with saved_grades := fill c } s =
      .ok { out with saved_grades := fill c } := by
  simp only [Protocol.update_confirmation] at h ⊢
  refine DRE.bind_agree (fun _ ha => ha) (fun _ h => ?_) h
  refine DRE.bind_agree (fun _ ha => ha) (fun _ h => ?_) h
  refine DRE.bind_agree (fun _ ha => get_sg_root_with_fill_ok C st c ha) (fun _ h => ?_) h
  refine DRE.bind_agree (fun _ ha => ha) (fun _ h => ?_) h
  refine DRE.bind_agree (fun _ ha => ha) (fun _ h => ?_) h
  refine DRE.bind_agree (fun _ ha => round_stable_root_fill_ok st c _ ha) (fun _ h => ?_) h
  refine DRE.bind_agree (fun _ ha => confirmation_candidate_fill_ok C st c ha)
    (fun _ h => ?_) h
  split_ifs at h ⊢ <;>
  · injection h with h
    subst h
    rfl

end Writers

/-! ## The filled members return the spec's answer -/

/-!
Each member reads the store through its tree (`Store.ofImage`), so the hypothesis of each lemma here
is the spec's answer on `Store.ofImage st`.
-/

namespace Member

open DecoupledConsensusModel.Sts.Record (Returns)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the spec's `propose_block`, run from the empty list, answers `out` and the objects `sent` on
    `st` with the saved grades `c` read through the tree and brought to the round the member reads,
    the member `duties_propose_block_with` at `c` can return `{ out with saved_grades := c }` and
    the image of the first block sent. -/
theorem duties_propose_block_with_returns_of_ok (c : SavedGrades V)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Store V) {out : Store V}
    {sent : List (NamedObject V)}
    (h : (Protocol.propose_block (Config.toSpec E hc cfg) (Provisional.toSpec E)
      (externalOfNode nd) nd.val_index { Store.ofImage st with saved_grades :=
        (Protocol.advance_to_round (st.contractOfImage c)
          ((Config.toSpec E hc cfg).round_of st.s)) }).run [] =
        .ok (out, sent)) :
    Returns (duties_propose_block_with c E hc cfg nd st)
      ({ out with saved_grades := c }, (firstSentBlock sent).map Block.toProofNamed) := by
  unfold duties_propose_block_with
  rw [returns_successOutcomes, propose_block_fill_ok _ _ _ _ (Store.ofImage st) _ [] h]
  rfl

/-- If the spec's `attest`, run from the empty list, answers `out` and the objects `sent` on `st`
    with the saved grades `c` read through the tree and brought to the round the member reads, and
    the first attestation of `sent` is `a`, the member `duties_attest_with` at `c` can return
    `{ out.1 with saved_grades := c }`, the signing history `out.2` and `a`'s image. -/
theorem duties_attest_with_returns_of_ok (c : SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Store V) (sh : SigningHistory)
    {out : Store V × SigningHistory} {sent : List (NamedObject V)}
    (h : (Protocol.attest (Config.toSpec E hc unreadHeightConfig) nd.val_index
      { Store.ofImage st with saved_grades :=
        (Protocol.advance_to_round (st.contractOfImage c)
          ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) } sh).run [] = .ok (out, sent))
    {a : Attestation V} (ha : firstSentAttestation sent = some a) :
    Returns (duties_attest_with c E hc nd st sh)
      ({ out.1 with saved_grades := c }, out.2, a.toProofNamed) := by
  unfold duties_attest_with
  rw [returns_successOutcomes, attest_fill_ok _ _ (Store.ofImage st) _ sh [] h]
  simp only [NoRaise.DRE.bind_ok]
  rw [show (liftM (firstSentAttestation sent) : DC.DRE (Attestation V)) = .ok a by rw [ha]; rfl]
  rfl

/-- If the spec's `update_confirmation` answers `out` on `st` with the saved grades `c` read through
    the tree and brought to the round the member reads, the member `duties_update_confirmation_with`
    at `c` can return `{ out with saved_grades := c }`. -/
theorem duties_update_confirmation_with_returns_of_ok (c : SavedGrades V)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : Store V) (s : Slot) {out : Store V}
    (h : Protocol.update_confirmation (Config.toSpec E hc unreadHeightConfig)
      { Store.ofImage st with saved_grades :=
        (Protocol.advance_to_round (st.contractOfImage c)
          ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) } s = .ok out) :
    Returns (duties_update_confirmation_with c E hc st s) { out with saved_grades := c } := by
  unfold duties_update_confirmation_with
  rw [returns_successOutcomes, update_confirmation_fill_ok _ (Store.ofImage st) _ s h]
  rfl

/-- If the spec's `goldfish_vote`, run from the empty list, answers `out` and the objects `sent` on
    `st` with the saved grades `c` read through the tree and brought to the round the member reads,
    the member `duties_goldfish_vote_with` at `c` can return `{ out with saved_grades := c }` and
    the image of the first vote sent. -/
theorem duties_goldfish_vote_with_returns_of_ok (c : SavedGrades V)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Store V) {out : Store V}
    {sent : List (NamedObject V)}
    (h : (Protocol.goldfish_vote (Config.toSpec E hc unreadHeightConfig) (Provisional.toSpec E)
      nd.val_index { Store.ofImage st with saved_grades :=
        (Protocol.advance_to_round (st.contractOfImage c)
          ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) }).run [] = .ok (out, sent)) :
    Returns (duties_goldfish_vote_with c E hc nd st)
      ({ out with saved_grades := c },
        (firstSentGoldfishVote sent).map GoldfishVote.toProof) := by
  unfold duties_goldfish_vote_with
  rw [returns_successOutcomes, goldfish_vote_fill_ok _ _ _ (Store.ofImage st) _ [] h]
  rfl

end Member

end SpecDraftRecord
