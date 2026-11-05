module
public import Goldilocks.AC.Confirmation
import all Goldilocks.AC.Confirmation

@[expose] public section

/-!
# Raising filters and images, the unique pick, the deepest block

The facts about the set operations of the routines that every walk lemma reads:

- raising filters (`Finset.filterM` at `DRE`): `filterM_eq_ok_filter`, `filterM_ok_total`,
  `mem_of_filterM_eq_ok_iff`, `filterM_eq_ok_of_total`;
- raising images (`Finset.imageM` at `DRE`): `imageM_eq_ok_image`, `mem_of_imageM_eq_ok`;
- binds: `dre_bind_ok`;
- the unique pick: `pickUnique?_eq_some`, `pickUnique?_eq_none`, `mem_of_pickUnique?_eq_some`;
- the values of a set of options: `present_mem_iff`;
- the deepest block: `deepest?_mem`, `deepest?_eq_some`.

The generic lemmas take their own binders, so that their statements do not depend on the
section variables of the file.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

/-! ## Raising filters -/

/-- A raising filter whose test answers, on every member, whether the member satisfies `q`,
answers the filter of the set by `q`.

The variables:
- `p`: the raising test; `q`: the predicate it decides; `s`: the set filtered. -/
theorem filterM_eq_ok_filter {α : Type} [DecidableEq α] (p : α → DRE Bool) (q : α → Prop)
    [DecidablePred q] (s : Finset α)
    -- the test answers, on every member of `s`, whether the member satisfies `q`
    (h : ∀ a ∈ s, p a = .ok (decide (q a))) : s.filterM p = .ok (s.filter q) := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.filterM]; rfl
  | @insert a s ha ih =>
    have hstep : (insert a s).filterM p =
        Finset.unionM (do if ← p a then return {a} else return ∅) (s.filterM p) := by
      simp only [Finset.filterM, Finset.fold_insert ha]
    rw [hstep, h a (Finset.mem_insert_self a s),
      ih (fun b hb => h b (Finset.mem_insert_of_mem hb)), Finset.filter_insert]
    by_cases hq : q a
    · simp [Finset.unionM, hq, bind, Except.bind, pure, Except.pure]
    · simp [Finset.unionM, hq, bind, Except.bind, pure, Except.pure]

/-- A raising filter that answers answers on every member of the set.

The variables:
- `p`: the raising test; `s`: the set. -/
theorem filterM_ok_total {α : Type} [DecidableEq α] (p : α → DRE Bool) (s : Finset α) :
    ∀ R : Finset α, s.filterM p = .ok R → ∀ a ∈ s, ∃ b : Bool, p a = .ok b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro R h
    have hstep : (insert a s).filterM p =
        Finset.unionM (do if ← p a then return {a} else return ∅) (s.filterM p) := by
      simp only [Finset.filterM, Finset.fold_insert ha]
    rw [hstep] at h
    cases hp : p a with
    | error e => simp [hp, Finset.unionM, bind, Except.bind] at h
    | ok b =>
      cases hs : s.filterM p with
      | error e =>
        cases b <;> simp [hp, hs, Finset.unionM, bind, Except.bind, pure, Except.pure] at h
      | ok R' =>
        intro x hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact ⟨b, hx ▸ hp⟩
        · exact ih R' hs x hx

open Classical in
/-- The answer of a raising filter holds exactly the members on which the test answers `true`.

The variables:
- `p`: the raising test; `s`: the set; `R`: the answer; `a`: the member tested. -/
theorem mem_of_filterM_eq_ok_iff {α : Type} [DecidableEq α] (p : α → DRE Bool) (s : Finset α)
    (R : Finset α) (h : s.filterM p = .ok R) (a : α) : a ∈ R ↔ a ∈ s ∧ p a = .ok true := by
  have htot := filterM_ok_total p s R h
  have h' := filterM_eq_ok_filter p (fun a => p a = .ok true) s (fun a ha => by
    obtain ⟨b, hb⟩ := htot a ha
    rw [hb]
    cases b <;> simp)
  rw [h] at h'
  cases h'
  exact Finset.mem_filter

/-- A raising filter whose test answers on every member answers.

The variables:
- `p`: the raising test; `s`: the set. -/
theorem filterM_eq_ok_of_total {α : Type} [DecidableEq α] (p : α → DRE Bool) (s : Finset α)
    -- the test answers on every member of `s`
    (h : ∀ a ∈ s, ∃ b : Bool, p a = .ok b) : ∃ R : Finset α, s.filterM p = .ok R := by
  classical
  exact ⟨_, filterM_eq_ok_filter p (fun a => p a = .ok true) s (fun a ha => by
    obtain ⟨b, hb⟩ := h a ha
    rw [hb]
    cases b <;> simp)⟩

/-! ## Binds -/

/-- A bind on an answer continues with it.

The variables:
- `a`: the answer; `f`: the continuation. -/
theorem dre_bind_ok {α β : Type} (a : α) (f : α → DRE β) :
    (Except.ok a >>= f : DRE β) = f a := rfl

/-! ## Raising images -/

/-- A raising image whose function answers `g a` on every member `a` answers the image of the set
by `g`.

The variables:
- `f`: the raising function; `g`: the function it computes; `s`: the set. -/
theorem imageM_eq_ok_image {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → DRE β)
    (g : α → β) (s : Finset α)
    -- the function answers `g a` on every member `a` of `s`
    (h : ∀ a ∈ s, f a = .ok (g a)) : s.imageM f = .ok (s.image g) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    have hstep : (insert a s).imageM f =
        Finset.unionM (do return {← f a}) (s.imageM f) := by
      simp only [Finset.imageM, Finset.fold_insert ha]
    rw [hstep, h a (Finset.mem_insert_self a s),
      ih (fun b hb => h b (Finset.mem_insert_of_mem hb)), Finset.image_insert]
    simp only [Finset.unionM, bind, Except.bind, pure, Except.pure]
    rw [Finset.insert_eq]

/-- Every member of the answer of a raising image is the answer of the function on a member of
the set.

The variables:
- `f`: the raising function; `s`: the set; `S`: the answer; `b`: the member of the answer. -/
theorem mem_of_imageM_eq_ok {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → DRE β)
    (s : Finset α) (S : Finset β) (h : s.imageM f = .ok S) (b : β) (hb : b ∈ S) :
    ∃ a ∈ s, f a = .ok b := by
  induction s using Finset.induction_on generalizing S with
  | empty =>
    simp only [Finset.imageM, Finset.fold_empty, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hb
  | @insert a s ha ih =>
    have hstep : (insert a s).imageM f =
        Finset.unionM (do return {← f a}) (s.imageM f) := by
      simp only [Finset.imageM, Finset.fold_insert ha]
    rw [hstep] at h
    cases hf : f a with
    | error e => simp [hf, Finset.unionM, bind, Except.bind] at h
    | ok b' =>
      cases hs : s.imageM f with
      | error e => simp [hf, hs, Finset.unionM, bind, Except.bind, pure, Except.pure] at h
      | ok S' =>
        simp only [hf, hs, Finset.unionM, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        rcases Finset.mem_union.1 hb with hb | hb
        · rw [Finset.mem_singleton.1 hb]
          exact ⟨a, Finset.mem_insert_self a s, hf⟩
        · obtain ⟨a', ha', hfa'⟩ := ih S' hs hb
          exact ⟨a', Finset.mem_insert_of_mem ha', hfa'⟩

/-! ## The unique pick -/

/-- `pickUnique? T p` is `a` when `a` is the one member of `T` that passes `p`.

The variables:
- `T`: the set; `p`: the test; `a`: the member that passes it. -/
theorem pickUnique?_eq_some {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool} {a : α}
    (ha : a ∈ T) (hp : p a = true)
    -- every member of `T` that passes `p` is `a`
    (hu : ∀ b ∈ T, p b = true → b = a) :
    pickUnique? T p = some a := by
  have h : ∃! a, a ∈ T ∧ p a = true := ⟨a, ⟨ha, hp⟩, fun b hb => hu b hb.1 hb.2⟩
  unfold pickUnique?
  rw [dif_pos h]
  exact congrArg some (hu _ (Finset.choose_mem _ _ h) (Finset.choose_property _ _ h))

/-- `pickUnique? T p` is `none` when no member of `T` passes `p`.

The variables:
- `T`: the set; `p`: the test. -/
theorem pickUnique?_eq_none {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    -- no member of `T` passes `p`
    (h : ∀ b ∈ T, p b = false) : pickUnique? T p = none := by
  unfold pickUnique?
  rw [dif_neg]
  rintro ⟨a, ⟨ha, hp⟩, -⟩
  simp [h a ha] at hp

/-- The member `pickUnique?` picks belongs to the set and passes the test.

The variables:
- `T`: the set; `p`: the test; `a`: the member picked. -/
theorem mem_of_pickUnique?_eq_some {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    {a : α} (h : pickUnique? T p = some a) : a ∈ T ∧ p a = true := by
  unfold pickUnique? at h
  split at h
  · rename_i hu
    cases h
    exact ⟨Finset.choose_mem _ _ hu, Finset.choose_property _ _ hu⟩
  · cases h

/-! ## The values of a set of options -/

/-- A value is among the values of a set of options exactly when the set holds it as an option.

The variables:
- `S`: the set of options; `a`: the value. -/
theorem present_mem_iff {α : Type} [DecidableEq α] (S : Finset (Option α)) (a : α) :
    a ∈ present S ↔ some a ∈ S := by
  simp [present]

/-! ## The deepest block -/

section Deepest

variable {V : Type} [DecidableEq V] [RootOrder]

/-- The deepest block of a set belongs to the set.

The variables:
- `T`: the set; `B`: its deepest block. -/
theorem deepest?_mem {T : Finset (Block V)} {B : Block V} (h : Block.deepest? T = some B) :
    B ∈ T :=
  (mem_of_pickUnique?_eq_some h).1

/-- A member of a set that has the greatest depth, and is the only member of that depth, is the
set's deepest block.

The variables:
- `T`: the set; `B`: the member. -/
theorem deepest?_eq_some {T : Finset (Block V)} {B : Block V} (hB : B ∈ T)
    -- no member of `T` is deeper than `B`
    (hle : ∀ C ∈ T, C.depth ≤ B.depth)
    -- every member of `T` with `B`'s depth is `B`
    (heq : ∀ C ∈ T, C.depth = B.depth → C = B) : Block.deepest? T = some B := by
  -- no member of `T` is deeper than `B` in the order `Block.deeper`
  have hdeep : Block.isDeepestIn T B = true := by
    simp only [Block.isDeepestIn, decide_eq_true_eq]
    intro C hC
    by_cases hd : C.depth = B.depth
    · rw [heq C hC hd]
      simp [Block.deeper, RootOrder.irrefl]
    · have h1 : ¬ B.depth < C.depth := by have := hle C hC; omega
      have h2 : ¬ B.depth = C.depth := fun h => hd h.symm
      simp [Block.deeper, h1, h2]
  refine pickUnique?_eq_some hB hdeep fun D hD hDdeep => ?_
  simp only [Block.isDeepestIn, decide_eq_true_eq] at hDdeep
  have hBD := hDdeep B hB
  have hlt : ¬ D.depth < B.depth := by
    intro hlt
    simp [Block.deeper, hlt] at hBD
  exact heq D hD (by have := hle D hD; omega)

end Deepest

end GoldilocksCorrectness.Proofs.Routines
