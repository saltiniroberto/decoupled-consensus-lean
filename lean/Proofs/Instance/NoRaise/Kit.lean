import Spec.Broadcast

/-!
# The no-raise kit over `DRE` and `DREB`

Lemmas saying that a composite answers when its parts answer: binds in `DRE` and `DREB`, the lift
out of `Option`, raising filters and maps, `for` loops over a list, `pure`, lifts and `broadcast` in
`DREB`. The statement shape is `∃ v, x = .ok v` for `DRE`, and `∃ out, x.run l = .ok out` for
`DREB`.
-/

set_option autoImplicit false

open DC (DRE)

namespace SpecRecord.NoRaise

/-! ## `DRE` -/

/-- `Except.ok a >>= f` is `f a`. -/
theorem DRE.bind_ok {α β : Type} (a : α) (f : α → DRE β) :
    (Except.ok a >>= f : DRE β) = f a := rfl

/-- A bind in `DRE` of two parts that answer, answers. -/
theorem DRE.bind_ok_of {α β : Type} {x : DRE α} {f : α → DRE β}
    (hx : ∃ a, x = .ok a) (hf : ∀ a, ∃ b, f a = .ok b) :
    ∃ b, (x >>= f : DRE β) = .ok b := by
  obtain ⟨a, rfl⟩ := hx
  exact hf a

/-- If `x` answers some `a` with `P a`, and `f a` answers some `b` with `Q b` whenever `P a`, then
    `x >>= f` answers some `b` with `Q b`. -/
theorem DRE.bind_ok_post {α β : Type} {x : DRE α} {f : α → DRE β} {P : α → Prop}
    {Q : β → Prop} (hx : ∃ a, x = .ok a ∧ P a) (hf : ∀ a, P a → ∃ b, f a = .ok b ∧ Q b) :
    ∃ b, (x >>= f : DRE β) = .ok b ∧ Q b := by
  obtain ⟨a, rfl, ha⟩ := hx
  exact hf a ha

/-- If `x >>= f` answers `b`, then `x` answers some `a` and `f a` answers `b`. -/
theorem DRE.of_bind_ok {α β : Type} {x : DRE α} {f : α → DRE β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

open scoped DC in
/-- The raising lift out of `Option` answers on a present value. -/
theorem optionLift_ok {α : Type} {x : Option α} (h : x ≠ none) :
    ∃ a, (liftM x : DRE α) = .ok a := by
  obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp h
  exact ⟨a, rfl⟩

/-! ## The raising filters and maps -/

/-- If the test `p` answers on every member `a` of `s`, and answers `true` only where `Q a` holds,
    then `s.filterM p` answers a set whose every member is a member of `s` with `Q`. -/
theorem filterM_post {α : Type} [DecidableEq α] (p : α → DRE Bool) (s : Finset α)
    (Q : α → Prop) (h : ∀ a ∈ s, ∃ b, p a = .ok b ∧ (b = true → Q a)) :
    ∃ v, s.filterM p = .ok v ∧ ∀ a ∈ v, a ∈ s ∧ Q a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | @insert a s ha ih =>
      obtain ⟨b, hb, hbQ⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨v, hv, hvs⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      simp only [Finset.filterM, Finset.fold_insert ha] at *
      simp only [hb, DRE.bind_ok, Finset.unionM, hv]
      cases b
      · refine ⟨_, rfl, fun x hx => ?_⟩
        rcases Finset.mem_union.mp hx with hx | hx
        · exact absurd hx (Finset.notMem_empty x)
        · exact ⟨Finset.mem_insert_of_mem (hvs x hx).1, (hvs x hx).2⟩
      · refine ⟨_, rfl, fun x hx => ?_⟩
        rcases Finset.mem_union.mp hx with hx | hx
        · rw [Finset.mem_singleton.mp hx]
          exact ⟨Finset.mem_insert_self a s, hbQ rfl⟩
        · exact ⟨Finset.mem_insert_of_mem (hvs x hx).1, (hvs x hx).2⟩

/-- A raising filter over a finite set answers when its test answers on every member. -/
theorem filterM_ok {α : Type} [DecidableEq α] (p : α → DRE Bool) (s : Finset α)
    (h : ∀ a ∈ s, ∃ b, p a = .ok b) : ∃ v, s.filterM p = .ok v := by
  obtain ⟨v, hv, -⟩ := filterM_post p s (fun _ => True)
    (fun a ha => (h a ha).imp fun _ hb => ⟨hb, fun _ => trivial⟩)
  exact ⟨v, hv⟩

/-- A raising filter over a list answers when its test answers on every member of the list. -/
theorem List.filterM_ok {α : Type} (p : α → DRE Bool) (l : List α)
    (h : ∀ a ∈ l, ∃ b, p a = .ok b) : ∃ v, l.filterM p = .ok v := by
  have aux : ∀ (l : List α) (acc : List α), (∀ a ∈ l, ∃ b, p a = .ok b) →
      ∃ v, (List.filterAuxM p l acc : DRE (List α)) = .ok v := by
    intro l
    induction l with
    | nil => intro acc _; exact ⟨acc, rfl⟩
    | cons a l ih =>
        intro acc h
        obtain ⟨b, hb⟩ := h a (List.mem_cons_self)
        simp only [List.filterAuxM, hb, DRE.bind_ok]
        exact ih _ (fun x hx => h x (List.mem_cons_of_mem a hx))
  obtain ⟨v, hv⟩ := aux l [] h
  simp only [List.filterM, hv, DRE.bind_ok]
  exact ⟨_, rfl⟩

/-- A raising map over a list answers when the function answers on every member of the list. -/
theorem List.mapM_ok {α β : Type} (f : α → DRE β) (l : List α)
    (h : ∀ a ∈ l, ∃ b, f a = .ok b) : ∃ v, l.mapM f = .ok v := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
      obtain ⟨b, hb⟩ := h a (List.mem_cons_self)
      obtain ⟨v, hv⟩ := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      rw [List.mapM_cons, hb, DRE.bind_ok, hv, DRE.bind_ok]
      exact ⟨_, rfl⟩

/-- A `for` loop over a list in `DRE` answers when its body answers at every element and every
    state. -/
theorem List.forIn_ok {α β : Type} (l : List α) (init : β)
    (body : α → β → DRE (ForInStep β)) (h : ∀ a b, ∃ s, body a b = .ok s) :
    ∃ v, (forIn l init body : DRE β) = .ok v := by
  induction l generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons a l ih =>
      rw [List.forIn_cons]
      refine DRE.bind_ok_of (h a init) ?_
      intro s
      cases s with
      | done b => exact ⟨b, rfl⟩
      | yield b => exact ih b

/-! ## `DREB` -/

/-- A bind in `DREB` answers from the list `l` when `x` answers from `l` and `f a` answers from
    every list for every `a`. -/
theorem DREB.bind_ok_of {V α β : Type} {x : Spec.DREB V α}
    {f : α → Spec.DREB V β} {l : List (Spec.NamedObject V)}
    (hx : ∃ p, x.run l = .ok p) (hf : ∀ a l', ∃ q, (f a).run l' = .ok q) :
    ∃ q, (x >>= f).run l = .ok q := by
  obtain ⟨⟨a, l'⟩, hx⟩ := hx
  rw [StateT.run_bind, hx, DRE.bind_ok]
  exact hf a l'

/-- `pure a` in `DREB` answers. -/
theorem DREB.pure_ok {V α : Type} (a : α) (l : List (Spec.NamedObject V)) :
    ∃ q, (pure a : Spec.DREB V α).run l = .ok q := ⟨(a, l), rfl⟩

/-- A `DRE` routine that answers, lifted into `DREB`, answers. -/
theorem DREB.liftM_ok {V α : Type} {x : DRE α} (hx : ∃ a, x = .ok a)
    (l : List (Spec.NamedObject V)) :
    ∃ q, (liftM x : Spec.DREB V α).run l = .ok q := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨(a, l), rfl⟩

/-- `broadcast m` answers. -/
theorem DREB.broadcast_ok {V : Type} (m : Spec.NamedObject V)
    (l : List (Spec.NamedObject V)) :
    ∃ q, (Spec.broadcast m).run l = .ok q := ⟨((), l ++ [m]), rfl⟩

end SpecRecord.NoRaise
