module
public import GoldilocksCorrectness.Statements.Routines.ObjectDefs

@[expose] public section

/-!
# What every answer of a routine satisfies, and what a duty sends

The outcome-set kit, over the routines of the spec that may fail (`DRE`) or that may fail and send
objects (`DREB`):

- `DREPost m Q`, `DREBPost m Q`: every answer of `m` satisfies `Q`;
- `DREBRuns R m`, `DREBSpec R m`: every answer of `m` and the list of objects `m` appends to the
  objects sent satisfy `R` together;
- `DREBEmits L m`: the list of objects `m` appends satisfies `L`; `DREBSends Q m`: every object
  `m` sends satisfies `Q`;
- their composition lemmas, which walk a routine's `do` block as written: a bind, an `if`, a
  lift, a return, a broadcast; and their readings at an `.ok` outcome of the duty
  (`Goldilocks.DREB.outcomes`): `….of_outcome`, `Goldilocks.DREB.run_eq_of_mem_outcomes`,
  `Goldilocks.DREB.run_mem_outcomes`, `Wiring.DREBOutcomesOk.exists_ok`;
- `forIn_yield_inv` (a `for` loop whose body always continues), `fun_getElem`,
  `ok_of_bind_eq_ok`.

They read the routines alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks

section

variable {V : Type}

/-- `DREPost m Q`: every answer of the routine `m`, which may fail, satisfies `Q`.

Read aloud: if `m` answers `a`, then `Q a`. -/
def DREPost {α : Type} (m : DRE α) (Q : (a : α) → Prop) : Prop :=
  ∀ a, m = .ok a → Q a

/-- `DREBPost m Q`: every answer of the routine `m`, which may fail and sends objects, satisfies
`Q`, whatever was sent before it ran.

Read aloud: if `m`, run after any list of objects sent, answers `a`, then `Q a`. -/
def DREBPost {α : Type} (m : DREB V α) (Q : (a : α) → Prop) : Prop :=
  ∀ out a out', m.run out = .ok (a, out') → Q a

/-- A routine that returns `a` satisfies `Q` when `a` does. -/
theorem DREPost.pure {α : Type} {Q : α → Prop} {a : α} (h : Q a) :
    DREPost (Pure.pure a : DRE α) Q := by
  intro a' ha
  cases ha
  exact h

/-- Every answer of a routine satisfies `True`. -/
theorem DREPost.true {α : Type} (x : DRE α) : DREPost x (fun _ => True) :=
  fun _ _ => trivial

/-- A weaker postcondition follows from a stronger one. -/
theorem DREPost.mono {α : Type} {m : DRE α} {P Q : α → Prop} (h : DREPost m P)
    (hPQ : ∀ a, P a → Q a) : DREPost m Q :=
  fun a ha => hPQ a (h a ha)

/-- A bind satisfies `Q` when its first routine's answers satisfy `P` and the continuation,
from any answer satisfying `P`, satisfies `Q`. -/
theorem DREPost.bind {α β : Type} {x : DRE α} {f : α → DRE β} {P : α → Prop} {Q : β → Prop}
    (hx : DREPost x P) (hf : ∀ a, P a → DREPost (f a) Q) : DREPost (x >>= f) Q := by
  intro b hb
  cases hxa : x with
  | error e => rw [hxa] at hb; cases hb
  | ok a => rw [hxa] at hb; exact hf a (hx a hxa) b hb

/-- A bind satisfies `Q` when the continuation does from any answer. -/
theorem DREPost.bind_any {α β : Type} {x : DRE α} {f : α → DRE β} {Q : β → Prop}
    (hf : ∀ a, DREPost (f a) Q) : DREPost (x >>= f) Q :=
  DREPost.bind (DREPost.true x) (fun a _ => hf a)

/-- A dependent `if` satisfies `Q` when both of its branches do. -/
theorem DREPost.dite {α : Type} {c : Prop} [Decidable c] {A : c → DRE α} {B : ¬c → DRE α}
    {Q : α → Prop} (hA : ∀ h, DREPost (A h) Q) (hB : ∀ h, DREPost (B h) Q) :
    DREPost (if h : c then A h else B h) Q := by
  by_cases h : c
  · rw [dif_pos h]; exact hA h
  · rw [dif_neg h]; exact hB h

/-- An `if` satisfies `Q` when both of its branches do. -/
theorem DREPost.ite {α : Type} {c : Prop} [Decidable c] {A B : DRE α}
    {Q : α → Prop} (hA : c → DREPost A Q) (hB : ¬ c → DREPost B Q) :
    DREPost (if c then A else B) Q := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

/-- A routine that returns `a` and sends nothing satisfies `Q` when `a` does. -/
theorem DREBPost.pure {α : Type} {Q : α → Prop} {a : α} (h : Q a) :
    DREBPost (Pure.pure a : DREB V α) Q := by
  intro out a' out' ha
  cases ha
  exact h

/-- Every answer of a routine satisfies `True`. -/
theorem DREBPost.true {α : Type} (x : DREB V α) : DREBPost x (fun _ => True) :=
  fun _ _ _ _ => trivial

/-- A weaker postcondition follows from a stronger one. -/
theorem DREBPost.mono {α : Type} {m : DREB V α} {P Q : α → Prop} (h : DREBPost m P)
    (hPQ : ∀ a, P a → Q a) : DREBPost m Q :=
  fun out a out' ha => hPQ a (h out a out' ha)

/-- A bind satisfies `Q` when its first routine's answers satisfy `P` and the continuation,
from any answer satisfying `P`, satisfies `Q`. -/
theorem DREBPost.bind {α β : Type} {x : DREB V α} {f : α → DREB V β} {P : α → Prop}
    {Q : β → Prop} (hx : DREBPost x P) (hf : ∀ a, P a → DREBPost (f a) Q) :
    DREBPost (x >>= f) Q := by
  intro out b out' hb
  have hb' : (x.run out >>= fun p => (f p.1).run p.2) = .ok (b, out') := hb
  cases hxa : x.run out with
  | error e => rw [hxa] at hb'; cases hb'
  | ok p => rw [hxa] at hb'; exact hf p.1 (hx out p.1 p.2 hxa) p.2 b out' hb'

/-- A bind satisfies `Q` when the continuation does from any answer. -/
theorem DREBPost.bind_any {α β : Type} {x : DREB V α} {f : α → DREB V β} {Q : β → Prop}
    (hf : ∀ a, DREBPost (f a) Q) : DREBPost (x >>= f) Q :=
  DREBPost.bind (DREBPost.true x) (fun a _ => hf a)

/-- A routine that may fail, run without sending, satisfies what it satisfies on its own. -/
theorem DREBPost.liftM {α : Type} {m : DRE α} {Q : α → Prop} (h : DREPost m Q) :
    DREBPost (liftM m : DREB V α) Q := by
  intro out a out' ha
  cases hm : m with
  | error e => rw [hm] at ha; cases ha
  | ok a' => rw [hm] at ha; cases ha; exact h _ hm

/-- A routine that may fail, lifted into a duty, satisfies what it satisfies on its own. -/
theorem DREBPost.monadLift {α : Type} {m : DRE α} {Q : α → Prop} (h : DREPost m Q) :
    DREBPost (MonadLift.monadLift m : DREB V α) Q := by
  intro out a out' ha
  cases hm : m with
  | error e => rw [hm] at ha; cases ha
  | ok a' => rw [hm] at ha; cases ha; exact h _ hm

/-- An `if` satisfies `Q` when both of its branches do. -/
theorem DREBPost.ite {α : Type} {c : Prop} [Decidable c] {A B : DREB V α}
    {Q : α → Prop} (hA : c → DREBPost A Q) (hB : ¬ c → DREBPost B Q) :
    DREBPost (if c then A else B) Q := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

/-- A dependent `if` satisfies `Q` when both of its branches do. -/
theorem DREBPost.dite {α : Type} {c : Prop} [Decidable c] {A : c → DREB V α}
    {B : ¬c → DREB V α} {Q : α → Prop} (hA : ∀ h, DREBPost (A h) Q)
    (hB : ∀ h, DREBPost (B h) Q) : DREBPost (if h : c then A h else B h) Q := by
  by_cases h : c
  · rw [dif_pos h]; exact hA h
  · rw [dif_neg h]; exact hB h

end

end

section

open Goldilocks

/-- A `for` loop over the list `l` whose body always continues with `f`, from a value satisfying
`Inv`, ends at a value satisfying `Inv`, when every step `f` keeps `Inv`.

The variables:
- `l`: the list walked; `init`: the starting value; `f`: the body; `Inv`: the invariant. -/
theorem forIn_yield_inv {α β : Type} (l : List α) (init : β) (f : β → α → β) (Inv : β → Prop)
    (hinit : Inv init) (hf : ∀ b a, a ∈ l → Inv b → Inv (f b a)) :
    Inv (forIn (m := Id) l init (fun a b => Pure.pure (ForInStep.yield (f b a)))) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a l ih =>
      rw [List.forIn_cons]
      exact ih (f init a) (hf init a List.mem_cons_self hinit)
        (fun b a' ha' hb => hf b a' (List.mem_cons_of_mem _ ha') hb)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A map read with the protocol's brackets is the map applied. -/
theorem fun_getElem {α β : Type} (f : α → β) (a : α) : f[a] = f a := rfl

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [Fintype V] [RootOrder] in
/-- A bind that answers has a first routine that answers. -/
theorem ok_of_bind_eq_ok {α β : Type} {x : DRE α} {f : α → DRE β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a : α, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

end

end

section

open Goldilocks

section

variable {V : Type}

/-- `DREBRuns R m`: for every list `sent₀` of objects sent before `m` runs and every answer
`(a, sent)` of `m.run sent₀`, the list `sent` is `sent₀ ++ l` for some list `l` with `R a l`.

Read aloud: `m`'s answer and what `m` appends satisfy `R` together. -/
def DREBRuns {α : Type} (R : α → List (NamedObject V) → Prop) (m : DREB V α) : Prop :=
  ∀ (sent₀ : List (NamedObject V)) (a : α) (sent : List (NamedObject V)),
    m.run sent₀ = .ok (a, sent) → ∃ l, sent = sent₀ ++ l ∧ R a l

/-- A weaker relation follows from a stronger one. -/
theorem DREBRuns.mono {α : Type} {m : DREB V α} {R R' : α → List (NamedObject V) → Prop}
    (h : DREBRuns R m) (hR : ∀ a l, R a l → R' a l) : DREBRuns R' m := by
  intro sent₀ a sent ha
  obtain ⟨l, hl, hr⟩ := h sent₀ a sent ha
  exact ⟨l, hl, hR a l hr⟩

/-- A return relates its value and the empty list. -/
theorem DREBRuns.pure {α : Type} {R : α → List (NamedObject V) → Prop} {a : α} (h : R a []) :
    DREBRuns R (Pure.pure a : DREB V α) := by
  intro sent₀ a' sent ha
  have ha' : (Except.ok (a, sent₀) : DRE (α × List (NamedObject V))) = .ok (a', sent) := ha
  cases ha'
  exact ⟨[], (List.append_nil _).symm, h⟩

/-- A bind relates its answer and what it appends by `R` when the continuation, from every answer
`a` of the first routine and every list `l₁` it appends with `R₁ a l₁`, relates its answer and
`l₁` followed by what it appends by `R`. -/
theorem DREBRuns.bind {α β : Type} {x : DREB V α} {f : α → DREB V β}
    {R₁ : α → List (NamedObject V) → Prop} {R : β → List (NamedObject V) → Prop}
    (hx : DREBRuns R₁ x)
    (hf : ∀ a l₁, R₁ a l₁ → DREBRuns (fun b l₂ => R b (l₁ ++ l₂)) (f a)) :
    DREBRuns R (x >>= f) := by
  intro out b out' hb
  have hb' : (x.run out >>= fun p => (f p.1).run p.2) = .ok (b, out') := hb
  cases hxa : x.run out with
  | error e => rw [hxa] at hb'; cases hb'
  | ok p =>
      rw [hxa] at hb'
      obtain ⟨l₁, hp, h₁⟩ := hx out p.1 p.2 hxa
      obtain ⟨l₂, h', h₂⟩ := hf p.1 l₁ h₁ p.2 b out' hb'
      exact ⟨l₁ ++ l₂, by rw [h', hp, List.append_assoc], h₂⟩

/-- An `if` relates what both of its branches relate. -/
theorem DREBRuns.ite {α : Type} {c : Prop} [Decidable c] {A B : DREB V α}
    {R : α → List (NamedObject V) → Prop} (hA : c → DREBRuns R A) (hB : ¬ c → DREBRuns R B) :
    DREBRuns R (if c then A else B) := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

/-- A bind on a lifted routine that may fail relates what its continuation relates, on every
answer of the routine. -/
theorem DREBRuns.liftM_bind {α β : Type} {m : DRE α} {f : α → DREB V β}
    {R : β → List (NamedObject V) → Prop} (hf : ∀ a, m = .ok a → DREBRuns R (f a)) :
    DREBRuns R (liftM m >>= f) := by
  intro sent₀ b sent hb
  cases hm : m with
  | error e => rw [hm] at hb; cases hb
  | ok a => rw [hm] at hb; exact hf a hm sent₀ b sent hb

end

end

section

open Goldilocks

section

variable {V : Type}

/-- `DREBSpec R m`: for every list `sent₀` of objects sent before `m` runs and every answer
`(a, sent)` of `m.run sent₀`, the list `sent` is `sent₀ ++ l` for some list `l` with `R a l`.

Read aloud: every answer of `m` is related by `R` to what `m` appends to the objects sent. -/
def DREBSpec {α : Type} (R : α → List (NamedObject V) → Prop) (m : DREB V α) : Prop :=
  ∀ (sent₀ : List (NamedObject V)) (a : α) (sent : List (NamedObject V)),
    m.run sent₀ = .ok (a, sent) → ∃ l, sent = sent₀ ++ l ∧ R a l

/-- A weaker relation follows from a stronger one. -/
theorem DREBSpec.mono {α : Type} {m : DREB V α} {R R' : α → List (NamedObject V) → Prop}
    (h : DREBSpec R m) (hR : ∀ a l, R a l → R' a l) : DREBSpec R' m := by
  intro sent₀ a sent ha
  obtain ⟨l, hl, hR'⟩ := h sent₀ a sent ha
  exact ⟨l, hl, hR a l hR'⟩

/-- A return appends nothing. -/
theorem DREBSpec.pure {α : Type} {R : α → List (NamedObject V) → Prop} {a : α} (h : R a []) :
    DREBSpec R (Pure.pure a : DREB V α) := by
  intro sent₀ a' sent ha
  have ha' : (Except.ok (a, sent₀) : DRE (α × List (NamedObject V))) = .ok (a', sent) := ha
  cases ha'
  exact ⟨[], (List.append_nil _).symm, h⟩

/-- A bind whose continuation, from an answer `a` of the first routine with what it appended
`l₁`, satisfies `R` with `l₁` prefixed. -/
theorem DREBSpec.bind' {α β : Type} {x : DREB V α} {f : α → DREB V β}
    {R₁ : α → List (NamedObject V) → Prop} {R : β → List (NamedObject V) → Prop}
    (hx : DREBSpec R₁ x)
    (hf : ∀ a l₁, R₁ a l₁ → DREBSpec (fun b l₂ => R b (l₁ ++ l₂)) (f a)) :
    DREBSpec R (x >>= f) := by
  intro out b out' hb
  have hb' : (x.run out >>= fun p => (f p.1).run p.2) = .ok (b, out') := hb
  cases hxa : x.run out with
  | error e => rw [hxa] at hb'; cases hb'
  | ok p =>
      rw [hxa] at hb'
      obtain ⟨l₁, hp, h₁⟩ := hx out p.1 p.2 hxa
      obtain ⟨l₂, h', h₂⟩ := hf p.1 l₁ h₁ p.2 b out' hb'
      exact ⟨l₁ ++ l₂, by rw [h', hp, List.append_assoc], h₂⟩

/-- A bind whose first routine is a lifted routine that may fail, whose answers satisfy `P`. -/
theorem DREBSpec.bind_liftPost {α β : Type} {m : DRE α} {f : α → DREB V β}
    {P : α → Prop} {R : β → List (NamedObject V) → Prop} (h : DREPost m P)
    (hf : ∀ a, P a → DREBSpec R (f a)) : DREBSpec R (liftM m >>= f) := by
  intro out b out' hb
  have hb' : ((liftM m : DREB V α).run out >>= fun p => (f p.1).run p.2) = .ok (b, out') := hb
  cases hm : m with
  | error e =>
      rw [hm] at hb'
      cases hb'
  | ok a =>
      rw [hm] at hb'
      exact hf a (h a hm) out b out' hb'

/-- An `if` relates what its branches relate. -/
theorem DREBSpec.ite {α : Type} {c : Prop} [Decidable c] {A B : DREB V α}
    {R : α → List (NamedObject V) → Prop} (hA : c → DREBSpec R A) (hB : ¬ c → DREBSpec R B) :
    DREBSpec R (if c then A else B) := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

/-- A dependent `if` relates what its branches relate. -/
theorem DREBSpec.dite {α : Type} {c : Prop} [Decidable c] {A : c → DREB V α}
    {B : ¬c → DREB V α} {R : α → List (NamedObject V) → Prop} (hA : ∀ h, DREBSpec R (A h))
    (hB : ∀ h, DREBSpec R (B h)) : DREBSpec R (if h : c then A h else B h) := by
  by_cases h : c
  · rw [dif_pos h]; exact hA h
  · rw [dif_neg h]; exact hB h

/-- `broadcast o` followed by the return of `b` appends `o` and answers `b`. -/
theorem DREBSpec.broadcast_pure {β : Type} {R : β → List (NamedObject V) → Prop}
    (o : NamedObject V) {b : β} (h : R b [o]) :
    DREBSpec R (Goldilocks.broadcast o >>= fun _ => (Pure.pure b : DREB V β)) := by
  intro sent₀ a sent ha
  have ha' : (Except.ok (b, sent₀ ++ [o]) : DRE (β × List (NamedObject V))) = .ok (a, sent) := ha
  cases ha'
  exact ⟨[o], rfl, h⟩

end

end

section

open Goldilocks

section

variable {V : Type}

/-- `DREBEmits L m`: for every list `sent₀` of objects sent before `m` runs and every answer
`(a, sent)` of `m.run sent₀`, the list `sent` is `sent₀ ++ l` for some list `l` with `L l`.

Read aloud: what `m` appends to the objects sent satisfies `L`. -/
def DREBEmits {α : Type} (L : List (NamedObject V) → Prop) (m : DREB V α) : Prop :=
  ∀ (sent₀ : List (NamedObject V)) (a : α) (sent : List (NamedObject V)),
    m.run sent₀ = .ok (a, sent) → ∃ l, sent = sent₀ ++ l ∧ L l

/-- `DREBSends Q m`: for every list `sent₀` of objects sent before `m` runs and every answer
`(a, sent)` of `m.run sent₀`, the list `sent` is `sent₀ ++ l` for some list `l` every object of
which satisfies `Q`.

Read aloud: every object `m` sends satisfies `Q`. -/
def DREBSends {α : Type} (Q : NamedObject V → Prop) (m : DREB V α) : Prop :=
  ∀ (sent₀ : List (NamedObject V)) (a : α) (sent : List (NamedObject V)),
    m.run sent₀ = .ok (a, sent) → ∃ l, sent = sent₀ ++ l ∧ ∀ o ∈ l, Q o

/-- `DREBSends Q m` is `DREBEmits` with "every object satisfies `Q`". -/
theorem DREBSends.iff {α : Type} {Q : NamedObject V → Prop} {m : DREB V α} :
    DREBSends Q m ↔ DREBEmits (fun l => ∀ o ∈ l, Q o) m :=
  Iff.rfl

/-- A weaker condition on what is appended follows from a stronger one. -/
theorem DREBEmits.mono {α : Type} {m : DREB V α} {L L' : List (NamedObject V) → Prop}
    (h : DREBEmits L m) (hL : ∀ l, L l → L' l) : DREBEmits L' m := by
  intro sent₀ a sent ha
  obtain ⟨l, hl, hL'⟩ := h sent₀ a sent ha
  exact ⟨l, hl, hL l hL'⟩

/-- A return appends nothing. -/
theorem DREBEmits.pure {α : Type} {L : List (NamedObject V) → Prop} {a : α} (h : L []) :
    DREBEmits L (Pure.pure a : DREB V α) := by
  intro sent₀ a' sent ha
  have ha' : (Except.ok (a, sent₀) : DRE (α × List (NamedObject V))) = .ok (a', sent) := ha
  cases ha'
  exact ⟨[], (List.append_nil _).symm, h⟩

/-- A bind appends what its first routine appends, then what its continuation appends. -/
theorem DREBEmits.bind {α β : Type} {x : DREB V α} {f : α → DREB V β}
    {L₁ L₂ : List (NamedObject V) → Prop} (hx : DREBEmits L₁ x) (hf : ∀ a, DREBEmits L₂ (f a)) :
    DREBEmits (fun l => ∃ l₁ l₂, l = l₁ ++ l₂ ∧ L₁ l₁ ∧ L₂ l₂) (x >>= f) := by
  intro out b out' hb
  have hb' : (x.run out >>= fun p => (f p.1).run p.2) = .ok (b, out') := hb
  cases hxa : x.run out with
  | error e => rw [hxa] at hb'; cases hb'
  | ok p =>
      rw [hxa] at hb'
      obtain ⟨l₁, hp, h₁⟩ := hx out p.1 p.2 hxa
      obtain ⟨l₂, h', h₂⟩ := hf p.1 p.2 b out' hb'
      exact ⟨l₁ ++ l₂, by rw [h', hp, List.append_assoc], l₁, l₂, rfl, h₁, h₂⟩

/-- A bind whose first routine appends nothing appends what its continuation appends. -/
theorem DREBEmits.bind_nil {α β : Type} {x : DREB V α} {f : α → DREB V β}
    {L : List (NamedObject V) → Prop} (hx : DREBEmits (· = []) x)
    (hf : ∀ a, DREBEmits L (f a)) : DREBEmits L (x >>= f) :=
  (DREBEmits.bind hx hf).mono (fun _ ⟨l₁, l₂, hl, h₁, h₂⟩ => by
    rw [hl, h₁, List.nil_append]
    exact h₂)

-- `DREBEmits.liftM_bind` comes before `DREBEmits.liftM`: its statement's `liftM` is the core
-- `liftM`, which inside the namespace `DREBEmits` the theorem `DREBEmits.liftM` would hide once
-- declared (moved here from `Proofs/Routines/Lemma14.lean`, record migration step 1c).
/-- A bind on a lifted routine that may fail appends what its continuation appends, on every
answer of the routine.

The variables:
- `m`: the lifted routine; `f`: the continuation; `L`: the condition on what is appended. -/
theorem DREBEmits.liftM_bind {α β : Type} {m : DRE α} {f : α → DREB V β}
    {L : List (NamedObject V) → Prop} (hf : ∀ a, m = .ok a → DREBEmits L (f a)) :
    DREBEmits L (liftM m >>= f) := by
  intro sent₀ b sent hb
  cases hm : m with
  | error e => rw [hm] at hb; cases hb
  | ok a => rw [hm] at hb; exact hf a hm sent₀ b sent hb

/-- A routine that may fail, run without sending, appends nothing. -/
theorem DREBEmits.liftM {α : Type} (m : DRE α) :
    DREBEmits (· = []) (liftM m : DREB V α) := by
  intro out a out' ha
  cases hm : m with
  | error e => rw [hm] at ha; cases ha
  | ok a' => rw [hm] at ha; cases ha; exact ⟨[], (List.append_nil _).symm, rfl⟩

/-- A routine that may fail, lifted into a duty, appends nothing. -/
theorem DREBEmits.monadLift {α : Type} (m : DRE α) :
    DREBEmits (· = []) (MonadLift.monadLift m : DREB V α) := by
  intro out a out' ha
  cases hm : m with
  | error e => rw [hm] at ha; cases ha
  | ok a' => rw [hm] at ha; cases ha; exact ⟨[], (List.append_nil _).symm, rfl⟩

/-- An `if` appends what its branches append. -/
theorem DREBEmits.ite {α : Type} {c : Prop} [Decidable c] {A B : DREB V α}
    {L : List (NamedObject V) → Prop} (hA : c → DREBEmits L A) (hB : ¬ c → DREBEmits L B) :
    DREBEmits L (if c then A else B) := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

/-- A dependent `if` appends what its branches append. -/
theorem DREBEmits.dite {α : Type} {c : Prop} [Decidable c] {A : c → DREB V α}
    {B : ¬c → DREB V α} {L : List (NamedObject V) → Prop} (hA : ∀ h, DREBEmits L (A h))
    (hB : ∀ h, DREBEmits L (B h)) : DREBEmits L (if h : c then A h else B h) := by
  by_cases h : c
  · rw [dif_pos h]; exact hA h
  · rw [dif_neg h]; exact hB h

/-- `broadcast o` appends `o`. -/
theorem DREBEmits.broadcast (o : NamedObject V) :
    DREBEmits (· = [o]) (Goldilocks.broadcast o) := by
  intro sent₀ a sent ha
  have ha' : (Except.ok ((), sent₀ ++ [o]) : DRE (Unit × List (NamedObject V))) =
      .ok (a, sent) := ha
  cases ha'
  exact ⟨[o], rfl, rfl⟩

/-- `broadcast o` followed by a routine that appends nothing appends `o`. -/
theorem DREBEmits.broadcast_then {β : Type} (o : NamedObject V) {f : Unit → DREB V β}
    (hf : ∀ u, DREBEmits (· = []) (f u)) :
    DREBEmits (· = [o]) (Goldilocks.broadcast o >>= f) :=
  (DREBEmits.bind (DREBEmits.broadcast o) hf).mono (by
    rintro _ ⟨l₁, l₂, rfl, rfl, rfl⟩
    rfl)

/-- A return sends nothing. -/
theorem DREBSends.pure {α : Type} {Q : NamedObject V → Prop} {a : α} :
    DREBSends Q (Pure.pure a : DREB V α) :=
  DREBEmits.pure (fun _ h => absurd h List.not_mem_nil)

/-- A bind sends what its two parts send. -/
theorem DREBSends.bind {α β : Type} {Q : NamedObject V → Prop} {x : DREB V α}
    {f : α → DREB V β} (hx : DREBSends Q x) (hf : ∀ a, DREBSends Q (f a)) :
    DREBSends Q (x >>= f) :=
  (DREBEmits.bind hx hf).mono (fun _ ⟨l₁, l₂, hl, h₁, h₂⟩ o ho => by
    rw [hl] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact h₁ o ho
    · exact h₂ o ho)

/-- An `if` sends what its branches send. -/
theorem DREBSends.ite {α : Type} {Q : NamedObject V → Prop} {c : Prop} [Decidable c]
    {A B : DREB V α} (hA : c → DREBSends Q A) (hB : ¬ c → DREBSends Q B) :
    DREBSends Q (if c then A else B) :=
  DREBEmits.ite hA hB

/-- A routine that may fail, run without sending, sends nothing. -/
theorem DREBSends.liftM {α : Type} {Q : NamedObject V → Prop} (m : DRE α) :
    DREBSends Q (liftM m : DREB V α) :=
  (DREBEmits.liftM m).mono (fun _ hl o ho => by rw [hl] at ho; exact absurd ho List.not_mem_nil)

/-- `broadcast o` sends `o`, which satisfies `Q` when `Q o`. -/
theorem DREBSends.broadcast {Q : NamedObject V → Prop} {o : NamedObject V} (h : Q o) :
    DREBSends Q (Goldilocks.broadcast o) :=
  (DREBEmits.broadcast o).mono (fun _ hl o' ho => by
    rw [hl, List.mem_singleton] at ho
    rw [ho]
    exact h)

end

end

section

open Goldilocks

section

variable {V : Type}

/-- A routine whose answers satisfy `P` and which appends lists satisfying `L` relates every
answer and what it appends by `P a ∧ L l`. -/
theorem DREBRuns.of_post_emits {α : Type} {m : DREB V α} {P : α → Prop}
    {L : List (NamedObject V) → Prop} (hP : DREBPost m P) (hL : DREBEmits L m) :
    DREBRuns (fun a l => P a ∧ L l) m := by
  intro sent₀ a sent ha
  obtain ⟨l, hl, h⟩ := hL sent₀ a sent ha
  exact ⟨l, hl, hP sent₀ a sent ha, h⟩

/-- `broadcast o` appends `o`. -/
theorem DREBRuns.broadcast (o : NamedObject V) :
    DREBRuns (fun _ l => l = [o]) (Goldilocks.broadcast o) :=
  (DREBRuns.of_post_emits (DREBPost.true _) (DREBEmits.broadcast o)).mono
    (fun _ _ h => h.2)

end

end

section

open Goldilocks (NamedObject DREB)

/-- The duty's run with nothing sent is one of its outcomes. -/
theorem _root_.Goldilocks.DREB.run_mem_outcomes {V α : Type} (d : DREB V α) :
    d.run [] ∈ d.outcomes :=
  Set.mem_singleton _

/-- An outcome of the deterministic duty `d` is its run with nothing sent.

Read aloud: the duty does one thing only. -/
theorem _root_.Goldilocks.DREB.run_eq_of_mem_outcomes {V α : Type} {d : DREB V α}
    {r : DRE (α × List (NamedObject V))} (h : r ∈ d.outcomes) : d.run [] = r :=
  (Set.mem_singleton_iff.mp h).symm

end

section

open Goldilocks

section

variable {V : Type}

/-- If every answer of `m` satisfies `Q` (`DREBPost m Q`), then so does the answer of every `.ok`
outcome of `m`.

The variables:
- `m`: the duty; `Q`: the postcondition; `a`, `sent`: the answer and the objects sent. -/
theorem DREBPost.of_outcome {α : Type} {m : DREB V α} {Q : α → Prop} (h : DREBPost m Q)
    {a : α} {sent : List (NamedObject V)} (hm : .ok (a, sent) ∈ m.outcomes) : Q a :=
  h [] a sent (DREB.run_eq_of_mem_outcomes hm)

end

end

section

open Goldilocks

section

variable {V : Type}

/-- If every answer of `m` is related by `R` to what `m` appends (`DREBSpec R m`), then the answer
of every `.ok` outcome of `m` is related by `R` to the objects that outcome sent.

The variables:
- `R`: the relation; `m`: the duty; `a`, `sent`: the answer and the objects sent. -/
theorem DREBSpec.of_outcome {α : Type} {R : α → List (NamedObject V) → Prop} {m : DREB V α}
    (h : DREBSpec R m) {a : α} {sent : List (NamedObject V)} (hm : .ok (a, sent) ∈ m.outcomes) :
    R a sent := by
  obtain ⟨l, hl, hR⟩ := h [] a sent (DREB.run_eq_of_mem_outcomes hm)
  rw [List.nil_append] at hl
  subst hl
  exact hR

end

end

section

open Goldilocks

section

variable {V : Type}

/-- If what `m` appends satisfies `L` (`DREBEmits L m`), then the objects every `.ok` outcome of
`m` sent satisfy `L`.

The variables:
- `L`: the condition; `m`: the duty; `a`, `sent`: the answer and the objects sent. -/
theorem DREBEmits.of_outcome {α : Type} {L : List (NamedObject V) → Prop} {m : DREB V α}
    (h : DREBEmits L m) {a : α} {sent : List (NamedObject V)} (hm : .ok (a, sent) ∈ m.outcomes) :
    L sent := by
  obtain ⟨l, hl, hL⟩ := h [] a sent (DREB.run_eq_of_mem_outcomes hm)
  rw [List.nil_append] at hl
  subst hl
  exact hL

end

end

section

open Goldilocks

/-! ## The lift of an option -/

/-- The lift of a present option answers its value.

The variables:
- `a`: the value. -/
theorem liftM_some {α : Type} (a : α) : (liftM (some a) : DRE α) = .ok a := rfl

/-- The lift of an absent option raises.

The variables:
- `α`: the type of the value. -/
theorem liftM_none {α : Type} : (liftM (none : Option α) : DRE α) = .error .error := rfl

end

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Wiring

section

open Goldilocks (NamedObject DREB)

/-- An answering duty has an `.ok` outcome. -/
theorem DREBOutcomesOk.exists_ok {V α : Type} {d : DREB V α} (h : DREBOutcomesOk d) :
    ∃ p : α × List (NamedObject V), .ok p ∈ d.outcomes := by
  obtain ⟨r, hr⟩ := h.2
  obtain ⟨p, rfl⟩ := h.1 r hr
  exact ⟨p, hr⟩

end

end GoldilocksCorrectness.Wiring
