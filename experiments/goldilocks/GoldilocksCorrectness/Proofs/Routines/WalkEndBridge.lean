module
public import GoldilocksCorrectness.Statements.Routines.WalkEndDefs
public import GoldilocksCorrectness.Proofs.Routines.Merge
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import Mathlib.SetTheory.Cardinal.Order
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# The spec's walk ends where the walk predicate says

The walk predicate `WalkEnd tree score eligible anchor H` of `Statements/Routines/WalkEndDefs.lean`
takes a tie-break function (`TieBreak`). This page gives the Goldilocks one and proves that the
spec's walk `ghost` answers exactly the block the predicate names, when no two blocks of the tree
share a root.

- the Goldilocks tie-break `goldilocksTieBreak` (a definition, made a local instance on this page
  only): from a set `S`, among the blocks of `S` whose root
  comes before the root of no block of `S` (`latestRootBlocks S`), the least in a classical
  well-order on blocks (`WellOrderingRel`); its laws `goldilocksTieBreak_mem`,
  `goldilocksTieBreak_subset`; what it picks, `tieBreak_root_before_false`,
  `tieBreak_eq_of_before`;
- what an answer of the spec's step tells: `ghost_step_ok_cases`, `mem_ghost_children_iff`,
  `eligible_ok_of_ghost_children_ok`, `score_ok_of_argmax?_ok`, `argmax?_some_of_nonempty`;
- one step: `walkStep_of_ghost_step` (a step of the spec is a walk step) and its converse
  `ghost_step_of_walkStep` (when no two blocks of the tree share a root);
- the end: `eligible_false_of_ghost_step_none` and its converse
  `ghost_step_none_of_eligible_false`;
- the walk: `walkEnd_of_ghost_eq_ok`, `ghost_eq_ok_of_walkEnd`, `ghost_eq_ok_iff_walkEnd`, and
  `goldfish_fork_choice_eq_ok_iff_walkEnd`.

The spec's step stops at a block two of whose eligible children of the highest score share the
root that comes last (`argmax?` answers none there), while a walk step goes on; so both directions
of the bridge take `RootsNameBlocksIn tree`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [RootOrder]

/-! ## The Goldilocks tie-break -/

/-- `latestRootBlocks S`: the blocks of `S` whose root comes before the root of no block of `S`
in the root order (`RootOrder.before`).

The variables:
- `S`: the set of blocks. -/
def latestRootBlocks (S : Finset (Block V)) : Finset (Block V) :=
  S.filter fun B => ∀ B' ∈ S, RootOrder.before B.root B'.root = false

/-- The blocks of a nonempty set whose root comes before no other root of the set are a nonempty
set.

Why: `exists_root_before_none`.

The variables:
- `S`: the set.

Read aloud: a nonempty set of blocks has a block whose root comes last. -/
theorem latestRootBlocks_nonempty {S : Finset (Block V)} (h : S.Nonempty) :
    (latestRootBlocks S).Nonempty := by
  obtain ⟨C, hC, hCmax⟩ := exists_root_before_none S h
  exact ⟨C, Finset.mem_filter.2 ⟨hC, hCmax⟩⟩

/-- `goldilocksTieBreakPick S`: the least block of `latestRootBlocks S` in the classical
well-order `WellOrderingRel` on blocks, or the genesis block when `S` is empty.

The variables:
- `S`: the set of blocks. -/
noncomputable def goldilocksTieBreakPick (S : Finset (Block V)) : Block V :=
  if h : (latestRootBlocks S).Nonempty then
    (WellOrderingRel.isWellOrder (α := Block V)).wf.min
      ((latestRootBlocks S : Finset (Block V)) : Set (Block V)) (Finset.coe_nonempty.2 h)
  else Block.genesis

/-- The pick from a nonempty set `S` is a block of `latestRootBlocks S`, and no block of
`latestRootBlocks S` comes before it in `WellOrderingRel`.

The variables:
- `S`: the set.

Read aloud: the pick is the least block in the well-order among the blocks of `S` whose root
comes last. -/
theorem goldilocksTieBreakPick_spec {S : Finset (Block V)} (h : S.Nonempty) :
    goldilocksTieBreakPick S ∈ latestRootBlocks S ∧
      ∀ B ∈ latestRootBlocks S, ¬ WellOrderingRel B (goldilocksTieBreakPick S) := by
  have hne := latestRootBlocks_nonempty h
  unfold goldilocksTieBreakPick
  rw [dif_pos hne]
  exact ⟨(WellOrderingRel.isWellOrder (α := Block V)).wf.min_mem _ _,
    fun B hB => (WellOrderingRel.isWellOrder (α := Block V)).wf.not_lt_min _
      (Finset.mem_coe.2 hB)⟩

/-- **The first law.** The pick from a nonempty set is a member of it.

The variables:
- `S`: the set.

Read aloud: the Goldilocks tie-break picks a member of a nonempty set. -/
theorem goldilocksTieBreak_mem (S : Finset (Block V)) (h : S.Nonempty) :
    goldilocksTieBreakPick S ∈ S :=
  (Finset.mem_filter.1 (goldilocksTieBreakPick_spec h).1).1

/-- **The second law.** When `T` is a subset of `S` and the pick from `S` is in `T`, the pick from
`T` is the pick from `S`.

Why: write `p` for the pick from `S`. Its root comes before no root of `S`, so before no root of
`T`: `p` is in `latestRootBlocks T`. A block `B` of `latestRootBlocks T` has a root that comes
before `p`'s neither way, so the same root (`RootOrder.total`), and is in `latestRootBlocks S`. So
`latestRootBlocks T` is a subset of `latestRootBlocks S` holding `p`, and the least block of each
in the well-order is `p`.

The variables:
- `S`: the set; `T`: the subset.

Read aloud: the Goldilocks tie-break keeps its pick when blocks it did not pick are removed. -/
theorem goldilocksTieBreak_subset (S T : Finset (Block V)) (hTS : T ⊆ S)
    (hp : goldilocksTieBreakPick S ∈ T) :
    goldilocksTieBreakPick T = goldilocksTieBreakPick S := by
  have hS : S.Nonempty := ⟨_, hTS hp⟩
  have hT : T.Nonempty := ⟨_, hp⟩
  obtain ⟨hpS, hpmin⟩ := goldilocksTieBreakPick_spec hS
  obtain ⟨hqT, hqmin⟩ := goldilocksTieBreakPick_spec hT
  set p := goldilocksTieBreakPick S with hpdef
  set q := goldilocksTieBreakPick T with hqdef
  have hplatest := (Finset.mem_filter.1 hpS).2
  -- `p` is in `latestRootBlocks T`
  have hpT : p ∈ latestRootBlocks T :=
    Finset.mem_filter.2 ⟨hp, fun B' hB' => hplatest B' (hTS hB')⟩
  -- `latestRootBlocks T` is a subset of `latestRootBlocks S`
  have hsub : ∀ B ∈ latestRootBlocks T, B ∈ latestRootBlocks S := by
    intro B hB
    obtain ⟨hBT, hBlatest⟩ := Finset.mem_filter.1 hB
    have hBp : B.root = p.root := by
      by_contra hne
      rcases RootOrder.total B.root p.root hne with h' | h'
      · rw [hBlatest p hp] at h'
        cases h'
      · rw [hplatest B (hTS hBT)] at h'
        cases h'
    refine Finset.mem_filter.2 ⟨hTS hBT, fun B' hB' => ?_⟩
    rw [hBp]
    exact hplatest B' hB'
  rcases trichotomous_of (r := WellOrderingRel) q p with h' | h' | h'
  · exact absurd h' (hpmin q (hsub q hqT))
  · exact h'
  · exact absurd h' (hqmin p hpT)

/-- `goldilocksTieBreak`: the Goldilocks tie-break, `goldilocksTieBreakPick` with its two laws.
From a set of blocks it picks a block whose root comes last in the root order, and among the
blocks sharing that root, the least in a classical well-order on blocks.

It is a definition, not a global instance: a statement meant for every tie-break, with
`[RootOrder]` in scope and no `[TieBreak V]` hypothesis, would otherwise use it silently. This page
makes it a local instance (`attribute [local instance]`), so the statements on it read
`WalkEnd tree score eligible anchor H` at the Goldilocks tie-break; another page that needs it
names it, or makes it a local instance in its turn. -/
@[reducible] noncomputable def goldilocksTieBreak : TieBreak V where
  tieBreak := goldilocksTieBreakPick
  tieBreak_mem := goldilocksTieBreak_mem
  tieBreak_subset := goldilocksTieBreak_subset

attribute [local instance] goldilocksTieBreak

/-- The root of the Goldilocks pick from a nonempty set `S` comes before the root of no block of
`S`.

The variables:
- `S`: the set.

Read aloud: the Goldilocks tie-break picks a block whose root comes last. -/
theorem tieBreak_root_before_false {S : Finset (Block V)} (h : S.Nonempty) :
    ∀ D ∈ S, RootOrder.before (TieBreak.tieBreak S).root D.root = false :=
  (Finset.mem_filter.1 (goldilocksTieBreakPick_spec h).1).2

/-- The Goldilocks pick from `S` is `C`, when `C` is in `S` and the root of every other block of
`S` comes before `C`'s.

Why: the pick's root comes before no root of `S`, and every block other than `C` has a root that
comes before `C`'s.

The variables:
- `S`: the set; `C`: the block.

Read aloud: a block whose root comes after every other root of the set is the one picked. -/
theorem tieBreak_eq_of_before {S : Finset (Block V)} {C : Block V} (hC : C ∈ S)
    -- the root of every other block of `S` comes before `C`'s
    (hbefore : ∀ D ∈ S, D ≠ C → RootOrder.before D.root C.root = true) :
    TieBreak.tieBreak S = C := by
  have hS : S.Nonempty := ⟨C, hC⟩
  have hpS : TieBreak.tieBreak S ∈ S := TieBreak.tieBreak_mem S hS
  by_contra hne
  have h1 := hbefore _ hpS hne
  rw [tieBreak_root_before_false hS C hC] at h1
  cases h1

/-! ## What an answer of the spec's step tells -/

omit [DecidableEq V] [RootOrder] in
/-- Membership in `highestEligibleChildren`, spelled out.

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the parent; `D`: the block.

Read aloud: `D` is an eligible child of `H` in `tree` with the highest score exactly when it is in
`tree`, its parent is `H`, the test accepts it, and its score answers some `k` that no other
eligible child's score exceeds. -/
theorem mem_highestEligibleChildren_iff {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {H D : Block V} :
    D ∈ highestEligibleChildren tree score eligible H ↔
      D ∈ tree ∧ D.parent? = some H ∧ eligible D = .ok true ∧
        ∃ k : ℕ, score D = .ok k ∧
          ∀ D' ∈ tree, D'.parent? = some H → eligible D' = .ok true →
            ∀ k' : ℕ, score D' = .ok k' → k' ≤ k := by
  simp only [highestEligibleChildren, Finset.mem_filter]

/-- A step of the spec that answers is `argmax?` over the children `ghost_children` answers.

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block stepped from; `r`: the answer.

Read aloud: the spec's step answers what `argmax?` answers on the children it computes. -/
theorem ghost_step_ok_cases {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {H : Block V} {r : Option (Block V)}
    (h : ghost_step tree score eligible H = .ok r) :
    ∃ R : Finset (Block V), ghost_children tree eligible H = .ok R ∧ argmax? score R = .ok r := by
  unfold ghost_step at h
  cases hc : ghost_children tree eligible H with
  | error e =>
    rw [hc] at h
    cases h
  | ok R =>
    rw [hc] at h
    exact ⟨R, rfl, h⟩

omit [RootOrder] in
/-- The children `ghost_children` answers are the blocks of `tree` whose parent is `H` and on
which the test answers `true`.

The variables:
- `tree`, `eligible`: the walk; `H`: the parent; `R`: the answer; `D`: the block.

Read aloud: a block is among the children the spec computes exactly when it is an eligible child
of `H` in `tree`. -/
theorem mem_ghost_children_iff {tree : Finset (Block V)} {eligible : Block V → DRE Bool}
    {H : Block V} {R : Finset (Block V)} (h : ghost_children tree eligible H = .ok R)
    (D : Block V) : D ∈ R ↔ D ∈ tree ∧ D.parent? = some H ∧ eligible D = .ok true := by
  unfold ghost_children at h
  rw [mem_of_filterM_eq_ok_iff _ tree R h D]
  by_cases hp : D.parent? = some H
  · simp [hp]
  · simp [hp, pure, Except.pure]

omit [RootOrder] in
/-- When `ghost_children` answers, the test answers on every child of `H` in `tree`.

The variables:
- `tree`, `eligible`: the walk; `H`: the parent; `R`: the answer.

Read aloud: the spec's children answer only when the test answers on every child. -/
theorem eligible_ok_of_ghost_children_ok {tree : Finset (Block V)}
    {eligible : Block V → DRE Bool} {H : Block V} {R : Finset (Block V)}
    (h : ghost_children tree eligible H = .ok R) :
    ∀ D ∈ tree, D.parent? = some H → ∃ b : Bool, eligible D = .ok b := by
  intro D hD hpar
  unfold ghost_children at h
  obtain ⟨b, hb⟩ := filterM_ok_total _ tree R h D hD
  refine ⟨b, ?_⟩
  simpa [hpar] using hb

omit [DecidableEq V] in
/-- When `outranks score B C` answers, the score answers on `B`.

The variables:
- `score`: the score; `B`, `C`: the two blocks.

Read aloud: `outranks` answers only when the first block's score answers. -/
theorem score_ok_of_outranks_ok {score : Block V → DRE ℕ} {B C : Block V}
    (h : ∃ b : Bool, outranks score B C = .ok b) : ∃ k : ℕ, score B = .ok k := by
  obtain ⟨b, hb⟩ := h
  unfold outranks at hb
  cases hs : score B with
  | error e =>
    rw [hs] at hb
    cases hb
  | ok k => exact ⟨k, rfl⟩

/-- When `argmax? score children` answers, the score answers on every member of `children`.

Why: `argmax?` runs `is_best_in` on every member `D`, which runs `outranks score D D`, which reads
`D`'s score.

The variables:
- `score`: the score; `children`: the set; `r`: the answer.

Read aloud: `argmax?` answers only when every member's score answers. -/
theorem score_ok_of_argmax?_ok {score : Block V → DRE ℕ} {children : Finset (Block V)}
    {r : Option (Block V)} (h : argmax? score children = .ok r) :
    ∀ D ∈ children, ∃ k : ℕ, score D = .ok k := by
  intro D hD
  unfold argmax? at h
  cases hf : children.filterM (is_best_in score children) with
  | error e =>
    rw [hf] at h
    cases h
  | ok best =>
    obtain ⟨b, hb⟩ := filterM_ok_total _ children best hf D hD
    unfold is_best_in at hb
    cases hg : children.filterM (fun C => outranks score C D) with
    | error e =>
      rw [hg] at hb
      cases hb
    | ok R => exact score_ok_of_outranks_ok (filterM_ok_total _ children R hg D hD)

/-- `argmax? score R` answers a block when `R` is nonempty, the score answers `n D` on every
member `D` of `R`, and no two members of `R` share a root.

Why: a member of the greatest score, then among those one whose root comes before no other's
(`exists_root_before_none`); with distinct roots it outranks every other member
(`argmax?_eq_some_of_outranks`).

The variables:
- `score`: the score; `R`: the set; `n`: the score's answers.

Read aloud: on a nonempty set whose roots name its blocks, `argmax?` picks a block. -/
theorem argmax?_some_of_nonempty {score : Block V → DRE ℕ} {R : Finset (Block V)}
    (n : Block V → ℕ) (hR : R.Nonempty)
    -- the score answers `n D` on every member `D` of `R`
    (hn : ∀ D ∈ R, score D = .ok (n D))
    -- no two members of `R` share a root
    (hRoots : RootsNameBlocksIn R) :
    ∃ C : Block V, argmax? score R = .ok (some C) := by
  obtain ⟨C₀, hC₀, hC₀max⟩ := Finset.exists_max_image R n hR
  set top := R.filter (fun D => n D = n C₀) with htop
  have htne : top.Nonempty := ⟨C₀, Finset.mem_filter.2 ⟨hC₀, rfl⟩⟩
  obtain ⟨C, hC, hCmax⟩ := exists_root_before_none top htne
  obtain ⟨hCR, hCn⟩ := Finset.mem_filter.1 hC
  refine ⟨C, argmax?_eq_some_of_outranks hCR n hn (fun D hD hDC => ?_)⟩
  have hle := hC₀max D hD
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega, ?_⟩
    have hCD := hCmax D (Finset.mem_filter.2 ⟨hD, heq⟩)
    have hroot : D.root ≠ C.root := fun hr => hDC (hRoots D hD C hCR hr)
    rcases RootOrder.total D.root C.root hroot with h' | h'
    · exact h'
    · rw [hCD] at h'
      cases h'

/-! ## One step -/

/-- **A step of the spec is a walk step.** When the spec's step from `H` answers `C`,
`WalkStep tree score eligible H C` holds under the Goldilocks tie-break.

Why: `C` is a child of `H` in `tree` that passes the test (`mem_ghost_children_iff`); the test
answers on every child (`eligible_ok_of_ghost_children_ok`) and the score on every eligible child
(`score_ok_of_argmax?_ok`); `C` outranks every other eligible child
(`outranks_of_argmax?_eq_some`), so it has the highest score and every other eligible child of
that score has a root before `C`'s, and the tie-break picks `C` (`tieBreak_eq_of_before`).

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block stepped from; `C`: the block stepped to.

Read aloud: the block the spec's step goes to is the block the walk predicate steps to. -/
theorem walkStep_of_ghost_step {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {H C : Block V}
    -- the spec's step from `H` answers `C`
    (h : ghost_step tree score eligible H = .ok (some C)) :
    WalkStep tree score eligible H C := by
  classical
  obtain ⟨R, hR, harg⟩ := ghost_step_ok_cases h
  have hmem := mem_ghost_children_iff hR
  have hsc := score_ok_of_argmax?_ok harg
  let n : Block V → ℕ := fun D => if hD : ∃ k : ℕ, score D = .ok k then hD.choose else 0
  have hn : ∀ D ∈ R, score D = .ok (n D) := by
    intro D hD
    have hD' := hsc D hD
    simp only [n, dif_pos hD']
    exact hD'.choose_spec
  obtain ⟨hCR, hdom⟩ := outranks_of_argmax?_eq_some n hn harg
  obtain ⟨hCt, hCp, hCe⟩ := (hmem C).1 hCR
  refine ⟨hCt, hCp, hCe, eligible_ok_of_ghost_children_ok hR,
    fun D hD hp he => hsc D ((hmem D).2 ⟨hD, hp, he⟩), ?_⟩
  symm
  apply tieBreak_eq_of_before
  · refine mem_highestEligibleChildren_iff.2 ⟨hCt, hCp, hCe, n C, hn C hCR,
      fun D' hD' hp' he' k' hk' => ?_⟩
    have hD'R := (hmem D').2 ⟨hD', hp', he'⟩
    rw [hn D' hD'R, Except.ok.injEq] at hk'
    subst hk'
    by_cases hDC : D' = C
    · rw [hDC]
    · rcases hdom D' hD'R hDC with h' | ⟨h', -⟩ <;> omega
  · intro D hD hDC
    obtain ⟨hDt, hDp, hDe, k, hk, -⟩ := mem_highestEligibleChildren_iff.1 hD
    have hDR := (hmem D).2 ⟨hDt, hDp, hDe⟩
    rcases hdom D hDR hDC with hlt | ⟨-, hb⟩
    · exfalso
      obtain ⟨-, -, -, k₂, hk₂, hk₂max⟩ := mem_highestEligibleChildren_iff.1 hD
      have hle := hk₂max C hCt hCp hCe (n C) (hn C hCR)
      rw [hn D hDR, Except.ok.injEq] at hk₂
      omega
    · exact hb

/-- **A walk step is a step of the spec**, when no two blocks of `tree` share a root: from
`WalkStep tree score eligible H C` under the Goldilocks tie-break, the spec's step from `H`
answers `C`.

Why: the test and the score answer on the children they are read on, so `ghost_children` answers
the eligible children (`ghost_children_eq`); `C` has the highest score, and every other eligible
child either scores less or has the same score and a root that comes before `C`'s, since `C`'s
root comes before no root of `highestEligibleChildren` (`tieBreak_root_before_false`) and roots
name blocks (`RootOrder.total`); so `argmax?` picks `C` (`argmax?_eq_some_of_outranks`).

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block stepped from; `C`: the block stepped to.

Read aloud: when roots name the blocks of the tree, the block the walk predicate steps to is the
block the spec's step goes to. -/
theorem ghost_step_of_walkStep {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {H C : Block V}
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree)
    -- the walk predicate steps from `H` to `C`
    (h : WalkStep tree score eligible H C) :
    ghost_step tree score eligible H = .ok (some C) := by
  classical
  obtain ⟨hCt, hCp, hCe, hel, hsc, hC⟩ := h
  let b : Block V → Bool := fun D => if hD : ∃ b : Bool, eligible D = .ok b then hD.choose
    else false
  have hb : ∀ D ∈ tree, D.parent? = some H → eligible D = .ok (b D) := by
    intro D hD hp
    have hD' := hel D hD hp
    simp only [b, dif_pos hD']
    exact hD'.choose_spec
  let n : Block V → ℕ := fun D => if hD : ∃ k : ℕ, score D = .ok k then hD.choose else 0
  have hn : ∀ D ∈ tree, D.parent? = some H → eligible D = .ok true → score D = .ok (n D) := by
    intro D hD hp he
    have hD' := hsc D hD hp he
    simp only [n, dif_pos hD']
    exact hD'.choose_spec
  -- `b D = true` exactly when the test accepts `D`, on the children of `H` in `tree`
  have hbtrue : ∀ D ∈ tree, D.parent? = some H → (b D = true ↔ eligible D = .ok true) := by
    intro D hD hp
    rw [hb D hD hp]
    constructor
    · intro h'
      rw [h']
    · intro h'
      exact Except.ok.inj h'
  set children := tree.filter (fun D => D.parent? = some H ∧ b D = true) with hchildren
  have hmem : ∀ D, D ∈ children ↔ D ∈ tree ∧ D.parent? = some H ∧ eligible D = .ok true := by
    intro D
    rw [hchildren, Finset.mem_filter]
    constructor
    · rintro ⟨hD, hp, hbD⟩
      exact ⟨hD, hp, (hbtrue D hD hp).1 hbD⟩
    · rintro ⟨hD, hp, he⟩
      exact ⟨hD, hp, (hbtrue D hD hp).2 he⟩
  have hCch : C ∈ children := (hmem C).2 ⟨hCt, hCp, hCe⟩
  -- the set the tie-break picks from is nonempty: a child of the greatest score is in it
  obtain ⟨C₀, hC₀, hC₀max⟩ := Finset.exists_max_image children n ⟨C, hCch⟩
  obtain ⟨hC₀t, hC₀p, hC₀e⟩ := (hmem C₀).1 hC₀
  have hS : (highestEligibleChildren tree score eligible H).Nonempty := by
    refine ⟨C₀, mem_highestEligibleChildren_iff.2 ⟨hC₀t, hC₀p, hC₀e, n C₀,
      hn C₀ hC₀t hC₀p hC₀e, fun D' hD' hp' he' k' hk' => ?_⟩⟩
    rw [hn D' hD' hp' he', Except.ok.injEq] at hk'
    subst hk'
    exact hC₀max D' ((hmem D').2 ⟨hD', hp', he'⟩)
  have hCS : C ∈ highestEligibleChildren tree score eligible H := by
    rw [hC]
    exact TieBreak.tieBreak_mem _ hS
  have hClatest : ∀ D ∈ highestEligibleChildren tree score eligible H,
      RootOrder.before C.root D.root = false := by
    rw [hC]
    exact tieBreak_root_before_false hS
  obtain ⟨-, -, -, k, hk, hkmax⟩ := mem_highestEligibleChildren_iff.1 hCS
  rw [hn C hCt hCp hCe, Except.ok.injEq] at hk
  have hch : ghost_children tree eligible H = .ok children := ghost_children_eq b hb
  unfold ghost_step
  rw [hch]
  refine argmax?_eq_some_of_outranks hCch n
    (fun D hD => hn D ((hmem D).1 hD).1 ((hmem D).1 hD).2.1 ((hmem D).1 hD).2.2)
    (fun D hD hDC => ?_)
  obtain ⟨hDt, hDp, hDe⟩ := (hmem D).1 hD
  have hle : n D ≤ n C := by
    rw [hk]
    exact hkmax D hDt hDp hDe (n D) (hn D hDt hDp hDe)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    -- `D` has the highest score too
    have hDS : D ∈ highestEligibleChildren tree score eligible H :=
      mem_highestEligibleChildren_iff.2 ⟨hDt, hDp, hDe, n D, hn D hDt hDp hDe,
        fun D' hD' hp' he' k' hk' => by
          rw [heq, hk]
          exact hkmax D' hD' hp' he' k' hk'⟩
    have hroot : D.root ≠ C.root := fun hr => hDC (hRoots D hDt C hCt hr)
    rcases RootOrder.total D.root C.root hroot with h' | h'
    · exact h'
    · rw [hClatest D hDS] at h'
      cases h'

/-! ## The end of the walk -/

/-- When the spec's step from `H` answers none and no two blocks of `tree` share a root, the test
answers `false` on every child of `H` in `tree`.

Why: the test answers on every child (`eligible_ok_of_ghost_children_ok`); an accepted child would
make the children nonempty, the scores answer on them (`score_ok_of_argmax?_ok`), and `argmax?`
would pick a block (`argmax?_some_of_nonempty`).

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block.

Read aloud: when roots name the blocks of the tree, the spec's step stops only where the test
accepts no child. -/
theorem eligible_false_of_ghost_step_none {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {H : Block V}
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree)
    -- the spec's step from `H` answers none
    (h : ghost_step tree score eligible H = .ok none) :
    ∀ D ∈ tree, D.parent? = some H → eligible D = .ok false := by
  classical
  obtain ⟨R, hR, harg⟩ := ghost_step_ok_cases h
  have hmem := mem_ghost_children_iff hR
  intro D hD hp
  obtain ⟨b, hb⟩ := eligible_ok_of_ghost_children_ok hR D hD hp
  cases b with
  | false => exact hb
  | true =>
    exfalso
    have hDR : D ∈ R := (hmem D).2 ⟨hD, hp, hb⟩
    have hsc := score_ok_of_argmax?_ok harg
    let n : Block V → ℕ := fun D => if hD : ∃ k : ℕ, score D = .ok k then hD.choose else 0
    have hn : ∀ D ∈ R, score D = .ok (n D) := by
      intro D hD
      have hD' := hsc D hD
      simp only [n, dif_pos hD']
      exact hD'.choose_spec
    obtain ⟨C, hC⟩ := argmax?_some_of_nonempty n ⟨D, hDR⟩ hn
      (fun B hB B' hB' hr => hRoots B ((hmem B).1 hB).1 B' ((hmem B').1 hB').1 hr)
    rw [hC] at harg
    cases harg

/-- When the test answers `false` on every child of `H` in `tree`, the spec's step from `H`
answers none.

Why: the children are then empty, and `argmax?` on the empty set answers none.

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block.

Read aloud: where the test accepts no child, the spec's step stops. -/
theorem ghost_step_none_of_eligible_false {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool} {H : Block V}
    -- the test answers `false` on every child of `H` in `tree`
    (h : ∀ D ∈ tree, D.parent? = some H → eligible D = .ok false) :
    ghost_step tree score eligible H = .ok none := by
  have hch : ghost_children tree eligible H = .ok ∅ := by
    rw [ghost_children_eq (fun _ => false) h]
    simp
  unfold ghost_step argmax?
  rw [hch]
  rfl

/-! ## The walk -/

omit [RootOrder] in
/-- A chain of walk steps from `A` to `H` goes from an ancestor of `H`: `A` is `H` or an ancestor
of `H`.

The variables:
- `tree`, `score`, `eligible`: the walk; `A`: the start; `H`: the end.

Read aloud: walk steps go down the tree. -/
theorem ancestorEq_of_walkSteps [TieBreak V] {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool} {A H : Block V}
    (h : Relation.ReflTransGen (WalkStep tree score eligible) A H) : A.AncestorEq H := by
  induction h with
  | refl => exact ancestorEq_refl A
  | tail _ hstep ih => exact ancestorEq_trans ih (ancestorEq_of_parent? hstep.2.1)

omit [RootOrder] in
/-- Every block after `A` on the way to `H` is in `tree`, when walk steps lead from `A` to `H`.

Why: each step goes to a child taken from `tree`, and the blocks on the way are the steps.

The variables:
- `tree`, `score`, `eligible`: the walk; `A`: the start; `H`: the end.

Read aloud: the blocks a chain of walk steps passes through after its start are in the tree. -/
theorem mem_tree_of_walkSteps [TieBreak V] {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool} {A H : Block V}
    (h : Relation.ReflTransGen (WalkStep tree score eligible) A H) :
    ∀ P : Block V, A.AncestorEq P → P ≠ A → P.AncestorEq H → P ∈ tree := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro P hAP hPA hPH
    exact absurd (ancestorEq_antisymm hPH hAP) hPA
  | @head A' C hstep hrest ih =>
    intro P hAP hPA hPH
    have hCH := ancestorEq_of_walkSteps hrest
    have hCP := child_ancestorEq_of_between hAP hPA hPH hstep.2.1 hCH
    by_cases hPC : P = C
    · rw [hPC]
      exact hstep.1
    · exact ih P hCP hPC hPH

/-- The spec's walk of `n` steps from `Y` answers `H`, when walk steps lead from `Y` to `H`, no
two blocks of `tree` share a root, the spec's step from `H` answers none, and `n` is at least the
depth gap from `Y` to `H`.

Why: induction on the chain of walk steps; each is a step of the spec (`ghost_step_of_walkStep`),
and at `H` the spec stops.

The variables:
- `tree`, `score`, `eligible`: the walk; `Y`: the start; `H`: the end; `n`: the number of steps.

Read aloud: the spec's walk follows a chain of walk steps to its end. -/
theorem ghost_walk_of_walkSteps {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {Y H : Block V}
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree)
    -- the spec's step from `H` answers none
    (hstop : ghost_step tree score eligible H = .ok none)
    -- walk steps lead from `Y` to `H`
    (h : Relation.ReflTransGen (WalkStep tree score eligible) Y H) :
    ∀ n : ℕ, H.depth ≤ Y.depth + n → ghost_walk tree score eligible n Y = .ok H := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro n _
    cases n with
    | zero => rfl
    | succ n =>
      simp only [ghost_walk, bind, Except.bind, hstop, ne_eq, not_true_eq_false, ↓reduceDIte,
        pure, Except.pure]
  | @head Y' C hstep hrest ih =>
    intro n hn
    have hCs := ghost_step_of_walkStep hRoots hstep
    have hdC := depth_of_parent? hstep.2.1
    have hCH := depth_le_of_ancestorEq (ancestorEq_of_walkSteps hrest)
    cases n with
    | zero => omega
    | succ n =>
      simp only [ghost_walk, bind, Except.bind, hCs, ne_eq, reduceCtorEq, not_false_eq_true,
        Option.value, Option.get_some]
      exact ih n (by omega)

/-- **From the spec to the predicate.** When the spec's walk `ghost anchor tree score eligible`
answers `H` and no two blocks of `tree` share a root, `WalkEnd tree score eligible anchor H`
holds under the Goldilocks tie-break.

Why: every step the spec takes is a walk step (`walkStep_of_ghost_step`); the spec's step from
`H` answers none (`ghost_step_none_of_ghost_eq`), so the test accepts no child of `H`
(`eligible_false_of_ghost_step_none`). Only this last part needs the roots to name the blocks.

The variables:
- `anchor`: the start; `tree`, `score`, `eligible`: the walk; `H`: the end.

Read aloud: when roots name the blocks of the tree, the block the spec's walk answers is where
the walk predicate ends. -/
theorem walkEnd_of_ghost_eq_ok {anchor : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool} {H : Block V}
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree)
    -- the spec's walk from `anchor` answers `H`
    (h : ghost anchor tree score eligible = .ok H) :
    WalkEnd tree score eligible anchor H := by
  refine ⟨?_, eligible_false_of_ghost_step_none hRoots (ghost_step_none_of_ghost_eq h)⟩
  unfold ghost at h
  -- every walk of the spec is a chain of walk steps
  have key : ∀ (n : ℕ) (A : Block V), ghost_walk tree score eligible n A = .ok H →
      Relation.ReflTransGen (WalkStep tree score eligible) A H := by
    intro n
    induction n with
    | zero =>
      intro A hA
      simp only [ghost_walk, pure, Except.pure, Except.ok.injEq] at hA
      rw [hA]
    | succ n ih =>
      intro A hA
      rcases ghost_walk_succ_cases hA with ⟨-, rfl⟩ | ⟨C, hC, hw⟩
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head (walkStep_of_ghost_step hC) (ih C hw)
  exact key _ anchor h

/-- **From the predicate to the spec.** When `WalkEnd tree score eligible anchor H` holds under the
Goldilocks tie-break and no two blocks of `tree` share a root, the spec's walk
`ghost anchor tree score eligible` answers `H`.

Why: the test accepts no child of `H`, so the spec stops there
(`ghost_step_none_of_eligible_false`); every walk step is a step of the spec
(`ghost_step_of_walkStep`, which needs the roots to name the blocks); the blocks after `anchor` on
the way to `H` are in `tree` (`mem_tree_of_walkSteps`), so `H` is at most `|tree|` deeper than
`anchor` (`path_card`) and the `|tree|` steps of `ghost` reach it (`ghost_walk_of_walkSteps`).

The variables:
- `anchor`: the start; `tree`, `score`, `eligible`: the walk; `H`: the end.

Read aloud: when roots name the blocks of the tree, the spec's walk answers the block where the
walk predicate ends. -/
theorem ghost_eq_ok_of_walkEnd {anchor : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool} {H : Block V}
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree)
    -- the walk predicate from `anchor` ends at `H`
    (h : WalkEnd tree score eligible anchor H) :
    ghost anchor tree score eligible = .ok H := by
  obtain ⟨hpath, hstop⟩ := h
  have hAH := ancestorEq_of_walkSteps hpath
  have hcard := path_card hAH (mem_tree_of_walkSteps hpath)
  exact ghost_walk_of_walkSteps hRoots (ghost_step_none_of_eligible_false hstop) hpath _ hcard

/-- **The bridge.** When no two blocks of `tree` share a root, the spec's walk
`ghost anchor tree score eligible` answers `H` exactly when `WalkEnd tree score eligible anchor H`
holds under the Goldilocks tie-break.

The variables:
- `anchor`: the start; `tree`, `score`, `eligible`: the walk; `H`: the end.

Read aloud: when roots name the blocks of the tree, the spec's walk answers `H` exactly when the
walk predicate ends at `H`. -/
theorem ghost_eq_ok_iff_walkEnd {anchor : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool} {H : Block V}
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree) :
    ghost anchor tree score eligible = .ok H ↔ WalkEnd tree score eligible anchor H :=
  ⟨walkEnd_of_ghost_eq_ok hRoots, ghost_eq_ok_of_walkEnd hRoots⟩

/-- **The bridge for the Goldfish fork choice.** When no two blocks of `tree` share a root,
`goldfish_fork_choice C Φ t anchor tree votes support_votes s` answers `H` exactly when
`WalkEnd tree (goldfish_score Φ votes support_votes s) (goldfish_eligible C Φ t votes
support_votes s) anchor H` holds under the Goldilocks tie-break.

Why: the fork choice is the walk with that score and that test (`goldfish_fork_choice_eq`), and
`ghost_eq_ok_iff_walkEnd`.

The variables:
- `C`: the parameters; `Φ`: the `Frame`; `t`: the time; `anchor`: the start; `tree`: the blocks
  walked; `votes`, `support_votes`: the votes counted; `s`: the slot; `H`: the end.

Read aloud: when roots name the blocks of the tree, the Goldfish fork choice answers `H` exactly
when the walk predicate, with the Goldfish score and eligibility test, ends at `H`. -/
theorem goldfish_fork_choice_eq_ok_iff_walkEnd [Fintype V] (C : Config) (Φ : Frame V)
    (t : Time) (anchor : Block V) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) {H : Block V}
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree) :
    goldfish_fork_choice C Φ t anchor tree votes support_votes s = .ok H ↔
      WalkEnd tree (goldfish_score Φ votes support_votes s)
        (goldfish_eligible C Φ t votes support_votes s) anchor H := by
  rw [goldfish_fork_choice_eq]
  exact ghost_eq_ok_iff_walkEnd hRoots

end GoldilocksCorrectness.Proofs.Routines
