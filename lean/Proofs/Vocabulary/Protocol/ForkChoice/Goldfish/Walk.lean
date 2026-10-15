module
public import Model.Vocabulary.Execution.Setup
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.ENatToNat

@[expose] public section

/-!
# The GHOST walk

Facts about `Protocol.ghost` alone: its result is a descendant of its anchor and is the anchor or an
eligible block, a child that strictly outscores its siblings is the `argmax`, and a walk whose every
path block is its own next step, ending at a target with no eligible child, returns that target.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## `pickUnique?` -/

omit [Fintype V] in
/-- `pickUnique?` commits to `C` when `C` passes the test and is the only member
that does. -/
theorem pickUnique?_eq_some {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    {C : α} (hC : C ∈ T) (hp : p C = true) (huniq : ∀ a ∈ T, p a = true → a = C) :
    pickUnique? T p = some C := by
  have hex : ∃! a, a ∈ T ∧ p a = true := ⟨C, ⟨hC, hp⟩, fun b hb => huniq b hb.1 hb.2⟩
  unfold pickUnique?
  rw [dif_pos hex]
  refine congrArg some ?_
  have hspec := Finset.choose_spec (fun a => p a = true) T hex
  exact huniq _ hspec.1 hspec.2

omit [Fintype V] in
/-- `pickUnique?` returns `none` on an empty set. -/
theorem pickUnique?_empty {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    (h : T = ∅) : pickUnique? T p = none := by
  unfold pickUnique?
  rw [dif_neg]
  rintro ⟨a, ⟨ha, -⟩, -⟩
  rw [h] at ha
  exact absurd ha (by simp)

/-! ## The `argmax` -/

omit [DecidableEq V] [Fintype V] in
/-- In a set where `C` strictly outscores every other member, a member that is best in the set is
    `C`. -/
theorem eq_of_is_best_in {score : Block V → Nat} {children : Finset (Block V)}
    {C a : Block V} (hC : C ∈ children) (ha : a ∈ children)
    (hdom : ∀ D ∈ children, D ≠ C → score D < score C)
    (hbest : Protocol.is_best_in score children a = true) : a = C := by
  by_contra hne
  simp only [Protocol.is_best_in, decide_eq_true_eq] at hbest
  have hCa := hbest C hC
  simp only [Protocol.outranks, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hCa
  exact absurd (hdom a ha hne) hCa.1

omit [Fintype V] in
/-- A child that strictly outscores every sibling is the `argmax`. -/
theorem argmax?_eq_some_of_dominates {score : Block V → Nat}
    {children : Finset (Block V)} {C : Block V} (hC : C ∈ children)
    (hdom : ∀ D ∈ children, D ≠ C → score D < score C) :
    Protocol.argmax? score children = some C := by
  refine pickUnique?_eq_some hC ?_ (fun a ha hbest => eq_of_is_best_in hC ha hdom hbest)
  simp only [Protocol.is_best_in, decide_eq_true_eq]
  intro D hD
  by_cases hDC : D = C
  · subst hDC
    simp [Protocol.outranks]
  · have hlt := hdom D hD hDC
    simp only [Protocol.outranks, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    exact ⟨by omega, Or.inl (by omega)⟩

omit [Fintype V] in
/-- A nonempty child set has an `argmax` when roots are injective in the containing tree. -/
theorem exists_argmax?_eq_some_of_rootInjectiveBelow
    {tree children : Finset (Block V)} {score : Block V → Nat}
    (hroot : RootInjectiveBelow tree) (hne : children.Nonempty)
    (hsub : children ⊆ tree) :
    ∃ C ∈ children, Protocol.argmax? score children = some C := by
  obtain ⟨M, hM, hMscore⟩ := Finset.exists_mem_eq_sup' hne score
  have hscoreMax : ∀ D ∈ children, score D ≤ score M := by
    intro D hD
    rw [← hMscore]
    exact Finset.le_sup' score hD
  let top := children.filter (fun D => score D = score M)
  have hMtop : M ∈ top := by
    dsimp only [top]
    exact Finset.mem_filter.mpr ⟨hM, rfl⟩
  obtain ⟨C, hCtop, hCroot⟩ :=
    Finset.exists_mem_eq_sup' ⟨M, hMtop⟩ Block.root
  have hCdata : C ∈ children ∧ score C = score M := by
    simpa only [top, Finset.mem_filter] using hCtop
  have hrootMax : ∀ D ∈ top, D.root ≤ C.root := by
    intro D hD
    rw [← hCroot]
    exact Finset.le_sup' Block.root hD
  have hCbest : Protocol.is_best_in score children C = true := by
    simp only [Protocol.is_best_in, decide_eq_true_eq]
    intro D hD
    simp only [Protocol.outranks, Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨?_, ?_⟩
    · have := hscoreMax D hD
      omega
    · by_cases heq : score C = score D
      · right
        have hDtop : D ∈ top := by
          dsimp only [top]
          exact Finset.mem_filter.mpr ⟨hD, heq.symm.trans hCdata.2⟩
        exact not_lt_of_ge (hrootMax D hDtop)
      · exact Or.inl heq
  refine ⟨C, hCdata.1, pickUnique?_eq_some hCdata.1 hCbest ?_⟩
  intro D hD hDbest
  simp only [Protocol.is_best_in, decide_eq_true_eq] at hDbest
  have hCD := hDbest C hCdata.1
  simp only [Protocol.outranks, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hCD
  have hDscoreLe : score D ≤ score C := by
    have := hscoreMax D hD
    omega
  have hscoreEq : score D = score C :=
    le_antisymm hDscoreLe (le_of_not_gt hCD.1)
  have hDtop : D ∈ top := by
    dsimp only [top]
    exact Finset.mem_filter.mpr ⟨hD, hscoreEq.trans hCdata.2⟩
  have hrootNot : ¬ D.root < C.root := by
    rcases hCD.2 with hneScore | hnot
    · exact False.elim (hneScore hscoreEq)
    · exact hnot
  have hrootEq : D.root = C.root :=
    le_antisymm (hrootMax D hDtop) (le_of_not_gt hrootNot)
  exact hroot D C
    ⟨D, hsub hD, Block.preceq_self D⟩
    ⟨C, hsub hCdata.1, Block.preceq_self C⟩ hrootEq

/-! ## One step of the walk -/

omit [Fintype V] in
/-- A step of the walk lands on an eligible child of the current head that is in the tree. -/
theorem ghost_step_child {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {H C : Block V}
    (h : Protocol.ghost_step tree score eligible H = some C) :
    C ∈ tree ∧ C.parent? = some H ∧ eligible C = true := by
  have hmem : C ∈ Protocol.ghost_children tree eligible H :=
    Proofs.Engine.pickUnique?_mem h
  rw [Protocol.ghost_children, Finset.mem_filter] at hmem
  exact ⟨hmem.1, hmem.2.1, hmem.2.2⟩

omit [Fintype V] in

/-- The walk takes no step at a head with no eligible child in the tree. -/
theorem ghost_step_none {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {H : Block V}
    (h : ∀ C ∈ tree, C.parent? = some H → eligible C = false) :
    Protocol.ghost_step tree score eligible H = none := by
  refine pickUnique?_empty ?_
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  rw [Protocol.ghost_children, Finset.mem_filter] at hC
  exact absurd hC.2.2 (by rw [h C hC.1 hC.2.1]; simp)

omit [DecidableEq V] [Fintype V] in
/-- A child is one edge deeper than its parent. -/
theorem depth_of_parent? {C H : Block V} (h : C.parent? = some H) :
    C.depth = H.depth + 1 := by
  cases C with
  | genesis => simp [Block.parent?] at h
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent?, Option.some.injEq] at h
      subst h
      rfl

omit [Fintype V] in
/-- A parent is an ancestor of its child. -/
theorem preceq_of_parent? {C H : Block V} (h : C.parent? = some H) :
    Block.preceq H C = true := by
  have hp := Proofs.parent_eq_of_parent? h
  rw [← hp]
  exact Proofs.preceq_parent C

/-! ## The walk never retreats past its anchor -/

omit [Fintype V] in
/-- A fuelled GHOST walk's result is a descendant of its starting block. -/
theorem ghost_walk_preceq (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    ∀ (n : Nat) (H : Block V),
      Block.Preceq H (Protocol.ghost_walk tree score eligible n H) := by
  intro n
  induction n with
  | zero => intro H; exact Block.preceq_self _
  | succ n ih =>
      intro H
      rw [Protocol.ghost_walk]
      split
      · exact Block.preceq_self _
      · rename_i C hstep
        exact Block.preceq_trans (preceq_of_parent? (ghost_step_child hstep).2.1) (ih C)

omit [Fintype V] in
/-- The result of `ghost` is a descendant of its anchor. -/
theorem ghost_preceq (anchor : Block V) (tree : Finset (Block V))
    (score : Block V → Nat) (eligible : Block V → Bool) :
    Block.Preceq anchor (Protocol.ghost anchor tree score eligible) :=
  ghost_walk_preceq tree score eligible tree.card anchor

omit [Fintype V] in
/-- A fuelled GHOST walk's result is its starting block or an eligible block. -/
theorem ghost_walk_eligible (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    ∀ (n : Nat) (H : Block V),
      Protocol.ghost_walk tree score eligible n H = H ∨
        eligible (Protocol.ghost_walk tree score eligible n H) = true := by
  intro n
  induction n with
  | zero => intro H; exact Or.inl rfl
  | succ n ih =>
      intro H
      rw [Protocol.ghost_walk]
      split
      · exact Or.inl rfl
      · rename_i C hstep
        rcases ih C with h | h
        · exact Or.inr (by rw [h]; exact (ghost_step_child hstep).2.2)
        · exact Or.inr h

omit [Fintype V] in
/-- The result of `ghost` is its anchor or an eligible block. -/
theorem ghost_eligible (anchor : Block V) (tree : Finset (Block V))
    (score : Block V → Nat) (eligible : Block V → Bool) :
    Protocol.ghost anchor tree score eligible = anchor ∨
      eligible (Protocol.ghost anchor tree score eligible) = true :=
  ghost_walk_eligible tree score eligible tree.card anchor

/-! ## Steps towards a target -/

omit [Fintype V] in
/-- A child is not an ancestor of its parent. -/
theorem preceq_parent_false {C H : Block V} (h : C.parent? = some H) :
    Block.preceq C H = false := by
  rw [← Bool.not_eq_true]
  intro hpre
  have := Block.preceq_depth_le hpre
  rw [depth_of_parent? h] at this
  omega


omit [Fintype V] in
/-- A strict ancestor `H` of `B` has a child that is an ancestor of `B`. -/
theorem exists_child_towards {H : Block V} :
    ∀ B : Block V, Block.preceq H B = true → H ≠ B →
      ∃ C, C.parent? = some H ∧ Block.preceq C B = true := by
  intro B
  induction B with
  | genesis =>
      intro hpre hne
      exact absurd (by simpa only [Block.preceq, decide_eq_true_eq] using hpre) hne
  | node p s r gv gsv ats i ih =>
      intro hpre hne
      by_cases hHp : H = p
      · subst hHp
        exact ⟨Block.node H s r gv gsv ats i, rfl, Block.preceq_self _⟩
      · have hp : Block.preceq H p = true := by
          simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hpre
          rcases hpre with h | h
          · exact absurd h hne
          · exact h
        obtain ⟨C, hpar, hCp⟩ := ih hp hHp
        refine ⟨C, hpar, Block.preceq_trans hCp ?_⟩
        simp only [Block.preceq, Bool.or_eq_true]
        exact Or.inr (Block.preceq_self _)

omit [Fintype V] in
/-- Two children of one block that are both ancestors of a common block `B` are equal. -/
theorem child_towards_unique {H C D B : Block V} (hC : C.parent? = some H)
    (hD : D.parent? = some H) (hCB : Block.preceq C B = true)
    (hDB : Block.preceq D B = true) : D = C := by
  rcases Block.preceq_linear hDB hCB with h | h
  · exact Block.preceq_eq_of_depth_le h (by rw [depth_of_parent? hC, depth_of_parent? hD])
  · exact (Block.preceq_eq_of_depth_le h
      (by rw [depth_of_parent? hC, depth_of_parent? hD])).symm

/-! ## The path fits in the tree -/

omit [Fintype V] in
/-- If every block after the anchor up to the target is in the tree, the target's depth is at most
    the anchor's depth plus `tree.card`. -/
theorem path_card (anchor : Block V) :
    ∀ (target : Block V) (tree : Finset (Block V)), Block.Preceq anchor target →
      (∀ C : Block V, Block.Preceq anchor C → C ≠ anchor → Block.Preceq C target →
        C ∈ tree) →
      target.depth ≤ anchor.depth + tree.card := by
  intro target
  induction target with
  | genesis =>
      intro tree hpre _
      have hg : anchor = Block.genesis := by
        simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using hpre
      subst hg
      simp
  | node p s r gv gsv ats i ih =>
      intro tree hpre hmem
      set T : Block V := Block.node p s r gv gsv ats i with hT
      by_cases hEq : anchor = T
      · rw [hEq]
        omega
      · have hanp : Block.Preceq anchor p := by
          simp only [Block.Preceq, hT, Block.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hpre
          rcases hpre with h | h
          · exact absurd h hEq
          · exact h
        have hpT : Block.Preceq p T := by
          simp only [Block.Preceq, hT, Block.preceq, Bool.or_eq_true]
          exact Or.inr (Block.preceq_self _)
        have hTmem : T ∈ tree := hmem T hpre (Ne.symm hEq) (Block.preceq_self _)
        have hmem' : ∀ C : Block V, Block.Preceq anchor C → C ≠ anchor →
            Block.Preceq C p → C ∈ tree.erase T := by
          intro C h1 h2 h3
          refine Finset.mem_erase.mpr ⟨?_, hmem C h1 h2 (Block.preceq_trans h3 hpT)⟩
          intro hCT
          have : (T : Block V).depth ≤ p.depth := by
            rw [← hCT]; exact Block.preceq_depth_le h3
          simp only [hT, Block.depth] at this
          omega
        have hIH := ih (tree.erase T) hanp hmem'
        have hcard : (tree.erase T).card = tree.card - 1 := Finset.card_erase_of_mem hTmem
        have hpos : 1 ≤ tree.card := Finset.card_pos.mpr ⟨T, hTmem⟩
        have hdT : (T : Block V).depth = p.depth + 1 := by simp [hT, Block.depth]
        omega

/-! ## Domination along a path drives the walk to its end -/

omit [Fintype V] in
/-- The fuelled walk reaches `target` when each block of the path after the current head is the
    walk's next step and `target` has no next step. -/
theorem ghost_walk_reaches {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hstop : Protocol.ghost_step tree score eligible target = none)
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    ∀ (n : Nat) (H : Block V), Block.Preceq anchor H → Block.Preceq H target →
      target.depth ≤ H.depth + n →
      Protocol.ghost_walk tree score eligible n H = target := by
  intro n
  induction n with
  | zero =>
      intro H _ hpre hd
      have : H = target := Block.preceq_eq_of_depth_le hpre (by omega)
      simpa only [Protocol.ghost_walk] using this
  | succ n ih =>
      intro H hanch hpre hd
      by_cases hHt : H = target
      · subst hHt
        simp only [Protocol.ghost_walk, hstop]
      · obtain ⟨C, hCs, hCp⟩ := hstep H hanch hpre hHt
        have hchild := ghost_step_child hCs
        have hdepth : C.depth = H.depth + 1 := depth_of_parent? hchild.2.1
        simp only [Protocol.ghost_walk, hCs]
        exact ih C (Block.preceq_trans hanch (preceq_of_parent? hchild.2.1)) hCp (by omega)

omit [Fintype V] in
/-- `ghost` returns `target` when the path from the anchor lies in the tree, each block of it is the
    walk's own next step, and `target` has no eligible child. -/
theorem ghost_reaches {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hpre : Block.Preceq anchor target)
    (hpath : ∀ C : Block V, Block.Preceq anchor C → C ≠ anchor → Block.Preceq C target →
      C ∈ tree)
    (hstop : Protocol.ghost_step tree score eligible target = none)
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    Protocol.ghost anchor tree score eligible = target :=
  ghost_walk_reaches hstop hstep tree.card anchor (Block.preceq_self _) hpre
    (path_card anchor target tree hpre hpath)

end Protocol
end DecoupledConsensusModel

end
