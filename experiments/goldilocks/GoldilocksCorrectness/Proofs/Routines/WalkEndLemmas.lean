module
public import GoldilocksCorrectness.Proofs.Routines.WalkEndBridge
public import GoldilocksCorrectness.Proofs.Routines.Lemma2
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# The single-walk lemmas over the walk predicate

The proofs of the statements of `Statements/Routines/WalkEndStatements.lean`: Lemmas 1, 2, 3, 4 and
10, and the two facts on where the Goldfish fork choice through a viable tree ends, each with the
walk given by the predicate `WalkEnd tree score eligible anchor H`
(`Statements/Routines/WalkEndDefs.lean`) for an arbitrary tie-break (`TieBreak V`), in place of
the spec's walk `ghost` or `goldfish_fork_choice`.

- the walk predicate's facts: `walkStep_unique` (the walk steps to one block),
  `mem_highestEligibleChildren_of_walkStep` (the block it steps to has the highest score),
  `walkStep_of_dominates` (a child that outscores every other eligible child is the step),
  `walkSteps_split` (a chain of walk steps passes every block between its ends),
  `walkSteps_spec`, `walkEnd_mem_tree_or_eq`, `walkEnd_eq_of_walkSteps` (where the walk ends is
  unique), `walkEnd_passes` (the walk passes a block when every step on the way to it goes
  towards it);
- Lemmas 1, 2, 3, 4, 9 and 10 over `WalkEnd`; Lemma 9's statement page is a later step's, and
  its proof is here because Lemma 10's proof calls it;
- `walkEnd_viable_of_below` and `walkEnd_extends`, the forms of `walk_end_viable_of_below` and
  `walk_end_extends` (`Proofs/Routines/ForkChoiceFacts.lean`).

No proof here reads the tie-break beyond its two laws.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V]

/-! ## The walk predicate's facts -/

omit [DecidableEq V] in
/-- The walk steps from `H` to one block: two walk steps from `H` go to the same block.

Why: both are the tie-break's pick from the same set.

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block stepped from; `C`, `C'`: the blocks
  stepped to.

Read aloud: a walk step from `H` goes to one block only. -/
theorem walkStep_unique [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {H C C' : Block V}
    (h : WalkStep tree score eligible H C) (h' : WalkStep tree score eligible H C') : C' = C :=
  h'.2.2.2.2.2.trans h.2.2.2.2.2.symm

omit [DecidableEq V] in
/-- The block a walk step from `H` goes to is an eligible child of `H` in `tree` with the highest
score.

Why: the eligible children of `H` in `tree` are a finite nonempty set (`C` is one) on which the
score answers, so some of them have the highest score, and the tie-break picks a member of that
nonempty set (`tieBreak_mem`).

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block stepped from; `C`: the block stepped to.

Read aloud: the walk steps to an eligible child with the highest score. -/
theorem mem_highestEligibleChildren_of_walkStep [TieBreak V] {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool} {H C : Block V}
    (h : WalkStep tree score eligible H C) :
    C ∈ highestEligibleChildren tree score eligible H := by
  classical
  obtain ⟨hCt, hCp, hCe, -, hsc, hC⟩ := h
  rw [hC]
  apply TieBreak.tieBreak_mem
  let n : Block V → ℕ := fun D => if hD : ∃ k : ℕ, score D = .ok k then hD.choose else 0
  have hn : ∀ D ∈ tree, D.parent? = some H → eligible D = .ok true → score D = .ok (n D) := by
    intro D hD hp he
    have hD' := hsc D hD hp he
    simp only [n, dif_pos hD']
    exact hD'.choose_spec
  set children := tree.filter (fun D => D.parent? = some H ∧ eligible D = .ok true) with hch
  have hCch : C ∈ children := Finset.mem_filter.2 ⟨hCt, hCp, hCe⟩
  obtain ⟨C₀, hC₀, hC₀max⟩ := Finset.exists_max_image children n ⟨C, hCch⟩
  obtain ⟨hC₀t, hC₀p, hC₀e⟩ := Finset.mem_filter.1 hC₀
  refine ⟨C₀, mem_highestEligibleChildren_iff.2 ⟨hC₀t, hC₀p, hC₀e, n C₀, hn C₀ hC₀t hC₀p hC₀e,
    fun D' hD' hp' he' k' hk' => ?_⟩⟩
  rw [hn D' hD' hp' he', Except.ok.injEq] at hk'
  subst hk'
  exact hC₀max D' (Finset.mem_filter.2 ⟨hD', hp', he'⟩)

omit [DecidableEq V] in
/-- The walk steps from `H` to its child `C` in `tree`, when the test accepts `C`, the test
answers on every child of `H` in `tree`, the score answers `n D` on every eligible child `D` of
`H` in `tree`, and every other eligible child of `H` in `tree` scores less than `C`.

Why: `C` is then the only eligible child of `H` with the highest score, and the tie-break picks
it from that one-block set (`tieBreak_mem`).

The variables:
- `tree`, `score`, `eligible`: the walk; `H`: the block stepped from; `C`: its child;
- `n`: the score's answers.

Read aloud: a child that outscores every other eligible child is where the walk steps, whatever
the tie-break. -/
theorem walkStep_of_dominates [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {H C : Block V} (n : Block V → ℕ)
    (hC : C.parent? = some H) (hCtree : C ∈ tree) (hCel : eligible C = .ok true)
    -- the test answers on every child of `H` in `tree`
    (hEl : ∀ D ∈ tree, D.parent? = some H → ∃ b : Bool, eligible D = .ok b)
    -- the score answers `n D` on every eligible child `D` of `H` in `tree`
    (hScore : ∀ D ∈ tree, D.parent? = some H → eligible D = .ok true → score D = .ok (n D))
    -- every other eligible child of `H` in `tree` scores less than `C`
    (hdom : ∀ D ∈ tree, D.parent? = some H → eligible D = .ok true → D ≠ C → n D < n C) :
    WalkStep tree score eligible H C := by
  refine ⟨hCtree, hC, hCel, hEl, fun D hD hp he => ⟨n D, hScore D hD hp he⟩, ?_⟩
  have hsingle : highestEligibleChildren tree score eligible H = {C} := by
    ext D
    rw [mem_highestEligibleChildren_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hD, hp, he, k, hk, hkmax⟩
      by_contra hDC
      have h1 := hdom D hD hp he hDC
      have h2 := hkmax C hCtree hC hCel (n C) (hScore C hCtree hC hCel)
      rw [hScore D hD hp he, Except.ok.injEq] at hk
      omega
    · intro hDC
      rw [hDC]
      refine ⟨hCtree, hC, hCel, n C, hScore C hCtree hC hCel, fun D' hD' hp' he' k' hk' => ?_⟩
      rw [hScore D' hD' hp' he', Except.ok.injEq] at hk'
      subst hk'
      by_cases hD'C : D' = C
      · rw [hD'C]
      · exact le_of_lt (hdom D' hD' hp' he' hD'C)
  rw [hsingle]
  exact (Finset.mem_singleton.1 (TieBreak.tieBreak_mem {C} (Finset.singleton_nonempty C))).symm

/-- A chain of walk steps from `A` to `H` passes every block `X` that is `A` or a descendant of
`A` and `H` or an ancestor of `H`: walk steps lead from `A` to `X` and from `X` to `H`.

Why: each step goes to a child; from a block before `X`, the child on the way to `H` is `X` or an
ancestor of `X` (`child_ancestorEq_of_between`).

The variables:
- `tree`, `score`, `eligible`: the walk; `A`: the start; `X`: the block passed; `H`: the end.

Read aloud: a chain of walk steps passes every block between its two ends. -/
theorem walkSteps_split [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {A X H : Block V}
    (h : Relation.ReflTransGen (WalkStep tree score eligible) A H) :
    -- `X` is `A` or a descendant of `A`, and `H` or an ancestor of `H`
    A.AncestorEq X → X.AncestorEq H →
      Relation.ReflTransGen (WalkStep tree score eligible) A X ∧
        Relation.ReflTransGen (WalkStep tree score eligible) X H := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hAX hXH
    rw [ancestorEq_antisymm hXH hAX]
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @head A' C hstep hrest ih =>
    intro hAX hXH
    by_cases hXA : X = A'
    · rw [hXA]
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.head hstep hrest⟩
    · have hCX : C.AncestorEq X :=
        child_ancestorEq_of_between hAX hXA hXH hstep.2.1 (ancestorEq_of_walkSteps hrest)
      obtain ⟨h1, h2⟩ := ih hCX hXH
      exact ⟨Relation.ReflTransGen.head hstep h1, h2⟩

/-- The block a chain of walk steps from `A` reaches is `A`, or a block of `tree` that is a
descendant of `A` and that the test accepts.

Why: the last step goes to a block of `tree` the test accepts (`WalkStep`'s first clause).

The variables:
- `tree`, `score`, `eligible`: the walk; `A`: the start; `H`: the block reached.

Read aloud: walk steps end at the start, or at an eligible block of the tree descending from it. -/
theorem walkSteps_spec [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {A H : Block V}
    (h : Relation.ReflTransGen (WalkStep tree score eligible) A H) :
    H = A ∨ (A.AncestorEq H ∧ eligible H = .ok true ∧ H ∈ tree) := by
  rcases Relation.ReflTransGen.cases_tail h with hHA | ⟨Y, -, hYH⟩
  · exact Or.inl hHA
  · exact Or.inr ⟨ancestorEq_of_walkSteps h, hYH.2.2.1, hYH.1⟩

/-- Where the walk from `A` ends is `A` or a block of `tree`.

The variables:
- `tree`, `score`, `eligible`: the walk; `A`: the start; `H`: the end.

Read aloud: the walk ends at its start or inside the tree. -/
theorem walkEnd_mem_tree_or_eq [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {A H : Block V}
    (h : WalkEnd tree score eligible A H) : H = A ∨ H ∈ tree := by
  rcases walkSteps_spec h.1 with hHA | ⟨-, -, hH⟩
  · exact Or.inl hHA
  · exact Or.inr hH

omit [DecidableEq V] in
/-- The walk from `A` ends at `P`, when walk steps lead from `A` to `P` and the test answers
`false` on every child of `P` in `tree`.

Why: the walk steps to one block from each block (`walkStep_unique`), so the chain of steps to
where the walk ends and the chain to `P` are one chain; neither can go past the other's end, since
a step leaves a block only to an eligible child.

The variables:
- `tree`, `score`, `eligible`: the walk; `A`: the start; `P`: the block walk steps reach; `H`:
  where the walk ends.

Read aloud: where the walk ends is the one block that walk steps reach and no walk step leaves. -/
theorem walkEnd_eq_of_walkSteps [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {A P H : Block V}
    -- walk steps lead from `A` to `P`
    (hP : Relation.ReflTransGen (WalkStep tree score eligible) A P)
    -- the test answers `false` on every child of `P` in `tree`
    (hPstop : ∀ D ∈ tree, D.parent? = some P → eligible D = .ok false)
    -- the walk from `A` ends at `H`
    (h : WalkEnd tree score eligible A H) : H = P := by
  obtain ⟨hpath, hstop⟩ := h
  revert hpath
  induction hP using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hpath
    rcases Relation.ReflTransGen.cases_head hpath with h' | ⟨C, hstep, -⟩
    · exact h'.symm
    · have hC := hPstop C hstep.1 hstep.2.1
      rw [hstep.2.2.1] at hC
      simp at hC
  | @head A' C hstep hrest ih =>
    intro hpath
    rcases Relation.ReflTransGen.cases_head hpath with h' | ⟨C', hstep', hrest'⟩
    · rw [← h'] at hstop
      have hC := hstop C hstep.1 hstep.2.1
      rw [hstep.2.2.1] at hC
      simp at hC
    · have hCC : C' = C := walkStep_unique hstep hstep'
      rw [hCC] at hrest'
      exact ih hrest'

/-- The walk from `A` ends at `B` or a descendant of `B`, when `A` is `B` or an ancestor of `B`
and from every block on the way from `A` to `B` other than `B` the walk steps to a child on the
way to `B`.

Why: induction on the chain of walk steps to the end: at a block before `B` a step leaves it, so
the walk does not end there, and the step it takes is the one towards `B` (`walkStep_unique`); at
`B` the rest of the chain goes from `B` to the end.

The variables:
- `tree`, `score`, `eligible`: the walk; `A`: the start; `B`: the block passed; `H`: the end.

Read aloud: the walk passes `B` when every step on the way to `B` goes towards `B`. -/
theorem walkEnd_passes [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE ℕ}
    {eligible : Block V → DRE Bool} {A B H : Block V}
    -- from every block on the way from `A` to `B` other than `B`, the walk steps to a child on
    -- the way to `B`
    (hstep : ∀ H₀ : Block V, A.AncestorEq H₀ → H₀.AncestorEq B → H₀ ≠ B →
      ∃ C : Block V, WalkStep tree score eligible H₀ C ∧ C.AncestorEq B)
    -- `A` is `B` or an ancestor of `B`
    (hAB : A.AncestorEq B)
    -- the walk from `A` ends at `H`
    (h : WalkEnd tree score eligible A H) : B.AncestorEq H := by
  obtain ⟨hpath, hstop⟩ := h
  have key : ∀ Y : Block V, Relation.ReflTransGen (WalkStep tree score eligible) Y H →
      A.AncestorEq Y → Y.AncestorEq B → B.AncestorEq H := by
    intro Y hY
    induction hY using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro hAY hYB
      by_cases hHB : H = B
      · rw [hHB]
        exact ancestorEq_refl B
      · obtain ⟨C, hC, -⟩ := hstep H hAY hYB hHB
        have hCf := hstop C hC.1 hC.2.1
        rw [hC.2.2.1] at hCf
        simp at hCf
    | @head Y' C' hst hrest ih =>
      intro hAY hYB
      by_cases hYB' : Y' = B
      · rw [← hYB']
        exact ancestorEq_of_walkSteps (Relation.ReflTransGen.head hst hrest)
      · obtain ⟨C, hC, hCB⟩ := hstep Y' hAY hYB hYB'
        have hCC : C' = C := walkStep_unique hC hst
        rw [hCC] at ih
        exact ih (ancestorEq_trans hAY (ancestorEq_of_parent? hC.2.1)) hCB
  exact key A hpath (ancestorEq_refl A) hAB

/-! ## Lemmas 1 to 4 -/

/-- **Lemma 1 over the walk predicate.** The walk from `A` through `tree`, scoring with
`goldfish_score` and stepping onto blocks the test `eligible` accepts, under any tie-break, ends
at `R` or a descendant of `R`, when `A` starts towards `R` in `tree`, each member of `Sup` has one
vote and it supports `R`'s chain, the voters are fewer than twice `Sup`, and the test accepts
every block after `A` up to `R` whose score `n` has `N < 2n`, with `N` less than twice `Sup`.

Why: from a block on the way to `R`, the child towards `R` is supported by all of `Sup`, so the
test accepts it; any other child conflicts with `R`, so it scores less; so the walk steps to the
child towards `R` (`walkStep_of_dominates`), and passes `R` (`walkEnd_passes`).

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes the score counts;
- `s`: the slot of the votes; `eligible`: the eligibility test; `N`: the test's threshold;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Sup`: the validators voting for `R`'s chain.

Read aloud: whatever the tie-break, the walk from a start towards a majority block ends at that
block or a descendant of it. -/
theorem lem1_walkEnd_extends_majority_block [Fintype V] [TieBreak V] (Φ : Frame V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (eligible : Block V → DRE Bool)
    (N : ℕ) (A R H : Block V) (tree : Finset (Block V)) (Sup : Finset V)
    (hStart : StartsTowards A R tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote for `R`'s chain
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v)
    -- the validators with a vote in `votes` are fewer than twice `Sup`
    (hVoters : voters_count votes < 2 * Sup.card)
    -- the threshold is less than twice `Sup`
    (hThreshold : N < 2 * Sup.card)
    -- the test answers on every block
    (hEligibleAnswers : ∀ D : Block V, ∃ b : Bool, eligible D = .ok b)
    -- the test accepts every block after `A` up to `R` whose score `n` has `N < 2n`
    (hEligibleTrue : ∀ D : Block V, A.AncestorEq D → D ≠ A → D.AncestorEq R → ∀ n : ℕ,
      goldfish_score Φ votes support_votes s D = .ok n → N < 2 * n → eligible D = .ok true)
    -- the walk from `A` ends at `H`
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s) eligible A H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H := by
  rcases hStart with hRA | ⟨hAR, hPath⟩
  · exact ancestorEq_trans hRA (ancestorEq_of_walkSteps hWalk.1)
  · have hScore := goldfish_score_eq_ok hRoots votes support_votes s
    refine walkEnd_passes ?_ hAR hWalk
    intro H₀ hAH₀ hH₀R hne
    obtain ⟨C, hC, hCR⟩ := exists_child_towards hH₀R hne
    have hAC : A.AncestorEq C := ancestorEq_trans hAH₀ (ancestorEq_of_parent? hC)
    have hCA : C ≠ A := fun hCA => by
      have := depth_le_of_ancestorEq hAH₀
      rw [← hCA, depth_of_parent? hC] at this
      omega
    have hCtree : C ∈ tree := hPath C hAC hCA hCR
    -- every member of `Sup` supports `C`, so the test accepts `C`
    have hSupC : Sup ⊆ supportersOf Φ votes support_votes s C :=
      fun v hv => mem_supportersOf_of_votesOnceFor (hSup v hv) hCR
    have hcardC := Finset.card_le_card hSupC
    have hCel : eligible C = .ok true := hEligibleTrue C hAC hCA hCR _ (hScore C) (by omega)
    refine ⟨C, walkStep_of_dominates
      (fun D => (equivocators votes).card + (supportersOf Φ votes support_votes s D).card)
      hC hCtree hCel (fun D _ _ => hEligibleAnswers D) (fun D _ _ _ => hScore D) ?_, hCR⟩
    -- every other child of `H₀` conflicts with `R`, so it scores less than `C`
    intro D _ hD _ hDC
    have hcount := card_add_le_voters hRoots hSupport hSup
      (conflicts_of_sibling_towards hC hD hCR hH₀R hne hDC)
    omega

/-- **Lemma 2 over the walk predicate.** The walk from `A` through `tree` with the Goldfish score
and the Goldfish eligibility test, under any tie-break, ends at `R` or a descendant of `R`, when
`A` starts towards `R` in `tree`, each member of `Sup` has one vote and it supports `R`'s chain,
and the voters are fewer than twice `Sup`.

Why: Lemma 1 over the walk predicate with the Goldfish test and the number of voters as the
threshold: the test accepts every block whose doubled score exceeds the number of voters.

The variables:
- `C`: the configuration; `Φ`: the frame; `t`: the time of the walk;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Sup`: the validators voting for `R`'s chain.

Read aloud: whatever the tie-break, the Goldfish walk from a start towards a majority block ends
at that block or a descendant of it. -/
theorem lem2_goldfish_walkEnd_extends_majority_block [Fintype V] [TieBreak V] (C : Config)
    (Φ : Frame V) (t : Time) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (A R H : Block V) (tree : Finset (Block V)) (Sup : Finset V)
    (hStart : StartsTowards A R tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote for `R`'s chain
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v)
    -- the validators with a vote in `votes` are fewer than twice `Sup`
    (hVoters : voters_count votes < 2 * Sup.card)
    -- the walk from `A` with the Goldfish score and test ends at `H`
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s)
      (goldfish_eligible C Φ t votes support_votes s) A H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H :=
  lem1_walkEnd_extends_majority_block Φ votes support_votes s
    (goldfish_eligible C Φ t votes support_votes s) (voters_count votes) A R H tree Sup hStart
    hRoots hSupport hSup hVoters hVoters
    (goldfish_eligible_answers C hRoots t votes support_votes s)
    (fun D _ _ _ => goldfish_eligible_of_score C Φ t votes support_votes s D) hWalk

/-- **Lemma 3 over the walk predicate.** The walk from `A` through `tree` with the Goldfish score
and the Goldfish eligibility test, under any tie-break, ends at `R` or a descendant of `R`, when
`A` starts towards `R` in `tree`, each member of `Hs` has one vote and it supports `R`'s chain,
every voter is a member of the slot-`s` committee, and `Hs` outnumbers the rest of the
committee.

Why: Lemma 2 over the walk predicate with `Sup := Hs`; the voters are members of the committee,
so they number at most the committee, which is less than twice `Hs`.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `Φ`: the frame; `t`: the time of the walk;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Hs`: the members of the committee voting for `R`'s chain.

Read aloud: whatever the tie-break, the Goldfish walk from a start towards a block a committee
majority votes for ends at that block or a descendant of it. -/
theorem lem3_goldfish_walkEnd_extends_committee_majority_block [Fintype V] [TieBreak V]
    (C : Config) (P : Provisional V) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (A R H : Block V)
    (tree : Finset (Block V)) (Hs : Finset V)
    (hStart : StartsTowards A R tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Hs` has one vote in `votes`, a slot-`s` support vote for `R`'s chain
    (hHs : ∀ v ∈ Hs, VotesOnceFor Φ votes support_votes s R v)
    -- every vote of `votes` is from a member of the slot-`s` committee
    (hCommittee : ∀ vote ∈ votes, vote.val_index ∈ P.committee s)
    -- the members of the committee outside `Hs` are fewer than `Hs`
    (hMajority : (P.committee s \ Hs).card < Hs.card)
    -- the walk from `A` with the Goldfish score and test ends at `H`
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s)
      (goldfish_eligible C Φ t votes support_votes s) A H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H := by
  have hP : participants votes ⊆ P.committee s := fun v hv => by
    obtain ⟨vote, hvote, rfl⟩ := (mem_participants_iff votes v).1 hv
    exact hCommittee vote hvote
  have h1 := Finset.card_le_card hP
  have h2 := Finset.card_le_card_sdiff_add_card (s := P.committee s) (t := Hs)
  have hVoters : voters_count votes < 2 * Hs.card := by
    rw [voters_count_eq]
    omega
  exact lem2_goldfish_walkEnd_extends_majority_block C Φ t votes support_votes s A R H tree Hs
    hStart hRoots hSupport hHs hVoters hWalk

/-- **Lemma 4 over the walk predicate.** The walk from `A`, an ancestor of `R` or `R`, with every
block after `A` up to `R` in `tree`, stepping onto a block exactly when `N` is less than twice its
score, under any tie-break, ends exactly at `R`, when each member of `Sup` has one vote and its
head is `R`'s root, `R` is in `Φ.tree`, the voters are at most `N`, and `N` is less than twice
`Sup`.

Why: Lemma 1 over the walk predicate gives that the walk ends at `R` or a descendant of `R`. A
strict descendant of `R` is supported by no member of `Sup`, so its doubled score is at most
twice the voters minus twice `Sup`, which is at most `N`: the test refuses it, and the walk ends
at a block the test accepts or at its start (`walkSteps_spec`).

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes the score counts;
- `s`: the slot of the votes; `N`: the test's threshold;
- `A`: the block the walk starts from; `R`: the block every supporter names; `H`: the block the
  walk ends at;
- `tree`: the tree walked; `Sup`: the validators naming `R`.

Read aloud: whatever the tie-break, the walk ends exactly at a block every supporter names. -/
theorem lem4_walkEnd_ends_at_unanimous_block [Fintype V] [TieBreak V] (Φ : Frame V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (N : ℕ) (A R H : Block V)
    (tree : Finset (Block V)) (Sup : Finset V)
    -- `A` is an ancestor of `R`, or `R`
    (hAR : A.AncestorEq R)
    -- every block after `A` up to `R`, `R` included, is in `tree`
    (hPath : ∀ P : Block V, A.AncestorEq P → P ≠ A → P.AncestorEq R → P ∈ tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote whose head is `R`'s
    -- root
    (hSup : ∀ v ∈ Sup, ∃ vote ∈ support_votes, vote.val_index = v ∧ vote.slot = s ∧
      vote.head = R.root ∧ ∀ vote' ∈ votes, vote'.val_index = v → vote' = vote)
    -- `R` is a block of `Φ.tree`
    (hR : R ∈ Φ.tree)
    -- the validators with a vote in `votes` are at most the threshold
    (hVotersLe : voters_count votes ≤ N)
    -- the threshold is less than twice `Sup`
    (hThreshold : N < 2 * Sup.card)
    -- the walk from `A`, stepping onto a block when `N` is less than twice its score, ends at `H`
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s)
      (fun D => do return N < 2 * (← goldfish_score Φ votes support_votes s D)) A H) :
    -- then `H` is `R`
    H = R := by
  -- the validators with a vote in `votes` are fewer than twice `Sup`
  have hVoters : voters_count votes < 2 * Sup.card := lt_of_le_of_lt hVotersLe hThreshold
  -- each member of `Sup` votes once for `R`'s chain
  have hSup' : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v := by
    intro v hv
    obtain ⟨vote, hvote, hval, hs, hhead, hu⟩ := hSup v hv
    exact ⟨vote, hvote, hval, hs, ⟨R, hR, hhead.symm, ancestorEq_refl R⟩, hu⟩
  have hScore := goldfish_score_eq_ok hRoots votes support_votes s
  -- the test answers whether `N` is less than twice the score
  have hTest : ∀ D : Block V,
      (do return N < 2 * (← goldfish_score Φ votes support_votes s D) : DRE Bool) =
        .ok (decide (N < 2 *
          ((equivocators votes).card + (supportersOf Φ votes support_votes s D).card))) := by
    intro D
    simp only [hScore D, dre_bind_ok]
    rfl
  have hRH : R.AncestorEq H := lem1_walkEnd_extends_majority_block Φ votes support_votes s
    (fun D => do return N < 2 * (← goldfish_score Φ votes support_votes s D)) N A R H tree Sup
    (Or.inr ⟨hAR, hPath⟩) hRoots hSupport hSup' hVoters hThreshold
    (fun D => ⟨_, hTest D⟩)
    (fun D _ _ _ n hn hlt => by
      simp only [hn, dre_bind_ok]
      show Except.ok _ = Except.ok _
      simp [hlt])
    hWalk
  by_contra hHR
  rcases walkSteps_spec hWalk.1 with hHA | ⟨-, hel, -⟩
  · rw [hHA] at hRH hHR
    exact hHR (ancestorEq_antisymm hAR hRH)
  · rw [hTest H] at hel
    have hlt : N < 2 *
        ((equivocators votes).card + (supportersOf Φ votes support_votes s H).card) := by
      simpa using hel
    -- no member of `Sup` supports `H`, a strict descendant of `R`
    have hdisj : Disjoint (supportersOf Φ votes support_votes s H) Sup := by
      rw [Finset.disjoint_right]
      intro v hv hmem
      obtain ⟨vote, -, -, -, hhead, hu⟩ := hSup v hv
      obtain ⟨vote', hvote', hval', -, -, H', hH', hr', hHH'⟩ :=
        (mem_supportersOf_iff _ _ _ _ _ _).1 hmem
      have hvv : vote' = vote := hu vote' (hSupport hvote') hval'
      rw [hvv] at hr'
      have hH'R : H' = R := hRoots H' hH' R hR (hr'.trans hhead)
      rw [hH'R] at hHH'
      exact hHR (ancestorEq_antisymm hHH' hRH)
    have hcount := card_add_le_voters_of_disjoint hSupport (sup_subset_participants hSupport hSup')
      (Finset.disjoint_left.2 fun v hv => not_mem_equivocators_of_votesOnceFor (hSup' v hv)) hdisj
    omega

/-! ## Lemmas 9 and 10 -/

/-- **Lemma 9 over the walk predicate.** Two walks under the same tie-break: the first, from
`A_p` over `tree_p`, ends at `P`'s parent; the second, from `A_w` over `tree_w`, ends at `H_w`.
If the two scores answer the same number on every child of a block from `X` to `P`'s parent, the
first walk passes `X`, the second starts at `X` or an ancestor of `X` and passes `X`, the blocks
of the first walk after `X` and `P` are in `tree_w`, `P` is eligible in the second walk and has
no child in `tree_w`, the second test accepts every block after `X` up to `P`'s parent, and every
child in `tree_w` of a block from `X` to `P`'s parent, other than `P`, that the second test
accepts is in `tree_p` and accepted by the first test, then the second walk ends at `P`.

Why: walk steps lead the second walk from `A_w` to `X` (`walkSteps_split`). From a block `Y` from
`X` on, before `P`'s parent, the first walk steps to `C`; the eligible children of `Y` with the
highest score in the second walk are among those of the first and include `C`, so the tie-break
keeps its pick `C` (`tieBreak_subset`). At `P`'s parent, `P` is the only eligible child of the
second walk, since the first walk ends there. At `P` no step leaves, so the second walk ends at
`P` (`walkEnd_eq_of_walkSteps`). No hypothesis on the roots of `tree_p` is needed: the first
walk's end says outright that no child of `P`'s parent in `tree_p` is eligible.

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `A_w`, `tree_w`, `score_w`,
  `eligible_w`: the second; `H_w`: where the second ends;
- `X`: the block both pass; `P`: the block after the first walk's end;
- `n`: the scores' answers; `b_p`, `b_w`: the two tests' answers.

Read aloud: under one tie-break, a walk that agrees with another from a shared block on ends at
the proposal that extends the other's end. -/
theorem lem9_walkEnd_ends_at_proposal_of_shared_block [TieBreak V] {A_p A_w X P H_w : Block V}
    {tree_p tree_w : Finset (Block V)}
    {score_p score_w : Block V → DRE Nat} {eligible_p eligible_w : Block V → DRE Bool}
    (n : Block V → ℕ) (b_p b_w : Block V → Bool)
    -- the first score answers `n D` on every child `D` of a block from `X` to `P`'s parent
    (hScoreP : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → score_p D = .ok (n D))
    -- the second score answers `n D` on every child `D` of a block from `X` to `P`'s parent
    (hScoreW : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → score_w D = .ok (n D))
    -- the first test answers `b_p D` on every block `D`
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    -- the second test answers `b_w D` on every block `D`
    (hTestW : ∀ D : Block V, eligible_w D = .ok (b_w D))
    -- `P` is a child of its parent: `P` is not the genesis block
    (hPpar : P.parent? = some P.parent)
    -- the first walk ends at `P`'s parent
    (hWalkP : WalkEnd tree_p score_p eligible_p A_p P.parent)
    -- the second walk ends at `H_w`
    (hWalkW : WalkEnd tree_w score_w eligible_w A_w H_w)
    -- `X` is `A_p` or a descendant of it, and `P`'s parent or an ancestor of it
    (hXOnWalkP : A_p.AncestorEq X ∧ X.AncestorEq P.parent)
    -- `X` is `A_w` or a descendant of it
    (hRootWX : A_w.AncestorEq X)
    -- `X` is `H_w` or an ancestor of it
    (hXW : X.AncestorEq H_w)
    -- every block after `X` up to `P`'s parent is in `tree_w`
    (hPathInTreeW : ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → Y ∈ tree_w)
    -- `P` is in `tree_w`
    (hPInTree : P ∈ tree_w)
    -- the second test answers `true` on `P`
    (hPTest : b_w P = true)
    -- no block of `tree_w` is a child of `P`
    (hNoChildP : ∀ D ∈ tree_w, D.parent? ≠ some P)
    -- the second test answers `true` on every block after `X` up to `P`'s parent
    (hPathTest : ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → b_w Y = true)
    -- every child in `tree_w` of a block from `X` to `P`'s parent, other than `P`, on which the
    -- second test answers `true`, is in `tree_p` and the first test answers `true` on it
    (hEligSub : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D ∈ tree_w, D.parent? = some Y → D ≠ P → b_w D = true → D ∈ tree_p ∧ b_p D = true) :
    -- then the second walk ends at `P`
    H_w = P := by
  obtain ⟨hpathP, hstopP⟩ := hWalkP
  -- the second walk reaches `X`
  have hAwX : Relation.ReflTransGen (WalkStep tree_w score_w eligible_w) A_w X :=
    (walkSteps_split hWalkW.1 hRootWX hXW).1
  -- the first walk goes from `X` to `P`'s parent
  have hXPp : Relation.ReflTransGen (WalkStep tree_p score_p eligible_p) X P.parent :=
    (walkSteps_split hpathP hXOnWalkP.1 hXOnWalkP.2).2
  -- a step of the first walk from `X` on, to a block that is `P`'s parent or an ancestor of it,
  -- is a step of the second walk
  have hstepW : ∀ Y C : Block V, X.AncestorEq Y → C.AncestorEq P.parent →
      WalkStep tree_p score_p eligible_p Y C → WalkStep tree_w score_w eligible_w Y C := by
    intro Y C hXY hCPp hst
    have hYC : Y.AncestorEq C := ancestorEq_of_parent? hst.2.1
    have hYPp : Y.AncestorEq P.parent := ancestorEq_trans hYC hCPp
    have hXC : X.AncestorEq C := ancestorEq_trans hXY hYC
    have hdC := depth_of_parent? hst.2.1
    have hCX : C ≠ X := fun h => by
      have h1 := depth_le_of_ancestorEq hXY
      rw [h] at hdC
      omega
    have hCw : C ∈ tree_w := hPathInTreeW C hXC hCX hCPp
    have hbwC : b_w C = true := hPathTest C hXC hCX hCPp
    -- `P` is not a child of `Y`: `Y` is a strict ancestor of `P`'s parent
    have hPY : ∀ D : Block V, D.parent? = some Y → D ≠ P := by
      intro D hD hDP
      rw [hDP, hPpar] at hD
      have hYeq : P.parent = Y := Option.some.inj hD
      have h1 := depth_le_of_ancestorEq hCPp
      rw [hYeq] at h1
      omega
    -- an eligible child of `Y` in `tree_w` is an eligible child of `Y` in `tree_p`
    have hsub : ∀ D ∈ tree_w, D.parent? = some Y → eligible_w D = .ok true →
        D ∈ tree_p ∧ eligible_p D = .ok true := by
      intro D hD hDp he
      have hbw : b_w D = true := by
        rw [hTestW D] at he
        exact Except.ok.inj he
      obtain ⟨h1, h2⟩ := hEligSub Y hXY hYPp D hD hDp (hPY D hDp) hbw
      exact ⟨h1, by rw [hTestP D, h2]⟩
    have hCel : eligible_w C = .ok true := by rw [hTestW C, hbwC]
    have hscP : ∀ D : Block V, D.parent? = some Y → score_p D = .ok (n D) := hScoreP Y hXY hYPp
    have hscW : ∀ D : Block V, D.parent? = some Y → score_w D = .ok (n D) := hScoreW Y hXY hYPp
    -- `C` has the highest score among the first walk's eligible children of `Y`
    obtain ⟨-, -, -, k, hk, hkmax⟩ :=
      mem_highestEligibleChildren_iff.1 (mem_highestEligibleChildren_of_walkStep hst)
    rw [hscP C hst.2.1, Except.ok.injEq] at hk
    -- `C` has the highest score among the second walk's eligible children of `Y`
    have hCw_mem : C ∈ highestEligibleChildren tree_w score_w eligible_w Y := by
      refine mem_highestEligibleChildren_iff.2 ⟨hCw, hst.2.1, hCel, n C, hscW C hst.2.1, ?_⟩
      intro D' hD' hp' he' k' hk'
      obtain ⟨hD'p, he'p⟩ := hsub D' hD' hp' he'
      rw [hscW D' hp', Except.ok.injEq] at hk'
      have := hkmax D' hD'p hp' he'p (n D') (hscP D' hp')
      omega
    -- the second walk's highest eligible children of `Y` are among the first walk's
    have hWsub : highestEligibleChildren tree_w score_w eligible_w Y ⊆
        highestEligibleChildren tree_p score_p eligible_p Y := by
      intro D hD
      obtain ⟨hDw, hDp, hDe, k₁, hk₁, hk₁max⟩ := mem_highestEligibleChildren_iff.1 hD
      obtain ⟨hDtp, hDep⟩ := hsub D hDw hDp hDe
      refine mem_highestEligibleChildren_iff.2 ⟨hDtp, hDp, hDep, n D, hscP D hDp, ?_⟩
      intro D' hD' hp' he' k' hk'
      rw [hscP D' hp', Except.ok.injEq] at hk'
      rw [hscW D hDp, Except.ok.injEq] at hk₁
      have h1 := hkmax D' hD' hp' he' (n D') (hscP D' hp')
      have h2 := hk₁max C hCw hst.2.1 hCel (n C) (hscW C hst.2.1)
      omega
    refine ⟨hCw, hst.2.1, hCel, fun D _ _ => ⟨b_w D, hTestW D⟩,
      fun D _ hDp _ => ⟨n D, hscW D hDp⟩, ?_⟩
    have hpick : TieBreak.tieBreak (highestEligibleChildren tree_p score_p eligible_p Y) ∈
        highestEligibleChildren tree_w score_w eligible_w Y := by
      rw [← hst.2.2.2.2.2]
      exact hCw_mem
    rw [TieBreak.tieBreak_subset _ _ hWsub hpick]
    exact hst.2.2.2.2.2
  -- the second walk goes from `X` to `P`'s parent
  have hXPw : Relation.ReflTransGen (WalkStep tree_w score_w eligible_w) X P.parent := by
    have key : ∀ Y : Block V,
        Relation.ReflTransGen (WalkStep tree_p score_p eligible_p) Y P.parent →
        X.AncestorEq Y → Relation.ReflTransGen (WalkStep tree_w score_w eligible_w) Y P.parent := by
      intro Y hY
      induction hY using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro _
        exact Relation.ReflTransGen.refl
      | @head Y' C hst hrest ih =>
        intro hXY
        exact Relation.ReflTransGen.head (hstepW Y' C hXY (ancestorEq_of_walkSteps hrest) hst)
          (ih (ancestorEq_trans hXY (ancestorEq_of_parent? hst.2.1)))
    exact key X hXPp (ancestorEq_refl X)
  -- at `P`'s parent the second walk steps to `P`, its only eligible child there
  have hlast : WalkStep tree_w score_w eligible_w P.parent P := by
    refine walkStep_of_dominates n hPpar hPInTree (by rw [hTestW P, hPTest])
      (fun D _ _ => ⟨b_w D, hTestW D⟩)
      (fun D _ hDp _ => hScoreW P.parent hXOnWalkP.2 (ancestorEq_refl _) D hDp) ?_
    intro D hD hDp he hDP
    exfalso
    have hbw : b_w D = true := by
      rw [hTestW D] at he
      exact Except.ok.inj he
    obtain ⟨hDtp, hbp⟩ := hEligSub P.parent hXOnWalkP.2 (ancestorEq_refl _) D hD hDp hDP hbw
    have hf := hstopP D hDtp hDp
    rw [hTestP D, hbp] at hf
    simp at hf
  have hAwP : Relation.ReflTransGen (WalkStep tree_w score_w eligible_w) A_w P :=
    (hAwX.trans hXPw).tail hlast
  exact walkEnd_eq_of_walkSteps hAwP (fun D hD hDp => absurd hDp (hNoChildP D hD)) hWalkW

/-- **Lemma 10 over the walk predicate.** Two walks under the same tie-break score the same
slot-`s` votes with `goldfish_score`: the first, from `A_p` over `tree_p`, ends at `P`'s parent;
the second, from `A_w` over `tree_w`, ends at `H_w`. The second ends at `P`, when each member of
a set `Sup` has one vote and it supports `X`'s chain, the voters are fewer than twice `Sup`, both
tests answer on every block, each test accepts every block after its walk's start up to `X` whose
score `n` has `N < 2n`, with `N` less than twice `Sup`, both walks start at `X` or an ancestor of
`X` with every block after their start up to `X` in their tree, the blocks after `X` up to `P`'s
parent and `P` are in `tree_w`, the second test accepts `P`, no block of `tree_w` is a child of
`P`, the second test accepts every block after `X` up to `P`'s parent, and every child in
`tree_w` of a block from `X` to `P`'s parent, other than `P`, that the second test accepts is in
`tree_p` and accepted by the first test.

Why: Lemma 1 over the walk predicate at each walk gives that it passes `X`. Then Lemma 9 over the
walk predicate, with the scores' answers of `goldfish_score_eq_ok`.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes both scores count;
- `s`: the slot of the votes; `eligible_p`, `eligible_w`: the two tests; `N`: their threshold;
- `A_p`, `A_w`: the starts of the two walks; `X`: the block both pass; `P`: the block after the
  first walk's end; `H_w`: where the second walk ends; `tree_p`, `tree_w`: the two trees;
- `Sup`: the validators voting for `X`'s chain; `b_p`, `b_w`: the two tests' answers.

Read aloud: under one tie-break, when a majority votes for a block both walks pass, the second
walk ends at the proposal extending the first walk's end. -/
theorem lem10_walkEnd_ends_at_proposal_of_majority [Fintype V] [TieBreak V] (Φ : Frame V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (eligible_p eligible_w : Block V → DRE Bool) (N : ℕ) (A_p A_w X P H_w : Block V)
    (tree_p tree_w : Finset (Block V)) (Sup : Finset V) (b_p b_w : Block V → Bool)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote for `X`'s chain
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s X v)
    -- the validators with a vote in `votes` are fewer than twice `Sup`
    (hVoters : voters_count votes < 2 * Sup.card)
    -- the threshold is less than twice `Sup`
    (hThreshold : N < 2 * Sup.card)
    -- the first test answers `b_p D` on every block `D`
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    -- the second test answers `b_w D` on every block `D`
    (hTestW : ∀ D : Block V, eligible_w D = .ok (b_w D))
    -- the first test accepts every block after `A_p` up to `X` whose score `n` has `N < 2n`
    (hTrueP : ∀ D : Block V, A_p.AncestorEq D → D ≠ A_p → D.AncestorEq X → ∀ n : ℕ,
      goldfish_score Φ votes support_votes s D = .ok n → N < 2 * n → b_p D = true)
    -- the second test accepts every block after `A_w` up to `X` whose score `n` has `N < 2n`
    (hTrueW : ∀ D : Block V, A_w.AncestorEq D → D ≠ A_w → D.AncestorEq X → ∀ n : ℕ,
      goldfish_score Φ votes support_votes s D = .ok n → N < 2 * n → b_w D = true)
    -- `P` is a child of its parent: `P` is not the genesis block
    (hPpar : P.parent? = some P.parent)
    -- `A_p` is `X` or an ancestor of `X`
    (hApX : A_p.AncestorEq X)
    -- every block after `A_p` up to `X` is in `tree_p`
    (hPathP : ∀ Y : Block V, A_p.AncestorEq Y → Y ≠ A_p → Y.AncestorEq X → Y ∈ tree_p)
    -- `A_w` is `X` or an ancestor of `X`
    (hAwX : A_w.AncestorEq X)
    -- every block after `A_w` up to `X` is in `tree_w`
    (hPathW : ∀ Y : Block V, A_w.AncestorEq Y → Y ≠ A_w → Y.AncestorEq X → Y ∈ tree_w)
    -- the first walk ends at `P`'s parent
    (hWalkP : WalkEnd tree_p (goldfish_score Φ votes support_votes s) eligible_p A_p P.parent)
    -- the second walk ends at `H_w`
    (hWalkW : WalkEnd tree_w (goldfish_score Φ votes support_votes s) eligible_w A_w H_w)
    -- every block after `X` up to `P`'s parent is in `tree_w`
    (hPathInTreeW : ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → Y ∈ tree_w)
    -- `P` is in `tree_w`
    (hPInTree : P ∈ tree_w)
    -- the second test answers `true` on `P`
    (hPTest : b_w P = true)
    -- no block of `tree_w` is a child of `P`
    (hNoChildP : ∀ D ∈ tree_w, D.parent? ≠ some P)
    -- the second test answers `true` on every block after `X` up to `P`'s parent
    (hPathTest : ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → b_w Y = true)
    -- every child in `tree_w` of a block from `X` to `P`'s parent, other than `P`, on which the
    -- second test answers `true`, is in `tree_p` and the first test answers `true` on it
    (hEligSub : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D ∈ tree_w, D.parent? = some Y → D ≠ P → b_w D = true → D ∈ tree_p ∧ b_p D = true) :
    -- then the second walk ends at `P`
    H_w = P := by
  -- the first walk passes `X`
  have hXP : X.AncestorEq P.parent :=
    lem1_walkEnd_extends_majority_block Φ votes support_votes s eligible_p N A_p X P.parent
      tree_p Sup (Or.inr ⟨hApX, hPathP⟩) hRoots hSupport hSup hVoters hThreshold
      (fun D => ⟨b_p D, hTestP D⟩)
      (fun D h₁ h₂ h₃ n hn hlt => by rw [hTestP D, hTrueP D h₁ h₂ h₃ n hn hlt])
      hWalkP
  -- the second walk passes `X`
  have hXW : X.AncestorEq H_w :=
    lem1_walkEnd_extends_majority_block Φ votes support_votes s eligible_w N A_w X H_w tree_w
      Sup (Or.inr ⟨hAwX, hPathW⟩) hRoots hSupport hSup hVoters hThreshold
      (fun D => ⟨b_w D, hTestW D⟩)
      (fun D h₁ h₂ h₃ n hn hlt => by rw [hTestW D, hTrueW D h₁ h₂ h₃ n hn hlt])
      hWalkW
  exact lem9_walkEnd_ends_at_proposal_of_shared_block
    (fun D => (equivocators votes).card + (supportersOf Φ votes support_votes s D).card) b_p b_w
    (fun _ _ _ D _ => goldfish_score_eq_ok hRoots votes support_votes s D)
    (fun _ _ _ D _ => goldfish_score_eq_ok hRoots votes support_votes s D) hTestP hTestW
    hPpar hWalkP hWalkW ⟨hApX, hXP⟩ hAwX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest
    hEligSub

/-! ## Where the Goldfish fork choice through a viable tree ends -/

/-- The end `H` of the walk from `A` through the viable tree of `VT`, with the Goldfish score and
the Goldfish eligibility test, under any tie-break, is a viable head, when `H` is on the chain of
the frame's fork-choice root, `H` is a strict ancestor of a viable head `Z ∈ VT`, and `VT` holds
every block from the root to a block of `VT`.

Why: the child of `H` towards `Z` is in the viable tree of `VT`, and when `H` is not a viable head
the Goldfish test accepts it (`goldfish_eligible_of_parent_not_viable`), while at the walk's end
the test accepts no child of `H`. No hypothesis on the roots or on the tree `VT` beyond `hClosed`
is needed: the walk's end says outright that the test refuses every child of `H`.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the start; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `Z`: the viable head.

Read aloud: whatever the tie-break, when the Goldfish walk through a viable tree ends at a strict
ancestor of a viable head of the tree, the end is itself a viable head. -/
theorem walkEnd_viable_of_below [Fintype V] [TieBreak V] (C : Config) (Φ : Frame V) (t : Time)
    (A : Block V) (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H Z : Block V)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hWalk : WalkEnd (viable_tree Φ VT) (goldfish_score Φ votes sv s)
      (goldfish_eligible C Φ t votes sv s) A H)
    (hρH : Φ.fc_root.AncestorEq H) (hZ : Z ∈ VT) (hZv : Z ∈ Φ.viable_heads)
    (hHZ : H.AncestorEq Z) (hne : H ≠ Z) :
    H ∈ Φ.viable_heads := by
  by_contra hnot
  obtain ⟨D, hDp, hDZ⟩ := exists_child_towards hHZ hne
  have hHD : H.AncestorEq D := ancestorEq_of_parent? hDp
  have hDVT : D ∈ VT := hClosed Z hZ D (ancestorEq_trans hρH hHD) hDZ
  have hDv : D ∈ viable_tree Φ VT := by
    simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hDVT, ancestorEq_trans hρH hHD, Z, Finset.mem_inter.2 ⟨hZ, hZv⟩, hDZ⟩
  have hpar : D.parent = H := by
    cases D with
    | genesis => simp [Block.parent?] at hDp
    | node p _ _ _ _ _ _ =>
        simp only [Block.parent?, Option.some.injEq] at hDp
        exact hDp
  have htrue := goldfish_eligible_of_parent_not_viable C Φ t votes sv s D
    (by rw [hpar]; exact hnot)
  have hfalse := hWalk.2 D hDv hDp
  rw [htrue] at hfalse
  simp at hfalse

/-- **The end of the Goldfish walk extends a block every viable head extends**, under any
tie-break. When the walk from the anchor `A` (the fork-choice root, or a block of the viable tree
of the frame's tree) through the viable tree of `VT`, with the Goldfish score and the Goldfish
eligibility test, ends at `H`; `VT` holds a viable head `Y` and every block from the root to a
block of `VT`; every viable head is `F'` or a descendant of `F'`; and no strict ancestor of `F'`
is a viable head — then `H` is `F'` or a descendant of `F'`.

Why: as `walk_end_extends`: the end is the anchor or a block of the viable tree of `VT`
(`walkEnd_mem_tree_or_eq`); a block on `F'`'s chain that is a strict ancestor of `F'` is not a
viable head, and the walk does not end there (`walkEnd_viable_of_below`).

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the anchor; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `F'`: the block;
  `Y`: a viable head of `VT`.

Read aloud: whatever the tie-break, the Goldfish walk through a viable tree ends at `F'` or a
descendant of it, when every viable head descends from `F'` and no strict ancestor of `F'` is a
viable head. -/
theorem walkEnd_extends [Fintype V] [TieBreak V] (C : Config) (Φ : Frame V) (t : Time)
    (A : Block V) (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H F' Y : Block V)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hA : A = Φ.fc_root ∨ A ∈ viable_tree Φ Φ.tree)
    (hWalk : WalkEnd (viable_tree Φ VT) (goldfish_score Φ votes sv s)
      (goldfish_eligible C Φ t votes sv s) A H)
    (hρV : ∀ W ∈ Φ.viable_heads, Φ.fc_root.AncestorEq W)
    (hYVT : Y ∈ VT) (hY : Y ∈ Φ.viable_heads)
    (hP : ∀ W ∈ Φ.viable_heads, F'.AncestorEq W)
    (hQ : ∀ B : Block V, B.AncestorEq F' → B ≠ F' → B ∉ Φ.viable_heads) :
    F'.AncestorEq H := by
  -- a block on the root's chain, an ancestor of a viable head `Z ∈ VT` and of `F'`, is `F'`
  have key : ∀ P : Block V, P = H → Φ.fc_root.AncestorEq P → ∀ Z ∈ VT, Z ∈ Φ.viable_heads →
      P.AncestorEq Z → F'.AncestorEq P := by
    intro P hPH hρP Z hZ hZv hPZ
    rcases ancestorEq_compatible hPZ (hP Z hZv) with hPF | hFP
    · by_cases he : P = F'
      · rw [he]
        exact ancestorEq_refl _
      · have hPv : P ∉ Φ.viable_heads := hQ P hPF he
        have hne : P ≠ Z := fun h => hPv (h ▸ hZv)
        subst hPH
        exact absurd (walkEnd_viable_of_below C Φ t A VT votes sv s P Z hClosed hWalk
          hρP hZ hZv hPZ hne) hPv
    · exact hFP
  rcases walkEnd_mem_tree_or_eq hWalk with hHA | hHT
  · -- the end is the anchor
    have hρA : Φ.fc_root.AncestorEq A := by
      rcases hA with h | h
      · rw [h]
        exact ancestorEq_refl _
      · simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2.1
    -- a viable head extending the anchor
    obtain ⟨Z, hZv, hAZ⟩ : ∃ Z ∈ Φ.viable_heads, A.AncestorEq Z := by
      rcases hA with h | h
      · exact ⟨Y, hY, h ▸ hρV Y hY⟩
      · simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨-, -, W, hW, hAW⟩ := h
        exact ⟨W, (Finset.mem_inter.mp hW).2, hAW⟩
    rcases ancestorEq_compatible hAZ (hP Z hZv) with hAF | hFA
    · -- the anchor is an ancestor of `F'`, so of `Y`
      have hAY : A.AncestorEq Y := ancestorEq_trans hAF (hP Y hY)
      rw [hHA]
      exact key A hHA.symm hρA Y hYVT hY hAY
    · rw [hHA]
      exact hFA
  · -- the end is in the viable tree of `VT`
    simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hHT
    obtain ⟨-, hρH, W, hW, hHW⟩ := hHT
    obtain ⟨hWVT, hWv⟩ := Finset.mem_inter.mp hW
    exact key H rfl hρH W hWVT hWv hHW

end GoldilocksCorrectness.Proofs.Routines
