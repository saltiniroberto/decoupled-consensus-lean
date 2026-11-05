module
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Proofs.Routines.MergeLe
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# The merge of two walks over the walk predicate

The facts of `Proofs/Routines/Merge.lean` and `Proofs/Routines/MergeLe.lean`, with the walk given
by the predicate `WalkStep tree score eligible H C` or `WalkEnd tree score eligible anchor H`
(`Statements/Routines/WalkEndDefs.lean`) under any tie-break (`TieBreak V`), in place of the
spec's step `ghost_step` and walk `ghost`:

- one step, read on two walks: `walkStep_transfer_le`, `walkStep_transfer` (a step the first walk
  takes is the step the second takes), `walkStep_eq_of_only` (a step with one eligible child takes
  it), `walkStep_none_not_eligible` (where no walk step leaves `Y`, no child of `Y` is eligible);
- the merge: `walkEnd_merge_le`, `walkEnd_merge` (the statement of Lemma 9 over the walk
  predicate, `lem9_walkEnd_ends_at_proposal_of_shared_block`);
- the tests along a walk: `walkSteps_visited_test_true` and `walkSteps_path_test_of_test_agree`
  over a chain of walk steps, and their forms over `WalkEnd`, `walkEnd_visited_test_true` and
  `walkEnd_path_test_of_test_agree`;
- Lemma 58 over the walk predicate, `lem58_walkEnd_is_viable_head`, proved here for the statement
  page `Statements/Routines/WalkEndStatements.lean`.

No proof of those reads the tie-break beyond its two laws, and none takes a hypothesis that roots
name the blocks of a tree.

After them, each landed fact recovered at the Goldilocks tie-break (`goldilocksTieBreak`) through
the bridge of `Proofs/Routines/WalkEndBridge.lean`: exactly (`…_recovered`) when the landed
statement provides what the bridge needs, and otherwise with the one added hypothesis that no two
blocks of the tree walked share a root (`…_recovered_of_rootsNameBlocksIn`). `walkSteps_of_ghost_eq_ok`
is the half of the bridge that needs no such hypothesis: every walk of the spec is a chain of walk
steps.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V]

/-! ## One step, read on two walks -/

omit [DecidableEq V] in
/-- When the walk over `tree` steps from `Y` to `C`, the walk over `tree'` steps from `Y` to `C`
too, under the same tie-break, if the two scores give every child of `Y` the same answer, `C` is
a block of `tree'` the second test accepts, and every child of `Y` in `tree'` the second test
accepts is in `tree` and accepted by the first test, or has a score less than `C`'s.

Why: `C` has the highest score among the eligible children of `Y` in `tree`
(`mem_highestEligibleChildren_of_walkStep`), so also among those in `tree'`; every eligible child
of `Y` in `tree'` with the highest score has a score at least `C`'s, so it is not one with a score
less than `C`'s, and it is an eligible child of `Y` in `tree` with the highest score there. The
second set of highest children is then a subset of the first that holds the first's pick `C`, and
the tie-break keeps its pick (`tieBreak_subset`).

The variables:
- `tree`, `score`, `eligible`: the first walk; `tree'`, `score'`, `eligible'`: the second;
- `Y`: the block stepped from; `C`: the block stepped to; `n`: the scores' answers;
- `b`, `b'`: the two tests' answers on the children of `Y`.

Read aloud: the second walk takes the first walk's step from `Y` when every child the second
walk could step to is one the first could step to or scores less than the first's choice. -/
theorem walkStep_transfer_le [TieBreak V] {tree tree' : Finset (Block V)}
    {score score' : Block V → DRE Nat} {eligible eligible' : Block V → DRE Bool} {Y C : Block V}
    (n : Block V → ℕ) (b b' : Block V → Bool)
    -- the first score answers `n D` on every child `D` of `Y`
    (hScore : ∀ D : Block V, D.parent? = some Y → score D = .ok (n D))
    -- the second score answers `n D` on every child `D` of `Y`
    (hScore' : ∀ D : Block V, D.parent? = some Y → score' D = .ok (n D))
    -- the first test answers `b D` on every child `D` of `Y` in `tree`
    (hTest : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok (b D))
    -- the second test answers `b' D` on every child `D` of `Y` in `tree'`
    (hTest' : ∀ D ∈ tree', D.parent? = some Y → eligible' D = .ok (b' D))
    -- the first walk steps from `Y` to `C`
    (h : WalkStep tree score eligible Y C)
    -- `C` is in `tree'`, and the second test answers `true` on it
    (hC : C ∈ tree' ∧ b' C = true)
    -- every child of `Y` in `tree'` the second test passes is in `tree` and passes the first, or
    -- has a score less than `C`'s
    (hSub : ∀ D ∈ tree', D.parent? = some Y → b' D = true →
      (D ∈ tree ∧ b D = true) ∨ n D < n C) :
    -- then the second walk steps from `Y` to `C`
    WalkStep tree' score' eligible' Y C := by
  have hmem := mem_highestEligibleChildren_of_walkStep h
  obtain ⟨-, hCp, -, -, -, hCpick⟩ := h
  obtain ⟨-, -, -, k, hk, hkmax⟩ := mem_highestEligibleChildren_iff.1 hmem
  rw [hScore C hCp, Except.ok.injEq] at hk
  subst hk
  have hCe' : eligible' C = .ok true := by rw [hTest' C hC.1 hCp, hC.2]
  -- an eligible child in the second walk passes the second test
  have hb' : ∀ D ∈ tree', D.parent? = some Y → eligible' D = .ok true → b' D = true := by
    intro D hD hp he
    rw [hTest' D hD hp] at he
    exact Except.ok.inj he
  -- a child the first test passes is eligible in the first walk
  have he : ∀ D ∈ tree, D.parent? = some Y → b D = true → eligible D = .ok true := by
    intro D hD hp hb
    rw [hTest D hD hp, hb]
  -- no eligible child of the first walk scores more than `C`
  have hle : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok true → n D ≤ n C :=
    fun D hD hp he' => hkmax D hD hp he' (n D) (hScore D hp)
  -- `C` has the highest score among the second walk's eligible children of `Y`
  have hCw : C ∈ highestEligibleChildren tree' score' eligible' Y := by
    refine mem_highestEligibleChildren_iff.2 ⟨hC.1, hCp, hCe', n C, hScore' C hCp, ?_⟩
    intro D' hD' hp' he' k' hk'
    rw [hScore' D' hp', Except.ok.injEq] at hk'
    subst hk'
    rcases hSub D' hD' hp' (hb' D' hD' hp' he') with ⟨hD't, hD'b⟩ | hlt
    · exact hle D' hD't hp' (he D' hD't hp' hD'b)
    · exact le_of_lt hlt
  -- the second walk's highest eligible children of `Y` are among the first walk's
  have hWsub : highestEligibleChildren tree' score' eligible' Y ⊆
      highestEligibleChildren tree score eligible Y := by
    intro D hD
    obtain ⟨hDw, hDp, hDe, k₁, hk₁, hk₁max⟩ := mem_highestEligibleChildren_iff.1 hD
    rw [hScore' D hDp, Except.ok.injEq] at hk₁
    subst hk₁
    have hCD : n C ≤ n D := hk₁max C hC.1 hCp hCe' (n C) (hScore' C hCp)
    rcases hSub D hDw hDp (hb' D hDw hDp hDe) with ⟨hDt, hDb⟩ | hlt
    · refine mem_highestEligibleChildren_iff.2 ⟨hDt, hDp, he D hDt hDp hDb, n D, hScore D hDp, ?_⟩
      intro D' hD' hp' he' k' hk'
      rw [hScore D' hp', Except.ok.injEq] at hk'
      subst hk'
      have := hle D' hD' hp' he'
      omega
    · omega
  refine ⟨hC.1, hCp, hCe', fun D hD hp => ⟨b' D, hTest' D hD hp⟩,
    fun D _ hp _ => ⟨n D, hScore' D hp⟩, ?_⟩
  have hpick : TieBreak.tieBreak (highestEligibleChildren tree score eligible Y) ∈
      highestEligibleChildren tree' score' eligible' Y := by
    rw [← hCpick]
    exact hCw
  rw [TieBreak.tieBreak_subset _ _ hWsub hpick]
  exact hCpick

omit [DecidableEq V] in
/-- When the walk over `tree` steps from `Y` to `C`, the walk over `tree'` steps from `Y` to `C`
too, under the same tie-break, if the two scores give every child of `Y` the same answer, `C` is
a block of `tree'` the second test accepts, and every child of `Y` in `tree'` the second test
accepts is in `tree` and accepted by the first test.

Why: `walkStep_transfer_le`, whose last hypothesis this one gives by its first case.

The variables:
- `tree`, `score`, `eligible`: the first walk; `tree'`, `score'`, `eligible'`: the second;
- `Y`: the block stepped from; `C`: the block stepped to; `n`: the scores' answers;
- `b`, `b'`: the two tests' answers on the children of `Y`.

Read aloud: removing candidates the first walk did not pick leaves its pick unchanged, so the
second walk takes the first walk's step. -/
theorem walkStep_transfer [TieBreak V] {tree tree' : Finset (Block V)}
    {score score' : Block V → DRE Nat} {eligible eligible' : Block V → DRE Bool} {Y C : Block V}
    (n : Block V → ℕ) (b b' : Block V → Bool)
    -- the first score answers `n D` on every child `D` of `Y`
    (hScore : ∀ D : Block V, D.parent? = some Y → score D = .ok (n D))
    -- the second score answers `n D` on every child `D` of `Y`
    (hScore' : ∀ D : Block V, D.parent? = some Y → score' D = .ok (n D))
    -- the first test answers `b D` on every child `D` of `Y` in `tree`
    (hTest : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok (b D))
    -- the second test answers `b' D` on every child `D` of `Y` in `tree'`
    (hTest' : ∀ D ∈ tree', D.parent? = some Y → eligible' D = .ok (b' D))
    -- the first walk steps from `Y` to `C`
    (h : WalkStep tree score eligible Y C)
    -- `C` is in `tree'`, and the second test answers `true` on it
    (hC : C ∈ tree' ∧ b' C = true)
    -- every child of `Y` in `tree'` the second test passes is in `tree` and passes the first
    (hSub : ∀ D ∈ tree', D.parent? = some Y → b' D = true → D ∈ tree ∧ b D = true) :
    -- then the second walk steps from `Y` to `C`
    WalkStep tree' score' eligible' Y C :=
  walkStep_transfer_le n b b' hScore hScore' hTest hTest' h hC
    (fun D hD hp hb => Or.inl (hSub D hD hp hb))

omit [DecidableEq V] in
/-- A walk step from `Y` with exactly one eligible child `P` in `tree` goes to `P`, under any
tie-break.

Why: `P` then outscores every other eligible child vacuously (`walkStep_of_dominates`).

The variables:
- `tree`, `score`, `eligible`: the walk; `Y`: the block stepped from; `P`: its eligible child;
- `n`: the score's answers; `b`: the test's answers on the children of `Y`.

Read aloud: where only one child is eligible, the walk steps to it. -/
theorem walkStep_eq_of_only [TieBreak V] {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {Y P : Block V} (n : Block V → ℕ) (b : Block V → Bool)
    -- the score answers `n D` on every child `D` of `Y`
    (hScore : ∀ D : Block V, D.parent? = some Y → score D = .ok (n D))
    -- the test answers `b D` on every child `D` of `Y` in `tree`
    (hTest : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok (b D))
    -- `P` is in `tree`
    (hP : P ∈ tree)
    -- `P` is a child of `Y`
    (hPpar : P.parent? = some Y)
    -- the test answers `true` on `P`
    (hPb : b P = true)
    -- every child of `Y` in `tree` the test passes is `P`
    (hOnly : ∀ D ∈ tree, D.parent? = some Y → b D = true → D = P) :
    -- then the walk steps from `Y` to `P`
    WalkStep tree score eligible Y P := by
  refine walkStep_of_dominates n hPpar hP (by rw [hTest P hP hPpar, hPb])
    (fun D hD hp => ⟨b D, hTest D hD hp⟩) (fun D _ hp _ => hScore D hp) ?_
  intro D hD hp he hne
  rw [hTest D hD hp] at he
  exact absurd (hOnly D hD hp (Except.ok.inj he)) hne

omit [DecidableEq V] in
/-- Where no walk step leaves `Y`, the test answers `false` on every child of `Y` in `tree`, when
the score answers on every child of `Y` and the test on every child of `Y` in `tree`; under any
tie-break, and with no hypothesis on the roots of `tree`.

Why: an accepted child makes the set of eligible children of `Y` with the highest score nonempty
(a finite nonempty set of children has one of the highest score, `Finset.exists_max_image`); the
tie-break picks a member of it (`tieBreak_mem`), and the walk steps to that member.

The variables:
- `tree`, `score`, `eligible`: the walk; `Y`: the block; `n`: the score's answers;
- `b`: the test's answers on the children of `Y`.

Read aloud: the walk stops only where the test accepts no child. -/
theorem walkStep_none_not_eligible [TieBreak V] {tree : Finset (Block V)}
    {score : Block V → DRE Nat} {eligible : Block V → DRE Bool} {Y : Block V} (n : Block V → ℕ)
    (b : Block V → Bool)
    -- the score answers `n D` on every child `D` of `Y`
    (hScore : ∀ D : Block V, D.parent? = some Y → score D = .ok (n D))
    -- the test answers `b D` on every child `D` of `Y` in `tree`
    (hTest : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok (b D))
    -- no walk step leaves `Y`
    (h : ∀ C : Block V, ¬ WalkStep tree score eligible Y C) :
    -- then the test answers `false` on every child of `Y` in `tree`
    ∀ D ∈ tree, D.parent? = some Y → b D = false := by
  classical
  intro D hD hDpar
  by_contra hb
  have hDb : b D = true := by simpa using hb
  set children := tree.filter (fun D => D.parent? = some Y ∧ eligible D = .ok true) with hch
  have hDch : D ∈ children := Finset.mem_filter.2 ⟨hD, hDpar, by rw [hTest D hD hDpar, hDb]⟩
  obtain ⟨C₀, hC₀, hC₀max⟩ := Finset.exists_max_image children n ⟨D, hDch⟩
  obtain ⟨hC₀t, hC₀p, hC₀e⟩ := Finset.mem_filter.1 hC₀
  have hne : (highestEligibleChildren tree score eligible Y).Nonempty := by
    refine ⟨C₀, mem_highestEligibleChildren_iff.2 ⟨hC₀t, hC₀p, hC₀e, n C₀, hScore C₀ hC₀p,
      fun D' hD' hp' he' k' hk' => ?_⟩⟩
    rw [hScore D' hp', Except.ok.injEq] at hk'
    subst hk'
    exact hC₀max D' (Finset.mem_filter.2 ⟨hD', hp', he'⟩)
  obtain ⟨hCt, hCp, hCe, -⟩ :=
    mem_highestEligibleChildren_iff.1 (TieBreak.tieBreak_mem _ hne)
  exact h _ ⟨hCt, hCp, hCe, fun D' hD' hp' => ⟨b D', hTest D' hD' hp'⟩,
    fun D' _ hp' _ => ⟨n D', hScore D' hp'⟩, rfl⟩

/-! ## The merge -/

/-- **The merge with the score argument, over the walk predicate.** Two walks under the same
tie-break, whose scores agree on the children of the blocks from `X` to `P`'s parent: the first,
from `A_p` over `tree_p`, ends at `P`'s parent; the second, from `A_w` over `tree_w`, ends at
`H_w`. If the first walk passes `X`, the second starts at `X` or an ancestor of `X` and passes
`X`, the blocks after `X` up to `P`'s parent and `P` are in `tree_w`, the second test accepts `P`
and every block after `X` up to `P`'s parent, `P` has no child in `tree_w`; if every child in
`tree_w` of a block from `X` to `P`'s parent, other than that parent, that the second test
accepts, is in `tree_p` and accepted by the first test, or has a score less than that of every
child of that block in `tree_p` that is `P`'s parent or an ancestor of it and that the first test
accepts; and if every child of `P`'s parent in `tree_w`, other than `P`, that the second test
accepts, is in `tree_p` and accepted by the first test, then the second walk ends at `P`.

Why: walk steps lead the second walk from `A_w` to `X` (`walkSteps_split`). From a block `Y` from
`X` on, before `P`'s parent, the first walk steps to a child `C` on the path, in `tree_p` and
accepted by the first test, so every child the second test accepts is one the first walk could
step to or scores less than `C`, and the second walk steps to `C` (`walkStep_transfer_le`). At
`P`'s parent the first walk ends, so no child of it in `tree_p` is eligible there, and `P` is the
only eligible child of the second walk (`walkStep_of_dominates`). At `P` no step leaves, so the
second walk ends at `P` (`walkEnd_eq_of_walkSteps`). No hypothesis on the roots of `tree_p` is
needed: the first walk's end says outright that no child of `P`'s parent in `tree_p` is eligible.

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `A_w`, `tree_w`, `score_w`,
  `eligible_w`: the second; `H_w`: where the second ends;
- `X`: the block both pass; `P`: the block after the first walk's end;
- `n`: the scores' answers; `b_p`, `b_w`: the two tests' answers.

Read aloud: under one tie-break, when, along the path, each child the second walk could step to
is one the first walk could step to or loses to every child of the path the first walk accepts,
and at the first walk's end only `P` is left to the second, the second walk ends at `P`. -/
theorem walkEnd_merge_le [TieBreak V] {A_p A_w X P H_w : Block V}
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
    -- every child in `tree_w` of a block `Y` from `X` to `P`'s parent, other than that parent, on
    -- which the second test answers `true`, is in `tree_p` with the first test answering `true`
    -- on it, or has a score less than every child of `Y` in `tree_p` that is `P`'s parent or an
    -- ancestor of it and on which the first test answers `true`
    (hEligSubLe : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent → Y ≠ P.parent →
      ∀ D ∈ tree_w, D.parent? = some Y → b_w D = true →
        (D ∈ tree_p ∧ b_p D = true) ∨
          ∀ D' ∈ tree_p, D'.parent? = some Y → D'.AncestorEq P.parent → b_p D' = true →
            n D < n D')
    -- every child in `tree_w` of `P`'s parent, other than `P`, on which the second test answers
    -- `true`, is in `tree_p` and the first test answers `true` on it
    (hEligSubEnd : ∀ D ∈ tree_w, D.parent? = some P.parent → D ≠ P → b_w D = true →
      D ∈ tree_p ∧ b_p D = true) :
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
    -- `Y` is not `P`'s parent: `C` is `P`'s parent or an ancestor of it
    have hYne : Y ≠ P.parent := fun h => by
      have h1 := depth_le_of_ancestorEq hCPp
      rw [← h] at h1
      omega
    -- the first walk's choice `C` is in `tree_p` and accepted by the first test
    have hCb : b_p C = true := by
      have hCe := hst.2.2.1
      rw [hTestP C] at hCe
      exact Except.ok.inj hCe
    exact walkStep_transfer_le n b_p b_w (hScoreP Y hXY hYPp) (hScoreW Y hXY hYPp)
      (fun D _ _ => hTestP D) (fun D _ _ => hTestW D) hst
      ⟨hPathInTreeW C hXC hCX hCPp, hPathTest C hXC hCX hCPp⟩
      (fun D hD hDp hDb => (hEligSubLe Y hXY hYPp hYne D hD hDp hDb).imp id
        (fun hlt => hlt C hst.1 hst.2.1 hCPp hCb))
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
    obtain ⟨hDtp, hbp⟩ := hEligSubEnd D hD hDp hDP hbw
    have hf := hstopP D hDtp hDp
    rw [hTestP D, hbp] at hf
    simp at hf
  have hAwP : Relation.ReflTransGen (WalkStep tree_w score_w eligible_w) A_w P :=
    (hAwX.trans hXPw).tail hlast
  exact walkEnd_eq_of_walkSteps hAwP (fun D hD hDp => absurd hDp (hNoChildP D hD)) hWalkW

/-- **The merge, over the walk predicate.** Two walks under the same tie-break, whose scores
agree on the children of the blocks from `X` to `P`'s parent: the first, from `A_p` over
`tree_p`, ends at `P`'s parent; the second, from `A_w` over `tree_w`, ends at `H_w`. If the first
walk passes `X`, the second starts at `X` or an ancestor of `X` and passes `X`, the blocks after
`X` up to `P`'s parent and `P` are in `tree_w`, the second test accepts `P` and every block after
`X` up to `P`'s parent, `P` has no child in `tree_w`, and every child in `tree_w` of a block from
`X` to `P`'s parent, other than `P`, that the second test accepts is in `tree_p` and accepted by
the first test, then the second walk ends at `P`.

This is the statement of Lemma 9 over the walk predicate
(`lem9_walkEnd_ends_at_proposal_of_shared_block`).

Why: `walkEnd_merge_le`: at a block before `P`'s parent a child of it is not `P`, so the last
hypothesis gives the first case of `hEligSubLe`; at `P`'s parent it is `hEligSubEnd`.

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `A_w`, `tree_w`, `score_w`,
  `eligible_w`: the second; `H_w`: where the second ends;
- `X`: the block both pass; `P`: the block after the first walk's end;
- `n`: the scores' answers; `b_p`, `b_w`: the two tests' answers.

Read aloud: under one tie-break, a walk that agrees with another from a shared block on ends at
the proposal that extends the other's end. -/
theorem walkEnd_merge [TieBreak V] {A_p A_w X P H_w : Block V}
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
  refine walkEnd_merge_le n b_p b_w hScoreP hScoreW hTestP hTestW hPpar hWalkP hWalkW hXOnWalkP
    hRootWX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest
    (fun Y hXY hYH hne D hD hDp hDb => Or.inl (hEligSub Y hXY hYH D hD hDp ?_ hDb))
    (fun D hD hDp hDP hDb => hEligSub P.parent hXOnWalkP.2 (ancestorEq_refl _) D hD hDp hDP hDb)
  rintro rfl
  rw [hPpar] at hDp
  exact hne (Option.some.inj hDp).symm

/-! ## The tests along a walk -/

/-- Every block a chain of walk steps passes through after its start passes the walk's test: for
walk steps from `A` to `H`, with the test answering `b D` on every block `D`, every block after
`A` up to `H` has `b` answering `true` on it.

Why: walk steps lead from `A` to such a block `Y` (`walkSteps_split`); since `Y` is not `A` the
last of them goes to `Y`, and a walk step goes only to a block the test accepts.

The variables:
- `A`: the start; `H`: the end; `tree`, `score`, `eligible`: the walk; `b`: the test's answers.

Read aloud: the walk steps only onto blocks its test accepts. -/
theorem walkSteps_visited_test_true [TieBreak V] {A H : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE Nat} {eligible : Block V → DRE Bool} (b : Block V → Bool)
    -- the test answers `b D` on every block `D`
    (hTest : ∀ D : Block V, eligible D = .ok (b D))
    -- walk steps lead from `A` to `H`
    (hWalk : Relation.ReflTransGen (WalkStep tree score eligible) A H) :
    -- then the test answers `true` on every block after `A` up to `H`
    ∀ Y : Block V, A.AncestorEq Y → Y ≠ A → Y.AncestorEq H → b Y = true := by
  intro Y hAY hYA hYH
  rcases Relation.ReflTransGen.cases_tail (walkSteps_split hWalk hAY hYH).1 with h | ⟨Z, -, hZY⟩
  · exact absurd h hYA
  · have he := hZY.2.2.1
    rw [hTest Y] at he
    exact Except.ok.inj he

/-- Every block a walk passes through after its start passes the walk's test: for a walk from `A`
over `tree` that ends at `H`, under any tie-break, with the test answering `b D` on every block
`D`, every block after `A` up to `H` has `b` answering `true` on it.

Why: `walkSteps_visited_test_true` on the walk steps from `A` to `H`.

The variables:
- `A`: the start; `H`: the end; `tree`, `score`, `eligible`: the walk; `b`: the test's answers.

Read aloud: every block the walk passes after its start is one its test accepts. -/
theorem walkEnd_visited_test_true [TieBreak V] {A H : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE Nat} {eligible : Block V → DRE Bool} (b : Block V → Bool)
    -- the test answers `b D` on every block `D`
    (hTest : ∀ D : Block V, eligible D = .ok (b D))
    -- the walk from `A` ends at `H`
    (hWalk : WalkEnd tree score eligible A H) :
    -- then the test answers `true` on every block after `A` up to `H`
    ∀ Y : Block V, A.AncestorEq Y → Y ≠ A → Y.AncestorEq H → b Y = true :=
  walkSteps_visited_test_true b hTest hWalk.1

/-- The second test accepts every block after `X` up to `P`'s parent, when walk steps of the first
walk lead from `A_p` to `P`'s parent and pass `X`, and the two tests agree on every child of a
block from `X` to `P`'s parent.

Why: such a block is a child of a block from `X` to `P`'s parent, so the two tests agree on it,
and the first test accepts it (`walkSteps_visited_test_true`).

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `X`: the block it passes; `P`: the
  block after its end; `b_p`, `b_w`: the two tests' answers.

Read aloud: where two tests agree along the first walk's path, the second accepts every block of
that path after `X`. -/
theorem walkSteps_path_test_of_test_agree [TieBreak V] {A_p X P : Block V}
    {tree_p : Finset (Block V)} {score_p : Block V → DRE Nat} {eligible_p : Block V → DRE Bool}
    (b_p b_w : Block V → Bool)
    -- the first test answers `b_p D` on every block `D`
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    -- walk steps of the first walk lead from `A_p` to `P`'s parent
    (hWalkP : Relation.ReflTransGen (WalkStep tree_p score_p eligible_p) A_p P.parent)
    -- `X` is `A_p` or a descendant of it, and `P`'s parent or an ancestor of it
    (hXOnWalkP : A_p.AncestorEq X ∧ X.AncestorEq P.parent)
    -- the two tests agree on every child of a block from `X` to `P`'s parent
    (hTestAgree : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → b_w D = b_p D) :
    -- then the second test answers `true` on every block after `X` up to `P`'s parent
    ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → b_w Y = true := by
  intro Y hXY hYX hYP
  have hYg : Y ≠ Block.genesis := by
    rintro rfl
    exact hYX ((ancestorEq_genesis_iff X).1 hXY).symm
  have hYpar := parent?_eq_some_parent hYg
  have hXQ : X.AncestorEq Y.parent := ancestorEq_parent_of_ne hXY (Ne.symm hYX)
  have hQP : Y.parent.AncestorEq P.parent := ancestorEq_trans (ancestorEq_of_parent? hYpar) hYP
  have hYA : Y ≠ A_p := by
    intro h
    have hYXa : Y.AncestorEq X := h ▸ hXOnWalkP.1
    exact hYX (ancestorEq_antisymm hXY hYXa).symm
  rw [hTestAgree Y.parent hXQ hQP Y hYpar]
  exact walkSteps_visited_test_true b_p hTestP hWalkP Y (ancestorEq_trans hXOnWalkP.1 hXY) hYA hYP

/-- The second test accepts every block after `X` up to `P`'s parent, when the first walk, from
`A_p` under any tie-break, ends at `P`'s parent and passes `X`, and the two tests agree on every
child of a block from `X` to `P`'s parent.

Why: `walkSteps_path_test_of_test_agree` on the walk steps from `A_p` to `P`'s parent.

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `X`: the block it passes; `P`: the
  block after its end; `b_p`, `b_w`: the two tests' answers.

Read aloud: where two tests agree along the first walk's path, the second accepts every block of
that path after `X`. -/
theorem walkEnd_path_test_of_test_agree [TieBreak V] {A_p X P : Block V}
    {tree_p : Finset (Block V)} {score_p : Block V → DRE Nat} {eligible_p : Block V → DRE Bool}
    (b_p b_w : Block V → Bool)
    -- the first test answers `b_p D` on every block `D`
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    -- the first walk ends at `P`'s parent
    (hWalkP : WalkEnd tree_p score_p eligible_p A_p P.parent)
    -- `X` is `A_p` or a descendant of it, and `P`'s parent or an ancestor of it
    (hXOnWalkP : A_p.AncestorEq X ∧ X.AncestorEq P.parent)
    -- the two tests agree on every child of a block from `X` to `P`'s parent
    (hTestAgree : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → b_w D = b_p D) :
    -- then the second test answers `true` on every block after `X` up to `P`'s parent
    ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → b_w Y = true :=
  walkSteps_path_test_of_test_agree b_p b_w hTestP hWalkP.1 hXOnWalkP hTestAgree

/-! ## Lemma 58 over the walk predicate -/

/-- **Lemma 58 over the walk predicate, the walk's end in the viable tree is a viable head.** When
the walk from `anchor` through the viable tree of `Φ.tree`, with the Goldfish score and the
Goldfish eligibility test, under any tie-break, ends at `H`, `H` is in the viable tree of
`Φ.tree`, and every block between two blocks of `Φ.tree` is in `Φ.tree`, then `H` is a viable
head of `Φ`.

Why: if `H` were not a viable head, the viable head `W` of the tree that `H` is an ancestor of
would be a strict descendant of `H`; the child `D` of `H` towards `W` is between `H` and `W`, so
in `Φ.tree` and in the viable tree; it passes the eligibility test by its first case, since its
parent `H` is not a viable head (`goldfish_eligible_of_parent_not_viable`); and at the walk's end
the test accepts no child of `H`. No hypothesis on the roots of `Φ.tree` is needed, and the
anchor is any block.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time;
- `votes`, `support_votes`: the votes and the support votes counted; `s`: their slot;
- `anchor`: the block the walk starts from; `H`: the walk's end.

Read aloud: whatever the tie-break, the walk through the viable tree stops at a viable head
whenever it stops inside the viable tree. -/
theorem lem58_walkEnd_is_viable_head [Fintype V] [TieBreak V] (C : Config) (Φ : Frame V)
    (t : Time) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (anchor H : Block V)
    -- every block between two blocks of `Φ.tree` (an ancestor-or-self of the second that the
    -- first is an ancestor-or-self of) is in `Φ.tree`
    (hBetween : ∀ X ∈ Φ.tree, ∀ Y ∈ Φ.tree, ∀ Z : Block V, X.AncestorEq Z → Z.AncestorEq Y →
      Z ∈ Φ.tree)
    -- the walk from `anchor` through the viable tree of `Φ.tree` ends at `H`
    (hWalk : WalkEnd (viable_tree Φ Φ.tree) (goldfish_score Φ votes support_votes s)
      (goldfish_eligible C Φ t votes support_votes s) anchor H)
    -- `H` is in the viable tree of `Φ.tree`
    (hIn : H ∈ viable_tree Φ Φ.tree) :
    -- then `H` is a viable head of `Φ`
    H ∈ Φ.viable_heads := by
  by_contra hnot
  simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hIn
  obtain ⟨hHt, hρH, W, hW, hHW⟩ := hIn
  obtain ⟨hWt, hWv⟩ := Finset.mem_inter.mp hW
  have hne : H ≠ W := fun he => hnot (he ▸ hWv)
  obtain ⟨D, hDp, hDW⟩ := exists_child_towards hHW hne
  have hHD : H.AncestorEq D := ancestorEq_of_parent? hDp
  have hDv : D ∈ viable_tree Φ Φ.tree := by
    simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hBetween H hHt W hWt D hHD hDW, ancestorEq_trans hρH hHD, W, hW, hDW⟩
  have htrue := goldfish_eligible_of_parent_not_viable C Φ t votes support_votes s D
    (by rw [parent_eq_of_parent? hDp]; exact hnot)
  have hfalse := hWalk.2 D hDv hDp
  rw [htrue] at hfalse
  simp at hfalse

/-! ## The landed facts, recovered at the Goldilocks tie-break -/

section Recovered

variable [RootOrder]

/-- Every walk of the spec is a chain of walk steps: when the spec's walk
`ghost anchor tree score eligible` answers `H`, walk steps under the Goldilocks tie-break lead
from `anchor` to `H`, with no hypothesis on the roots of `tree`.

Why: induction on the steps of `ghost_walk`; each step of the spec that answers a block is a walk
step (`walkStep_of_ghost_step`), as in the first half of `walkEnd_of_ghost_eq_ok`, whose second
half (the test accepts no child of `H`) is the only part that needs the roots to name the blocks.

The variables:
- `anchor`: the start; `tree`, `score`, `eligible`: the walk; `H`: the end.

Read aloud: the blocks the spec's walk passes are a chain of walk steps. -/
theorem walkSteps_of_ghost_eq_ok {anchor H : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE ℕ} {eligible : Block V → DRE Bool}
    -- the spec's walk from `anchor` answers `H`
    (h : ghost anchor tree score eligible = .ok H) :
    -- then walk steps under the Goldilocks tie-break lead from `anchor` to `H`
    Relation.ReflTransGen (@WalkStep V goldilocksTieBreak tree score eligible) anchor H := by
  letI : TieBreak V := goldilocksTieBreak
  unfold ghost at h
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

/-- The landed `ghost_step_transfer`, recovered from `walkStep_transfer` at the Goldilocks
tie-break, when no two blocks of `tree'` share a root (a hypothesis the landed statement does not
have).

Why: the spec's step is a walk step (`walkStep_of_ghost_step`); the walk step of the second walk
is a step of the spec when no two blocks of `tree'` share a root (`ghost_step_of_walkStep`).

Read aloud: when no two blocks of the second tree share a root, the landed one-step transfer
follows from its form over the walk predicate. -/
theorem ghost_step_transfer_recovered_of_rootsNameBlocksIn :
    ∀ {tree tree' : Finset (Block V)} {score score' : Block V → DRE Nat}
      {eligible eligible' : Block V → DRE Bool} {Y C : Block V},
      -- no two blocks of `tree'` share a root
      RootsNameBlocksIn tree' →
      type_of% (@ghost_step_transfer V _ _ tree tree' score score' eligible eligible' Y C) := by
  intro tree tree' score score' eligible eligible' Y C hTree' n b b' hScore hScore' hTest hTest' h
    hC hSub
  letI : TieBreak V := goldilocksTieBreak
  exact ghost_step_of_walkStep hTree'
    (walkStep_transfer n b b' hScore hScore' hTest hTest' (walkStep_of_ghost_step h) hC hSub)

/-- The landed `ghost_step_transfer_le`, recovered from `walkStep_transfer_le` at the Goldilocks
tie-break, when no two blocks of `tree'` share a root (a hypothesis the landed statement does not
have).

Why: as for `ghost_step_transfer_recovered_of_rootsNameBlocksIn`.

Read aloud: when no two blocks of the second tree share a root, the landed one-step transfer with
the score argument follows from its form over the walk predicate. -/
theorem ghost_step_transfer_le_recovered_of_rootsNameBlocksIn :
    ∀ {tree tree' : Finset (Block V)} {score score' : Block V → DRE Nat}
      {eligible eligible' : Block V → DRE Bool} {Y C : Block V},
      -- no two blocks of `tree'` share a root
      RootsNameBlocksIn tree' →
      type_of% (@ghost_step_transfer_le V _ _ tree tree' score score' eligible eligible' Y C) := by
  intro tree tree' score score' eligible eligible' Y C hTree' n b b' hScore hScore' hTest hTest' h
    hC hSub
  letI : TieBreak V := goldilocksTieBreak
  exact ghost_step_of_walkStep hTree'
    (walkStep_transfer_le n b b' hScore hScore' hTest hTest' (walkStep_of_ghost_step h) hC hSub)

/-- The landed `ghost_step_eq_of_only`, recovered from `walkStep_eq_of_only` at the Goldilocks
tie-break, when no two blocks of `tree` share a root (a hypothesis the landed statement does not
have).

Why: the walk step is a step of the spec when no two blocks of `tree` share a root
(`ghost_step_of_walkStep`).

Read aloud: when no two blocks of the tree share a root, the landed fact that a step with one
eligible child takes it follows from its form over the walk predicate. -/
theorem ghost_step_eq_of_only_recovered_of_rootsNameBlocksIn :
    ∀ {tree : Finset (Block V)} {score : Block V → DRE Nat} {eligible : Block V → DRE Bool}
      {Y P : Block V},
      -- no two blocks of `tree` share a root
      RootsNameBlocksIn tree →
      type_of% (@ghost_step_eq_of_only V _ _ tree score eligible Y P) := by
  intro tree score eligible Y P hTree n b hScore hTest hP hPpar hPb hOnly
  letI : TieBreak V := goldilocksTieBreak
  exact ghost_step_of_walkStep hTree (walkStep_eq_of_only n b hScore hTest hP hPpar hPb hOnly)

/-- The landed `ghost_step_none_not_eligible`, recovered from `walkStep_none_not_eligible` at the
Goldilocks tie-break.

Why: a walk step from `Y` would be a step of the spec (`ghost_step_of_walkStep`, with the landed
hypothesis that no two blocks of `tree` share a root), and the spec's step from `Y` answers none.

Read aloud: the landed fact that a step answering none has no eligible child follows from its
form over the walk predicate. -/
theorem ghost_step_none_not_eligible_recovered :
    type_of% (@ghost_step_none_not_eligible V _ _) := by
  intro tree score eligible Y n b hScore hTest hRoots h
  letI : TieBreak V := goldilocksTieBreak
  refine walkStep_none_not_eligible n b hScore hTest (fun C hC => ?_)
  have h' := h.symm.trans (ghost_step_of_walkStep hRoots hC)
  simp at h'

/-- The landed `ghost_merge`, recovered from `walkEnd_merge` at the Goldilocks tie-break, when no
two blocks of `tree_w` share a root (a hypothesis the landed statement does not have; it has the
same of `tree_p`, `hRootsP`).

Why: `walkEnd_of_ghost_eq_ok` at each walk, which needs that no two blocks of the tree walked
share a root: `hRootsP` for the first, the added hypothesis for the second.

Read aloud: when no two blocks of the second tree share a root, the landed merge follows from its
form over the walk predicate. -/
theorem ghost_merge_recovered_of_rootsNameBlocksIn :
    ∀ {A_p A_w X P H_w : Block V} {tree_p tree_w : Finset (Block V)}
      {score_p score_w : Block V → DRE Nat} {eligible_p eligible_w : Block V → DRE Bool},
      -- no two blocks of `tree_w` share a root
      RootsNameBlocksIn tree_w →
      type_of% (@ghost_merge V _ _ A_p A_w X P H_w tree_p tree_w score_p score_w eligible_p
        eligible_w) := by
  intro A_p A_w X P H_w tree_p tree_w score_p score_w eligible_p eligible_w hTreeW n b_p b_w
    hScoreP hScoreW hTestP hTestW hRootsP hPpar hWalkP hWalkW hXOnWalkP hRootWX hXW hPathInTreeW
    hPInTree hPTest hNoChildP hPathTest hEligSub
  letI : TieBreak V := goldilocksTieBreak
  exact walkEnd_merge n b_p b_w hScoreP hScoreW hTestP hTestW hPpar
    (walkEnd_of_ghost_eq_ok hRootsP hWalkP) (walkEnd_of_ghost_eq_ok hTreeW hWalkW) hXOnWalkP
    hRootWX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSub

/-- The landed `ghost_merge_le`, recovered from `walkEnd_merge_le` at the Goldilocks tie-break,
when no two blocks of `tree_w` share a root (a hypothesis the landed statement does not have; it
has the same of `tree_p`, `hRootsP`).

Why: `walkEnd_of_ghost_eq_ok` at each walk: `hRootsP` for the first, the added hypothesis for the
second.

Read aloud: when no two blocks of the second tree share a root, the landed merge with the score
argument follows from its form over the walk predicate. -/
theorem ghost_merge_le_recovered_of_rootsNameBlocksIn :
    ∀ {A_p A_w X P H_w : Block V} {tree_p tree_w : Finset (Block V)}
      {score_p score_w : Block V → DRE Nat} {eligible_p eligible_w : Block V → DRE Bool},
      -- no two blocks of `tree_w` share a root
      RootsNameBlocksIn tree_w →
      type_of% (@ghost_merge_le V _ _ A_p A_w X P H_w tree_p tree_w score_p score_w eligible_p
        eligible_w) := by
  intro A_p A_w X P H_w tree_p tree_w score_p score_w eligible_p eligible_w hTreeW n b_p b_w
    hScoreP hScoreW hTestP hTestW hRootsP hPpar hWalkP hWalkW hXOnWalkP hRootWX hXW hPathInTreeW
    hPInTree hPTest hNoChildP hPathTest hEligSubLe hEligSubEnd
  letI : TieBreak V := goldilocksTieBreak
  exact walkEnd_merge_le n b_p b_w hScoreP hScoreW hTestP hTestW hPpar
    (walkEnd_of_ghost_eq_ok hRootsP hWalkP) (walkEnd_of_ghost_eq_ok hTreeW hWalkW) hXOnWalkP
    hRootWX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSubLe hEligSubEnd

/-- The landed `ghost_visited_test_true`, recovered from `walkSteps_visited_test_true` at the
Goldilocks tie-break.

Why: every walk of the spec is a chain of walk steps (`walkSteps_of_ghost_eq_ok`).

Read aloud: the landed fact that the spec's walk passes only blocks its test accepts follows from
its form over walk steps. -/
theorem ghost_visited_test_true_recovered :
    type_of% (@ghost_visited_test_true V _ _) := by
  intro A H tree score eligible b hTest hWalk
  letI : TieBreak V := goldilocksTieBreak
  exact walkSteps_visited_test_true b hTest (walkSteps_of_ghost_eq_ok hWalk)

/-- The landed `path_test_of_test_agree`, recovered from `walkSteps_path_test_of_test_agree` at
the Goldilocks tie-break.

Why: every walk of the spec is a chain of walk steps (`walkSteps_of_ghost_eq_ok`).

Read aloud: the landed fact that the second test accepts the first walk's path after `X` follows
from its form over walk steps. -/
theorem path_test_of_test_agree_recovered :
    type_of% (@path_test_of_test_agree V _ _) := by
  intro A_p X P tree_p score_p eligible_p b_p b_w hTestP hWalkP hXOnWalkP hTestAgree
  letI : TieBreak V := goldilocksTieBreak
  exact walkSteps_path_test_of_test_agree b_p b_w hTestP (walkSteps_of_ghost_eq_ok hWalkP)
    hXOnWalkP hTestAgree

end Recovered

end GoldilocksCorrectness.Proofs.Routines
