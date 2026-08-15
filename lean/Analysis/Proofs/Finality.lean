import Analysis.Proofs.Provenance
import Analysis.Proofs.ChainTarget

/-!
# Proofs: finalized blocks form a chain, and conflicting finalization pays (Lemmas 10, 11, Theorem 5)

Three results, one dependency line:

* **Lemma 10** (`lem:past-finalized`) is this file's outstanding `sorry` — the intersection of a
  finality quorum with the first quorum that advanced a chain past the finalized height. Its
  quorums are in hand (`Certified`, `Analysis/Proofs/Provenance.lean`); what is missing is the
  walk to the *first* advance past `h` and the E1 analysis at the intersection.
* **Lemma 11** (`lem:finalized-chain`) is proved. `h = 0` is genesis by `Certified.fin0` and
  `genesis_preceq`. Equal heights intersect `C`'s commit quorum with `C'`'s target quorum — both
  recovered from the recorded pairs by `Certified.fin` — and every intersection signer is
  E1-slashable unless `C = C'`. Different heights go through Lemma 10: either its evidence, or
  `C` is on `C'`'s own chain, and then the two anchors (`Certified.fin`'s third conjunct), the
  comparability of two ancestors (`preceq_or_preceq`) and height monotonicity
  (`postState_h_le`) order `C` below `C'`.
* **Theorem 5** (`thm:accountable-safety`) is Lemma 11 plus a case split: order the two heights
  with `Nat.le_total`, and in each branch the lemma's first disjunct is one arm of `Compatible`,
  which `Conflicts` refuses — so the evidence disjunct is all that is left.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- Lemma 10's content; `lemPastFinalized` in `Analysis/Lemmas.lean` is the statement of
    record and is this, verbatim. The proof is outstanding — the module docstring says what it
    is missing. -/
theorem pastFinalized [PositiveWeight Node] {B_F C B : Blk Node Root} {h : Nat}
    (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    (hB : postState B ≠ invalid) (t : Time) :
    (h < (postState' B).h → C ⪯ B ∨
      (1 ≤ h ∧ ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          IncludedOn x B_F ∧ IncludedOn y B ∧ E1 x y)) ∧
    (h < (actionState (postState' B) t).h → C ⪯ B ∨
      (1 ≤ h ∧ ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          IncludedOn x B_F ∧ IncludedOn y B ∧ E1 x y)) := by
  sorry

/-- Lemma 11's content; `lemFinalizedChain` in `Analysis/Lemmas.lean` is the statement of
    record and is this, verbatim. The module docstring gives the three cases. -/
theorem finalizedChain [PositiveWeight Node] {B_F B_F' C C' : Blk Node Root} {h h' : Nat}
    (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    (hBF' : postState B_F' ≠ invalid)
    (hC' : (postState' B_F').F = C') (hhF' : (postState' B_F').h_F = h')
    (hle : h ≤ h') :
    C ⪯ C' ∨
      ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
        ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
          IncludedOn x B_F ∧ IncludedOn y B_F' ∧ (E1 x y ∨ E2 x y) := by
  have hσeq := TransitionResult.state_get _ hBF
  have hσeq' := TransitionResult.state_get _ hBF'
  have hbp : BlockPostState (postState' B_F) := blockPostState_of_postState B_F hσeq
  have hbp' : BlockPostState (postState' B_F') := blockPostState_of_postState B_F' hσeq'
  have hcert := certified_of_blockPostState hbp
  have hcert' := certified_of_blockPostState hbp'
  have hL : (postState' B_F).L = B_F := postState_L B_F hσeq
  have hL' : (postState' B_F').L = B_F' := postState_L B_F' hσeq'
  by_cases h0 : h = 0
  · -- height 0 is genesis, an ancestor of everything
    left
    have hFg : (postState' B_F).F = .genesis := hcert.fin0 (by rw [hhF, h0])
    rw [← hC, hFg]
    exact genesis_preceq C'
  · have h1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · -- equal heights: C's commit quorum against C''s target quorum
      by_cases hCC : C = C'
      · exact Or.inl (hCC ▸ Preceq.refl C)
      · obtain ⟨⟨Qc, hQcV, hQcw, hQca⟩, -, -⟩ := hcert.fin (by rw [hhF]; exact h1)
        obtain ⟨-, ⟨Qt, hQtV, hQtw, hQta⟩, -⟩ := hcert'.fin (by rw [hhF']; omega)
        right
        refine ⟨Qc ∩ Qt, quorumIntersection hQcV hQtV hQcw hQtw, fun i hi => ?_⟩
        obtain ⟨x, hxv, hxp, hxi⟩ := hQca i (Finset.mem_inter.1 hi).1
        obtain ⟨y, hyv, hyp, hyi⟩ := hQta i (Finset.mem_inter.1 hi).2
        refine ⟨x, y, hxv, hyv, by rwa [hL] at hxi, by rwa [hL'] at hyi, Or.inl ?_⟩
        rw [hhF, hC] at hxp
        rw [hhF', hC', ← heq] at hyp
        exact ⟨h, C, hxp, Or.inl ⟨C', hyp, fun he => hCC he.symm⟩⟩
    · -- different heights: through Lemma 10
      have hch' := chained_of_blockPostState hbp'
      have hadv : h < (postState' B_F').h := by
        have g1 := hch'.hF_le_hj
        have g2 := hch'.hj_lt_h
        rw [hhF'] at g1
        omega
      rcases (pastFinalized hBF hC hhF hBF' 0).1 hadv with hCB | ⟨-, S, hw, hev⟩
      · -- C is on C''s own chain: order the two by their post-state heights
        have hC'B : C' ⪯ B_F' := by
          have hj := Preceq.trans hch'.finJust hch'.justLatest
          rwa [hC', hL'] at hj
        obtain ⟨-, -, hanc⟩ := hcert.fin (by rw [hhF]; exact h1)
        obtain ⟨-, -, hanc'⟩ := hcert'.fin (by rw [hhF']; omega)
        rw [hC, hhF] at hanc
        rw [hC', hhF'] at hanc'
        obtain ⟨σC, hpC, hhC⟩ := TransitionResult.map_eq_some hanc
        obtain ⟨σC', hpC', hhC'⟩ := TransitionResult.map_eq_some hanc'
        rcases preceq_or_preceq B_F' hCB hC'B with hcc | hcc
        · exact Or.inl hcc
        · -- C' ⪯ C would put h' at or below h
          have := postState_h_le C hcc hpC' hpC
          omega
      · right
        refine ⟨S, hw, fun i hi => ?_⟩
        obtain ⟨x, y, hxv, hyv, hxi, hyi, he⟩ := hev i hi
        exact ⟨x, y, hxv, hyv, hxi, hyi, Or.inl he⟩

/-- Theorem 5's content: order the heights, apply `finalizedChain` in that order, and refuse its
    first disjunct with the conflict — `Conflicts` is `¬ (C ⪯ C' ∨ C' ⪯ C)`, and each branch's
    ancestry lands in one arm. The evidence's inclusions come out in the order the lemma was
    applied, which is the theorem's either-order disjunction. -/
theorem accountableSafety [PositiveWeight Node] {B_F B_F' C C' : Blk Node Root} {h h' : Nat}
    (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    (hBF' : postState B_F' ≠ invalid)
    (hC' : (postState' B_F').F = C') (hhF' : (postState' B_F').h_F = h')
    (hconf : Conflicts C C') :
    ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
      ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
        ((IncludedOn x B_F ∧ IncludedOn y B_F') ∨ (IncludedOn x B_F' ∧ IncludedOn y B_F)) ∧
        (E1 x y ∨ E2 x y) := by
  rcases Nat.le_total h h' with hle | hle
  · rcases finalizedChain hBF hC hhF hBF' hC' hhF' hle with hpre | ⟨S, hw, hev⟩
    · exact absurd (Or.inl hpre) hconf
    · refine ⟨S, hw, fun i hi => ?_⟩
      obtain ⟨x, y, hx, hy, hix, hiy, he⟩ := hev i hi
      exact ⟨x, y, hx, hy, Or.inl ⟨hix, hiy⟩, he⟩
  · rcases finalizedChain hBF' hC' hhF' hBF hC hhF hle with hpre | ⟨S, hw, hev⟩
    · exact absurd (Or.inr hpre) hconf
    · refine ⟨S, hw, fun i hi => ?_⟩
      obtain ⟨x, y, hx, hy, hix, hiy, he⟩ := hev i hi
      exact ⟨x, y, hx, hy, Or.inr ⟨hix, hiy⟩, he⟩

end Proofs

end Decoupled
