import Analysis.Vocabulary

/-!
# Proofs: finalized blocks form a chain, and conflicting finalization pays (Lemmas 11, Theorem 5)

Theorem 5 (`thm:accountable-safety`) is Lemma 11 (`lem:finalized-chain`) plus a case split: order
the two finalized heights with `Nat.le_total`, and in each branch the lemma's first disjunct is
one arm of `Compatible`, which `Conflicts` refuses — so the evidence disjunct is all that is
left. The paper's proof carries its two cases (equal heights, different heights) directly; here
both live inside Lemma 11, whose own statement splits the same way.

**Lemma 11's proof is the outstanding `sorry` in this file.** What it is missing:

* the equal-heights case is a quorum intersection between `C`'s finality quorum and `C'`'s
  justification quorum — and the statements' finalization hypotheses are *recorded pairs*, not
  certificates, so both quorums must first be recovered from the state: a provenance invariant
  for `P` and for `(J, h_j)` in the shape of `Witnessed`, which today covers the target and
  progress bits only;
* the different-heights case is Lemma 10 (`lem:past-finalized`), itself outstanding, plus
  Lemma 7's post-state anchor and height monotonicity along the chain
  (`postState_h_le`, `Analysis/Proofs/ChainTarget.lean`).
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- Lemma 11's content; `lemFinalizedChain` in `Analysis/Lemmas.lean` is the statement of
    record and is this, verbatim. The proof is outstanding — the module docstring says what it
    is missing. -/
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
  sorry

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
