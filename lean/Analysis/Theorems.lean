import Analysis.Proofs.Finality

/-!
# The paper's numbered theorems

*Height Filtering and Healing for a Simplex-Style Finality Variant*
(`height_filter_healing.tex`). Statements of record, one per numbered theorem, against the
specification in `Spec` — the file `Analysis/Lemmas.lean` is for the numbered lemmas, and its
rules apply here unchanged: statements only, proofs as one-line calls into `Analysis/Proofs/`,
no section-level `variable`, and each docstring carries the paper's sentence verbatim.

**Present so far: Theorem 5** (`thm:accountable-safety`), derived from Lemma 11, which is
proved; both are proved outright the moment Lemma 10 is.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

/-- **Theorem 5** (`thm:accountable-safety`, lines 1166–1172): conflicting finalization exposes
    slashable weight.

    > Conflicting blocks cannot both finalize unless, for some height `h`, at least `2q − W`
    > weight is provably E1- or E2-slashable.

    Read aloud: if two conflicting blocks are both finalized, there is a set of validators of
    weight at least `2q − W`, each of which signed a slashable pair of messages retained on the
    two chains.

    Noun by noun. "Both finalize" is one recorded pair per chain: `B_F` replays to a state with
    `(F, h_F) = (C, h)` and `B_F'` to one with `(C', h')` — the state fact rather than Definition
    21's certificate, for the reason `lemPastFinalized` gives; "conflicting" is Definition 5's
    `Conflicts`. "Cannot … unless" is rendered
    as the paper's "unless" made the conclusion, as in Lemma 5: both certificates in hand, the
    slashable set exists. "Provably E1- or E2-slashable" is the pair `x, y` with
    `E1 x y ∨ E2 x y`, each message retained — included — on one of the two chains, in either
    order, since which chain carries the finality commitment depends on which height is lower.
    "For some height `h`": the height lives inside E1 and E2's own pairs and is not separately
    quantified.

    Proved in `Analysis/Proofs/Finality.lean` **from Lemma 11**: order the heights, apply the
    lemma in that order, and refuse its ancestry disjunct with the conflict. Lemma 11 is proved;
    its different-heights case rests on Lemma 10, that file's one remaining `sorry`, so this is
    not proved in the kernel's sense until Lemma 10 is. -/
theorem thmAccountableSafety {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] [PositiveWeight Node] {B_F B_F' C C' : Blk Node Root}
    {h h' : Nat} (hBF : postState B_F ≠ invalid)
    (hC : (postState' B_F).F = C) (hhF : (postState' B_F).h_F = h)
    (hBF' : postState B_F' ≠ invalid)
    (hC' : (postState' B_F').F = C') (hhF' : (postState' B_F').h_F = h')
    (hconf : Conflicts C C') :
    ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
      ∀ i ∈ S, ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
        ((IncludedOn x B_F ∧ IncludedOn y B_F') ∨ (IncludedOn x B_F' ∧ IncludedOn y B_F)) ∧
        (E1 x y ∨ E2 x y) :=
  Proofs.accountableSafety hBF hC hhF hBF' hC' hhF' hconf

end Decoupled
