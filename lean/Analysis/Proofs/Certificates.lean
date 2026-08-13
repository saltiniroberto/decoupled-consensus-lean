import Analysis.Vocabulary
import Analysis.Proofs.Weights
import Analysis.Proofs.Ancestry

/-!
# Certificates against each other

What two certificates at one height force, which is Lemma 5 (`lem:target-uniqueness`,
`height_filter_healing.tex:967-973`) and, when the rest of Definition 21 lands, the lemmas that
follow it.

**The proof is outstanding** — a `sorry`, and the project's only one. What it needs is below, at
the theorem.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- **Lemma 5** (`lem:target-uniqueness`). Read aloud: if two conflicting blocks each have a
    justification certificate at the same height, then some set of validators of weight at least
    `2q - W` each signed both of those targets at that height, which is E2.

    **Outstanding.** A `sorry`. Nothing is missing from the specification: the argument is the
    paper's own two sentences, and both ingredients exist.

    * The two signer sets intersect in weight at least `2q - W` — that is Lemma 2, already proved
      as `quorumIntersection`, and the witness set is `Q ∩ Q'`.
    * Every validator in the intersection has an attestation from each certificate, and the two
      make E2: same height, both targets exact, and the targets differ.

    Only the **first** clause of each certificate is used. The height-event invocation clause is
    not read, so the theorem holds of the quorum halves alone — worth knowing, because it means this
    lemma says nothing about the invocation and cannot be cited for it.

    Conflict is used only through distinctness: E2 asks for `T ≠ T'`, and conflicting blocks are
    distinct because `⪯` is reflexive, so equal blocks are compatible. The converse fails, which
    makes the distinctness form strictly stronger than the paper's sentence. It is not stated
    separately until something needs it. -/
theorem targetUniqueness (B B' T T' : Blk Node Root) (h : Nat)
    (hJC : JustificationCertificate B h T) (hJC' : JustificationCertificate B' h T')
    (hconf : Conflicts T T') :
    ∃ S : Finset Node, w(S) ≥ 2 * q Node - W Node ∧
      ∀ i ∈ S, ∃ x y : Attestation Node Root,
        x.validator = i ∧ y.validator = i ∧ IncludedOn x B ∧ IncludedOn y B' ∧ E2 x y := by
  sorry

end Proofs

end Decoupled
