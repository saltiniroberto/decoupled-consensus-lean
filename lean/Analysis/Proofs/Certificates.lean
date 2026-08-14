import Analysis.Vocabulary
import Analysis.Proofs.Weights
import Analysis.Proofs.Ancestry

/-!
# Certificates against each other

What two certificates at one height force, which is Lemma 5 (`lem:target-uniqueness`,
`height_filter_healing.tex:967-973`) and, when the rest of Definition 21 lands, the lemmas that
follow it.

Lemma 5's proof reads only the **quorum** clause of each certificate. The height-event invocation
clause is not touched, so the lemma says nothing about it and cannot be cited for it.
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

    The argument is the paper's own two sentences. The two signer sets intersect in weight at least
    `2q - W`, which is Lemma 2 as `quorumIntersection`, so the witness set is `Q ∩ Q'`. Every
    validator in the intersection has an attestation from each certificate, and the two make E2:
    same height, both targets exact, and the targets differ.

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
  obtain ⟨⟨Q, hQV, hQq, hQa⟩, -⟩ := hJC
  obtain ⟨⟨Q', hQ'V, hQ'q, hQ'a⟩, -⟩ := hJC'
  have hTT' : T ≠ T' := fun he => hconf (Or.inl (he ▸ Preceq.refl T))
  refine ⟨Q ∩ Q', quorumIntersection hQV hQ'V hQq hQ'q, ?_⟩
  intro i hi
  obtain ⟨hiQ, hiQ'⟩ := Finset.mem_inter.mp hi
  obtain ⟨x, hxv, hxh, hxinc⟩ := hQa i hiQ
  obtain ⟨y, hyv, hyh, hyinc⟩ := hQ'a i hiQ'
  exact ⟨x, y, hxv, hyv, hxinc, hyinc, h, T, T', hxh, hyh, hTT'⟩

end Proofs

end Decoupled
