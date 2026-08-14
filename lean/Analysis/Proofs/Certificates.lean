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

Lemma 6 (`lem:height-progression`, lines 987–994) is the other direction — a height transition
*produces* a certificate — and its proof is outstanding. What it needs is at the theorem.
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

/-- **Lemma 6** (`lem:height-progression`). Read aloud: if a block's transition changes the height at
    all, then it raises it by exactly one, and the block carries either a justification certificate
    or a progress certificate for the height it left.

    **Outstanding.** A `sorry`. Both halves need work, and neither needs anything absent from the
    specification.

    *The increment.* `advance_height` raises `h` by one, and it is the only writer of `h`
    (`advanceHeight_h`, not yet stated). What makes the total increment exactly one rather than one
    per closed slot is Lemma 3: from a block post-state the empty-slot height checks do not fire, so
    the only height event in the transition is the block's own. That is where `PositiveWeight` is
    needed — with `q = 0` every empty slot advances the height, and a block after two empty slots
    would raise it by more than one.

    *The certificate.* Whichever branch fired supplies the quorum clause, and it has to be dug out of
    Figure 2: the target branch fires on `w(Qtarget) ≥ q`, and every bit in `Qtarget` was set by
    `process_attestation` from an attestation whose height pair is exactly `(h, T_h)` — line 778 is
    the only writer. The first attempt calls that step `advance_quorum`; nothing here does it yet.
    The invocation clause is `σ` itself, which is a block post-state with `σ.L = B`.

    The paper's own proof is two sentences, "the justification and progress rules are the only rules
    that advance height. Both increment it by one, and both use the weights required by
    Assumption 1" — so the work here is in what those sentences take for granted. -/
theorem heightProgression [PositiveWeight Node] {σp σ : ChainState Node Root}
    (B : Blk Node Root) (hp : BlockPostState σp) (ht : stateTransition σp B = .state σ)
    (hne : σ.h ≠ σp.h) :
    σ.h = σp.h + 1 ∧
      (JustificationCertificate B σp.h σ.J ∨ ProgressCertificate B σp.h) := by
  sorry

end Proofs

end Decoupled
