import Analysis.Vocabulary
import Analysis.Proofs.Weights
import Analysis.Proofs.Ancestry
import Analysis.Proofs.Witnessed

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

/-! ### The transition's three fields, and the branch that fired

Lemma 6 reads only three fields of the post-block state: the height, which has not moved yet; the
latest block, which is now `B`; and the latest justification, which the block phase never writes.
-/

/-- The post-block state of a transition, in those three fields. The slot phase contributes nothing
    beyond Lemma 3's record equation, which is where `PositiveWeight` comes in. -/
theorem postBlock_fields [PositiveWeight Node] {σp σ₂ : ChainState Node Root} {B : Blk Node Root}
    (hp : BlockPostState σp) (hb : processBlock (processSlots σp B.slot) B = .state σ₂) :
    σ₂.h = σp.h ∧ σ₂.L = B ∧ σ₂.J = σp.J := by
  obtain ⟨Th, -, heq⟩ := emptySlotNoop B.slot hp
  rw [actionState] at heq
  obtain ⟨h1, h2, h3⟩ := processAttestations_chainFields B.attestations
    (σ := { processSlots σp B.slot with L := B }) (processSlots σp B.slot).L
  rw [processBlock_state hb]
  exact ⟨by rw [h3, heq], by rw [h1], by rw [h2, heq]⟩

/-! ## Lemma 6 -/

/-- **Lemma 6** (`lem:height-progression`). Read aloud: if a block's transition changes the height at
    all, then it raises it by exactly one, and the block carries either a justification certificate
    or a progress certificate for the height it left.

    Four pieces meet here, and each is where the paper's two-sentence proof takes something for
    granted.

    * `processHeightEvents_advance` — the height moved, so a branch fired; it says which, and hands
      over that branch's quorum and what it justified.
    * `postBlock_fields` — the height the branch fired at is still `σp.h`. This is Lemma 3 underneath:
      the empty slots closed on the way to `B` did not move the height. `PositiveWeight` is needed
      exactly here.
    * `witnessed_of_blockPostState` — the fired branch's bits come back as attestations included on
      the chain. This is the whole of `Analysis/Proofs/Witnessed.lean`, and it is what the paper
      leaves implicit in "counted using the fixed validator weights".
    * `BlockPostState.step` — the state after the transition is itself a block post-state, which is
      the invocation clause of both certificates.

    The two tallies are `V.filter`, so `Q ⊆ V` is `Finset.filter_subset` and nothing more is needed
    for Definition 9's part of "valid inclusion". -/
theorem heightProgression [PositiveWeight Node] {σp σ : ChainState Node Root}
    (B : Blk Node Root) (hp : BlockPostState σp) (ht : stateTransition σp B = .state σ)
    (hne : σ.h ≠ σp.h) :
    σ.h = σp.h + 1 ∧
      (JustificationCertificate B σp.h σ.J ∨ ProgressCertificate B σp.h) := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state ht
  obtain ⟨hh₂, hL₂, hJ₂⟩ := postBlock_fields hp hb
  have hwit : Witnessed σ₂ :=
    ((witnessed_of_blockPostState hp).processSlots (settled_of_blockPostState hp) q_pos
      B.slot).processBlock hb
  have hne₂ : (processHeightEvents σ₂ B.slot).h ≠ σ₂.h := by rw [hh₂]; exact hne
  obtain ⟨hadv, hLeq, hbranch⟩ := processHeightEvents_advance σ₂ B.slot hne₂
  have hpost : BlockPostState (processHeightEvents σ₂ B.slot) := .step hp ht
  have hLB : (processHeightEvents σ₂ B.slot).L = B := by rw [hLeq, hL₂]
  refine ⟨by rw [hadv, hh₂], ?_⟩
  rcases hbranch with ⟨hQ, hTh, hhj⟩ | ⟨hQ, hJ⟩
  · -- the justification branch fired: its target tally is the certificate's quorum
    refine Or.inl ⟨⟨σ₂.Qtarget, Finset.filter_subset _ _, hQ, ?_⟩,
      processHeightEvents σ₂ B.slot, hpost, by rw [hLB]; exact Preceq.refl B, rfl,
      by rw [hhj, hh₂]⟩
    intro i hi
    obtain ⟨T, a, hT, hv, hpair, hinc⟩ := hwit.target i hi
    rw [hTh] at hT
    obtain rfl : T = (processHeightEvents σ₂ B.slot).J := (Option.some_injective _ hT).symm
    exact ⟨a, hv, by rw [hpair, hh₂], by rw [← hL₂]; exact hinc⟩
  · -- the progress branch fired: its progress tally is the certificate's quorum
    refine Or.inr ⟨⟨σ₂.Qprog, Finset.filter_subset _ _, hQ, ?_⟩,
      σp, processHeightEvents σ₂ B.slot, B, hp, Preceq.refl B, ht, rfl,
      by rw [hadv, hh₂], by rw [hJ, hJ₂]⟩
    intro i hi
    obtain ⟨a, hv, hht, hinc⟩ := hwit.progress_height i hi
    exact ⟨a, hv, by rw [hht, hh₂], by rw [← hL₂]; exact hinc⟩

end Proofs

end Decoupled
