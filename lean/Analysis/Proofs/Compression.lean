import Analysis.Proofs.Witnessed
import Analysis.Proofs.Determinism
import Analysis.Proofs.Provenance

/-!
# Proofs: the two tallies' provenance (Lemma 9)

Lemma 9 (`lem:target-bit-compression`) says the two participation arrays carry everything the
justification and progress rules need. In this rendering that claim splits in two, and only one
half is a theorem:

* that the height-event check reads the state only through `Q_target` and `Q_prog` is visible in
  `processHeightEvents`'s own text — its conditions are `w(Q_target) ≥ q` and `w(Q_prog) ≥ q` —
  so it is a fact about the definition, not a statement in the model;
* that the compression **loses nothing** is `Witnessed`, the third invariant: behind each set bit
  sits an included vote whose content is exactly what the rule would otherwise need.

So the proof here is a re-export of `Witnessed` over `postState`, with the endpoint moved from
`σ.L` to the block by `postState_L`.

The lemma's **second** sentence, "retaining the signed messages is sufficient to prove E1 and E2
violations", is the two `…Evidence` theorems below, one per condition. Both have the same shape —
the state's own bits point at a validator, and the messages those bits stand for are what prove
the violation — and they differ only in which bit points and which invariant carries it back:

* E2: two target bits, `Witnessed.target` on each chain;
* E1: a finality-tally bit on one chain and a height bit on the other, `Certified.commits` for
  the first and `Witnessed` for the second.

**The E1 half reaches outside the sentence's own two arrays**, and that is not a slip. Lemma 9's
first sentence is about `target_participation` and `progress`; a commit has no bit in either, and
what the state retains of one is membership of Definition 13's `P` together with `(J, h_j)`. So
the E1 half is stated over `P`, and it is the finality-side analogue of the E2 half rather than a
second reading of the same two arrays.

**The E1 half concludes a disjunction where the E2 half takes a hypothesis.** For E2 the two
states hold everything needed to see the conflict: two stored targets that differ. For E1 they do
not — a counted progress bit has forgotten which target its vote named, which is Lemma 9's own
point — so the second chain may turn out to agree rather than conflict, and "the committed block
is on that chain" is the disjunct that says so.

**The paper's proof cites Lemma 8; this one does not need it.** The paper reaches "every vote
counted toward justification names `T_h`" through Lemma 8's transfer argument. In this rendering
the target test (Figure 2, line 778) compares the vote's target with `T_h` directly, so the
naming is `Witnessed.target` with no chain comparison anywhere.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- The two tallies' provenance, over a block's own replay: every counted target bit is backed
    by an included vote naming the stored target at the current height, and every counted
    progress bit by an included vote at the current height. -/
theorem targetBitCompression [PositiveWeight Node] {B : Blk Node Root}
    {σ : ChainState Node Root} (hB : postState B = .state σ) :
    (∀ i ∈ σ.Qtarget, ∃ T, σ.T_h = some T ∧ ∃ a, a.validator = i ∧
        a.heightPair = .target σ.h T ∧ IncludedOn a B) ∧
    ∀ i ∈ σ.Qprog, ∃ a : Attestation Node Root,
        a.validator = i ∧ a.height = some σ.h ∧ IncludedOn a B := by
  have hw := witnessed_of_blockPostState (blockPostState_of_postState B hB)
  have hL : σ.L = B := postState_L B hB
  constructor
  · intro i hi
    obtain ⟨T, a, h1, h2, h3, h4⟩ := hw.target i hi
    exact ⟨T, h1, a, h2, h3, hL ▸ h4⟩
  · intro i hi
    obtain ⟨a, h1, h2, h3⟩ := hw.progress_height i hi
    exact ⟨a, h1, h2, hL ▸ h3⟩

/-- The second sentence's E2 half: one validator's target bit counted on two chains at one height
    naming different targets produces the pair that proves the violation.

    Nothing beyond `targetBitCompression` is needed. Each bit hands back an included attestation
    whose height pair is that chain's own height and stored target; the two heights agree by
    hypothesis and the two targets differ, which is E2 read off the two pairs. The participation
    state contributes only the two bits — the messages are what prove the violation, which is the
    sentence's own point. -/
theorem targetBitCompressionEvidence [PositiveWeight Node] {B B' T T' : Blk Node Root}
    {σ σ' : ChainState Node Root} {i : Node}
    (hB : postState B = .state σ) (hB' : postState B' = .state σ')
    (hi : i ∈ σ.Qtarget) (hi' : i ∈ σ'.Qtarget)
    (hheight : σ.h = σ'.h) (hT : σ.T_h = some T) (hT' : σ'.T_h = some T') (hne : T ≠ T') :
    ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
      IncludedOn x B ∧ IncludedOn y B' ∧ E2 x y := by
  obtain ⟨T0, hT0, x, hx1, hx2, hx3⟩ := (targetBitCompression hB).1 i hi
  obtain ⟨T1, hT1, y, hy1, hy2, hy3⟩ := (targetBitCompression hB').1 i hi'
  rw [hT, Option.some.injEq] at hT0
  rw [hT', Option.some.injEq] at hT1
  subst hT0; subst hT1
  refine ⟨x, y, hx1, hy1, hx3, hy3, σ.h, T, T', hx2, ?_, hne⟩
  rw [hheight]; exact hy2

/-- The second sentence's E1 half: a validator counted in one chain's finality tally and in
    either tally of another chain at that commitment's height has either committed to a block
    that other chain contains, or signed the pair that proves E1.

    `Certified.commits` turns the finality-tally bit into an included commit to `(h_j, J)`;
    `Witnessed` turns the other chain's bit into an included vote at that chain's height, and
    both of its arms land in E1 — a timeout is E1's second constructor outright, and a target is
    E1's first once the target differs from `J`. What makes it differ is exactly the disjunction:
    every block the other chain's bits can vouch for is on that chain, so a target equal to `J`
    puts `J` there and lands in the left disjunct instead. -/
theorem targetBitCompressionEvidenceE1 [PositiveWeight Node] {B B' : Blk Node Root}
    {σ σ' : ChainState Node Root} {i : Node}
    (hB : postState B = .state σ) (hB' : postState B' = .state σ')
    (hi : i ∈ σ.P) (hi' : i ∈ σ'.Qtarget ∨ i ∈ σ'.Qprog)
    (hheight : σ.h_j = σ'.h) :
    σ.J ⪯ B' ∨ ∃ x y : Attestation Node Root, x.validator = i ∧ y.validator = i ∧
      IncludedOn x B ∧ IncludedOn y B' ∧ E1 x y := by
  have hbp := blockPostState_of_postState B hB
  have hbp' := blockPostState_of_postState B' hB'
  have hL : σ.L = B := postState_L B hB
  have hL' : σ'.L = B' := postState_L B' hB'
  obtain ⟨x, hx1, hx2, hx3⟩ := (certified_of_blockPostState hbp).commits i hi
  by_cases hJ : σ.J ⪯ B'
  · exact Or.inl hJ
  refine Or.inr ?_
  rcases hi' with hi' | hi'
  · obtain ⟨T0, y, hT0, hy1, hy2, hy3⟩ := (witnessed_of_blockPostState hbp').target i hi'
    have hT0B' : T0 ⪯ B' := by
      have h := (fresh_of_blockPostState hbp').onChain T0 hT0
      rwa [hL'] at h
    exact ⟨x, y, hx1, hy1, hL ▸ hx3, hL' ▸ hy3, σ.h_j, σ.J, hx2,
      Or.inl ⟨T0, by rw [hheight]; exact hy2, fun he => hJ (he ▸ hT0B')⟩⟩
  · obtain ⟨y, hy1, hy2, hy3⟩ := (witnessed_of_blockPostState hbp').progress i hi'
    refine ⟨x, y, hx1, hy1, hL ▸ hx3, hL' ▸ hy2, σ.h_j, σ.J, hx2, ?_⟩
    rcases hy3 with harm | ⟨T, harm, hTL⟩
    · exact Or.inr (by rw [hheight]; exact harm)
    · refine Or.inl ⟨T, by rw [hheight]; exact harm, fun he => hJ ?_⟩
      rw [← he]; rwa [hL'] at hTL

end Proofs

end Decoupled
