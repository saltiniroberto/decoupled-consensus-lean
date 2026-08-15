import Analysis.Proofs.Witnessed
import Analysis.Proofs.Determinism

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
violations", is `targetBitCompressionEvidence` below, for E2. It is that re-export applied twice,
once per chain: the bits point and the messages prove. Its E1 half is not stated, E1's place in
that sentence not being rendered.

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

end Proofs

end Decoupled
