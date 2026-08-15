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
    obtain ⟨a, h1, h2, h3⟩ := hw.progress i hi
    exact ⟨a, h1, h2, hL ▸ h3⟩

end Proofs

end Decoupled
