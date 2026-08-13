import Analysis.Proofs.SlotClosure

/-!
# Ancestry and the height inequalities

Lemma 4 (`lem:finalized-before-justified`, `height_filter_healing.tex:920-931`): the finalized
block precedes the justified block, which precedes the latest block, and the finalized height is
at most the justified height, which is below the state height.

The paper's own proof (lines 933–943) calls these "ancestry and height inequalities", which is
what names this file.

**The proof is outstanding** — a `sorry`, and the only one in the project. What it needs is below,
at the theorem.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- **Lemma 4** over a block post-state. Read aloud: the finalized block is the justified block or
    an ancestor of it, the justified block is the latest block or an ancestor of it, and the
    finalized height is at most the justified height, which is below the state height.

    **Outstanding.** A `sorry`. The shape is another induction over `BlockPostState`, and genesis
    is immediate: `F = J = L = genesis` makes both `⪯` reflexive, and `h_F = h_j = 0 < 1 = h`.

    What the step needs, and does not have. The target branch of `process_height_events` sets
    `J ← T_h` and then increments `h`, so preserving `F ⪯ J ⪯ L` there needs two facts about the
    named target that this statement does not mention:

        σ.T_h = some T → σ.J ⪯ T ∧ T ⪯ σ.L

    The paper asserts exactly that, in prose, inside its own proof: "the justification branch sets
    `J = T_h`, which lies on the current chain and already contains the previous `J`"
    (lines 939–940). It is a further invariant, and the argument for it has to come from the two
    writers of `T_h` — `process_slot`, which writes `some σ.L`, and `advance_height`, which writes
    `⊥`. So this lemma will be proved from a strengthened invariant in the same style as `Settled`,
    not from the four conjuncts alone.

    Also missing, and cheaper: `process_block` replaces `L` by the block, so the `J ⪯ L` conjunct
    needs the block's `parent = σ.L` check — which `state_transition` has already made, and
    `processBlock_state` is where that becomes usable. -/
theorem finalizedBeforeJustified {σ : ChainState Node Root} (h : BlockPostState σ) :
    σ.F ⪯ σ.J ∧ σ.J ⪯ σ.L ∧ σ.h_F ≤ σ.h_j ∧ σ.h_j < σ.h := by
  sorry

end Proofs

end Decoupled
