import LARuns.Statements.Statement4Defs

/-!
# The conclusion of statement 1, finality safety after healing, read on the observed run

`FinalizedCompatibleBy`, the conclusion of statement 1 (`LARuns.FinalizedCompatibleAfterHealingOnRuns`)
besides the root-collision disjunct `RootCollisionBy`: the finalized blocks of any two nodes, each
honest in a configuration entered by a time, are compatible. Read on `τ`, an execution of any type
with an `RStsVariant2.Observable` whose nodes' states are read as views (`NodeViewOf`), through
`HonestStateBy` and `BlockVocab.Compatible`.

This page imports `LARuns.Statements.Statement4Defs`.
-/

set_option autoImplicit false

namespace LARuns

section Conclusions

variable {X Node Msg Ev Block L : Type} [DecidableEq Node] [DecidableEq Msg]
  [RStsVariant2.Observable X Node Msg L Ev] [NodeViewOf L Block]

/-- `FinalizedCompatibleBy τ tBy`: for every two nodes `v₁`, `v₂`, each honest in a configuration
of `τ` entered at or before `tBy` (`HonestStateBy`), the finalized blocks of their views there are
compatible (`BlockVocab.Compatible`): one is the other or an ancestor of it.

Read aloud: by `tBy`, no two honest nodes have finalized conflicting blocks.

Kind: part of the statements. -/
def FinalizedCompatibleBy [BlockVocab Block] (τ : X) (tBy : ℝ) : Prop :=
  -- for every two nodes `v₁`, `v₂`, configurations `i`, `j` of `τ`, and their states `l₁`, `l₂`
  -- there
  ∀ (v₁ v₂ : Node) (i j : ℕ) (l₁ l₂ : L),
    -- `v₁` is honest in configuration `i`, entered by `tBy`, and its state is `l₁`
    HonestStateBy τ tBy i v₁ l₁ →
    -- `v₂` is honest in configuration `j`, entered by `tBy`, and its state is `l₂`
    HonestStateBy τ tBy j v₂ l₂ →
    -- the finalized block of `v₁`'s view is the finalized block of `v₂`'s view, an ancestor of
    -- it, or a descendant of it
    BlockVocab.Compatible (NodeViewOf.view l₁).F (NodeViewOf.view l₂).F

end Conclusions

end LARuns
