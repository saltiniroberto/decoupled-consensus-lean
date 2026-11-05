import LARuns.Statements.Statement4Defs
import LARuns.Bridge

/-!
# Statement 7, finalized blocks agree unless there is slashable evidence, over the runs of a protocol of `RStsVariant2`

The statement takes a protocol `Pr` of the bare framework `RStsVariant2` and reads every run
`π : Exec Pr` as observed, `τ = RStsVariant2.observe NodeViewOf.view π`: the run with each node's
local state replaced by its view (the class `NodeViewOf`), its finalized block `F`, its confirmed tip
`C` and the blocks it holds `T`. Blocks are compared through the class `BlockVocab`. No committee is
read, so the run is observed without committees.

What counts as slashable evidence between two blocks is the protocol's own: the statement takes it as
the parameter `slashableBetween`, a relation on blocks that each claim supplies.

The conditions on `τ` are the extra conditions a claim assumes, and that no two blocks held by
honest nodes, in any configurations, have slashable evidence between them. The conclusion: the
finalized blocks of any two nodes, each honest in some configuration, are compatible, or two
different blocks held by the two nodes there carry one root.

This page imports `LARuns.Statements.Statement4Defs` (the class `BlockVocab`) and `LARuns.Bridge`.
-/

set_option autoImplicit false

namespace LARuns

open RStsVariant2 (Exec Protocol ObservedRun HonestG)
open RStsVariant2.Observable

/-! ## The statement -/

/-- Top statement 7 over the runs of a protocol of `RStsVariant2`, finalized blocks agree unless
there is slashable evidence: for every run `π` of the protocol `Pr` whose observed run `τ` meets each
extra condition in `extraConditions`, and in which no two blocks held by honest nodes are
`slashableBetween`, the finalized blocks of the views of any two nodes, each honest in a
configuration of `τ`, are compatible (`BlockVocab.Compatible`), or two different blocks among those
the two views hold carry one root (`BlockVocab.sameRoot`).

Read aloud: for every run of the protocol, seen through its nodes' views, that meets the extra
conditions, with no slashable evidence between the blocks honest nodes hold, no two honest nodes
finalize conflicting blocks, unless a root collision hits the blocks they hold.

Variables: the instance of `BlockVocab` on `Block`, the ancestry and the roots of blocks; `Pr`, the
protocol; the instance of `NodeViewOf` on its node states, a node state's view; `extraConditions`,
the conditions on the observed runs a claim assumes (`∅` for none); `slashableBetween`, the
protocol's slashable evidence between two blocks.

Kind: part of the statements. -/
def FinalizedCompatibleUnlessSlashableOnRuns {Node Msg NodeState Ev Block : Type}
    [DecidableEq Node] [DecidableEq Msg]
    -- the ancestry and the roots of blocks (read by the conclusion)
    [BlockVocab Block]
    -- the protocol of `RStsVariant2`
    (Pr : Protocol Node Msg NodeState Ev)
    -- a node state read as a view: its finalized block, its confirmed tip and the blocks it holds
    [NodeViewOf NodeState Block]
    -- the extra conditions on the observed runs that the claim assumes, `∅` for none
    (extraConditions : Set (ObservedRun Node Msg Ev (NodeView Block) → Prop))
    -- `slashableBetween B B'`: the chains ending at `B` and `B'` carry evidence that the protocol
    -- counts as slashable
    (slashableBetween : (B : Block) → (B' : Block) → Prop) : Prop :=
  -- every run `π` of the protocol
  ∀ π : Exec Pr,
    -- `τ`, the run `π` as observed: the run with each node's local state replaced by its view
    let τ : ObservedRun Node Msg Ev (NodeView Block) := RStsVariant2.observe NodeViewOf.view π
    -- `τ` meets each extra condition the claim assumes (none when `extraConditions` is `∅`)
    (∀ condition ∈ extraConditions, condition τ) →
    -- no two blocks held by honest nodes, in any configurations of `τ`, are slashable between them:
    (∀ (v₁ v₂ : Node) (i j : ℕ) (l₁ l₂ : NodeView Block),
      -- `l₁` is `v₁`'s view in configuration `i`
      state τ i v₁ = some l₁ →
      -- `v₁` is honest in configuration `i`
      HonestG τ i v₁ →
      -- `l₂` is `v₂`'s view in configuration `j`
      state τ j v₂ = some l₂ →
      -- `v₂` is honest in configuration `j`
      HonestG τ j v₂ →
      -- no block `B₁` that `l₁` holds and block `B₂` that `l₂` holds are slashable between them
      ∀ B₁ ∈ l₁.T, ∀ B₂ ∈ l₂.T, ¬ slashableBetween B₁ B₂) →
    -- for every two nodes `v₁`, `v₂`, configurations `i`, `j` of `τ`, and their views `l₁`, `l₂`
    -- there
    ∀ (v₁ v₂ : Node) (i j : ℕ) (l₁ l₂ : NodeView Block),
      -- `l₁` is `v₁`'s view in configuration `i`
      state τ i v₁ = some l₁ →
      -- `v₁` is honest in configuration `i`
      HonestG τ i v₁ →
      -- `l₂` is `v₂`'s view in configuration `j`
      state τ j v₂ = some l₂ →
      -- `v₂` is honest in configuration `j`
      HonestG τ j v₂ →
      -- either the finalized block of `l₁` is the finalized block of `l₂`, an ancestor of it, or a
      -- descendant of it
      BlockVocab.Compatible l₁.F l₂.F ∨
      -- or two different blocks, each held by `l₁` or by `l₂`, carry one root
      ∃ B B' : Block,
        (B ∈ l₁.T ∨ B ∈ l₂.T) ∧
        (B' ∈ l₁.T ∨ B' ∈ l₂.T) ∧
        BlockVocab.sameRoot B B' ∧
        B ≠ B'

#check @FinalizedCompatibleUnlessSlashableOnRuns

end LARuns
