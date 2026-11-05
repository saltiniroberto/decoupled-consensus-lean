import LARuns.Statements.Statement4Defs
import LARuns.Bridge

/-!
# Statement 6, the finalized block only extends, over the runs of a protocol of `RStsVariant2`

The statement takes a protocol `Pr` of the bare framework `RStsVariant2` and reads every run
`π : Exec Pr` as observed, `τ = RStsVariant2.observe NodeViewOf.view π`: the run with each node's
local state replaced by its view (the class `NodeViewOf`), its finalized block `F`, its confirmed tip
`C` and the blocks it holds `T`. Blocks are compared through the class `BlockVocab`. No committee is
read, so the run is observed without committees.

The only conditions on `τ` are the extra conditions a claim assumes. The conclusion: for two
configurations `i ≤ j` of `τ` and a node honest in configuration `j`, the finalized block of its view
in configuration `i` is the finalized block of its view in configuration `j` or an ancestor of it.
The node may crash and restart between the two configurations. A node corrupted in a configuration
stays corrupted, so it is honest in configuration `i` too.

This page imports `LARuns.Statements.Statement4Defs` (the class `BlockVocab`) and `LARuns.Bridge`.
-/

set_option autoImplicit false

namespace LARuns

open RStsVariant2 (Exec Protocol ObservedRun HonestG)
open RStsVariant2.Observable

/-! ## The statement -/

/-- Top statement 6 over the runs of a protocol of `RStsVariant2`, the finalized block only extends:
for every run `π` of the protocol `Pr` whose observed run `τ` meets each extra condition in
`extraConditions`, for two configurations `i ≤ j` of `τ` and a node honest in configuration `j`, the
finalized block of the node's view in configuration `i` is the finalized block of its view in
configuration `j` or an ancestor of it (`BlockVocab.anc`).

Read aloud: for every run of the protocol, seen through its nodes' views, that meets the extra
conditions, an honest node never abandons a block it has finalized.

Variables: the instance of `BlockVocab` on `Block`, the ancestry of blocks; `Pr`, the protocol; the
instance of `NodeViewOf` on its node states, a node state's view; `extraConditions`, the conditions
on the observed runs a claim assumes (`∅` for none).

Kind: part of the statements. -/
def FinalizedOnlyExtendsOnRuns {Node Msg NodeState Ev Block : Type}
    [DecidableEq Node] [DecidableEq Msg]
    -- the ancestry and the roots of blocks (the conclusion reads the ancestry)
    [BlockVocab Block]
    -- the protocol of `RStsVariant2`
    (Pr : Protocol Node Msg NodeState Ev)
    -- a node state read as a view: its finalized block, its confirmed tip and the blocks it holds
    [NodeViewOf NodeState Block]
    -- the extra conditions on the observed runs that the claim assumes, `∅` for none
    (extraConditions : Set (ObservedRun Node Msg Ev (NodeView Block) → Prop)) : Prop :=
  -- every run `π` of the protocol
  ∀ π : Exec Pr,
    -- `τ`, the run `π` as observed: the run with each node's local state replaced by its view
    let τ : ObservedRun Node Msg Ev (NodeView Block) := RStsVariant2.observe NodeViewOf.view π
    -- `τ` meets each extra condition the claim assumes (none when `extraConditions` is `∅`)
    (∀ condition ∈ extraConditions, condition τ) →
    -- for every node `v`, every two configurations `i`, `j` of `τ`, and `v`'s views `l`, `l'` there
    ∀ (v : Node) (i j : ℕ) (l l' : NodeView Block),
      -- configuration `i` comes no later than configuration `j`
      i ≤ j →
      -- `l` is `v`'s view in configuration `i`
      state τ i v = some l →
      -- `l'` is `v`'s view in configuration `j`
      state τ j v = some l' →
      -- `v` is honest in configuration `j`
      HonestG τ j v →
      -- the finalized block of `l` is the finalized block of `l'`, or an ancestor of it
      BlockVocab.anc l.F l'.F

#check @FinalizedOnlyExtendsOnRuns

end LARuns
