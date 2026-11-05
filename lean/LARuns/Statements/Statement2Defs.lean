import LARuns.Statements.Statement4Defs

/-!
# The conclusions of statement 2, the confirmed tip after healing, read on the observed run

The four conclusions of statement 2 (`LARuns.ConfirmedTipAfterHealingOnRuns`) besides the
root-collision disjunct `RootCollisionBy`, read on `τ`, an execution of any type with an
`RStsVariant2.Observable` whose nodes' states are read as views (`NodeViewOf`):

- `ConfirmedAgreeBetween`: from a time up to a time, the confirmed tips of two honest nodes are
  compatible;
- `ConfirmedMonotoneBetween`: from a time up to a time, an honest node's confirmed tip only
  extends;
- `ConfirmedIncludedBetween`: a block an honest proposer proposed is, once a node that was up and
  honest throughout a committee's sleepiness window ending at or after the proposer's hand-over has
  ticked past that window's end, the node's confirmed tip or an ancestor of it;
- `ConfirmedExtendedBetween`: a block an honest proposer proposed at a clock reading is a strict
  descendant of the confirmed tip of every honest node whose clock read less than that reading.

This page imports `LARuns.Statements.Statement4Defs`.
-/

set_option autoImplicit false

namespace LARuns

open RStsVariant2 (UpAndHonestThroughoutG ObservableWithCommittees)
open RStsVariant2.Observable

section Conclusions

variable {X Node Msg Ev Block L : Type} [DecidableEq Node] [DecidableEq Msg]
  [RStsVariant2.Observable X Node Msg L Ev] [NodeViewOf L Block]

/-- `ConfirmedAgreeBetween τ tFrom tBy`: for every two nodes `v₁`, `v₂` and configurations `i`, `j`
of `τ` entered within `[tFrom, tBy]`, each node honest in every configuration entered by the time
its configuration is entered (`HonestThroughEntryStateWithin`), the confirmed tips of their views
there are compatible (`BlockVocab.Compatible`).

Read aloud: from `tFrom` up to `tBy`, the confirmed tips of two honest nodes are on one chain.

Kind: part of the statements. -/
def ConfirmedAgreeBetween [BlockVocab Block] (τ : X) (tFrom tBy : ℝ) : Prop :=
  -- for every two nodes `v₁`, `v₂`, configurations `i`, `j` of `τ`, and their states `l₁`, `l₂`
  -- there
  ∀ (v₁ v₂ : Node) (i j : ℕ) (l₁ l₂ : L),
    -- configuration `i` is entered within `[tFrom, tBy]`, `v₁` is honest in every configuration
    -- entered by the time configuration `i` is entered, and its state in `i` is `l₁`
    HonestThroughEntryStateWithin τ tFrom tBy i v₁ l₁ →
    -- configuration `j` is entered within `[tFrom, tBy]`, `v₂` is honest in every configuration
    -- entered by the time configuration `j` is entered, and its state in `j` is `l₂`
    HonestThroughEntryStateWithin τ tFrom tBy j v₂ l₂ →
    -- the confirmed tip of `v₁`'s view is the confirmed tip of `v₂`'s view, an ancestor of it, or
    -- a descendant of it
    BlockVocab.Compatible (NodeViewOf.view l₁).C (NodeViewOf.view l₂).C

/-- `ConfirmedMonotoneBetween τ tFrom tBy`: for every node `v` and every two configurations `i ≤ j`
of `τ` entered within `[tFrom, tBy]`, `v` honest in every configuration entered by the time each of
them is entered (`HonestThroughEntryStateWithin`), the confirmed tip of `v`'s view in configuration
`i` is the confirmed tip of its view in configuration `j` or an ancestor of it (`BlockVocab.anc`).

Read aloud: from `tFrom` up to `tBy`, an honest node's confirmed tip only extends.

Kind: part of the statements. -/
def ConfirmedMonotoneBetween [BlockVocab Block] (τ : X) (tFrom tBy : ℝ) : Prop :=
  -- for every node `v`, configurations `i`, `j` of `τ`, and `v`'s states `l`, `l'` there
  ∀ (v : Node) (i j : ℕ) (l l' : L),
    -- configuration `i` is at or before configuration `j`
    i ≤ j →
    -- configuration `i` is entered within `[tFrom, tBy]`, `v` is honest in every configuration
    -- entered by the time configuration `i` is entered, and its state in `i` is `l`
    HonestThroughEntryStateWithin τ tFrom tBy i v l →
    -- configuration `j` is entered within `[tFrom, tBy]`, `v` is honest in every configuration
    -- entered by the time configuration `j` is entered, and its state in `j` is `l'`
    HonestThroughEntryStateWithin τ tFrom tBy j v l' →
    -- the confirmed tip of `v`'s view in configuration `i` is the confirmed tip of its view in
    -- configuration `j`, or an ancestor of it
    BlockVocab.anc (NodeViewOf.view l).C (NodeViewOf.view l').C

/-- `ConfirmedExtendedBetween τ tFrom tBy vProposer B`: for every step `iProposal` of `τ` at which
`vProposer`, while honest, proposes `B` (`ProposesAt`) with its clock reading `tProposal` there,
and every node `v` and configuration `i` of `τ` entered within `[tFrom, tBy]`, `v` honest in every
configuration entered by the time configuration `i` is entered (`HonestThroughEntryStateWithin`),
whose clock reads less than `tProposal` there, the confirmed tip of `v`'s view is an ancestor of
`B` (`BlockVocab.anc`) other than `B`.

Read aloud: from `tFrom` up to `tBy`, a block `vProposer` proposed while honest strictly extends
the confirmed tip of every honest node whose clock was before the proposal's reading.

Kind: part of the statements. -/
def ConfirmedExtendedBetween [BlockVocab Block] [MessageVocab Msg Node Block] (τ : X)
    (tFrom tBy : ℝ) (vProposer : Node) (B : Block) : Prop :=
  -- for every step `iProposal` of `τ` and reading `tProposal`
  ∀ (iProposal : ℕ) (tProposal : ℕ),
    -- at step `iProposal`, `vProposer`, while honest, proposes `B`
    ProposesAt τ iProposal vProposer B →
    -- `vProposer`'s clock reads `tProposal` in the configuration step `iProposal` is taken from
    clock τ iProposal vProposer = some tProposal →
    -- for every node `v`, every configuration `i` of `τ`, `v`'s state `l` and clock reading `c`
    -- there
    ∀ (v : Node) (i : ℕ) (l : L) (c : ℕ),
      -- configuration `i` is entered within `[tFrom, tBy]`, `v` is honest in every configuration
      -- entered by the time configuration `i` is entered, and its state in `i` is `l`
      HonestThroughEntryStateWithin τ tFrom tBy i v l →
      -- `v`'s clock reads `c` in configuration `i`
      clock τ i v = some c →
      -- `c` is less than the reading at which `B` was proposed
      c < tProposal →
      -- then the confirmed tip of `v`'s view is `B` or an ancestor of it, and is not `B`
      BlockVocab.anc (NodeViewOf.view l).C B ∧ (NodeViewOf.view l).C ≠ B

end Conclusions

/-! ## The inclusion, which reads the committees -/

section Inclusion

variable {X Node Msg Ev Block L : Type} [DecidableEq Node] [DecidableEq Msg]
  [ObservableWithCommittees X Node Msg L Ev] [NodeViewOf L Block]

/-- `ConfirmedIncludedBetween τ tHandover tBy vProposer B`: if `vProposer`, while honest, proposed
`B` (`ProposedBy`), then for every committee `ci` of `τ` whose sleepiness window ends within
`[tHandover, tBy]`, every node `v` up and honest throughout that window
(`RStsVariant2.UpAndHonestThroughoutG`) has `B` as the confirmed tip of its view, or an ancestor of
it (`BlockVocab.anc`), in every configuration of `τ` entered by `tBy`, with `v` honest in every
configuration entered by the time that configuration is entered (`HonestThroughEntryStateBy`),
before which `v` has ticked at a reading at least the window's end (`TickedAtLeastBefore`). The
committees are read through `RStsVariant2.ObservableWithCommittees`.

Read aloud: if `vProposer`, while honest, proposed `B`, then every node that was up and honest
through a committee's window ending at or after `tHandover` holds `B` in its confirmed chain, up to
`tBy`, from its tick past that window's end on.

Kind: part of the statements. -/
def ConfirmedIncludedBetween [BlockVocab Block] [MessageVocab Msg Node Block] (τ : X)
    (tHandover tBy : ℝ) (vProposer : Node) (B : Block) : Prop :=
  -- if `vProposer`, while honest, proposed `B`
  ProposedBy τ vProposer B →
    -- then for every committee `ci` of `τ`
    ∀ ci : ℕ,
      -- whose sleepiness window ends at or after `tHandover`
      tHandover ≤ (ObservableWithCommittees.committees τ ci).sleepinessWindow.tEnd →
      -- and at or before `tBy`
      (ObservableWithCommittees.committees τ ci).sleepinessWindow.tEnd ≤ tBy →
      -- for every node `v`, every configuration `i` of `τ`, and `v`'s state `l` there
      ∀ (v : Node) (i : ℕ) (l : L),
        -- `v` was up and honest throughout the committee's sleepiness window
        UpAndHonestThroughoutG τ (ObservableWithCommittees.committees τ ci).sleepinessWindow.tStart
          (ObservableWithCommittees.committees τ ci).sleepinessWindow.tEnd v →
        -- configuration `i` is entered by `tBy`, `v` is honest in every configuration entered by
        -- the time configuration `i` is entered, and its state in `i` is `l`
        HonestThroughEntryStateBy τ tBy i v l →
        -- before configuration `i`, `v` has ticked at a reading at least the window's end
        TickedAtLeastBefore τ i v (ObservableWithCommittees.committees τ ci).sleepinessWindow.tEnd →
        -- then `B` is the confirmed tip of `v`'s view, or an ancestor of it
        BlockVocab.anc B (NodeViewOf.view l).C

end Inclusion

end LARuns
