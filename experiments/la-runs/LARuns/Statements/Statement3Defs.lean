import LARuns.Statements.Statement4Defs

/-!
# The conclusions of statement 3, finality liveness after healing, read on the observed run

The two conclusions of statement 3 (`LARuns.FinalityLivenessAfterHealingOnRuns`) besides the
root-collision disjunct `RootCollisionBy`, read on `τ`, an execution of any type with an
`RStsVariant2.Observable` whose nodes' states are read as views (`NodeViewOf`), for a window
`[·, tWindowEnd]` of the run after which a proposed block is finalized:

- `FinalizedIncludedBetween`: a block an honest proposer proposed is the finalized block, or an
  ancestor of it, of every honest node that has been up and honest for `ΔFinalityDelivery` from the
  clock value of one of its ticks at or after `tWindowEnd`, and that finalized block is new: no node
  had it as its finalized block up to the proposal;
- `FinalizedExtendedBetween`: that finalized block is a strict descendant of the finalized block of
  every honest node whose clock read less than the proposal's reading.

Both are written with `UpAndHonestForFrom` (a node up and honest for a duration from the clock value
of one of its ticks at or after a time, which has ticked at a clock value at least the window's end
before a configuration).

This page imports `LARuns.Statements.Statement4Defs`.
-/

set_option autoImplicit false

namespace LARuns

open RStsVariant2 (UpAndHonestThroughoutG)
open RStsVariant2.Observable

section Conclusions

variable {X Node Msg Ev Block L : Type} [DecidableEq Node] [DecidableEq Msg]
  [RStsVariant2.Observable X Node Msg L Ev] [NodeViewOf L Block]

/-- `UpAndHonestForFrom τ tFrom ΔUp i v`: for some step `k` of `τ` that is `v`'s tick at a clock
value `c₀` at or after `tFrom` (`TickAtG`), the node `v` is up and honest throughout the real-time
window `[c₀, c₀ + ΔUp]` (`RStsVariant2.UpAndHonestThroughoutG`), which starts at the real time equal
to the tick's clock value, and before configuration `i` of `τ`, `v` has ticked at a clock value at
least `c₀ + ΔUp` (`TickedAtLeastBefore`).

Read aloud: at some tick of `v` at a clock value `c₀` at or after `tFrom`, `v` is up and honest from
the real time `c₀` for `ΔUp`, and before configuration `i`, `v` has ticked at a clock value at least
`c₀ + ΔUp`.

Kind: part of the statements. -/
def UpAndHonestForFrom (τ : X) (tFrom ΔUp : ℝ) (i : ℕ) (v : Node) : Prop :=
  -- some step `k` and clock value `c₀`
  ∃ (k c₀ : ℕ),
    -- step `k` is `v`'s tick at the clock value `c₀`
    TickAtG τ k v c₀ ∧
    -- `c₀` is at or after `tFrom`
    tFrom ≤ (c₀ : ℝ) ∧
    -- `v` is up and honest throughout `[c₀, c₀ + ΔUp]`
    UpAndHonestThroughoutG τ c₀ (c₀ + ΔUp) v ∧
    -- before configuration `i`, `v` has ticked at a clock value at least `c₀ + ΔUp`
    TickedAtLeastBefore τ i v ((c₀ : ℝ) + ΔUp)

/-- `FinalizedIncludedBetween τ tWindowEnd ΔFinalityDelivery tBy vProposer B`: for every step
`iProposal` of `τ` at which `vProposer`, while honest, proposes `B` (`ProposesAt`), and every node
`v` and configuration `i` of `τ` entered by `tBy`, `v` honest in every configuration entered by the
time configuration `i` is entered (`HonestThroughEntryStateBy`), that was up and honest for
`ΔFinalityDelivery` from the clock value of one of its ticks at or after `tWindowEnd`, before
configuration `i` (`UpAndHonestForFrom`): `B` is the finalized block of `v`'s view there, or an
ancestor of it (`BlockVocab.anc`), and no node had that finalized block as the finalized block of
its view in any configuration up to the one step `iProposal` is taken from.

Read aloud: once `vProposer`, while honest, proposed `B`, every honest node that has been up and
honest for `ΔFinalityDelivery` from one of its ticks at or after `tWindowEnd` has finalized `B` or a
descendant of it, up to `tBy`, a block nobody had finalized when `B` was proposed.

Kind: part of the statements. -/
def FinalizedIncludedBetween [BlockVocab Block] [MessageVocab Msg Node Block] (τ : X)
    (tWindowEnd ΔFinalityDelivery tBy : ℝ) (vProposer : Node) (B : Block) : Prop :=
  -- for every step `iProposal` of `τ`
  ∀ iProposal : ℕ,
    -- at step `iProposal`, `vProposer`, while honest, proposes `B`
    ProposesAt τ iProposal vProposer B →
    -- for every node `v`, every configuration `i` of `τ`, and `v`'s state `l` there
    ∀ (v : Node) (i : ℕ) (l : L),
      -- configuration `i` is entered by `tBy`, `v` is honest in every configuration entered by the
      -- time configuration `i` is entered, and its state in `i` is `l`
      HonestThroughEntryStateBy τ tBy i v l →
      -- from the clock value `c₀` of one of its ticks at or after `tWindowEnd`, `v` stayed up and
      -- honest for `ΔFinalityDelivery`, and ticked at a clock value at least
      -- `c₀ + ΔFinalityDelivery` before configuration `i`
      UpAndHonestForFrom τ tWindowEnd ΔFinalityDelivery i v →
      -- then `B` is the finalized block of `v`'s view, or an ancestor of it
      BlockVocab.anc B (NodeViewOf.view l).F ∧
        -- and no node `v'` whose state `l'` is known in a configuration `i'` up to the one step
        -- `iProposal` is taken from had that block as the finalized block of its view
        ∀ (v' : Node) (i' : ℕ) (l' : L),
          i' ≤ iProposal → state τ i' v' = some l' →
          (NodeViewOf.view l').F ≠ (NodeViewOf.view l).F

/-- `FinalizedExtendedBetween τ tFrom tWindowEnd ΔFinalityDelivery tBy vProposer B`: for every
step `iProposal` of `τ` at which `vProposer`, while honest, proposes `B` (`ProposesAt`) with its
clock reading `tProposal` there, every node `v` and configuration `i` of `τ` entered by `tBy`, `v`
honest in every configuration entered by the time configuration `i` is entered
(`HonestThroughEntryStateBy`), that was up and honest for `ΔFinalityDelivery` from the clock value
of one of its ticks at or after `tWindowEnd`, before configuration `i` (`UpAndHonestForFrom`), and
every node `v'` honest in a
configuration of `τ` entered within `[tFrom, tBy]` (`HonestStateWithin`) whose clock reads less than
`tProposal` there: the finalized block of `v'`'s view is an ancestor of the finalized block of `v`'s
view (`BlockVocab.anc`) other than it.

Read aloud: once `vProposer`, while honest, proposed `B` at a clock reading, the finalized block of
every honest node that has been up and honest for `ΔFinalityDelivery` from one of its ticks at or
after `tWindowEnd` strictly extends every finalized block an honest node had while its clock was
before that reading.

Kind: part of the statements. -/
def FinalizedExtendedBetween [BlockVocab Block] [MessageVocab Msg Node Block] (τ : X)
    (tFrom tWindowEnd ΔFinalityDelivery tBy : ℝ) (vProposer : Node) (B : Block) : Prop :=
  -- for every step `iProposal` of `τ` and reading `tProposal`
  ∀ (iProposal : ℕ) (tProposal : ℕ),
    -- at step `iProposal`, `vProposer`, while honest, proposes `B`
    ProposesAt τ iProposal vProposer B →
    -- `vProposer`'s clock reads `tProposal` in the configuration step `iProposal` is taken from
    clock τ iProposal vProposer = some tProposal →
    -- for every node `v`, every configuration `i` of `τ`, and `v`'s state `l` there
    ∀ (v : Node) (i : ℕ) (l : L),
      -- configuration `i` is entered by `tBy`, `v` is honest in every configuration entered by the
      -- time configuration `i` is entered, and its state in `i` is `l`
      HonestThroughEntryStateBy τ tBy i v l →
      -- from the clock value `c₀` of one of its ticks at or after `tWindowEnd`, `v` stayed up and
      -- honest for `ΔFinalityDelivery`, and ticked at a clock value at least
      -- `c₀ + ΔFinalityDelivery` before configuration `i`
      UpAndHonestForFrom τ tWindowEnd ΔFinalityDelivery i v →
      -- for every node `v'`, every configuration `i'` of `τ`, `v'`'s state `l'` and clock reading
      -- `c` there
      ∀ (v' : Node) (i' : ℕ) (l' : L) (c : ℕ),
        -- `v'` is honest in configuration `i'`, entered within `[tFrom, tBy]`, and its state is
        -- `l'`
        HonestStateWithin τ tFrom tBy i' v' l' →
        -- `v'`'s clock reads `c` in configuration `i'`
        clock τ i' v' = some c →
        -- `c` is less than the reading at which `B` was proposed
        c < tProposal →
        -- then the finalized block of `v'`'s view is the finalized block of `v`'s view or an
        -- ancestor of it, and is not it
        BlockVocab.anc (NodeViewOf.view l').F (NodeViewOf.view l).F ∧
          (NodeViewOf.view l').F ≠ (NodeViewOf.view l).F

end Conclusions

end LARuns
