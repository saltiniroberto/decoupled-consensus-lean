module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Score

@[expose] public section

/-!
# ScoreDefs, over a model

The definition `supportersOf` of `GoldilocksCorrectness/Proofs/Routines/Score.lean` over a model
`M`, on a page that imports no facts, for the facts of the fork-choice family: their field
`goldfish_score_eq_ok` names the supporters of a block.

Record step 6 restated the same definition, under the same name in the namespace
`GoldilocksCorrectness.Record.Proofs.Routines`, on `Record/Restated/Proofs/Routines/ScoreACStore.lean`,
a page that imports the facts `Facts`; the facts page cannot import it. This page's definition is
`ScoreDefs.supportersOf`, with the same body: the two are equal by definition, and the restated
`goldfish_score_eq_ok` (`Record/Restated/Proofs/Routines/ScoreForkChoice.lean`) states the field
with step 6's. The copy goes when step 6's definition moves to a page of its own.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines.ScoreDefs

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `supportersOf M Φ votes support_votes s B`: the validators that are not equivocators of
`votes` and have a slot-`s` vote in `support_votes` whose head is the root of a block of `Φ.tree`
that is `B` or a descendant of `B`.

The variables:
- `M`: the model;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block supported.

Read aloud: the validators that are not equivocators of `votes` and have a slot-`s` vote in
`support_votes` whose head is a block of `Φ.tree` that is `B` or a descendant of `B`. -/
def supportersOf (M : GoldilocksModel V) (Φ : Frame V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) : Finset V :=
  (support_votes.filter fun vote => vote.val_index ∉ M.equivocators votes ∧ vote.slot = s ∧
    ∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H).map' fun vote => vote.val_index

/-- At the spec's model, `ScoreDefs.supportersOf` is the landed definition.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes counted; `s`: the slot;
  `B`: the block.

Read aloud: the spec's model has the landed `supportersOf`. -/
theorem goldilocks_supportersOf (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (B : Block V) :
    GoldilocksCorrectness.Proofs.Routines.supportersOf Φ votes support_votes s B =
      supportersOf (Model.goldilocks (V := V)) Φ votes support_votes s B := rfl

end GoldilocksCorrectness.Record.Proofs.Routines.ScoreDefs
