module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Statements.Routines.WalkDefs

@[expose] public section

/-!
# One vote of a validator, over a model

The AC-store definitions of `GoldilocksCorrectness/Statements/Routines/WalkDefs.lean` over a
model `M`, each read on a node state `n : M.N`: one vote of a validator among the node's votes of a
slot, for a block's chain or for a block, resolved or resolved early. The page's other definitions,
`StartsTowards`, `RootsNameBlocksIn` and `VotesOnceFor`, name no member and are shared. At the
spec's model each is the landed definition when no two blocks of the node's tree share a root; the
theorems are on `Record/Restated/Statements/Routines/TickDefsGoldilocks.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `VotesOnceInPoolFor M n s' R v`: `v` has exactly one vote in `M.votesHeldSet n s'`; it resolves
in `n` (`ResolvesAt`), and its head is the root of a block of the tree of `M.fg_to_ac n` that is `R`
or a descendant of `R`.

The variables:
- `M`: the model;
- `n`: the node state; `s'`: the slot of the vote;
- `R`: the block whose chain the vote supports; `v`: the validator.

Read aloud: `v` has exactly one slot-`s'` vote in `n`; it resolves, and its head is a block of the
tree of `M.fg_to_ac n` that is `R` or a descendant of `R`. -/
def VotesOnceInPoolFor (M : GoldilocksModel V) (n : M.N) (s' : Slot) (R : Block V) (v : V) : Prop :=
  ∃ vote ∈ M.votesHeldSet n s', vote.val_index = v ∧ (∃ x : Stamp, ResolvesAt M n vote x) ∧
    (∃ H ∈ (M.fg_to_ac n).tree, H.root = vote.head ∧ R.AncestorEq H) ∧
    ∀ vote' ∈ M.votesHeldSet n s', vote'.val_index = v → vote' = vote

/-- `EarlyVoteOnceAt M n t s' B v`: `v` has exactly one vote in `M.votesHeldSet n s'`, its head is
`B`'s root, and it resolves in `n` strictly before the time `t`. This is `EarlyVoteOnceFor` with the
cutoff a parameter.

The variables:
- `M`: the model;
- `n`: the node state; `t`: the cutoff; `s'`: the slot of the vote;
- `B`: the block the vote names; `v`: the validator.

Read aloud: `v` has exactly one slot-`s'` vote in `n`; its head is `B`'s root, and it resolves
strictly before `t`. -/
def EarlyVoteOnceAt (M : GoldilocksModel V) (n : M.N) (t : Time) (s' : Slot) (B : Block V)
    (v : V) : Prop :=
  ∃ vote ∈ M.votesHeldSet n s', vote.val_index = v ∧ vote.head = B.root ∧
    (∃ x : Stamp, ResolvesAt M n vote x ∧ occurrenceBefore (some x) t = true) ∧
    ∀ vote' ∈ M.votesHeldSet n s', vote'.val_index = v → vote' = vote

/-- `EarlyVoteOnceFor M C n s' B v`: `v` has exactly one vote in `M.votesHeldSet n s'`, its head
is `B`'s root, and it resolves in `n` strictly before `C.t_ s' + 2 * C.Δ`.

The variables:
- `M`: the model;
- `C`: the configuration; `n`: the node state; `s'`: the slot of the vote;
- `B`: the block the vote names; `v`: the validator.

Read aloud: `v` has exactly one slot-`s'` vote in `n`; its head is `B`'s root, and it resolves
strictly before `C.t_ s' + 2 · C.Δ`. -/
def EarlyVoteOnceFor (M : GoldilocksModel V) (C : Config) (n : M.N) (s' : Slot) (B : Block V)
    (v : V) : Prop :=
  ∃ vote ∈ M.votesHeldSet n s', vote.val_index = v ∧ vote.head = B.root ∧
    (∃ x : Stamp, ResolvesAt M n vote x ∧
      occurrenceBefore (some x) (C.t_ s' + 2 * C.Δ) = true) ∧
    ∀ vote' ∈ M.votesHeldSet n s', vote'.val_index = v → vote' = vote

end GoldilocksCorrectness.Record.Statements.Routines
