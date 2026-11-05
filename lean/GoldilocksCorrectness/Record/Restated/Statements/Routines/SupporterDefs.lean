module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Statements.Routines.SupporterDefs

@[expose] public section

/-!
# An early supporter of a block, over a model

The definition of `GoldilocksCorrectness/Statements/Routines/SupporterDefs.lean` over a model
`M`, read on a node state `n : M.N`: an early supporter of a block. At the spec's model it is the
landed definition when no two blocks of the node's tree share a root; the theorem is on
`Record/Restated/Statements/Routines/TickDefsGoldilocks.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `EarlySupporterOf M C n s B u`: `u` has exactly one vote in `M.votesHeldSet n s`; its head is
the root of a block of the tree of `M.fg_to_ac n` that is `B` or a descendant of `B`, and it
resolves in `n` strictly before `C.t_ s + 2 * C.Δ`.

The variables:
- `M`: the model;
- `C`: the configuration; `n`: the node state; `s`: the slot of the vote;
- `B`: the block supported; `u`: the validator.

Read aloud: `u` has exactly one slot-`s` vote in `n`, for `B` or a descendant of `B`, and it
resolves strictly before `C.t_ s + 2 · C.Δ`. -/
def EarlySupporterOf (M : GoldilocksModel V) (C : Config) (n : M.N) (s : Slot) (B : Block V)
    (u : V) : Prop :=
  ∃ vote ∈ M.votesHeldSet n s, vote.val_index = u ∧
    (∃ H ∈ (M.fg_to_ac n).tree, H.root = vote.head ∧ B.AncestorEq H) ∧
    (∃ y : Stamp, ResolvesAt M n vote y ∧
      occurrenceBefore (some y) (C.t_ s + 2 * C.Δ) = true) ∧
    ∀ vote' ∈ M.votesHeldSet n s, vote'.val_index = u → vote' = vote

end GoldilocksCorrectness.Record.Statements.Routines
