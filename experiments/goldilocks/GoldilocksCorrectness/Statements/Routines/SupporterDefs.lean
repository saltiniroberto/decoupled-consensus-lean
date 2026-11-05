module
public import Goldilocks.AC.State

@[expose] public section

/-!
# Early supporters

`EarlySupporterOf C A Φ s B u`, over an AC state `A : ACState V` and the record
`Φ : Frame V` that `fg_to_ac` returns: `u` has exactly one slot-`s` vote in `A`'s pool; its head
is a block of `Φ.tree` that is `B` or a descendant of `B`; and it resolves strictly before
`C.t_ s + 2 · C.Δ`. Nothing is proved here.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `EarlySupporterOf C A Φ s B u`: `u` has exactly one slot-`s` vote in `A`'s pool; its head is
the root of a block `H` of `Φ.tree` that is `B` or a descendant of `B`; and it resolves (`A.tau`)
strictly before `C.t_ s + 2 · C.Δ`. This is `EarlyVoteOnceFor` with "head `B`" widened to "head on
`B`'s chain".

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame;
- `s`: the slot of the vote; `B`: the block whose chain the vote supports; `u`: the validator.

Read aloud: `u` has exactly one slot-`s` vote in `A`'s pool; its head is a block of `Φ.tree` that
is `B` or a descendant of `B`; and it resolves strictly before `C.t_ s + 2 · C.Δ`. -/
def EarlySupporterOf (C : Config) (A : ACState V) (Φ : Frame V) (s : Slot) (B : Block V)
    (u : V) : Prop :=
  ∃ vote ∈ A.pool s, vote.val_index = u ∧
    (∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H) ∧
    (∃ y : Stamp, A.tau Φ vote = .ok (some y) ∧
      occurrenceBefore (some y) (C.t_ s + 2 * C.Δ) = true) ∧
    ∀ vote' ∈ A.pool s, vote'.val_index = u → vote' = vote

end

end GoldilocksCorrectness.Statements.Routines
