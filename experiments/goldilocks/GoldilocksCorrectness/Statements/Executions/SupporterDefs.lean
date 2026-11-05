module
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Statements.Routines.SupporterDefs

@[expose] public section

/-!
# G2 over executions: its vocabulary

What G2 over executions (`lem21_goldfish_vote_extends_eligible_block`) assumes of each member of
the set `Sup` that makes a block `B` eligible at the confirmation update of an honest validator, as
one definition over an AC state and a frame (`EarlySupporterOf`). The same with the
cutoff a parameter is `EarlySupporterAt`; the one theorem, `earlySupporterOf_iff`, says the two
agree at the cutoff `C.t_ s + 2 · C.Δ`, and holds by definition.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

namespace GoldilocksCorrectness.Statements.Executions

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `EarlySupporterAt A Φ t s B u`: `u` has exactly one slot-`s` vote in `A`'s pool; its head is
the root of a block `H` of `Φ.tree` that is `B` or a descendant of `B`; and it resolves (`A.tau`)
strictly before the time `t`. This is `EarlySupporterOf` with the cutoff a parameter.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the cutoff;
- `s`: the slot of the vote; `B`: the block whose chain the vote supports; `u`: the validator.

Read aloud: `u` has exactly one slot-`s` vote in `A`'s pool; its head is a block of `Φ.tree` that
is `B` or a descendant of `B`; and it resolves strictly before `t`. -/
def EarlySupporterAt (A : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V)
    (u : V) : Prop :=
  ∃ vote ∈ A.pool s, vote.val_index = u ∧
    (∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H) ∧
    (∃ y : Stamp, A.tau Φ vote = .ok (some y) ∧ occurrenceBefore (some y) t = true) ∧
    ∀ vote' ∈ A.pool s, vote'.val_index = u → vote' = vote

omit [Fintype V] [RootOrder] in
/-- `EarlySupporterOf` is `EarlySupporterAt` at the cutoff `C.t_ s + 2 · C.Δ`.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame;
- `s`: the slot of the vote; `B`: the block whose chain the vote supports; `u`: the validator.

Read aloud: `u` is an early supporter of `B`'s chain exactly when it is one with the cutoff
`C.t_ s + 2 · C.Δ`. -/
theorem earlySupporterOf_iff (C : Config) (A : ACState V) (Φ : Frame V) (s : Slot) (B : Block V)
    (u : V) : EarlySupporterOf C A Φ s B u ↔ EarlySupporterAt A Φ (C.t_ s + 2 * C.Δ) s B u :=
  Iff.rfl

end GoldilocksCorrectness.Statements.Executions
