module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.SupporterDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefsGoldilocks
public import GoldilocksCorrectness.Statements.Executions.SupporterDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# SupporterDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/SupporterDefs.lean` over a model `M`,
read on a node state `n : M.N`: an early supporter of a block with the cutoff a parameter, and the
record's `EarlySupporterOf` as its instance at two delays into the slot. At the spec's model it is
the landed definition read on `n.A` and `fg_to_ac n.S` when no two blocks of that frame's tree share
a root (`goldilocks_EarlySupporterAt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (VoterTreeAt AwakeFor ResolvesAt)
open GoldilocksCorrectness.Record.Statements.Routines (EarlySupporterOf)

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `EarlySupporterAt M n t s B u`: `u` has exactly one vote in `M.votesHeldSet n s`; its head
is the root of a block `H` of the tree of `M.fg_to_ac n` that is `B` or a descendant of `B`;
and it resolves in `n` strictly before the time `t`. This is `EarlySupporterOf` with the
cutoff a parameter.

The variables:
- `M`: the model;
- `n`: the node state; `t`: the cutoff;
- `s`: the slot of the vote; `B`: the block whose chain the vote supports; `u`: the validator.

Read aloud: `u` has exactly one slot-`s` vote in `n`; its head is a block of the frame's tree
that is `B` or a descendant of `B`; and it resolves strictly before `t`. -/
def EarlySupporterAt (n : M.N) (t : Time) (s : Slot) (B : Block V) (u : V) : Prop :=
  ∃ vote ∈ M.votesHeldSet n s, vote.val_index = u ∧
    (∃ H ∈ (M.fg_to_ac n).tree, H.root = vote.head ∧ B.AncestorEq H) ∧
    (∃ y : Stamp, ResolvesAt M n vote y ∧ occurrenceBefore (some y) t = true) ∧
    ∀ vote' ∈ M.votesHeldSet n s, vote'.val_index = u → vote' = vote

omit [RootOrder] in
/-- `EarlySupporterOf` is `EarlySupporterAt` at the cutoff `C.t_ s + 2 · C.Δ`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state;
- `s`: the slot of the vote; `B`: the block whose chain the vote supports; `u`: the validator.

Read aloud: `u` is an early supporter of `B`'s chain exactly when it is one with the cutoff
`C.t_ s + 2 · C.Δ`. -/
theorem earlySupporterOf_iff (C : Config) (n : M.N) (s : Slot) (B : Block V) (u : V) :
    EarlySupporterOf M C n s B u ↔ EarlySupporterAt M n (C.t_ s + 2 * C.Δ) s B u :=
  Iff.rfl

end GoldilocksCorrectness.Record.Statements.Executions

