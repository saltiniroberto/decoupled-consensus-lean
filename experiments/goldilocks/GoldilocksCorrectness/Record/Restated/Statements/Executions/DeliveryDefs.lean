module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefsGoldilocks
public import GoldilocksCorrectness.Statements.Executions.DeliveryDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# DeliveryDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/DeliveryDefs.lean` over a model `M`,
read on a node state `n : M.N`: a held early vote, with the cutoff a parameter and at the cutoff two
delays into the slot. The landed definitions read an AC state and a frame apart; the twins read the
node's votes, stamps and frame `M.fg_to_ac n`, and the vote's resolution through `ResolvesAt`. At
the spec's model each is the landed definition read on `n.A` and `fg_to_ac n.S` when no two blocks
of that frame's tree share a root (`goldilocks_HeldEarlyVoteAt`, `goldilocks_HeldEarlyVoteFor`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (VoterTreeAt AwakeFor ResolvesAt)

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `HeldEarlyVoteAt M n t s H_u u`: the node state `n` holds `u`'s slot-`s` vote for the
block `H_u`, stamped strictly before the time `t`; `H_u` is in the tree of `M.fg_to_ac n`;
the vote resolves in `n` strictly before `t`; and it is `u`'s only slot-`s` vote in `n`. This
is `HeldEarlyVoteFor` with the cutoff a parameter.

The variables:
- `M`: the model;
- `n`: the node state; `t`: the cutoff;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: `n` holds `u`'s slot-`s` vote for `H_u`, stamped strictly before `t`; `H_u` is in
the frame's tree; the vote resolves strictly before `t`; and it is `u`'s only slot-`s` vote in
`n`. -/
def HeldEarlyVoteAt (n : M.N) (t : Time) (s : Slot) (H_u : Block V) (u : V) : Prop :=
  GoldfishVote.mk u s H_u.root ∈ M.votesHeldSet n s ∧
    (∃ τ : Stamp, n.voteStamp (GoldfishVote.mk u s H_u.root) = some τ ∧ τ < (t : Stamp)) ∧
    H_u ∈ (M.fg_to_ac n).tree ∧
    (∃ y : Stamp, ResolvesAt M n (GoldfishVote.mk u s H_u.root) y ∧
      occurrenceBefore (some y) t = true) ∧
    ∀ vote' ∈ M.votesHeldSet n s, vote'.val_index = u → vote' = GoldfishVote.mk u s H_u.root

/-- `HeldEarlyVoteFor M C n s H_u u`: the node state `n` holds `u`'s slot-`s` vote for the
block `H_u`, stamped strictly before `C.t_ s + 2 · C.Δ`; `H_u` is in the tree of
`M.fg_to_ac n`; the vote resolves in `n` strictly before `C.t_ s + 2 · C.Δ`; and it is `u`'s
only slot-`s` vote in `n`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: `n` holds `u`'s slot-`s` vote for `H_u`, stamped strictly before
`C.t_ s + 2 · C.Δ`; `H_u` is in the frame's tree; the vote resolves strictly before
`C.t_ s + 2 · C.Δ`; and it is `u`'s only slot-`s` vote in `n`. -/
def HeldEarlyVoteFor (C : Config) (n : M.N) (s : Slot) (H_u : Block V) (u : V) : Prop :=
  GoldfishVote.mk u s H_u.root ∈ M.votesHeldSet n s ∧
    (∃ τ : Stamp, n.voteStamp (GoldfishVote.mk u s H_u.root) = some τ ∧
      τ < ((C.t_ s + 2 * C.Δ : Time) : Stamp)) ∧
    H_u ∈ (M.fg_to_ac n).tree ∧
    (∃ y : Stamp, ResolvesAt M n (GoldfishVote.mk u s H_u.root) y ∧
      occurrenceBefore (some y) (C.t_ s + 2 * C.Δ) = true) ∧
    ∀ vote' ∈ M.votesHeldSet n s, vote'.val_index = u → vote' = GoldfishVote.mk u s H_u.root

omit [RootOrder] in
/-- `HeldEarlyVoteFor` is `HeldEarlyVoteAt` at the cutoff `C.t_ s + 2 · C.Δ`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: `n` holds `u`'s early vote for `H_u` exactly when it holds it with the cutoff
`C.t_ s + 2 · C.Δ`. -/
theorem heldEarlyVoteFor_iff (C : Config) (n : M.N) (s : Slot) (H_u : Block V) (u : V) :
    HeldEarlyVoteFor M C n s H_u u ↔ HeldEarlyVoteAt M n (C.t_ s + 2 * C.Δ) s H_u u :=
  Iff.rfl

end GoldilocksCorrectness.Record.Statements.Executions

