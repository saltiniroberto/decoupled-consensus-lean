module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Statements.Routines.ProposalDefs

@[expose] public section

/-!
# The votes a proposal counts, over a model

The definition of `GoldilocksCorrectness/Statements/Routines/ProposalDefs.lean` over a model
`M`, read on a node state `n : M.N`: the two sets of votes the proposal counts. At the spec's model
it is the landed definition when no two blocks of the node's tree share a root; the theorem is on
`Record/Restated/Statements/Routines/TickDefsGoldilocks.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `ProposalCountedVotes M n s votes support_votes`: `votes` is the set `M.votesHeldSet n s` of
the slot-`s` votes the node state `n` holds, and `support_votes` is the set of those that resolve
in `n` (`ResolvesAt`).

The variables:
- `M`: the model;
- `n`: the node state; `s`: the slot; `votes`, `support_votes`: the two sets.

Read aloud: the proposal counts every slot-`s` vote of `n`, and as support votes those that
resolve. -/
def ProposalCountedVotes (M : GoldilocksModel V) (n : M.N) (s : Slot)
    (votes support_votes : Finset (GoldfishVote V)) : Prop :=
  votes = M.votesHeldSet n s ∧
    ∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      vote ∈ M.votesHeldSet n s ∧ ∃ y : Stamp, ResolvesAt M n vote y

end GoldilocksCorrectness.Record.Statements.Routines
