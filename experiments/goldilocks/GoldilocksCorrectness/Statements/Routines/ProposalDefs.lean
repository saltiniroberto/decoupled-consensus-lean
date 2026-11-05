module
public import GoldilocksCorrectness.Statements.Routines.TickDefs

@[expose] public section

/-!
# The vocabulary of the proposal statements

One definition the statements about the proposal of the available chain read
(`ProposalStatements.lean`, and the statement of G0 over executions):

- `ProposalCountedVotes A Φ s votes support_votes`, the sets of votes the proposal of slot `s + 1`
  counts, written as membership conditions on `A`'s pool of slot `s` and `A`'s resolution times.


-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `ProposalCountedVotes A Φ s votes support_votes`: `votes` and `support_votes` are the two sets
of votes the proposal of slot `s + 1` counts, read off the AC state `A` and the frame `Φ`: `votes`
is `A`'s pool of slot `s`, and a vote is in `support_votes` exactly when it is a vote of that pool
whose resolution time (`A.tau`) answers a time.

The variables:
- `A`: the AC state; `Φ`: the frame; `s`: the slot of the votes;
- `votes`, `support_votes`: the two sets.

Read aloud: the proposal of slot `s + 1` counts every slot-`s` vote of the pool, and as support
votes exactly those whose resolution time `A.tau` answers a time. -/
def ProposalCountedVotes (A : ACState V) (Φ : Frame V) (s : Slot)
    (votes support_votes : Finset (GoldfishVote V)) : Prop :=
  votes = A.pool s ∧
    ∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      vote ∈ A.pool s ∧ ∃ y : Stamp, A.tau Φ vote = .ok (some y)

end GoldilocksCorrectness.Statements.Routines
