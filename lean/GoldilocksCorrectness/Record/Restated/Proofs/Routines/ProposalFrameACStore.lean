module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalDefs

@[expose] public section

/-!
# ProposalFrame, over a model: the sets the proposal counts

The theorem of `GoldilocksCorrectness/Proofs/Routines/ProposalFrame.lean` that reads the node's
votes, over a model `M` whose facts `F` hold: `proposalCountedVotes_of_lists`, the lists the
proposal reads give the sets `ProposalCountedVotes` describes (with the resolution time read as
`ResolvesAt`, and the node's votes of a slot as the reader `n.votesHeld`).

The page's other theorems are not restated: `goldfish_eligible_current_slot` and
`goldfish_eligible_congr` are about the shared library definition `goldfish_eligible`, which the
record's statements use unchanged; `get_anchor_expireLocks` is about the spec's `expireLocks`,
which the record does not have; `mem_filterAuxM_ok_iff` and `mem_filterM_ok_iff` are about lists.

The recovery section states the landed theorem again, as the landed statement (`type_of%`), at the
AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n` whose frame's tree has no two
blocks sharing a root, and proves it from its record form at the spec's model
(`goldilocks_proposalCountedVotes`, `goldilocks_resolvesAt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Record.Statements.Routines (ResolvesAt ProposalCountedVotes)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- The lists the proposal reads give the sets `ProposalCountedVotes` describes: `votes` is the
node's list of the votes of slot `s`, and `support_votes` holds exactly its votes that resolve in
the node (the record form of `proposalCountedVotes_of_lists`).

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `s`: the slot of the votes; `votes`, `support_votes`: the two lists.

Read aloud: the proposal's two lists, as sets, are the sets it counts. -/
theorem proposalCountedVotes_of_lists (n : M.N) (s : Slot)
    (votes support_votes : List (GoldfishVote V))
    -- `votes` is the node's list of the votes of slot `s`
    (hv : votes = n.votesHeld s)
    -- `support_votes` holds exactly the votes of `votes` that resolve in `n`
    (hs : ∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      vote ∈ votes ∧ ∃ y : Stamp, ResolvesAt M n vote y) :
    ProposalCountedVotes M n s votes.toFinset support_votes.toFinset := by
  refine ⟨by rw [hv, F.rd.votesHeldSet_eq], fun vote => ?_⟩
  rw [List.mem_toFinset, hs vote, F.rd.votesHeldSet_eq, List.mem_toFinset, hv]

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.proposalCountedVotes_of_lists`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose frame's tree has no two blocks sharing a root.

Read aloud: the landed theorem holds at every such node state. -/
theorem proposalCountedVotes_of_lists_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V) (s : Slot) (votes support_votes : List (GoldfishVote V)),
      RootsNameBlocksIn (fg_to_ac n.S).tree →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.proposalCountedVotes_of_lists V _ n.A
        (fg_to_ac n.S) s votes support_votes) := by
  intro n s votes support_votes hRoots hv hs
  refine (GoldilocksCorrectness.Record.Statements.Routines.goldilocks_proposalCountedVotes n s
    _ _ hRoots).2 (proposalCountedVotes_of_lists Model.goldilocks goldilocksFacts n s votes
      support_votes hv (fun vote => ?_))
  rw [hs vote]
  exact and_congr_right (fun _ => exists_congr (fun y =>
    GoldilocksCorrectness.Record.Statements.Routines.goldilocks_resolvesAt n vote y hRoots))

end GoldilocksCorrectness.Record.Proofs.Routines
