module
public import Mathlib.Data.Finset.Union
public import Model.Vocabulary.Protocol.StoreBase

@[expose] public section

/-!
# Voter and proposer views

The vote views and the block view a Goldfish voter reads in slot `s`, and the vote views a proposer
reads.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The voter's raw view in slot `s`: the slot-`(s−1)` votes received before
    `view_freeze E (s − 1)`, together with every slot-`(s−1)` vote included in a stored slot-`s`
    block. -/
def voter_view (E : Env V) (st : GoldfishStore V) (s : Slot) : Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (view_freeze E (s - 1)) (st.pool (s - 1)) ∪
    (st.T.filter (fun B => B.slot = s)).biUnion (fun B =>
      B.gf_votes.toFinset.filter (fun vote => vote.slot = s - 1))

/-- The voter's support view in slot `s`: the slot-`(s−1)` votes whose resolution time is before
    `view_freeze E (s − 1)`, and the support votes of a stored slot-`s` block whose block resolves
    in the store's tree. -/
def voter_support_view (E : Env V) (st : GoldfishStore V) (s : Slot) :
    Finset (GoldfishVote V) :=
  beforeCutoff st.tau (view_freeze E (s - 1)) (st.pool (s - 1)) ∪
    (st.T.filter (fun B => B.slot = s)).biUnion (fun B =>
      B.gf_support_votes.toFinset.filter (fun vote =>
        resolved st.T vote = true ∧ vote.slot = s - 1))

/-- The block view of the slot-`s` voter: the blocks of `Σ.T` stamped before
    `view_freeze E (s − 1)`, and every stored ancestor of, or equal to, a stored slot-`s` block. -/
def voter_processed_block_tree (E : Env V) (st : GoldfishStore V) (s : Slot) :
    Finset (Block V) :=
  let freeze := view_freeze E (s - 1)
  let proposals := st.T.filter (fun P => P.slot = s)
  st.T.filter (fun B =>
    stampedBefore st.timestamp_block freeze B = true ∨
      ∃ P ∈ proposals, Block.preceq B P = true)

/-- The proposer's raw view in slot `s`: every slot-`(s−1)` vote in the store, unfiltered. -/
def proposer_view (st : GoldfishStore V) (s : Slot) : List (GoldfishVote V) :=
  st.gf_votes (s - 1)

/-- The proposer's support view: the resolved members of its raw view. -/
def proposer_support_view (st : GoldfishStore V) (s : Slot) : List (GoldfishVote V) :=
  (st.gf_votes (s - 1)).filter (fun vote => resolved st.T vote = true)

end Protocol
end DecoupledConsensusModel

end
