module
public import GoldilocksCorrectness.Proofs.Routines.Lemma19

@[expose] public section

/-!
# The statements about the node's proposal

The audited statement about the block a successful tick of the node (`tick`) sends, proved in
`GoldilocksCorrectness/Proofs/Routines/Lemma19.lean`: it is the node's proposal for the slot of
the tick's time, at that slot's start, by that slot's proposer (Lemma 19).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 19, the block a tick sends is the node's proposal.** If the tick at `t` answered and
sent the block `B`, then the slot of `t`, `C.slot t`, is positive, `t` is its start
`C.t_ (C.slot t)`, and the node's validator is its proposer `P.proposer (C.slot t)`; and `B` is
the block with parent `H`, the end of the Goldfish fork choice from the anchor of the node's AC
state (`get_anchor n.A (fg_to_ac n.S) t`) through the viable tree of the frame's tree, counting
the node's list `votes` of slot `C.slot t − 1` and, as support votes, the list `support_votes` of
those that resolve (`n.A.tau` answers a time); its votes are `votes`, its support votes
`support_votes`, its attestations `proposal_attestations n.S H`, its root the digest of its content
(`X.digest`), and its proposer the node's validator.

Why: the tick of the available chain sends only Goldfish votes and the attestation duty only an
attestation, so the proposal sent `B`, inside its `if`; at the start of a slot the tick of the
available chain only deletes the expired lock entries, which keeps the pool and the stamps and does
not move the anchor; the proposal builds its block from the answer of `ac_proposal`, whose votes are
the pool's list, whose support votes are those that resolve, and whose parent is the head from the
anchor.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the proposers; `X`: the digest;
- `n`: the node state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `B`: the block sent;
- `H`: the parent; `votes`, `support_votes`: the lists the proposal counts.

Read aloud: a block the tick at `t` sent is the node's proposal for the slot of `t`, at that
slot's start, by that slot's proposer: its parent is the block the Goldfish fork choice reaches
from the node's anchor, counting the node's slot-`(s − 1)` votes, and its content is the pool's
list, the resolving votes, the pool's valid attestations, the digest, and the node's validator. -/
theorem lem19_tick_proposes (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (B : Block V)
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hBlock : NamedObject.block B ∈ sent) :
    0 < C.slot t ∧ t = C.t_ (C.slot t) ∧ n.v = P.proposer (C.slot t) ∧
      ∃ (H : Block V) (votes support_votes : List (GoldfishVote V)),
        votes = n.A.gf_votes (C.slot t - 1) ∧
        (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
          vote ∈ votes ∧ ∃ y : Stamp, n.A.tau (fg_to_ac n.S) vote = .ok (some y)) ∧
        goldfish_fork_choice C (fg_to_ac n.S) t (get_anchor n.A (fg_to_ac n.S) t)
          (viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree) votes.toFinset
          support_votes.toFinset (C.slot t - 1) = .ok H ∧
        B = Block.node H (C.slot t)
          (X.digest H.root (C.slot t) (proposal_attestations n.S H) votes support_votes)
          votes support_votes (proposal_attestations n.S H) n.v :=
  GoldilocksCorrectness.Proofs.Routines.lem19_tick_proposes C P X n n' t sent B hRun hBlock

end GoldilocksCorrectness.Statements.Routines
