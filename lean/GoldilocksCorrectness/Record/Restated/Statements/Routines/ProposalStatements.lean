module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements

@[expose] public section

/-!
# The statements about the node's proposal, over a model

The audited statement of `GoldilocksCorrectness/Statements/Routines/ProposalStatements.lean`,
Lemma 19, over a model `M` whose facts `F` hold: the tick's fact T7 (`TickFacts3.tick_proposal`).
The record has no member for the Goldfish fork choice: the parent is the end of the walk counting
the node's votes of the previous slot from the node's anchor (`PoolHeadOf`); and the support votes
are those that resolve in the node (`ResolvesAt`). The statement takes a node state satisfying the
model's node invariant, and says, beside the landed conclusion, that the proposer has been awake
since the slot's proposal window started (`AwakeForProposal`): the spec proposes only then.

The recovery section states Lemma 19 again, as the landed statement (`type_of%`), at every node
state satisfying the spec's model's node invariant, and proves it from its record form: the walk's
end is the spec's fork choice's answer (`goldfish_fork_choice_eq_ok_iff_walkEnd`) and a vote
resolves in the record's sense exactly when the spec's resolution time answers a time
(`goldilocks_resolvesAt`), both when no two blocks of the frame's tree share a root, a clause of the
node invariant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **Lemma 19 over the record, the block a tick sends is the node's proposal.** A block `B` that a
tick sends, from a node state satisfying the model's node invariant, is sent at the start of the
slot of `t`, a slot other than slot `0`, by that slot's proposer, awake since that slot's proposal
window started; and `B` is the block of that slot whose parent `H` is the end of the walk counting
`n`'s votes of the previous slot from `n`'s anchor, whose votes are `n`'s list `votes` of the
previous slot, whose support votes are a list `support_votes` of exactly those of `votes` that
resolve in `n`, whose attestations are those a child of `H` includes, whose root is the digest of
that content, and whose proposer is the node's validator.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values (with the proposers) and the digest; `n`: the node
  state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `B`: the block sent.

Read aloud: a block the tick at `t` sent is the awake proposer's block at its slot's start, built
on the end of the walk from the node's anchor, with the node's votes of the previous slot. -/
theorem lem19_tick_proposes [RootOrder] {M : GoldilocksModel V} (F : Facts M) (C : Config)
    (P : Provisional V) (X : External V) (n n' : M.N) (t : Time) (sent : List (NamedObject V))
    (B : Block V)
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ M.tick C P X n t)
    -- `n` satisfies the model's node invariant
    (hInv : M.nodeInv C P X n)
    -- the tick sent the block `B`
    (hBlock : NamedObject.block B ∈ sent) :
    0 < C.slot t ∧ t = C.t_ (C.slot t) ∧ n.v = P.proposer (C.slot t) ∧
      AwakeForProposal M C n (C.slot t) ∧
      ∃ (H : Block V) (votes support_votes : List (GoldfishVote V)),
        votes = n.votesHeld (C.slot t - 1) ∧
        (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
          vote ∈ votes ∧ ∃ y : Stamp, ResolvesAt M n vote y) ∧
        PoolHeadOf M C n (M.get_anchor n t) t (C.slot t - 1) H ∧
        B = Block.node H (C.slot t)
          (X.digest H.root (C.slot t) (M.proposal_attestations n H) votes support_votes)
          votes support_votes (M.proposal_attestations n H) n.v :=
  F.tk3.tick_proposal C P X n t n' sent B hRun hInv hBlock

/-! ## At the spec's model -/

/-- The landed statement `lem19_tick_proposes`, recovered from its record form at the spec's model,
at every node state satisfying the spec's model's node invariant.

Read aloud: the landed Lemma 19 holds at every node state satisfying the invariant. -/
theorem lem19_tick_proposes_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (B : Block V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes V _ _ _ C P X n n'
        t sent B) := by
  intro C P X n n' t sent B hI hRun hB
  obtain ⟨hpos, ht, hprop, -, H, votes, sv, hvotes, hsv, ⟨votes', sv', ⟨hv', hsv'⟩, hW⟩, hBeq⟩ :=
    lem19_tick_proposes goldilocksFacts C P X n n' t sent B hRun hI hB
  have hRoots := GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hI.1
  have hvotes' : votes = n.A.gf_votes (C.slot t - 1) := hvotes
  have hres : ∀ vote : GoldfishVote V,
      (∃ y : Stamp, n.A.tau (fg_to_ac n.S) vote = .ok (some y)) ↔
        ∃ y : Stamp, ResolvesAt (Model.goldilocks (V := V)) n vote y :=
    fun vote => exists_congr (fun y => goldilocks_resolvesAt n vote y hRoots)
  have e1 : votes.toFinset = votes' := by
    rw [hv', goldilocksFacts.rd.votesHeldSet_eq, hvotes]
  have e2 : sv.toFinset = sv' := by
    ext vote
    rw [List.mem_toFinset, hsv vote, hsv' vote, goldilocksFacts.rd.votesHeldSet_eq,
      List.mem_toFinset, ← hvotes]
  have hsub : viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree ⊆ (fg_to_ac n.S).tree :=
    fun D hD => ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff _ _ D).1 hD).1
  refine ⟨hpos, ht, hprop, H, votes, sv, hvotes', fun vote => by rw [hsv vote, hres vote], ?_,
    hBeq⟩
  rw [e1, e2]
  exact (GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C
    (fg_to_ac n.S) t _ _ votes' sv' _
    (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots)).2 hW

end GoldilocksCorrectness.Record.Statements.Routines
