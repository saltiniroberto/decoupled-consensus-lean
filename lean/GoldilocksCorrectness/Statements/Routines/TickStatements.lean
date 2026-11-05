module
public import GoldilocksCorrectness.Proofs.Routines.Lemma13
public import GoldilocksCorrectness.Proofs.Routines.Lemma14
public import GoldilocksCorrectness.Proofs.Routines.Lemma15

@[expose] public section

/-!
# The statements about the node's tick

The audited statements about what a successful tick of the node (`tick`) did at the two duty times
of its slot, each proved in its own file under `GoldilocksCorrectness/Proofs/Routines/`: at the
vote time it revoked the locks (Lemma 13) and, when it sent a Goldfish vote, that vote is the end
of the Goldfish fork choice from the anchor of the revoked AC state (Lemma 14); at the support
cutoff it ran the confirmation update (Lemma 15). With them, `mem_voter_block_tree_iff_at`: the voter's tree
holds the blocks `VoterTreeAt` describes at the view freeze.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 13, the tick at the vote time revokes the locks.** If the tick at `t` answered, `t` is
the vote time of its slot, `C.t_ (C.slot t) + C.Δ`, and the node's stored `awakeSince` is some time
at most the duty window's start `duty_window_start C (C.slot t)`, then the revocation of that slot
(`revoke_locks`) answered some `A'` on the node's AC state with its expired entries removed
(`expireLocks n.A t`), over the frame `fg_to_ac n.S`, and the tick's AC state has `A'`'s lock
entries.

Why: the tick's first step keeps a present `awakeSince`, so the duty test passes; its tick of the
available chain deletes the expired entries, takes the `if` at the vote time, revokes the locks,
and runs the Goldfish vote duty, which writes no lock entry; the confirmation update does not run
at the vote time; the proposal and the attestation duty write no lock entry.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees; `X`: the digest;
- `n`: the node state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent;
- `A'`: the answer of the revocation.

Read aloud: if the tick at `t` answered, `t` is the vote time of its slot, and the node had been
awake since the duty window's start, then the revocation of that slot answered some `A'` on the
node's AC state with its expired entries removed, and the tick's AC state has `A'`'s lock
entries. -/
theorem lem13_tick_revokes_locks (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V))
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    -- `t` is the vote time of its slot
    (hVoteTime : t = C.t_ (C.slot t) + C.Δ)
    -- the node has been awake since the duty window's start of that slot, or earlier
    (hAwake : ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t)) :
    -- then the revocation answered `A'`, and the tick left `A'`'s lock entries
    ∃ A' : ACState V,
      revoke_locks P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A' ∧
        n'.A.lock_entries = A'.lock_entries :=
  GoldilocksCorrectness.Proofs.Routines.lem13_tick_revokes_locks C P X n n' t sent hRun hVoteTime
    hAwake

/-- **Lemma 14, the vote a tick sends is the end of the Goldfish fork choice.** If the tick at `t`
answered and sent the Goldfish vote `vote`, then `t` is the vote time of its slot,
`C.t_ (C.slot t) + C.Δ`; `vote` is the node's validator's vote for that slot, and the validator is
a member of that slot's committee; the revocation of that slot (`revoke_locks`) answered some `A'`
on the node's AC state with its expired entries removed (`expireLocks n.A t`), over the frame
`fg_to_ac n.S`; for the sets `votes` and `support_votes` counted on the node's AC state
(`CountedVotes`) and the answer `vbt` of the voter's tree (`voter_block_tree`), the Goldfish fork
choice from the anchor of `A'` (`get_anchor A' (fg_to_ac n.S) t`) through the viable tree of `vbt`
answered a block `H` whose root is `vote`'s head; and the tick's AC state has `A'`'s lock entries.

Why: only the Goldfish vote duty sends a Goldfish vote, inside the `if` at the vote time, so the
duty test passed and the revocation ran first; the duty runs on `A'` and sends, in the `if` on the
committee, the vote for the root of the block its fork choice reached; the revocation writes the
lock entries only, so the counted sets and the voter's tree read on `A'` are those read on `n.A`;
the lock entries are Lemma 13's.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees; `X`: the digest;
- `n`: the node state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `vote`: the vote sent;
- `A'`: the answer of the revocation; `votes`, `support_votes`: the counted sets; `vbt`: the
  voter's tree; `H`: the block the fork choice reaches.

Read aloud: a vote the tick at `t` sent is a vote of `t`'s slot by the node's validator, who is in
that slot's committee; the revocation answered `A'`; the vote's head is the root of the block `H`
the Goldfish fork choice reaches from the anchor of `A'`, through the viable tree of the voter's
tree `vbt`, counting the sets `CountedVotes` describes; and the tick left `A'`'s lock entries. -/
theorem lem14_tick_vote_walk (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (vote : GoldfishVote V)
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    -- the tick sent the Goldfish vote `vote`
    (hVote : NamedObject.gfVote vote ∈ sent) :
    -- then `t` is the vote time, `vote` is the validator's, a committee member's, for that slot
    t = C.t_ (C.slot t) + C.Δ ∧ vote.val_index = n.v ∧ vote.slot = C.slot t ∧
      n.v ∈ P.committee (C.slot t) ∧
      -- and its head is the root of the fork choice's answer from the revoked state's anchor
      ∃ (A' : ACState V) (votes support_votes : Finset (GoldfishVote V))
        (vbt : Finset (Block V)) (H : Block V),
        revoke_locks P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A' ∧
        CountedVotes C n.A (fg_to_ac n.S) (C.slot t) votes support_votes ∧
        voter_block_tree C n.A (fg_to_ac n.S) (C.slot t) = .ok vbt ∧
        goldfish_fork_choice C (fg_to_ac n.S) t (get_anchor A' (fg_to_ac n.S) t)
          (viable_tree (fg_to_ac n.S) vbt) votes support_votes (C.slot t - 1) = .ok H ∧
        vote.head = H.root ∧ n'.A.lock_entries = A'.lock_entries :=
  GoldilocksCorrectness.Proofs.Routines.lem14_tick_vote_walk C P X n n' t sent vote hRun hVote

/-- **Lemma 15, the tick at the support cutoff runs the confirmation update.** If the tick at `t`
answered, `t` is the support cutoff of its slot, `C.t_ (C.slot t) + 2 * C.Δ`, and the node's stored
`awakeSince` is some time at most the duty window's start `duty_window_start C (C.slot t)`, then
the confirmation update of that slot (`update_confirmation`) answered some `A''` on the node's AC
state with its expired entries removed (`expireLocks n.A t`), over the frame `fg_to_ac n.S`, and
the tick's AC state has `A''`'s saved confirmations, fast blocks, lock entries and record of the
confirmed tip.

Why: the duty test passes as for Lemma 13; the tick of the available chain deletes the expired
entries, does not take the `if` at the vote time (the support cutoff is one `C.Δ` later, and
`C.Δ` is positive), and runs the confirmation update; the proposal, when it runs, admits a block,
which writes stamps and votes only, and the attestation duty, when it runs, leaves the AC state
unchanged.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees; `X`: the digest;
- `n`: the node state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent;
- `A''`: the answer of the confirmation update.

Read aloud: if the tick at `t` answered, `t` is the support cutoff of its slot, and the node had
been awake since the duty window's start, then the update of that slot answered some `A''` on the
node's AC state with its expired entries removed, and the tick's AC state has `A''`'s saved
confirmations, fast blocks, lock entries and confirmed tip. -/
theorem lem15_tick_updates_confirmation (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V))
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    -- `t` is the support cutoff of its slot
    (hCutoff : t = C.t_ (C.slot t) + 2 * C.Δ)
    -- the node has been awake since the duty window's start of that slot, or earlier
    (hAwake : ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t)) :
    -- then the update answered `A''`, and the tick left its four confirmation fields
    ∃ A'' : ACState V,
      update_confirmation C P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A'' ∧
        n'.A.saved_confirmation = A''.saved_confirmation ∧ n'.A.fast_blocks = A''.fast_blocks ∧
        n'.A.lock_entries = A''.lock_entries ∧ n'.A.latest_confirmed = A''.latest_confirmed :=
  GoldilocksCorrectness.Proofs.Routines.lem15_tick_updates_confirmation C P X n n' t sent hRun
    hCutoff hAwake

omit [Fintype V] [RootOrder] in
/-- The voter's tree of slot `s'` (`voter_block_tree`) holds exactly the blocks `VoterTreeAt`
describes at the view freeze `C.t_ (s' − 1) + 3 · C.Δ`.

Why: `mem_voter_block_tree_iff`, whose right side is `VoterTreeAt`'s body at that time.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `s'`: the slot of the vote;
- `vbt`: the voter's tree; `B`: the block.

Read aloud: a block is in the voter's tree exactly when it is a stamped block of the frame's tree
that is stamped strictly before the view freeze or leads to a slot-`s'` block. -/
theorem mem_voter_block_tree_iff_at (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot)
    (vbt : Finset (Block V)) (h : voter_block_tree C A Φ s' = .ok vbt) (B : Block V) :
    B ∈ vbt ↔ VoterTreeAt A Φ (C.t_ (s' - 1) + 3 * C.Δ) s' B :=
  GoldilocksCorrectness.Proofs.Routines.mem_voter_block_tree_iff C A Φ s' vbt h B

end GoldilocksCorrectness.Statements.Routines
