module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Statements.Routines.TickStatements

@[expose] public section

/-!
# The statements about the node's tick, over a model

The audited statements of `GoldilocksCorrectness/Statements/Routines/TickStatements.lean` over a
model `M` whose facts `F` hold: Lemma 13 and Lemma 15 are the tick's facts T4 and T6
(`TickFacts2`), Lemma 14 the tick's fact T5 (`TickFacts3.tick_vote_head`), each from a node state
satisfying the model's node invariant; and `mem_voter_block_tree_iff_at` reads the record's voter's
tree `VoterTree`. The record has no member for the revocation, the confirmation update, the voter's
tree as a routine or the Goldfish fork choice: Lemmas 13 and 15 conclude the predicates
`LocksRevoked` and `ConfirmationUpdated`, and Lemma 14 the walk of the Goldfish vote over `n`
(`HeadOf`) from the anchor over `n`'s frame with the lock entries of the tick's answer
(`AnchorAt`), with the wake condition `AwakeFor`, which the spec's vote duty runs behind.

None of the four has a recovery: each landed conclusion names the answer of a routine the record
does not have (`revoke_locks`, `update_confirmation`, `voter_block_tree`, `goldfish_fork_choice`),
and the record's predicates give no such answer back.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **Lemma 13 over the record, the tick at the vote time revokes the locks.** A tick at the vote
time of the slot of `t`, from a node state satisfying the model's node invariant and awake since
that slot's duty window started, leaves the lock entries of the revocation of that slot
(`LocksRevoked`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values (with the committees) and the digest; `n`: the node
  state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent.

Read aloud: at the vote time, an awake node's tick revokes its locks. -/
theorem lem13_tick_revokes_locks [RootOrder] {M : GoldilocksModel V} (F : Facts M) (C : Config)
    (P : Provisional V) (X : External V) (n n' : M.N) (t : Time) (sent : List (NamedObject V))
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ M.tick C P X n t)
    -- `n` satisfies the model's node invariant
    (hInv : M.nodeInv C P X n)
    -- `t` is the vote time of its slot
    (hVoteTime : t = C.t_ (C.slot t) + C.Δ)
    -- the node has been awake since the duty window's start of that slot, or earlier
    (hAwake : AwakeFor M C n (C.slot t)) :
    LocksRevoked M P n t (C.slot t) n' :=
  F.tk2.tick_voteTime_locks C P X n t n' sent hRun hInv hVoteTime hAwake

/-- **Lemma 14 over the record, the vote a tick sends is the end of the walk.** A Goldfish vote
`vote` that a tick sends, from a node state satisfying the model's node invariant, is sent at the
vote time of the slot of `t`; it is the node's validator's vote for that slot; the validator is in
that slot's committee; the node has been awake since that slot's duty window started; and
`vote.head` is the root of the end `H` of the walk of the Goldfish vote of that slot over `n`
(`HeadOf`), from the anchor over `n`'s frame with the lock entries of `n'`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values (with the committees) and the digest; `n`: the node
  state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `vote`: the vote sent.

Read aloud: a vote the tick at `t` sent is an awake committee member's vote at the vote time, for
the root of the end of its walk from the anchor its revoked locks give. -/
theorem lem14_tick_vote_walk [RootOrder] {M : GoldilocksModel V} (F : Facts M) (C : Config)
    (P : Provisional V) (X : External V) (n n' : M.N) (t : Time) (sent : List (NamedObject V))
    (vote : GoldfishVote V)
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ M.tick C P X n t)
    -- `n` satisfies the model's node invariant
    (hInv : M.nodeInv C P X n)
    -- the tick sent the Goldfish vote `vote`
    (hVote : NamedObject.gfVote vote ∈ sent) :
    t = C.t_ (C.slot t) + C.Δ ∧ vote.val_index = n.v ∧ vote.slot = C.slot t ∧
      n.v ∈ P.committee (C.slot t) ∧ AwakeFor M C n (C.slot t) ∧
      ∃ H : Block V, HeadOf M C n (AnchorAt M (M.fg_to_ac n) n'.lockEntries t) t (C.slot t) H ∧
        vote.head = H.root :=
  F.tk3.tick_vote_head C P X n t n' sent vote hRun hInv hVote

/-- **Lemma 15 over the record, the tick at the support cutoff runs the confirmation update.** A
tick at the support cutoff of the slot of `t`, from a node state satisfying the model's node
invariant and awake since that slot's duty window started, leaves what the confirmation update of
that slot leaves (`ConfirmationUpdated`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values (with the committees) and the digest; `n`: the node
  state the tick starts from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent.

Read aloud: at the support cutoff, an awake node's tick updates its confirmation. -/
theorem lem15_tick_updates_confirmation [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    (C : Config) (P : Provisional V) (X : External V) (n n' : M.N) (t : Time)
    (sent : List (NamedObject V))
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ M.tick C P X n t)
    -- `n` satisfies the model's node invariant
    (hInv : M.nodeInv C P X n)
    -- `t` is the support cutoff of its slot
    (hCutoff : t = C.t_ (C.slot t) + 2 * C.Δ)
    -- the node has been awake since the duty window's start of that slot, or earlier
    (hAwake : AwakeFor M C n (C.slot t)) :
    ConfirmationUpdated M C P n t (C.slot t) n' :=
  F.tk2.tick_supportCutoff_confirmation C P X n t n' sent hRun hInv hCutoff hAwake

/-- The voter's tree of slot `s'` over the record (`VoterTree`) holds exactly the blocks
`VoterTreeAt` describes at the view freeze `C.t_ (s' − 1) + 3 · C.Δ` (the record form of
`mem_voter_block_tree_iff_at`).

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot of the vote;
  `B`: the block.

Read aloud: a block is in the voter's tree exactly when it is a stamped block of the frame's tree
that is stamped strictly before the view freeze or leads to a slot-`s'` block. -/
theorem mem_voter_block_tree_iff_at {M : GoldilocksModel V} (C : Config) (n : M.N) (s' : Slot)
    (B : Block V) :
    B ∈ VoterTree M C n s' ↔ VoterTreeAt M n (C.t_ (s' - 1) + 3 * C.Δ) s' B := by
  simp only [VoterTree, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

end GoldilocksCorrectness.Record.Statements.Routines
