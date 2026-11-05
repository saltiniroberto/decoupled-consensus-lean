module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Routines.TickDefs

@[expose] public section

/-!
# The votes a Goldfish vote counts, over a model

The AC-store definitions of `GoldilocksCorrectness/Statements/Routines/TickDefs.lean` over a
model `M`, each read on a node state `n : M.N`: the time at which a Goldfish vote resolves in `n`
(`ResolvesAt`), the two sets of votes the Goldfish vote of a slot counts (`CountedVotesAt`,
`CountedVotes`), membership in the voter's tree with the view freeze a parameter (`VoterTreeAt`),
and a node awake since a slot's duty window started (`AwakeFor`). The landed `expireLocks` has no
twin: the record has no decomposition of the tick.

What the tick does to the locks and the confirmations at two duty times of a slot is stated as two
predicates over the readers of the node states before and after: `LocksRevoked` (the revocation of
the locks at the vote time, with `Opposes`, `OpponentsOf`, `MoveCandidate` and `MovesTo`) and
`ConfirmationUpdated` (the confirmation update at the support cutoff, with `EarlyVotes`,
`LateVotes`, `SupportVotes`, `ConfirmationScore`, `ConfirmationEligible` and `Lockable`). The walk
the update reads is `WalkEnd` at the model's tie-break `M.tieBreak`. At the spec's model, the spec's
`revoke_locks` and `update_confirmation` satisfy them
(`Record/Restated/Statements/Routines/TickLocksGoldilocks.lean`).

At the spec's model, `VoterTreeAt` is the landed definition, and `ResolvesAt` and the counted sets
are the landed ones when no two blocks of the node's tree share a root; the theorems are on
`Record/Restated/Statements/Routines/TickDefsGoldilocks.lean`.

What the tick sends is described with the walks of its duties and the validator client's
attestation: `AwakeForProposal` (the proposal's wake condition), `LockedViableBlocks` and
`AnchorAt` (the anchor over a frame and a set of lock entries), `VoterTree`, `HeadOf` (the walk of
the Goldfish vote), `PoolHeadOf` (the walk of the proposal and of the attestation duty, the spec's
`get_head`), `AttestationFrom` (the attestation the client builds) and `AttestationRecorded` (the
record after it). The facts are on `Record/TickFacts3.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (WalkEnd)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `ResolvesAt M n vote y`: the Goldfish vote `vote` resolves at the stamp `y` in the node state
`n`: `vote` is stamped, some block `H` of the tree `(M.fg_to_ac n).tree` has the root `vote.head`
and a slot at most `vote.slot`, `H` is stamped, and `y` is the later of the two stamps.

The variables:
- `M`: the model;
- `n`: the node state; `vote`: the vote; `y`: the stamp.

Read aloud: `vote` resolves at `y` in `n`. -/
def ResolvesAt (M : GoldilocksModel V) (n : M.N) (vote : GoldfishVote V) (y : Stamp) : Prop :=
  ∃ (τv τH : Stamp) (H : Block V), n.voteStamp vote = some τv ∧ H ∈ (M.fg_to_ac n).tree ∧
    H.root = vote.head ∧ H.slot ≤ vote.slot ∧ n.blockStamp H = some τH ∧ y = max τv τH

/-- `CountedVotesAt M n t s' votes support_votes`: `votes` and `support_votes` are the two sets of
votes the Goldfish vote of slot `s'` counts in the node state `n` with the view freeze the time `t`.
A vote is in `votes` exactly when it is a vote of `M.votesHeldSet n (s' - 1)` stamped strictly
before `t`, or a vote included in a slot-`s'` block of the tree of `M.fg_to_ac n`
(`M.included_votes`). A vote is in `support_votes` exactly when it is a vote of
`M.votesHeldSet n (s' - 1)` stamped strictly before `t` that resolves in `n` strictly before `t`
(`ResolvesAt`), or a support vote included in a slot-`s'` block of that tree
(`M.included_support_votes`) whose head is resolved in that tree (`resolved`). This is
`CountedVotes` with the view freeze a parameter.

The variables:
- `M`: the model;
- `n`: the node state; `t`: the view freeze;
- `s'`: the slot of the vote; `votes`, `support_votes`: the two sets.

Read aloud: a vote is counted exactly when it is a slot-`(s' − 1)` vote of `n` stamped strictly
before `t`, or a vote included in a slot-`s'` block of the tree of `M.fg_to_ac n`; it is a support
vote exactly when it is a counted vote of `n` that also resolves strictly before `t`, or an
included support vote whose head is resolved in that tree. -/
def CountedVotesAt (M : GoldilocksModel V) (n : M.N) (t : Time) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V)) : Prop :=
  (∀ vote : GoldfishVote V, vote ∈ votes ↔
      (vote ∈ M.votesHeldSet n (s' - 1) ∧ ∃ τ : Stamp, n.voteStamp vote = some τ ∧
        τ < (t : Stamp)) ∨
      vote ∈ M.included_votes (M.fg_to_ac n) s') ∧
  (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      (vote ∈ M.votesHeldSet n (s' - 1) ∧
        (∃ τ : Stamp, n.voteStamp vote = some τ ∧ τ < (t : Stamp)) ∧
        ∃ y : Stamp, ResolvesAt M n vote y ∧ y < (t : Stamp)) ∨
      (vote ∈ M.included_support_votes (M.fg_to_ac n) s' ∧
        resolved (M.fg_to_ac n).tree vote = .ok true))

/-- `CountedVotes M C n s' votes support_votes`: `votes` and `support_votes` are the two sets of
votes the Goldfish vote of slot `s'` counts in the node state `n`: `CountedVotesAt` at the view
freeze of slot `s' − 1`, `C.t_ (s' - 1) + 3 * C.Δ`. At `s' = 0` the slot `s' − 1` reads as slot
`0`.

The variables:
- `M`: the model;
- `C`: the configuration; `n`: the node state;
- `s'`: the slot of the vote; `votes`, `support_votes`: the two sets.

Read aloud: a vote is counted exactly when it is a slot-`(s' − 1)` vote of `n` stamped strictly
before the freeze, or a vote included in a slot-`s'` block of the tree of `M.fg_to_ac n`; it is a
support vote exactly when it is a counted vote of `n` that also resolves strictly before the
freeze, or an included support vote whose head is resolved in that tree. -/
def CountedVotes (M : GoldilocksModel V) (C : Config) (n : M.N) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V)) : Prop :=
  (∀ vote : GoldfishVote V, vote ∈ votes ↔
      (vote ∈ M.votesHeldSet n (s' - 1) ∧ ∃ τ : Stamp, n.voteStamp vote = some τ ∧
        τ < ((C.t_ (s' - 1) + 3 * C.Δ : Time) : Stamp)) ∨
      vote ∈ M.included_votes (M.fg_to_ac n) s') ∧
  (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      (vote ∈ M.votesHeldSet n (s' - 1) ∧
        (∃ τ : Stamp, n.voteStamp vote = some τ ∧
          τ < ((C.t_ (s' - 1) + 3 * C.Δ : Time) : Stamp)) ∧
        ∃ y : Stamp, ResolvesAt M n vote y ∧
          y < ((C.t_ (s' - 1) + 3 * C.Δ : Time) : Stamp)) ∨
      (vote ∈ M.included_support_votes (M.fg_to_ac n) s' ∧
        resolved (M.fg_to_ac n).tree vote = .ok true))

/-- `VoterTreeAt M n t s' B`: `B` is a block of `(M.fg_to_ac n).tree` with a stamp in `n`, and
the stamp is strictly before `t`, or `B` is a slot-`s'` block of that tree or an ancestor of one.

The variables:
- `M`: the model;
- `n`: the node state; `t`: the view freeze; `s'`: the slot of the vote;
- `B`: the block.

Read aloud: `B` is a stamped block of the tree of `M.fg_to_ac n` that is early or leads to a
slot-`s'` block. -/
def VoterTreeAt (M : GoldilocksModel V) (n : M.N) (t : Time) (s' : Slot) (B : Block V) : Prop :=
  B ∈ (M.fg_to_ac n).tree ∧ ∃ τ : Stamp, n.blockStamp B = some τ ∧
    (τ < (t : Stamp) ∨ ∃ B' ∈ (M.fg_to_ac n).tree, B'.slot = s' ∧ B.AncestorEq B')

/-- `AwakeFor M C n s`: the node has been awake since the start of slot `s`'s duty window or
earlier: `n.awakeSince` is a time at most `duty_window_start C s`.

The variables:
- `M`: the model;
- `C`: the configuration; `n`: the node state; `s`: the slot.

Read aloud: `n` was awake since the duty window's start of slot `s`. -/
def AwakeFor (M : GoldilocksModel V) (C : Config) (n : M.N) (s : Slot) : Prop :=
  ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C s

/-! ## The revocation of the locks -/

/-- `Opposes M n B' vote`: the head of the Goldfish vote `vote` conflicts with the block `B'` in
the node state `n`: some block of the tree of `M.fg_to_ac n` has the root `vote.head` and
conflicts with `B'`.

The variables:
- `M`: the model; `n`: the node state;
- `B'`: the block; `vote`: the vote.

Read aloud: `vote` opposes `B'` in `n`. -/
def Opposes (M : GoldilocksModel V) (n : M.N) (B' : Block V) (vote : GoldfishVote V) : Prop :=
  ∃ H ∈ (M.fg_to_ac n).tree, H.root = vote.head ∧ H.conflicts B' = true

/-- `OpponentsOf M n votes eqv B' o`: `o` is the set of the validators not in `eqv` with a vote in
`votes` that resolves in `n` (`ResolvesAt`) and opposes `B'` (`Opposes`).

The variables:
- `M`: the model; `n`: the node state;
- `votes`: the votes counted; `eqv`: the validators counted out;
- `B'`: the block; `o`: the set of validators.

Read aloud: `o` is the set of the validators outside `eqv` whose resolving vote in `votes`
conflicts with `B'`. -/
def OpponentsOf (M : GoldilocksModel V) (n : M.N) (votes : Finset (GoldfishVote V))
    (eqv : Finset V) (B' : Block V) (o : Finset V) : Prop :=
  ∀ v : V, v ∈ o ↔ v ∉ eqv ∧ ∃ vote ∈ votes, vote.val_index = v ∧
    (∃ y : Stamp, ResolvesAt M n vote y) ∧ Opposes M n B' vote

/-- `MoveCandidate M P n s e B''`: `B''` is a block the lock entry `e` may move back to in the
revocation of slot `s`: a block of the tree of `M.fg_to_ac n` other than the genesis block, `e.B`
or an ancestor of `e.B`, whose opponents among the slot-`(s − 1)` votes `n` holds, the validators
with two of those votes counted out, are, counted twice, fewer than the committee of slot `s − 1`.

The variables:
- `M`: the model; `P`: the provisional parameters, with the committees;
- `n`: the node state; `s`: the slot of the revocation;
- `e`: the lock entry; `B''`: the block.

Read aloud: `B''` is a non-genesis block of `e`'s chain that fewer than half of the committee of
slot `s − 1` oppose. -/
def MoveCandidate (M : GoldilocksModel V) (P : Provisional V) (n : M.N) (s : Slot) (e : M.LE)
    (B'' : Block V) : Prop :=
  B'' ∈ (M.fg_to_ac n).tree ∧ B'' ≠ Block.genesis ∧ B''.AncestorEq e.B ∧
    ∃ o : Finset V, OpponentsOf M n (M.votesHeldSet n (s - 1))
      (M.equivocators (M.votesHeldSet n (s - 1))) B'' o ∧
      2 * o.card < (P.committee (s - 1)).card

/-- `MovesTo M P n s e B'`: `B'` is the block the lock entry `e` moves back to in the revocation of
slot `s`: `B'` is a block `e` may move back to (`MoveCandidate`), and every such block is `B'` or
an ancestor of `B'`.

The variables:
- `M`: the model; `P`: the provisional parameters, with the committees;
- `n`: the node state; `s`: the slot of the revocation;
- `e`: the lock entry; `B'`: the block.

Read aloud: `B'` is the deepest block of `e`'s chain that fewer than half of the committee of the
previous slot oppose. -/
def MovesTo (M : GoldilocksModel V) (P : Provisional V) (n : M.N) (s : Slot) (e : M.LE)
    (B' : Block V) : Prop :=
  MoveCandidate M P n s e B' ∧ ∀ B'' : Block V, MoveCandidate M P n s e B'' → B''.AncestorEq B'

/-- `LocksRevoked M P n t s n'`: what the revocation of the locks of slot `s` at the time `t`
leaves in the lock entries of `n'`, from the node state `n`:

1. at `s = 0`, the lock entries of `n'` are those of `n` whose deadline is after `t`;
2. at `s ≥ 1`, every lock entry of `n'` comes from a lock entry `e` of `n` live at `t`
   (`M.is_live n t e`), with `e`'s deadline and the block `e` moves back to (`MovesTo`); and every
   lock entry `e` of `n` live at `t` with a block `B'` to move back to has an entry in `n'` with
   the block `B'` and `e`'s deadline.

The other readers of `n'` are not described here.

The variables:
- `M`: the model; `P`: the provisional parameters, with the committees;
- `n`: the node state before the revocation; `t`: the time; `s`: the slot;
- `n'`: the node state after it.

Read aloud: `n'` holds `n`'s live locks, each pulled back to the deepest block of its chain that
fewer than half of the previous slot's committee oppose, and no other. -/
def LocksRevoked (M : GoldilocksModel V) (P : Provisional V) (n : M.N) (t : Time) (s : Slot)
    (n' : M.N) : Prop :=
  (s = 0 ∧ ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d) ∨
  (1 ≤ s ∧
    (∀ e' ∈ n'.lockEntries, ∃ e ∈ n.lockEntries, M.is_live n t e = true ∧
      e'.d = e.d ∧ MovesTo M P n s e e'.B) ∧
    (∀ e ∈ n.lockEntries, M.is_live n t e = true → ∀ B' : Block V, MovesTo M P n s e B' →
      ∃ e' ∈ n'.lockEntries, e'.B = B' ∧ e'.d = e.d))

/-! ## The confirmation update -/

open Classical in
/-- `EarlyVotes M C n s'`: the slot-`s'` Goldfish votes the node state `n` holds that resolve in
`n` (`ResolvesAt`) strictly before `C.t_ s' + 2 * C.Δ`.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot.

Read aloud: the early votes of slot `s'` in `n`. -/
noncomputable def EarlyVotes (M : GoldilocksModel V) (C : Config) (n : M.N) (s' : Slot) :
    Finset (GoldfishVote V) :=
  {vote ∈ M.votesHeldSet n s' |
    ∃ y : Stamp, ResolvesAt M n vote y ∧ y < ((C.t_ s' + 2 * C.Δ : Time) : Stamp)}

open Classical in
/-- `LateVotes M C n s'`: the slot-`s'` Goldfish votes the node state `n` holds that `n` stamped
strictly before `C.t_ s' + 6 * C.Δ`.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot.

Read aloud: the late votes of slot `s'` in `n`. -/
noncomputable def LateVotes (M : GoldilocksModel V) (C : Config) (n : M.N) (s' : Slot) :
    Finset (GoldfishVote V) :=
  {vote ∈ M.votesHeldSet n s' |
    ∃ τ : Stamp, n.voteStamp vote = some τ ∧ τ < ((C.t_ s' + 6 * C.Δ : Time) : Stamp)}

/-- `SupportVotes M C n s'`: the early votes of slot `s'` in `n` (`EarlyVotes`) whose validator has
no second vote among the late votes (`LateVotes`, `M.no_second_vote_in`).

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot.

Read aloud: the support votes of the confirmation update of slot `s'` in `n`. -/
noncomputable def SupportVotes (M : GoldilocksModel V) (C : Config) (n : M.N) (s' : Slot) :
    Finset (GoldfishVote V) :=
  {vote ∈ EarlyVotes M C n s' | M.no_second_vote_in (LateVotes M C n s') vote = true}

/-- `ConfirmationScore M C n s' B`: the Goldfish score of the block `B` over the support votes of
slot `s'` (`SupportVotes`), for the slot `s'`, in the tree of `M.fg_to_ac n` (the library's
`goldfish_score`).

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot; `B`: the block.

Read aloud: `B`'s score in the confirmation update of slot `s'`. -/
noncomputable def ConfirmationScore [RootOrder] (M : GoldilocksModel V) (C : Config) (n : M.N)
    (s' : Slot) (B : Block V) : DC.DRE ℕ :=
  goldfish_score (M.fg_to_ac n) (SupportVotes M C n s') (SupportVotes M C n s') s' B

/-- `ConfirmationEligible M C n s' B`: whether the number of validators with a late vote of slot
`s'` (`M.voters_count` of `LateVotes`) is less than twice `B`'s score (`ConfirmationScore`).

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot; `B`: the block.

Read aloud: `B` passes the count test of the confirmation update of slot `s'`. -/
noncomputable def ConfirmationEligible [RootOrder] (M : GoldilocksModel V) (C : Config) (n : M.N)
    (s' : Slot) (B : Block V) : DC.DRE Bool := do
  return M.voters_count (LateVotes M C n s') < 2 * (← ConfirmationScore M C n s' B)

/-- `Lockable M C P n s' C' B`: `B` is a block the confirmation update of slot `s'` may lock under
the confirmation `C'`: a block of the tree of `M.fg_to_ac n` other than the genesis block, `C'` or
an ancestor of `C'`, that passes the fast test (`fast_test` over the support votes,
`SupportVotes`) or the slow test (`M.slow_test`).

The variables:
- `M`: the model; `C`: the configuration; `P`: the provisional parameters, with the committees;
- `n`: the node state; `s'`: the slot; `C'`: the confirmation; `B`: the block.

Read aloud: `B` is a non-genesis block of `C'`'s chain that a lock test accepts. -/
noncomputable def Lockable [RootOrder] (M : GoldilocksModel V) (C : Config) (P : Provisional V)
    (n : M.N) (s' : Slot) (C' B : Block V) : Prop :=
  B ∈ (M.fg_to_ac n).tree ∧ B ≠ Block.genesis ∧ B.AncestorEq C' ∧
    (fast_test P (M.fg_to_ac n) (SupportVotes M C n s') s' B = .ok true ∨
      M.slow_test C n s' B = true)

/-- `ConfirmationUpdated M C P n t s n'`: what the confirmation update of slot `s` at the time `t`
leaves in `n'`, from the node state `n`. Write `s'` for `s − 1` and `Φ` for `M.fg_to_ac n`.

1. At `s = 0`: the saved confirmations, the fast blocks and the record of the confirmed tip of
   `n'` are `n`'s, and its lock entries are those of `n` whose deadline is after `t`.
2. At `s ≥ 1`: the walk from `Φ.F` through `Φ.tree`, with the score `ConfirmationScore` and the
   test `ConfirmationEligible`, at the model's tie-break, ends at some `H` (`WalkEnd`), and:
   - the saved confirmation of slot `s'` in `n'` is `H` when `H` passes the test, none otherwise;
     every other slot's is `n`'s;
   - when `H` does not pass the test or a lock entry of `n` live at `t` conflicts with it
     (`M.live_lock_vetoes`), the fast blocks of `n'` are empty, its record of the confirmed tip is
     `n`'s and its lock entries are those of `n` whose deadline is after `t`;
   - when `H` passes the test and no live lock entry conflicts with it: the record of the
     confirmed tip is `n`'s advanced by `H` (`M.advance`); the fast blocks are the non-genesis
     blocks of `Φ.tree` that are `H` or ancestors of `H` and pass the fast test; when no block is
     lockable (`Lockable`), the lock entries are those of `n` whose deadline is after `t`; and
     when `L` is a lockable block of which every lockable block is an ancestor or `L` itself, the
     lock entries are those of `n` whose deadline is after `t` and an entry with the block `L` and
     the deadline `C.t_ (s' + C.k) + 5 * C.Δ`.

The other readers of `n'` are not described here.

The variables:
- `M`: the model; `C`: the configuration; `P`: the provisional parameters, with the committees;
- `n`: the node state before the update; `t`: the time; `s`: the slot;
- `n'`: the node state after it.

Read aloud: the node computes the confirmation of the previous slot from the votes it holds,
saves it, and, when no live lock vetoes it, advances its confirmed tip, marks the fast blocks and
locks the deepest block of its chain that a test accepts. -/
noncomputable def ConfirmationUpdated [RootOrder] (M : GoldilocksModel V) (C : Config)
    (P : Provisional V) (n : M.N) (t : Time) (s : Slot) (n' : M.N) : Prop :=
  (s = 0 ∧ M.savedConfirmation n' = M.savedConfirmation n ∧ n'.fastBlocks = n.fastBlocks ∧
    n'.latestConfirmed = n.latestConfirmed ∧
    ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d) ∨
  (1 ≤ s ∧ ∃ H : Block V,
    @WalkEnd V M.tieBreak (M.fg_to_ac n).tree (ConfirmationScore M C n (s - 1))
      (ConfirmationEligible M C n (s - 1)) (M.fg_to_ac n).F H ∧
    n'.savedConfirmation (s - 1) =
      (if ConfirmationEligible M C n (s - 1) H = .ok true then some H else none) ∧
    (∀ j : Slot, j ≠ s - 1 → n'.savedConfirmation j = n.savedConfirmation j) ∧
    ((ConfirmationEligible M C n (s - 1) H ≠ .ok true ∨ M.live_lock_vetoes n t H = true) →
      n'.fastBlocks = ∅ ∧ n'.latestConfirmed = n.latestConfirmed ∧
      ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d) ∧
    (ConfirmationEligible M C n (s - 1) H = .ok true → M.live_lock_vetoes n t H = false →
      n'.latestConfirmed = M.advance (M.fg_to_ac n) n.latestConfirmed (some H) ∧
      (∀ B : Block V, B ∈ n'.fastBlocks ↔ B ∈ (M.fg_to_ac n).tree ∧ B ≠ Block.genesis ∧
        B.AncestorEq H ∧
        fast_test P (M.fg_to_ac n) (SupportVotes M C n (s - 1)) (s - 1) B = .ok true) ∧
      ((¬ ∃ B : Block V, Lockable M C P n (s - 1) H B) →
        ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d) ∧
      (∀ L : Block V, Lockable M C P n (s - 1) H L →
        (∀ B : Block V, Lockable M C P n (s - 1) H B → B.AncestorEq L) →
        (∀ e' ∈ n'.lockEntries, (e' ∈ n.lockEntries ∧ t < e'.d) ∨
          (e'.B = L ∧ e'.d = C.t_ (s - 1 + C.k) + 5 * C.Δ)) ∧
        (∀ e ∈ n.lockEntries, t < e.d → e ∈ n'.lockEntries) ∧
        ∃ e' ∈ n'.lockEntries, e'.B = L ∧ e'.d = C.t_ (s - 1 + C.k) + 5 * C.Δ)))

/-! ## The walks of the duties: the vote's head, the proposal's parent, the attestation's head -/

/-- `AwakeForProposal M C n s`: the node has been awake since the start of slot `s`'s proposal
window or earlier: `n.awakeSince` is a time at most `proposal_window_start C s`.

The variables:
- `M`: the model;
- `C`: the configuration; `n`: the node state; `s`: the slot.

Read aloud: `n` was awake since the proposal window's start of slot `s`. -/
def AwakeForProposal (M : GoldilocksModel V) (C : Config) (n : M.N) (s : Slot) : Prop :=
  ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ proposal_window_start C s

open Classical in
/-- `LockedViableBlocks M Φ E t`: the blocks of the viable tree of `Φ.tree`
(`M.viable_tree Φ Φ.tree`) that are the block of an entry of `E` live at `t`, or an ancestor of
it. An entry is live at `t` when its deadline is after `t` and its block is in `Φ.tree`.

The variables:
- `M`: the model; `Φ`: the frame; `E`: the lock entries; `t`: the time.

Read aloud: the blocks of the viable tree that a live entry of `E` locks. -/
noncomputable def LockedViableBlocks (M : GoldilocksModel V) (Φ : Frame V) (E : Finset M.LE)
    (t : Time) : Finset (Block V) :=
  {B ∈ M.viable_tree Φ Φ.tree | ∃ e ∈ E, t < e.d ∧ e.B ∈ Φ.tree ∧ B.ancestorEq e.B = true}

/-- `AnchorAt M Φ E t`: the block a walk over the frame `Φ` starts from at the time `t`, with the
lock entries `E`: the deepest block (`Block.deepest?`) of `LockedViableBlocks M Φ E t`, when there
is one, and the fgroot `Φ.fc_root` otherwise.

The variables:
- `M`: the model; `Φ`: the frame; `E`: the lock entries; `t`: the time.

Read aloud: the anchor over `Φ` with the lock entries `E` at `t`: the deepest locked block of the
viable tree, or the fgroot. -/
noncomputable def AnchorAt [RootOrder] (M : GoldilocksModel V) (Φ : Frame V) (E : Finset M.LE)
    (t : Time) : Block V :=
  if h : Block.deepest? (LockedViableBlocks M Φ E t) ≠ none
  then (Block.deepest? (LockedViableBlocks M Φ E t)).value h
  else Φ.fc_root

open Classical in
/-- `VoterTree M C n s`: the voter's tree of the Goldfish vote of slot `s` in the node state `n`:
the blocks `B` of the tree of `M.fg_to_ac n` with `VoterTreeAt M n (C.t_ (s - 1) + 3 * C.Δ) s B`
(stamped strictly before the view freeze of slot `s − 1`, or leading to a slot-`s` block).

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s`: the slot of the vote.

Read aloud: the blocks the Goldfish vote of slot `s` may walk through, before the viable part is
taken. -/
noncomputable def VoterTree (M : GoldilocksModel V) (C : Config) (n : M.N) (s : Slot) :
    Finset (Block V) :=
  {B ∈ (M.fg_to_ac n).tree | VoterTreeAt M n (C.t_ (s - 1) + 3 * C.Δ) s B}

/-- `HeadOf M C n A₀ t s H`: the walk of the Goldfish vote of slot `s` in the node state `n`, at
the time `t`, from the block `A₀`, ends at `H`: for the two sets of votes the vote counts
(`CountedVotes M C n s votes support_votes`), the walk through the viable part of the voter's tree
(`M.viable_tree (M.fg_to_ac n) (VoterTree M C n s)`), with the Goldfish score and the Goldfish
eligibility test of those sets for the slot `s − 1`, at the model's tie-break `M.tieBreak`, from
`A₀` ends at `H` (`WalkEnd`).

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state;
- `A₀`: the start of the walk; `t`: the time; `s`: the slot of the vote; `H`: the end.

Read aloud: the Goldfish vote of slot `s` of `n`, walking from `A₀`, ends at `H`. -/
noncomputable def HeadOf [RootOrder] (M : GoldilocksModel V) (C : Config) (n : M.N)
    (A₀ : Block V) (t : Time) (s : Slot) (H : Block V) : Prop :=
  ∃ votes support_votes : Finset (GoldfishVote V), CountedVotes M C n s votes support_votes ∧
    @WalkEnd V M.tieBreak (M.viable_tree (M.fg_to_ac n) (VoterTree M C n s))
      (goldfish_score (M.fg_to_ac n) votes support_votes (s - 1))
      (goldfish_eligible C (M.fg_to_ac n) t votes support_votes (s - 1)) A₀ H

/-- `PoolHeadOf M C n A₀ t s' H`: the head for the slot `s'` in the node state `n`, at the time
`t`, from the block `A₀`, is `H`: with `votes` the slot-`s'` votes `n` holds
(`M.votesHeldSet n s'`) and `support_votes` those of them that resolve in `n` (`ResolvesAt`), the
walk through the viable tree of the tree of `M.fg_to_ac n`, with the Goldfish score and the
Goldfish eligibility test of those sets for the slot `s'`, at the model's tie-break `M.tieBreak`,
from `A₀` ends at `H` (`WalkEnd`).

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state;
- `A₀`: the start of the walk; `t`: the time; `s'`: the slot of the votes counted; `H`: the end.

Read aloud: counting `n`'s votes of slot `s'` and those that resolve, the walk through the viable
tree from `A₀` ends at `H`. -/
noncomputable def PoolHeadOf [RootOrder] (M : GoldilocksModel V) (C : Config) (n : M.N)
    (A₀ : Block V) (t : Time) (s' : Slot) (H : Block V) : Prop :=
  ∃ votes support_votes : Finset (GoldfishVote V),
    (votes = M.votesHeldSet n s' ∧
      ∀ vote : GoldfishVote V, vote ∈ support_votes ↔
        vote ∈ M.votesHeldSet n s' ∧ ∃ y : Stamp, ResolvesAt M n vote y) ∧
    @WalkEnd V M.tieBreak (M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree)
      (goldfish_score (M.fg_to_ac n) votes support_votes s')
      (goldfish_eligible C (M.fg_to_ac n) t votes support_votes s') A₀ H

/-- `AttestationFrom M n v h_c T_c h_j J h_F a`: `a` is the attestation the validator client of the
node state `n` builds for the validator `v`, from a source at the height `h_c` taken into it by the
block with the root `T_c`, and a head with the justification height `h_j`, the justified root `J`
and the finalization height `h_F`: the height pair `n` allows
(`M.height_pair n (some (h_c, T_c)) (M.finality_pair n h_j J h_F)`) is the vote at `h_c` for `T_c`
(a timeout when `τ`), `n` is not forbidden it (`M.already_sent n h_c T_c τ = false`), and `a` is
the attestation of `v` with that vote and the finality pair `M.finality_pair n h_j J h_F` when it
is at a height less than `h_c`, none otherwise.

The variables:
- `M`: the model; `n`: the node state; `v`: the validator;
- `h_c`, `T_c`: the source's height and the root of the block that took the source into it;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height;
- `a`: the attestation.

Read aloud: `a` is the attestation `n`'s validator client builds for `v` from that source and
head. -/
def AttestationFrom (M : GoldilocksModel V) (n : M.N) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V) : Prop :=
  ∃ τ : Bool, M.height_pair n (some (h_c, T_c)) (M.finality_pair n h_j J h_F) =
      HeightPair.vote h_c T_c τ ∧
    M.already_sent n h_c T_c τ = false ∧
    a = Attestation.mk v h_c T_c τ
      (match M.finality_pair n h_j J h_F with
        | some q => if h_c ≤ q.hf then none else some q
        | none => none)

/-- `AttestationRecorded M n a n'`: the anti-slashing record of `n'` is `n`'s with the attestation
`a` written into it: the contents sent are `n`'s and `a`'s; the lock at the height of `a`'s
finality pair, if any, is the pair's block, every other lock `n`'s; the target at `a`'s height is
`a`'s block when `a` is a target vote and `n` holds no target there, every other target `n`'s; the
timeout at `a`'s height is set when `a` is a timeout, every other timeout `n`'s.

The variables:
- `M`: the model; `n`: the node state before; `a`: the attestation; `n'`: the node state after.

Read aloud: `n'`'s record is `n`'s with `a` written into it. -/
def AttestationRecorded (M : GoldilocksModel V) (n : M.N) (a : Attestation V) (n' : M.N) :
    Prop :=
  n'.sentAttestations = n.sentAttestations ∪ {a.content} ∧
    (∀ h : Height, n'.sentLock h =
      match a.finality_pair with
      | some p => if h = p.hf then some p.Tf else n.sentLock h
      | none => n.sentLock h) ∧
    (∀ h : Height, n'.sentTarget h =
      if a.τ = false ∧ n.sentTarget a.h = none ∧ h = a.h then some a.T else n.sentTarget h) ∧
    (∀ h : Height, n'.sentTimeout h = if a.τ = true ∧ h = a.h then true else n.sentTimeout h)

end GoldilocksCorrectness.Record.Statements.Routines
