module
public import GoldilocksCorrectness.Proofs.Executions.Lemma18
public import GoldilocksCorrectness.Proofs.Executions.Lemma27
public import GoldilocksCorrectness.Proofs.Executions.Lemma29

@[expose] public section

/-!
# An honest validator's confirmation update

The audited statement of G1 over executions, `lem18_update_confirmation_confirms_majority_block`,
proved in `GoldilocksCorrectness/Proofs/Executions/Lemma18.lean`.

Its voter forms, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma27.lean` and
`GoldilocksCorrectness/Proofs/Executions/Lemma29.lean`: the committee majority replaced by
the voter bound on `v`'s slot-`s` pool before the support cutoff of slot `s + 1`.
`lem27_update_confirmation_confirms_voter_majority_block` concludes `B` saved and the confirmed
tip advanced, under the lock condition; `lem29_update_confirmation_fast_locks_voter_majority_block`
concludes `B` fast and locked, under the half condition.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 18, an honest validator's confirmation update confirms a block a committee majority
voted for early.** In an execution where every time is reached, corruption is permanent, blocks
and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and
catch-up on wake), a root names one block among what honest validators
hold, a block reaches a validator only once it holds the parent, and nobody votes in an honest
validator's name: if `GST` is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s`
committee, honest through the support cutoff `t₂` of slot `s + 1`, put its slot-`s` vote for `B` on
the wire at its tick at the vote time of slot `s`, and holds `B` in its tree then; `Hs` outnumbers
the rest of the slot-`s` committee; `B` is not the genesis block; `v` is awake and honest at every
time from the duty window's start of slot `s + 1` to `t₂`; and `v`'s finalized block before `t₂`
is `B` or an ancestor of `B` (F1) — then `v`'s node state before `t₂ + 1` has `B` saved as the
confirmation of slot `s`, `B` among its fast blocks, the lock entry on `B` with the deadline
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, and its record of the confirmed tip advanced with `B` from what
it was before `t₂`.



Why: `v` is awake from the start of slot `s`, so by Lemma 12 every `u ∈ Hs` has its vote for `B`
in `v`'s pool as its only slot-`s` vote, resolved strictly before `S.C.t_ s + 2 · S.C.Δ`, at the
vote time `t₃` of slot `s + 1` and at `t₂`. `v` has been awake since the duty window's start, so
its tick at `t₃` passes the duty test and revokes the locks (Lemma 13), after which every lock
entry is compatible with `B` (Lemma 5); no tick strictly between `t₃` and `t₂` adds an entry. Its
tick at `t₂` runs the confirmation update (Lemma 15), which confirms `B` (Lemma 8b), no live lock
vetoing it; nothing after that tick and before `t₂ + 1` changes the four fields.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `B`: the block their votes are for;
- `v`: the validator running the confirmation update of slot `s`.

Read aloud: if more than half of the slot-`s` committee are honest members that sent at the vote
time of slot `s` a vote for a non-genesis block `B` they hold, and `v` is awake and honest from the
duty window's start of slot `s + 1` to its support cutoff, with its finalized block before that
cutoff `B` or an ancestor of `B`, then right after that cutoff `v` has `B` saved as the
confirmation of slot `s`, fast, locked until `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, and its confirmed
tip advanced with `B`.

Roots name blocks until `supportCutoff S s`: the proof takes as held by `v` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`). -/
theorem lem18_update_confirmation_confirms_majority_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    (hMajority : (S.P.committee s \ Hs).card < Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF1 : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) :
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B ∧
      B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        advance (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          (stateBefore x (supportCutoff S (s + 1)) v).A.latest_confirmed (some B) :=
  GoldilocksCorrectness.Proofs.Executions.lem18_update_confirmation_confirms_majority_block S Sched
    x GST s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hMajority hBne hv
    hF1

/-- **Lemma 27, an honest validator's confirmation update confirms a block a voter majority voted
for.** In an execution where every time is reached, corruption is permanent, blocks and Goldfish
votes are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on
wake), a root names one block among what honest validators hold, a
block reaches a validator only once it holds the parent, and nobody votes in an honest validator's
name: if `GST` is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee,
honest through the support cutoff `t₂` of slot `s + 1`, put its slot-`s` vote for `B` on the wire
at its tick at the vote time of slot `s`, and holds `B` in its tree then; the validators with a
slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`; `B` is not the genesis block;
`v` is awake and honest at every time from the duty window's start of slot `s + 1` to `t₂`; `v`'s
finalized block before `t₂` is `B` or an ancestor of `B` (F1); and for every answer `A'` of `v`'s
revocation of slot `s + 1` at its vote time `t₃`, run on `v`'s AC state before `t₃` with its
expired lock entries removed, the block of every lock entry of `A'` live at `t₃` is compatible with
`B` — then `v`'s node state before `t₂ + 1` has `B` saved as the confirmation of slot `s`, and its
record of the confirmed tip advanced with `B` from what it was before `t₂`.

This is Lemma 18 with its committee majority (`Hs` outnumbers the rest of the slot-`s` committee)
replaced by the voter bound and the lock condition, and with the two conclusions that do not read
the committee size. The lock condition is a hypothesis because a voter majority does not make the
revocation clear a conflicting lock.
`B` fast and locked are Lemma 29: the fast test reads the committee size (`fast_test`,
`experiments/goldilocks/Goldilocks/AC/Confirmation.lean:149`).

Why: as for Lemma 18, with three changes. `Hs` is not empty, since the voter bound gives
`0 ≤ voters_count < 2 · |Hs|`. The lock condition, on the answer of the revocation `v`'s tick at
`t₃` ran, takes the place of Lemma 5: a lock entry live at `t₂` is an entry of that answer, and it
was live at `t₃`, since its deadline is after `t₂`, hence after `t₃`, and the revocation keeps only
entries on blocks of the tree; so it is compatible with `B`. The update at `t₂` is read by
Lemma 25, with the voter bound, in place of Lemma 8b.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `B`: the block their votes are for;
- `v`: the validator running the confirmation update of slot `s`.

Read aloud: if every member of `Hs` is an honest member of the slot-`s` committee that sent at the
vote time of slot `s` a vote for a non-genesis block `B` it holds, the members of `Hs` are more than
half of the validators with a slot-`s` vote in `v`'s pool before the support cutoff of slot
`s + 1`, `v` is awake and honest from the duty window's start of slot `s + 1` to that cutoff, with
its finalized block before that cutoff `B` or an ancestor of `B`, and every lock entry live at the
vote time of slot `s + 1` that `v`'s revocation then leaves is on a block compatible with `B`, then
right after that cutoff `v` has `B` saved as the confirmation of slot `s` and its confirmed tip
advanced with `B`.

Roots name blocks until `supportCutoff S s`: the proof takes as held by `v` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`). -/
theorem lem27_update_confirmation_confirms_voter_majority_block (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF1 : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- the block of every lock entry live at `t₃` that `v`'s revocation leaves is compatible
    -- with `B`
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) v).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) v).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        advance (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          (stateBefore x (supportCutoff S (s + 1)) v).A.latest_confirmed (some B) :=
  GoldilocksCorrectness.Proofs.Executions.lem27_update_confirmation_confirms_voter_majority_block S
    Sched x GST s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hBne
    hv hF1 hLocks

/-- **Lemma 29, an honest validator's confirmation update makes a block a voter majority voted for
fast and locks it.** In an execution where every time is reached, corruption is permanent, blocks
and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and
catch-up on wake), a root names one block among what honest validators
hold, a block reaches a validator only once it holds the parent, and nobody votes in an honest
validator's name: if `GST` is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s`
committee, honest through the support cutoff `t₂` of slot `s + 1`, put its slot-`s` vote for `B` on
the wire at its tick at the vote time of slot `s`, and holds `B` in its tree then; the validators
with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`; the slot-`s` committee is
at most twice `Hs`; `B` is not the genesis block; `v` is awake and honest at every time from the
duty window's start of slot `s + 1` to `t₂`; and `v`'s finalized block before `t₂` is `B` or an
ancestor of `B` (F1) — then `v`'s node state before `t₂ + 1` has `B` among its fast blocks and the
lock entry on `B` with the deadline `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`.

This is Lemma 18 with its committee majority replaced by the voter bound and the half condition,
and with the two conclusions that read the committee size: the fast test asks that the committee
be at most twice `B`'s score (`fast_test`,
`experiments/goldilocks/Goldilocks/AC/Confirmation.lean:149`). No lock condition is assumed: the
half condition clears the conflicting locks at `v`'s revocation by Lemma 5.

Why: by Lemma 12 at the vote time `t₃` of slot `s + 1` every `u ∈ Hs` has its vote for `B` in
`v`'s pool as its only slot-`s` vote, so Lemma 5 with the half condition makes every lock entry
`v`'s revocation at `t₃` leaves compatible with `B`, which is Lemma 27's lock condition. By the
argument of Lemma 27, `v`'s update at `t₂` confirms `B` with a score at least `|Hs|`, and Lemma 28,
with the half condition, makes `B` fast and the block of the new lock entry.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `B`: the block their votes are for;
- `v`: the validator running the confirmation update of slot `s`.

Read aloud: if every member of `Hs` is an honest member of the slot-`s` committee that sent at the
vote time of slot `s` a vote for a non-genesis block `B` it holds, the members of `Hs` are more than
half of the validators with a slot-`s` vote in `v`'s pool before the support cutoff of slot
`s + 1` and at least half of the slot-`s` committee, and `v` is awake and honest from the duty
window's start of slot `s + 1` to that cutoff, with its finalized block before that cutoff `B` or
an ancestor of `B`, then right after that cutoff `B` is one of `v`'s fast blocks and `v` holds the
lock entry on `B` until `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`.

Roots name blocks until `supportCutoff S s`: the proof takes as held by `v` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`). -/
theorem lem29_update_confirmation_fast_locks_voter_majority_block (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    -- the slot-`s` committee is at most twice `Hs`
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF1 : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) :
    B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries :=
  GoldilocksCorrectness.Proofs.Executions.lem29_update_confirmation_fast_locks_voter_majority_block
    S Sched x GST s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters
    hHalf hBne hv hF1

end GoldilocksCorrectness.Statements.Executions
