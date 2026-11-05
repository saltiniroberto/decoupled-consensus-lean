module
public import GoldilocksCorrectness.Statements.Executions.HonestChainDefs
public import GoldilocksCorrectness.Statements.Routines.ChainConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Proofs.Executions.Lemma79

@[expose] public section

/-!
# The slot invariant restricted to a block, and its step

The audited statements of Lemma 78, `lem78_update_confirmation_extends_voter_majority_chain`
(proved in `GoldilocksCorrectness/Proofs/Executions/Lemma78.lean`); of the two kit facts
`update_state_of_duty` and `update_state_of_lock_entry` on the tick at a support cutoff (proved in
`GoldilocksCorrectness/Proofs/Executions/TickUpdateState.lean`); and of the kit theorem
`live_locks_compatible_of_honestChainExtends` and Lemma 79, the step of `HonestChainExtends`
(`GoldilocksCorrectness/Statements/Executions/HonestChainDefs.lean`), in four theorems (proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma79.lean`).
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
open GoldilocksCorrectness.Statements.Routines (CountedVotes expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The tick at a support cutoff -/

/-- **The tick at the support cutoff leaves the update's answer, the awake form.** Write `c` for
the support cutoff of slot `s + 1`. In an execution where every time is reached:
when `v` is awake and honest at `c` and its tick at `c` starts from a record of
awakeness since the duty window's start of slot `s + 1` or earlier, the confirmation update of slot
`s + 1` on `v`'s state before `c`, its expired lock entries removed, answers some `A''`, and `v`'s
state before `c + 1` has `A''`'s saved confirmations, fast blocks, lock entries and record of the
confirmed tip.

Why: the tick at `c` answers (`ticksSucceed_of_exec`) and runs the update (Lemma 15, `c` being
the support cutoff of its slot and the duty test passing); nothing after that tick and before the
next one changes those four fields.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s`: the slot before the cutoff's slot; `v`: the validator.

Read aloud: the state right after the support cutoff holds what the update answered. -/
theorem update_state_of_duty (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (v : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- `v` is awake and honest at the support cutoff of slot `s + 1`
    (hv : v ∈ Sched.awake (supportCutoff S (s + 1) : Int) ∧
      v ∉ Sched.adv (supportCutoff S (s + 1) : Int))
    -- `v`'s tick there starts from a record of awakeness passing the duty test of slot `s + 1`
    (hAw : ∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) :
    -- then the update answered `A''`, and the state right after the cutoff has its four fields
    ∃ A'' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
        A''.saved_confirmation ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks = A''.fast_blocks ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries = A''.lock_entries ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        A''.latest_confirmed :=
  GoldilocksCorrectness.Proofs.Executions.update_state_of_duty S Sched x s v hDiv hv hAw

/-- **A lock of slot `s` in hand means its holder ran the update of slot `s + 1`.** Write `c` for
the support cutoff of slot `s + 1`. In an execution where every time is reached: when `v` holds
before `t` a lock entry `e` with the deadline of a lock of slot `s`, `S.C.t_ (s + S.C.k) + 5 ·
S.C.Δ`, and `c` is before `t`, then `v` was awake and honest at `c`, its tick at `c` started from a
record of awakeness since the duty window's start of slot `s + 1` or earlier, the confirmation
update of slot `s + 1` on `v`'s state before `c`, its expired lock entries removed, answered some
`A''`, and `v`'s state before `c + 1` has `A''`'s saved confirmations and lock entries.

Why: the entry is traced to the update of the slot its deadline names (Lemma 39's invariant), so
right after the tick at `c` an entry with that deadline is held, and none is held before it; the
step of that tick changed the lock entries, and of what a step does to them only the update at the
support cutoff adds an entry with a new deadline.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t`: the time; `s`: the slot of the lock; `v`: the validator; `e`: the lock entry.

Read aloud: a lock of slot `s` in hand means the holder ran the update of slot `s + 1`, awake, and
kept its answer. -/
theorem update_state_of_lock_entry (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t s : ℕ) (v : V) (e : LockEntry V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- `e` is a lock entry of `v`'s state before `t`
    (he : e ∈ (stateBefore x t v).A.lock_entries)
    -- `e` has the deadline of a lock of slot `s`
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the support cutoff of slot `s + 1` is before `t`
    (hts : supportCutoff S (s + 1) < t) :
    -- then `v` ran the update of slot `s + 1` awake and honest, and kept its answer
    (v ∈ Sched.awake (supportCutoff S (s + 1) : Int) ∧
      v ∉ Sched.adv (supportCutoff S (s + 1) : Int)) ∧
    (∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
    ∃ A'' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
        A''.saved_confirmation ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries = A''.lock_entries :=
  GoldilocksCorrectness.Proofs.Executions.update_state_of_lock_entry S Sched x t s v e hDiv he hd
    hts

/-! ## Lemma 78 -/

/-- **Lemma 78, an honest confirmation update over a voter majority's chain.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the support cutoff `c` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at
the vote time of slot `s`, and holds `H u`, a block that is `B` or a descendant of `B`, in its tree
then; the validators with a slot-`s` vote in `v`'s pool before `c` are fewer than twice `Hs`; `v`
is awake and honest at every time from the duty window's start of slot `s + 1` to `c`; and `v`'s
finalized block before `c` is compatible with `B` — then the confirmation of slot `s` that `v`
holds right after `c`, when it holds one, is `B` or a descendant of `B`.

Why: the state right after `c` holds the confirmation the update of slot `s + 1` saved
(`update_state_of_duty`). When `v`'s finalized block is `B` or an ancestor of `B`, Lemma 12 at `c`
delivers every member's vote to `v`, held early, and Lemma 77 makes the saved confirmation `B` or a
descendant of `B`. When `B` is an ancestor of `v`'s finalized block, the saved confirmation is that
finalized block or a descendant of it (`saved_confirmation_F_ancestorEq`). This is Lemma 27 with
the votes on `B`'s chain in place of votes for `B`, the finalized block compatible with `B` in
place of an ancestor of `B`, without its conditions that `B` is not the genesis block and on the
locks, and concluding on the saved confirmation only.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `B`: the block every vote of `Hs` extends; `v`: the validator running the confirmation update of
  slot `s + 1`.

Read aloud: if every member of `Hs` is a member of the slot-`s` committee, honest through the
support cutoff of slot `s + 1`, that sent at the vote time of slot `s` a vote for a block it holds
that is `B` or a descendant of `B`; the members of `Hs` are more than half of the validators with a
slot-`s` vote in `v`'s pool before that cutoff; `v` is awake and honest from the duty window's
start of slot `s + 1` to that cutoff; and `v`'s finalized block before the cutoff is compatible with
`B` — then the confirmation of slot `s` that `v` holds right after the cutoff, when it holds one,
is `B` or a descendant of `B`.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 call at slot `s` its
proof passes the premise to. -/
theorem lem78_update_confirmation_extends_voter_majority_chain (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- every member of `Hs` is a member of the slot-`s` committee, honest through the support
    -- cutoff of slot `s + 1`, that sent its slot-`s` vote for `H u`, a block it holds that is `B`
    -- or a descendant of `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ B.AncestorEq (H u))
    -- the validators with a slot-`s` vote in `v`'s pool before the cutoff are fewer than twice
    -- `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to the cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s finalized block before the cutoff is compatible with `B`
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    -- then `v`'s confirmation of slot `s` right after the cutoff is on `B`'s chain
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      B.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Executions.lem78_update_confirmation_extends_voter_majority_chain S
    Sched x GST s Hs H B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hv
    hF

/-! ## The live locks under the invariant -/

/-- **The live locks of a member are compatible with `B`.** In an execution where every time is
reached: when `HonestChainExtends S Sched x Hon B s'` holds, `w` is
a member of `Hon`, awake and honest at every time from the duty window's start of slot `s' + 2` to
`t`, and `t` is after the support cutoff of slot `s' + 1` and at most the vote time of slot
`s' + 2`, then every lock entry `w` holds before `t` whose deadline is after `t` is on a block
compatible with `B`.

Why: the entry was added by `w`'s confirmation update of a slot `s₁ + 1` with `s₁ ≤ s'`, on a block
that is the saved confirmation of slot `s₁` or an ancestor of it, and its block is that block or an
ancestor of it (Lemma 39). When `s₁ = s'`, the saved confirmation is the one the third clause of the
invariant reads (`update_state_of_lock_entry`), `B` or a descendant of `B`. When `s₁ < s'`, the
deadline being after `t` makes `s₁ + S.C.k ≥ s' + 1` (Lemma 41), so that update ran after the duty
window's start of slot `s' + 2`, `w` was awake from it on, and its tick at the vote time of slot `s' + 1` ran the revocation (Lemma 13); an entry with the
entry's deadline, on its block or a descendant of it, survived the revocation live (Lemma 39's
trace), and the second clause of the invariant makes it compatible with `B`.


The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the validators the invariant is read at; `B`: the block; `s'`: the slot of the
  invariant; `t`: the time; `w`: the member.

Read aloud: between the update of slot `s' + 1` and the revocation of slot `s' + 2`, every lock a
member holds that has not expired is on a block compatible with `B`. -/
theorem live_locks_compatible_of_honestChainExtends (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon : Finset V) (B : Block V) (s' t : ℕ) (w : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends S Sched x Hon B s')
    -- `w` is a member of `Hon`
    (hw : w ∈ Hon)
    -- `w` is awake and honest from the duty window's start of slot `s' + 2` to `t`
    (hHon : ∀ t'' : ℕ, dutyWindowStart S (s' + 2) ≤ t'' → t'' ≤ t →
      w ∈ Sched.awake (t'' : Int) ∧ w ∉ Sched.adv (t'' : Int))
    -- `t` is after the support cutoff of slot `s' + 1`
    (ht1 : supportCutoff S (s' + 1) < t)
    -- `t` is at most the vote time of slot `s' + 2`
    (ht2 : t ≤ voteTime S (s' + 2)) :
    -- then every entry `w` holds before `t`, with its deadline after `t`, is compatible with `B`
    ∀ e ∈ (stateBefore x t w).A.lock_entries, ((t : ℕ) : Int) < e.d →
      e.B.compatible B = true :=
  GoldilocksCorrectness.Proofs.Executions.live_locks_compatible_of_honestChainExtends S Sched x Hon
    B s' t w hDiv hInv hw hHon ht1 ht2

/-! ## Lemma 79, the step -/

/-- **Lemma 79a, the first clause of the step.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s'`; `HonestChainExtends S Sched x Hon B s'` holds; the members of `Hon` are awake and honest
from the duty window's start of slot `s' + 1` to the vote time of slot `s' + 1`; every member of
`Hs` is a member of `Hon` and of the slot-`s'` committee that put a slot-`s'` vote on the wire at
its tick at the vote time of slot `s'`; at every member `w` voting at slot `s' + 1`, the validators
with a vote among those `w` counts are fewer than twice `Hs`, the root of `w`'s fork choice is
compatible with `B`, and, when that root is `B`
or an ancestor of `B`, some block of `w`'s voter tree on `B`'s chain is a viable head — then every
slot-`(s' + 1)` vote a member put on the wire at its tick at the vote time of slot `s' + 1` is its
vote for a block it holds then that is `B` or a descendant of `B`.

Why: the first clause of the invariant makes each member of `Hs` an honest voter of slot `s'` for a
block it holds on `B`'s chain, and the second clause gives the lock condition at the vote time of
slot `s' + 1`; Lemma 26b with `R := B` concludes.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of slot `s'`;
- `B`: the block.

Read aloud: under the invariant at slot `s'`, the members' votes of slot `s' + 1` are for blocks
they hold on `B`'s chain.

Roots name blocks until `supportCutoff S s'`: Lemma 26b, which the proof calls at slot `s'`,
takes blocks as held up to the support cutoff of slot `s'`. -/
theorem lem79a_honestChainExtends_votes_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends S Sched x Hon B s')
    -- the members of `Hon` are awake and honest from the duty window's start of slot `s' + 1` to
    -- the vote time of slot `s' + 1`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ voteTime S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- every member of `Hs` is a member of `Hon` and of the slot-`s'` committee that sent a
    -- slot-`s'` vote at the vote time of slot `s'`
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- at every member voting at slot `s' + 1`, the validators it counts are fewer than twice `Hs`
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) votes support_votes →
      voters_count votes < 2 * Hs.card)
    -- at every member voting at slot `s' + 1`, the root of its fork choice is compatible with `B`
    (hF2 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true)
    -- at every member voting at slot `s' + 1`, when that root is `B` or an ancestor of `B`, a
    -- block of its voter tree on `B`'s chain is a viable head
    (hF3 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
          B.AncestorEq W) :
    -- then the first clause holds at slot `s' + 1`
    ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s' + 1)) u).S.T,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u :=
  GoldilocksCorrectness.Proofs.Executions.lem79a_honestChainExtends_votes_step S Sched x GST s'
    Hon Hs B hDiv hMono hSync hCatch hRoots hParent hOwner hGST hInv hHon hHs hVotersW hF2
    hF3

/-- **Lemma 79b, the second clause of the step.** In an execution where every time is reached:
when `HonestChainExtends S Sched x Hon B s'` holds and the members of
`Hon` are awake and honest from the duty window's start of slot `s' + 2` to the vote time of slot
`s' + 2`, then for every member `w` and every answer `A'` of `w`'s revocation of slot `s' + 2` at
its vote time, run on `w`'s AC state then with its expired entries removed, the block of every
lock entry of `A'` live then is compatible with `B`.

Why: every entry the revocation leaves is on the block of an entry of `w`'s state then, or an
ancestor of it, whose deadline is after that time (Lemma 38); that entry is compatible with `B`
(`live_locks_compatible_of_honestChainExtends` at the vote time of slot `s' + 2`), and so is every
ancestor of its block.


The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s'`: the slot of the invariant; `Hon`: the validators the invariant is read at; `B`: the block.

Read aloud: under the invariant at slot `s'`, the live locks the members' revocations of slot
`s' + 2` leave are compatible with `B`. -/
theorem lem79b_honestChainExtends_locks_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' : ℕ) (Hon : Finset V) (B : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends S Sched x Hon B s')
    -- the members of `Hon` are awake and honest from the duty window's start of slot `s' + 2` to
    -- the vote time of slot `s' + 2`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ voteTime S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int)) :
    -- then the second clause holds at slot `s' + 1`
    ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 2)) w).A
        ((voteTime S (s' + 2) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
        ((voteTime S (s' + 2) : ℕ) : Int) (s' + 2) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
          ((voteTime S (s' + 2) : ℕ) : Int) e = true → e.B.compatible B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem79b_honestChainExtends_locks_step S Sched x s' Hon B
    hDiv hInv hHon

/-- **Lemma 79c, the third clause of the step.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s' + 1`; every slot-`(s' + 1)` vote a member of `Hon` put on the wire at its tick at the vote
time of slot `s' + 1` is its vote for a block it holds then that is `B` or a descendant of `B` (the
first clause at slot `s' + 1`, Lemma 79a's conclusion); the members of `Hon` are awake and honest
from the duty window's start of slot `s' + 2` to the support cutoff of slot `s' + 2`; every member
of `Hs` is a member of `Hon` and of the slot-`(s' + 1)` committee that put a slot-`(s' + 1)` vote on
the wire at its tick at the vote time of slot `s' + 1`; at every member `v`, the validators with a
slot-`(s' + 1)` vote in `v`'s pool before the support cutoff of slot `s' + 2` are fewer than twice
`Hs`, and `v`'s finalized block then is compatible with `B` — then every confirmation of slot
`s' + 1` a member holds right after the support cutoff of slot `s' + 2` is `B` or a descendant of
`B`.

Why: Lemma 78 at slot `s' + 1`, each member of `Hs` voting for a block it holds on `B`'s chain.


The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of slot `s' + 1`;
- `B`: the block.

Read aloud: when the members' votes of slot `s' + 1` are on `B`'s chain, their confirmations of slot
`s' + 1` are too.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemma 78, which the proof calls at slot `s'
+ 1`, takes blocks as held up to the support cutoff of slot `s' + 1`. -/
theorem lem79c_honestChainExtends_confirmations_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S (s' + 1))
    -- every member's slot-`(s' + 1)` vote is for a block it holds on `B`'s chain
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s' + 1)) u).S.T,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u)
    -- the members of `Hon` are awake and honest from the duty window's start of slot `s' + 2` to
    -- the support cutoff of slot `s' + 2`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- every member of `Hs` is a member of `Hon` and of the slot-`(s' + 1)` committee that sent a
    -- slot-`(s' + 1)` vote at the vote time of slot `s' + 1`
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- at every member, the slot-`(s' + 1)` voters of its pool before the support cutoff of slot
    -- `s' + 2` are fewer than twice `Hs`
    (hVotersV : ∀ v ∈ Hon,
      voters_count ((stateBefore x (supportCutoff S (s' + 2)) v).A.pool (s' + 1)) <
        2 * Hs.card)
    -- at every member, its finalized block before that cutoff is compatible with `B`
    (hFv : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s' + 2)) v).S.F.compatible B = true) :
    -- then the third clause holds at slot `s' + 1`
    ∀ v ∈ Hon, ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 2) + 1) v).A.saved_confirmation (s' + 1) = some C' →
      B.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Executions.lem79c_honestChainExtends_confirmations_step S Sched x
    GST s' Hon Hs B hDiv hMono hSync hCatch hRoots hParent hOwner hGST hVotes hHon hHs
    hVotersV hFv

/-- **Lemma 79, the step of the slot invariant restricted to a block.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after
`GST` (synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s'`; `HonestChainExtends S Sched x Hon B s'` holds; the members of `Hon` are awake and honest
from the duty window's start of slot `s' + 1` to the support cutoff of slot `s' + 2`; for each of
the slots `s'` and `s' + 1`, every member of `Hs` of that slot is a member of `Hon` and of that
slot's committee that put a vote of that slot on the wire at its tick at that slot's vote time; at
every member `w` voting at slot `s' + 1`, the validators with a vote among those `w` counts are
fewer than twice `Hs s'`, the root of `w`'s fork choice is compatible with `B`, and, when that root
is `B` or an ancestor of `B`, some block of `w`'s voter tree on `B`'s chain is a viable head; and at
every member `v` running the update of slot `s' + 2`, the slot-`(s' + 1)` voters of `v`'s pool
before the support cutoff of slot `s' + 2` are fewer than twice `Hs (s' + 1)`, and `v`'s finalized
block then is compatible with `B` — then `HonestChainExtends S Sched x Hon B (s' + 1)` holds.



Why: the three clauses at slot `s' + 1` are Lemmas 79a, 79b and 79c; Lemma 79c reads Lemma 79a's
conclusion.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of each slot;
- `B`: the block.

Read aloud: the invariant at slot `s'` gives the invariant at slot `s' + 1`, when the members stay
awake and honest through the next slot, the honest voters of each slot are a majority of the voters
the members count, and the members' finalized blocks and fork-choice roots are compatible with `B`.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemma 79c, which the proof calls, takes
blocks as held up to the support cutoff of slot `s' + 1`; Lemma 79a reads earlier. -/
theorem lem79_honestChainExtends_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends S Sched x Hon B s')
    -- the members of `Hon` are awake and honest from the duty window's start of slot `s' + 1` to
    -- the support cutoff of slot `s' + 2`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the honest voters of slots `s'` and `s' + 1`, members of `Hon` and of the slot's committee
    -- that sent a vote of the slot at its vote time
    (hHs : ∀ s₀ : ℕ, s₀ = s' ∨ s₀ = s' + 1 → ∀ u ∈ Hs s₀, u ∈ Hon ∧ u ∈ S.P.committee s₀ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the voter bound at every member voting at slot `s' + 1`
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) votes support_votes →
      voters_count votes < 2 * (Hs s').card)
    -- the voter bound at every member running the update of slot `s' + 2`
    (hVotersV : ∀ v ∈ Hon,
      voters_count ((stateBefore x (supportCutoff S (s' + 2)) v).A.pool (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    -- at every member voting at slot `s' + 1`, the root of its fork choice is compatible with `B`
    (hF2 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true)
    -- at every member voting at slot `s' + 1`, when that root is `B` or an ancestor of `B`, a
    -- block of its voter tree on `B`'s chain is a viable head
    (hF3 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
          B.AncestorEq W)
    -- the finalized block of every member running the update of slot `s' + 2` is compatible
    -- with `B`
    (hFv : ∀ v ∈ Hon,
      (stateBefore x (supportCutoff S (s' + 2)) v).S.F.compatible B = true) :
    -- then the slot invariant restricted to `B` holds at slot `s' + 1`
    HonestChainExtends S Sched x Hon B (s' + 1) :=
  GoldilocksCorrectness.Proofs.Executions.lem79_honestChainExtends_step S Sched x GST s' Hon Hs B
    hDiv hMono hSync hCatch hRoots hParent hOwner hGST hInv hHon hHs hVotersW hVotersV hF2
    hF3 hFv

end GoldilocksCorrectness.Statements.Executions
