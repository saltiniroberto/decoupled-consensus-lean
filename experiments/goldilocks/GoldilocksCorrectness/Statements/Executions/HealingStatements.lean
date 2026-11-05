module
public import GoldilocksCorrectness.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Proofs.Executions.Lemma34
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Proofs.Executions.Lemma44

@[expose] public section

/-!
# The healing argument as statements

The audited statements of the deck's healing argument over an execution
: how the honest validators' lock
entries become compatible with each other after `GST`. Lemma 42,
`lem42_fast_lock_clears_conflicting_locks`, a fast lock clears every conflicting lock at the next
revocation of an honest validator. Each is proved in its own file under
`GoldilocksCorrectness/Proofs/Executions/`.






-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 42, a fast lock clears every conflicting lock.** When `v`'s confirmation update of
slot `s + 1` makes `L` a fast block, every lock entry that `w`'s revocation of slot `s + 1` leaves
is on a block compatible with `L`. This holds in an execution that reaches every time, with
permanent corruption, the network synchronous from `GST`, roots naming
blocks, and parents held at delivery, when `GST` is at most the support cutoff of slot `s`; `v` is
awake and honest at every time from the vote time of slot `s + 1` to the support cutoff of slot
`s + 1`; `w` is awake and honest at every time from the support cutoff of slot `s` to the view
freeze of slot `s`; and `w`'s finalized block before the vote time of slot `s + 1` is compatible
with `L`.

Why: when `L` is `w`'s finalized block or an ancestor of it, every entry the revocation leaves is
on a block of `w`'s frame tree, which descends from that finalized block. Otherwise `w`'s
finalized block is an ancestor of `L` or `L`. A fast block of the update is the saved confirmation
of slot `s` or an ancestor of it, so Lemma 36 gives a set `Sup` of early supporters of `L` at `v`
with the slot-`s` committee at most twice `Sup`. Each member's vote was in `v`'s pool before the
support cutoff of slot `s`, so `v` re-sent it and it reached `w` before the view freeze of slot
`s`, with its head block; a second vote of that member in `w`'s pool would have been re-sent by
`w` and reached `v` before the support cutoff of slot `s + 1`, where the member has one vote. So
each member of `Sup` votes once for `L`'s chain in `w`'s pool, and Lemma 5 makes every entry
left compatible with `L`.

The awake windows are narrowed from Lemma 21's (both from the start of slot `s`) to what the
proof uses; `v`'s honesty at the support cutoff of slot `s` follows from its honesty at the vote
time of slot `s + 1`, corruption being permanent. Dropping the premise strengthens the conclusion.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose votes `v`'s update of slot `s + 1` counts;
- `L`: the fast block; `v`: the validator whose update makes `L` fast; `w`: the validator whose
  revocation is read; `A'`: `v`'s update's answer; `A''`: `w`'s revocation's answer; `e`: a lock
  entry it leaves.

Read aloud: when `v`'s update of slot `s + 1` makes `L` a fast block, every lock entry that `w`'s
revocation of slot `s + 1` leaves is on a block compatible with `L`, provided `GST` is at most
the support cutoff of slot `s`, `v` is awake and honest from the vote time to the support cutoff of
slot `s + 1`, `w` from the support cutoff to the view freeze of slot `s`, and `w`'s finalized
block before the vote time of slot `s + 1` is compatible with `L`.

Roots name blocks until `supportCutoff S (s + 1)`: `supporters_vote_once_in_pool_at`, which the
proof calls with `t_w := voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s
vote time of slot `s + 1`. -/
theorem lem42_fast_lock_clears_conflicting_locks (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (L : Block V) (v w : V) (A' : ACState V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- `GST` is at most the support cutoff of slot `s`
    (hGST : GST ≤ supportCutoff S s)
    -- `v` is awake and honest from the vote time to the support cutoff of slot `s + 1`
    (hv : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `w` is awake and honest from the support cutoff to the view freeze of slot `s`
    (hw : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1` answers `A'` and makes `L` a fast block
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    -- `w`'s finalized block before the vote time of slot `s + 1` is compatible with `L`
    (hF : (stateBefore x (voteTime S (s + 1)) w).S.F.compatible L = true) :
    -- then every lock entry `w`'s revocation of slot `s + 1` leaves is on a block compatible with
    -- `L`
    ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries, e.B.compatible L = true :=
  GoldilocksCorrectness.Proofs.Executions.lem42_fast_lock_clears_conflicting_locks S Sched x GST s
    L v w A' hDiv hMono hSync hCatch hRoots hParent hGST hv hw hUpdate hFast hF


/-- Write `c` for the support cutoff of slot `s + 1`, the
time of the confirmation update of slot `s`, and `k` for `S.C.k`. In an execution that reaches
every time: when, for the slot `s'` whose lock deadline `S.C.t_ (s' + k) + 5 · S.C.Δ` is `e_w`'s,
the saved confirmations of slot `s'` on `v`'s and `w`'s node states before `c + 1` are compatible
whenever both are present; `e_v` is a lock entry of `v`'s node state before `c + 1` with the
deadline of a lock of slot `s`, `S.C.t_ (s + k) + 5 · S.C.Δ`; `e_w` is a lock entry of `w`'s node
state before `c + 1` whose deadline is after `c + 1`; and either `e_v`'s block passes the slow
test of slot `s` on `v`'s state before `c`, or `e_w` has `e_v`'s deadline; then `e_v`'s block is
compatible with `e_w`'s.

Why: `e_w` is a lock of a slot `s'` whose update ran before `c + 1`, so `s' ≤ s`, and its block is
`w`'s saved confirmation of slot `s'` before `c + 1` or an ancestor of it; it is still live at
`c + 1`, so `s' ≥ s + 1 − k` (Lemma 41). When `s' = s`, `e_v`'s block is likewise `v`'s saved
confirmation of slot `s` or an ancestor of it. When `s' < s`, the deadlines differ, so `e_v`'s
block passed the slow test, and Lemma 37 makes it `v`'s saved confirmation of slot `s'` or an
ancestor of it, kept to `c + 1`. The hypothesis on the saved confirmations at slot `s'`, the slot
`e_w`'s deadline names, makes the two saved confirmations compatible, and two ancestors-or-equal
of compatible blocks are compatible. No network assumption enters.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `v`'s lock, whose
  update runs at the support cutoff of slot `s + 1`;
- `v`, `w`: the two validators; `e_v`: `v`'s lock entry of slot `s`; `e_w`: `w`'s live lock entry;
- `s'`: the slot whose lock deadline `e_w` has; `Cv`, `Cw`: `v`'s and `w`'s saved confirmations of
  slot `s'`.

Read aloud: when `v`'s and `w`'s saved confirmations of the slot `e_w`'s deadline names are
compatible, a lock `v` makes at slot `s` that passes the slow test is compatible with the lock
`e_w` that `w` holds live just after, and so are two locks the two made at slot `s`. -/
theorem lem33_slow_lock_compatible_of_slotwise_confirmations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (v w : V) (e_v e_w : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    -- at the slot `s'` whose lock deadline `e_w` has, the saved confirmations of slot `s'` of `v`
    -- and `w`, right after the update of slot `s`, are compatible
    (hCompat : ∀ s' : ℕ, e_w.d = S.C.t_ (s' + S.C.k) + 5 * S.C.Δ → ∀ Cv Cw : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s' = some Cv →
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s' = some Cw →
      Cv.compatible Cw = true)
    -- `e_v` is a lock entry of slot `s`, held by `v` right after the update of slot `s`
    (he_v : e_v ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries)
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- `e_w` is a lock entry `w` holds then, with its deadline not yet reached
    (he_w : e_w ∈ (stateBefore x (supportCutoff S (s + 1) + 1) w).A.lock_entries)
    (hlive_w : ((supportCutoff S (s + 1) + 1 : ℕ) : Int) < e_w.d)
    -- `e_v`'s block passes the slow test at `v`'s update of slot `s`, or `e_w` is a lock entry of
    -- slot `s` too
    (hSlowOrSame : slow_test S.C (stateBefore x (supportCutoff S (s + 1)) v).A
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s e_v.B = true ∨
      e_w.d = e_v.d) :
    e_v.B.compatible e_w.B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem33_slow_lock_compatible_of_slotwise_confirmations S
    Sched x s v w e_v e_w hDiv hCompat he_v hd_v he_w hlive_w hSlowOrSame

/-- **Lemma 34, a fast lock against an older lock, through the revocation.** Write `t₃` for the
vote time of slot `s + 1` and `c` for its support cutoff. In an execution that reaches every
time: when `e_v` is a lock entry with the deadline of a lock of slot
`s`, `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; `e_w` is a lock entry of
`w`'s node state before `c + 1` whose deadline is after `c + 1` and before `e_v`'s; `w` is awake and
honest at `t₃`; `w`'s tick at `t₃` starts from a state whose `awakeSince` is some time at most the
duty window's start of slot `s + 1`; and every lock entry that `w`'s revocation of slot `s + 1`
leaves, on `w`'s state before `t₃` with its expired entries removed, and that is live at `t₃`, is
on a block compatible with `e_v`'s; then `e_v`'s block is compatible with `e_w`'s.

Why: `e_w` is a lock of a slot before `s`, since its deadline is before `e_v`'s, so the update that
added it ran before `t₃`, and `w`'s state before `t₃ + 1` holds an entry `e'` with `e_w`'s deadline
whose block is `e_w`'s block or a descendant of it (Lemma 39). `w`'s tick at `t₃` answered, ran the
revocation with the duty test passing, and left its answer's lock entries (Lemma 13), so `e'` is
one of them; `e'` is live at `t₃`, its deadline being after `c + 1` and its block in the frame's
tree. So `e'`'s block is compatible with `e_v`'s, and so is its ancestor `e_w`'s block.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `e_v`'s lock;
- `w`: the validator whose revocation is read; `e_v`: a lock entry with the deadline of a lock of
  slot `s`; `e_w`: `w`'s older live lock entry; `τ`: the time `w` has been awake since; `A'`: the revocation's answer; `e`: a lock entry it
  leaves.

Read aloud: a lock entry `e_v` with the deadline of a lock of slot `s` is compatible with an older
lock `w` holds live, when `w` is awake and honest at the vote time of slot `s + 1`, its tick then
starts with the duty test of slot `s + 1` passing, and every entry `w`'s revocation of slot `s + 1`
leaves, live then, is compatible with `e_v`'s block. -/
theorem lem34_fast_lock_compatible_of_revocation (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (w : V) (e_v e_w : LockEntry V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- `e_v` has the deadline of a lock entry of slot `s`
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- `e_w` is a lock entry `w` holds right after the update of slot `s`, with its deadline not
    -- yet reached
    (he_w : e_w ∈ (stateBefore x (supportCutoff S (s + 1) + 1) w).A.lock_entries)
    (hlive_w : ((supportCutoff S (s + 1) + 1 : ℕ) : Int) < e_w.d)
    -- `e_w` is older: a lock entry of a slot before `s`
    (hOlder : e_w.d < e_v.d)
    -- `w` is awake and honest at the vote time of slot `s + 1`
    (hw₃ : w ∈ Sched.awake (voteTime S (s + 1) : Int) ∧ w ∉ Sched.adv (voteTime S (s + 1) : Int))
    -- `w`'s tick then starts with `awakeSince` passing the duty test of slot `s + 1`
    (hDuty : ∃ τ : Time, (tickInputState x (stepBefore x (voteTime S (s + 1)))
      (voteTime S (s + 1)) w).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1))
    -- every lock entry live at the vote time of slot `s + 1` that `w`'s revocation of slot
    -- `s + 1` leaves is compatible with `e_v`'s block
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible e_v.B = true) :
    e_v.B.compatible e_w.B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem34_fast_lock_compatible_of_revocation S Sched x s w
    e_v e_w hDiv hd_v he_w hlive_w hOlder hw₃ hDuty hLocks


/-- **Lemma 45, a lock whose window is after `GST` is extended by the next slot's honest votes.** In
an execution that reaches every time, with permanent corruption, blocks and Goldfish votes delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
roots naming blocks, and parents held at delivery: when `GST` is at most the
support cutoff of slot `s + 1 − S.C.k`; `v` is awake and honest at every time from the duty window's start of
slot `s + 1` to the support cutoff of slot `s + 1`; `w` is awake and honest at every time from the
duty window's start of slot `s + 1` to the vote time of slot `s + 1`; `v`'s confirmation update of
slot `s + 1`, on its node state before that support cutoff with the expired lock entries removed,
answers `A'`, and `e` is a lock entry of `A'` with the deadline of a lock of slot `s`,
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; on `w`'s node state before the vote time of slot `s + 1`, the
root of the fork choice is compatible with `e`'s block; when that root is `e`'s block or an ancestor
of it, some block of `w`'s voter tree for slot `s + 1` that is `e`'s block or a descendant of it is
a viable head; and `w` put the Goldfish vote `vote` on the wire at its tick at the vote time of slot
`s + 1`: then `vote`'s head is the root of a block that is `e`'s block or a descendant of it.

Why: `e` is not an entry of the update's input, since such an entry was added by the update of its
own slot before the support cutoff (Lemma 39), and the deadline names the slot. So `e`'s block is
the saved confirmation of slot `s` or an ancestor of it, a fast block of `A'` or passing the slow
test (Lemma 35), and Lemma 36 gives a set `Sup` of early supporters of it at `v`, with `v`'s
slot-`s` voters fewer than twice `Sup`. Lemma 21 then gives the conclusion, once every lock entry
that `w`'s revocation of slot `s + 1` leaves, live at the vote time, is on a block compatible with
`e`'s. When `e`'s block is fast, this is Lemma 42. When it passes the slow test, each such entry
comes from a live entry of the revocation's input (Lemma 38), a lock of a slot `s'` with
`s + 1 − S.C.k ≤ s' < s` (Lemmas 39 and 41) on `w`'s saved confirmation of slot `s'` or an
ancestor of it; the slow test makes `e`'s block `v`'s saved confirmation of slot `s'` or an
ancestor of it (Lemma 37); and the two updates of slot `s' + 1` that saved these confirmations
(Lemma 40) saved compatible blocks (Lemma 31), the support cutoff of slot `s'` being after `GST`
and inside both awake windows.





The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `A'`: that update's
  answer; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote;
- `tree`: a voter tree of `w` for slot `s + 1`; `W`: a viable head in it; `H_w`: the block `vote`
  names.

Read aloud: once the support cutoff of every slot from `s + 1 − S.C.k` to `s` is at or after
`GST`, the lock `v` makes at slot
`s` is extended by the Goldfish vote every honest `w` sends at the vote time of slot `s + 1`, when
`v` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff, `w`
from that start to its vote time, `w`'s finalized block is the root of its fork choice or an
ancestor of it, that root is compatible with the lock block, and, when the root is the lock block
or an ancestor of it, some block of `w`'s voter tree that is the lock block or a descendant of it
is a viable head.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 21 and Lemma 42, which the proof calls
at slot `s`, take blocks as held up to the support cutoff of slot `s + 1`; Lemma 31 reads at an
earlier slot. -/
theorem lem45_honest_vote_extends_lock_of_post_GST_window (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (v w : V) (A' : ACState V) (e : LockEntry V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from the support cutoff of slot `s + 1 − C.k` on
    (hGST : GST ≤ supportCutoff S (s + 1 - S.C.k))
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `w` is awake and honest from the duty window's start of slot `s + 1` to its vote time
    (hw : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1` answers `A'`, with `e` the lock entry of slot `s` it adds
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (he : e ∈ A'.lock_entries)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the finality-gadget conditions at `w`, relative to the lock block (as Lemma 21's)
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible e.B = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq e.B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          e.B.AncestorEq W)
    -- `w` put `vote` on the wire at its tick at the vote time of slot `s + 1`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ e.B.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem45_honest_vote_extends_lock_of_post_GST_window S Sched
    x GST s v w A' e vote hDiv hMono hSync hCatch hRoots hParent hGST hv hw hUpdate he
    hd hF2 hF3 hSend

/-- **Lemma 43, two live locks made after `GST` are compatible.** In an execution that reaches every
time, with permanent corruption, blocks and Goldfish votes delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), roots
naming blocks, and parents held at delivery: when `GST` is at most the vote time of slot `s₁`; the
slot `s` has started by the time `t`; `v` and `w` are awake and honest at every time from the duty
window's start of slot `s` to `t`; `e_v` is a lock entry of `v`'s node state before `t`, live at
`t`, with a deadline at least `S.C.t_ (s₁ + S.C.k) + 5 · S.C.Δ`, the deadline of a lock of slot
`s₁`; `e_w` likewise at `w`; and `w`'s finalized block before `t` is compatible with `e_v`'s block,
and `v`'s with `e_w`'s: then `e_v`'s block is compatible with `e_w`'s.

Why: the statement is symmetric in `v` and `w`; write `s' ≤ s''` for the slots of the two locks
(Lemma 39). Both are at least `s₁`, and `s' ≥ s − S.C.k − 1`, since `e_w` is live at `t`, so the
update of slot `s' + 1` and every later time the proof reads are inside the awake windows. When
the two slots are equal, or `e_v`'s block passes the slow test, both blocks are ancestors-or-equal
of the two validators' saved confirmations of slot `s'` (Lemmas 37, 39, 40), which their updates
of slot `s' + 1` saved compatible (Lemma 31); Lemma 31's awake windows come from the duty tests
of those updates, since a validator whose tick records that it has been awake since a time `τ`,
and that is awake and honest at that tick, has been awake at every time since `τ`. When
`s' < s''` and `e_v`'s block is a fast block of `v`'s update: if `e_v`'s block is an
ancestor-or-equal of `w`'s finalized block, `e_w`'s block, in `w`'s frame tree, descends from it;
otherwise Lemma 34 at slot `s''` applies, with Lemma 42 for `w`'s revocation of slot `s'' + 1`,
whose duty test passes because the `awakeSince` of `w`'s own update of slot `s' + 1` is kept
while `w` stays awake.

The proof does not call Lemma 33: when it was written, Lemma 33's hypothesis asked the saved
confirmations to be compatible at every slot from `s'' + 1 − S.C.k` to `s''`, and a slot of that
range may be before `s₁`, where Lemma 31's synchrony hypothesis does not hold.
Lemma 31's awake windows are not inside `[dutyWindowStart S s, t]` when `s' = s − S.C.k − 1` (a
lock of that slot is live from the start of slot `s` to before its vote time); the proof takes
them from the updates' duty tests.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₁`: a slot whose vote time is at or after `GST`; `s`: a slot started
  by `t`; `t`: the time;
- `v`, `w`: the two validators; `e_v`, `e_w`: their lock entries.

Read aloud: at a time `t` of a slot `s` that has started, two lock entries live at `t`, held by two
validators awake and honest since the duty window's start of slot `s`, each the lock of a slot at
least `s₁`, are on compatible blocks, when `GST` is at most the vote time of slot `s₁` and each
validator's finalized block before `t` is compatible with the other's lock block.

Roots name blocks until `t`: Lemma 31 and Lemma 42, which the proof calls at the slots of the
two entries, take blocks as held up to support cutoffs before `t`
(`lem39_lock_entry_provenance`). -/
theorem lem43_live_locks_after_GST_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s₁ s t : ℕ) (v w : V) (e_v e_w : LockEntry V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold
    (hRoots : RootsNameBlocksUntil S Sched x t)
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- `GST` is at most the vote time of slot `s₁`
    (hGST : GST ≤ voteTime S s₁)
    -- slot `s` has started by `t`
    (hst : slotStart S s ≤ t)
    -- `v` and `w` are awake and honest from the duty window's start of slot `s` through `t`
    (hv : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int))
    (hw : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `e_v` is an entry of `v`'s state before `t`, live at `t`, of a slot at least `s₁`
    (he_v : e_v ∈ (stateBefore x t v).A.lock_entries)
    (hlive_v : is_live (fg_to_ac (stateBefore x t v).S) (t : Int) e_v = true)
    (hd_v : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_v.d)
    -- likewise `e_w` at `w`
    (he_w : e_w ∈ (stateBefore x t w).A.lock_entries)
    (hlive_w : is_live (fg_to_ac (stateBefore x t w).S) (t : Int) e_w = true)
    (hd_w : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_w.d)
    -- each validator's finalized block before `t` is compatible with the other's lock block
    (hFwv : (stateBefore x t w).S.F.compatible e_v.B = true)
    (hFvw : (stateBefore x t v).S.F.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem43_live_locks_after_GST_compatible S Sched x GST s₁ s
    t v w e_v e_w hDiv hMono hSync hCatch hRoots hParent hGST hst hv hw he_v hlive_v
    hd_v he_w hlive_w hd_w hFwv hFvw

/-- **Lemma 44, after `GST` plus `L`, every two live honest locks are compatible.** In an execution
that reaches every time, with permanent corruption, blocks and Goldfish votes delivered within `Δ`
after `GST`, roots naming blocks, and parents held at delivery: when
`GST` is at most the vote time of slot `s₁`; `t` is at or after the vote time of slot `s₁ + S.C.k`;
the slot `s` has started by `t`; `v` and `w` are awake and honest at every time from the duty
window's start of slot `s` to `t`; `e_v` is a lock entry of `v`'s node state before `t`, live at
`t`, and `e_w` likewise at `w`; and `w`'s finalized block before `t` is compatible with `e_v`'s
block, and `v`'s with `e_w`'s: then `e_v`'s block is compatible with `e_w`'s.

Why: each entry is a lock of the slot its deadline names (Lemma 39), and a lock live at or after
the vote time of slot `s₁ + S.C.k` is of a slot at least `s₁` (Lemma 41); so both deadlines are at
least that of a lock of slot `s₁`, and Lemma 43 applies.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₁`: a slot whose vote time is at or after `GST`; `s`: a slot started
  by `t`; `t`: the time;
- `v`, `w`: the two validators; `e_v`, `e_w`: their lock entries.

Read aloud: from the vote time of slot `s₁ + S.C.k` on, any two live lock entries of two
validators awake and honest since the duty window's start of the slot in progress are on
compatible blocks, when `GST` is at most the vote time of slot `s₁` and each validator's finalized
block is compatible with the other's lock block.

Roots name blocks until `t`: Lemma 43, which the proof calls, takes blocks as held up to `t`. -/
theorem lem44_live_locks_compatible_from_GST_plus_L (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s₁ s t : ℕ) (v w : V) (e_v e_w : LockEntry V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold
    (hRoots : RootsNameBlocksUntil S Sched x t)
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- `GST` is at most the vote time of slot `s₁`
    (hGST : GST ≤ voteTime S s₁)
    -- `t` is at or after the vote time of slot `s₁ + C.k`
    (ht : voteTime S (s₁ + S.C.k) ≤ t)
    -- slot `s` has started by `t`
    (hst : slotStart S s ≤ t)
    -- `v` and `w` are awake and honest from the duty window's start of slot `s` through `t`
    (hv : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int))
    (hw : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `e_v` and `e_w` are entries of the two states before `t`, live at `t`
    (he_v : e_v ∈ (stateBefore x t v).A.lock_entries)
    (hlive_v : is_live (fg_to_ac (stateBefore x t v).S) (t : Int) e_v = true)
    (he_w : e_w ∈ (stateBefore x t w).A.lock_entries)
    (hlive_w : is_live (fg_to_ac (stateBefore x t w).S) (t : Int) e_w = true)
    -- each validator's finalized block before `t` is compatible with the other's lock block
    (hFwv : (stateBefore x t w).S.F.compatible e_v.B = true)
    (hFvw : (stateBefore x t v).S.F.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem44_live_locks_compatible_from_GST_plus_L S Sched x GST
    s₁ s t v w e_v e_w hDiv hMono hSync hCatch hRoots hParent hGST ht hst hv hw he_v
    hlive_v he_w hlive_w hFwv hFvw

end GoldilocksCorrectness.Statements.Executions
