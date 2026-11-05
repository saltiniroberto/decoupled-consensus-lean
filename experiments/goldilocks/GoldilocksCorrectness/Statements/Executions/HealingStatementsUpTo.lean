module
public import GoldilocksCorrectness.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma42UpTo

@[expose] public section

/-!
# `HealingStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/HealingStatements.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem42_fast_lock_clears_conflicting_locks`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

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
vote time of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S (s + 1)`: `supporters_vote_once_in_pool_at` reads the votes due one delay after `w`'s vote time of slot `s + 1`. -/
theorem lem42_fast_lock_clears_conflicting_locks_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (L : Block V) (v w : V) (A' : ACState V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
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
  GoldilocksCorrectness.Proofs.Executions.lem42_fast_lock_clears_conflicting_locks_upTo S Sched x GST s
    L v w A' hDiv hMono hSync hCatch hRoots hParent hGST hv hw hUpdate hFast hF

end GoldilocksCorrectness.Statements.Executions

