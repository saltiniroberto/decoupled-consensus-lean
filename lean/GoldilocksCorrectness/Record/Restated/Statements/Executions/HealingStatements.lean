module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma34
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma44
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealingStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealingStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the lock lemmas of the healing
argument (Lemmas 33, 34, 42, 43, 44 and 45). Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma33.lean`, `Lemma34.lean`, `Lemma42.lean`, `Lemma43.lean`,
`Lemma44.lean` or `Lemma45.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked
  VotesOnceInPoolFor)
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated EarlySupporterOf
  VoterTreeAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 42, a fast lock clears every conflicting lock.** When `v`'s confirmation update of
slot `s + 1` makes `L` a fast block, every lock entry that `w`'s revocation of slot `s + 1` leaves
is on a block compatible with `L`. This holds in an execution that reaches every time, with
permanent corruption, the network synchronous from `GST`, roots naming
blocks, and parents held at delivery, when `GST` is at most the support cutoff of slot `s`; `v` is
active from a time `tStart` up to its tick to the support cutoff of slot `s + 1`, `tStart` strictly
before that cutoff less `max (6 * Δ S) Δs` and by more than `ΔClockAhead + ΔClockBehind`; `w` is active from a time `tStartW`, more than `ΔClockAhead + ΔClockBehind` before the view freeze of slot `s` less `max (3 * Δ S) Δs`, up to its tick to that view freeze; and `w`, ticking to the vote time of slot `s + 1`, has its finalized block there compatible
with `L`. Read at the validators' own ticks (T-RC8-2): `v`'s update at its tick to the support cutoff of
slot `s + 1`, `w`'s revocation at its tick to the vote time of slot `s + 1`; the holders `v` and `w`
active for the sync delay after the read times.

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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose votes `v`'s update of slot `s + 1` counts;
- `L`: the fast block; `v`: the validator whose update makes `L` fast; `w`: the validator whose
  revocation is read; `n'`: the node state `v`'s update leaves; `n''`: a node state `w`'s revocation
  may leave; `e`: a lock entry of `n''`.

Read aloud: when `v`'s update of slot `s + 1` makes `L` a fast block, every lock entry that `w`'s
revocation of slot `s + 1` leaves is on a block compatible with `L`, provided `GST` is at most
the support cutoff of slot `s`, `v` is active from `tStart` up to its tick to the support cutoff
of slot `s + 1`, `w` from `tStartW` up to its tick to the view freeze of slot `s`, and `w`'s finalized
block at its tick to the vote time of slot `s + 1` is compatible with `L`.

Roots name blocks until the latest real time of `w`'s tick to the view freeze of slot `s`:
`supporters_vote_once_in_pool_at`, which the proof calls with `t_e := M.supportCutoff S.C s`, reads a
block as delivered before that tick (T-RC8-2). -/
theorem lem42_fast_lock_clears_conflicting_locks (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (L : Block V) (v w : V) (n' : M.N)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the latest real time of `w`'s tick
    -- to the view freeze of slot `s`, the one receiver of a block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from one delay or one sync delay before the view freeze of slot `s`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- the holders: `v` active for the sync delay after the view freeze of slot `s` less one
    -- delay or one sync delay, whichever is longer; `w` for the sync delay after the support cutoff of
    -- slot `s + 1` less the same
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v`'s update of slot `s + 1`, at its tick to the support cutoff of slot `s + 1`, leaves `n'` and makes
    -- `L` a fast block (T-RC8-2,)
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hFast : L ∈ n'.fastBlocks)
    -- `w` ticks to the vote time of slot `s + 1` at `kV`, and its finalized block there is compatible with `L`
    (kV : ℕ) (hkV : x.lbl kV = Event.tick w (M.voteTime S.C (s + 1)))
    (hF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible L = true) :
    -- then every lock entry `w`'s revocation of slot `s + 1` at that tick leaves is on a block compatible
    -- with `L`
    ∀ n'' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n'' →
      ∀ e ∈ n''.lockEntries, e.B.compatible L = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem42_fast_lock_clears_conflicting_locks M F U) S
    A x R GST s L v w n' E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST tStart htStart hv tStartW
    htStartW hw hv₀ hw₀ hUpdate hFast kV hkV hF

/-- Write `c` for the support cutoff of slot `s + 1`, the
time of the confirmation update of slot `s`, and `k` for `S.C.k`. In an execution that reaches
every time: when, for the slot `s'` whose lock deadline `S.C.t_ (s' + k) + 5 · S.C.Δ` is `e_w`'s,
`v` and `w` each tick to `c`, the saved confirmations of slot `s'` on the node states those ticks
leave are compatible whenever both are present; `e_v` is a lock entry of the state `v`'s tick leaves
with the deadline of a lock of slot `s`, `S.C.t_ (s + k) + 5 · S.C.Δ`; `e_w` is a lock entry of the
state `w`'s tick leaves whose deadline is after `c + 1`; and either `e_v`'s block passes the slow
test of slot `s` on the state `v`'s tick starts from, or `e_w` has `e_v`'s deadline; then `e_v`'s
block is compatible with `e_w`'s. Every state is read at its validator's own tick to `c` (T-RC5-1).

Why: `e_w` is a lock of a slot `s'` whose update, `w`'s tick to the support cutoff of slot
`s' + 1`, ran at or before `w`'s tick to `c`; `w` does not set its clock back, so `s' ≤ s`; its block
is `w`'s saved confirmation of slot `s'` on the state `w`'s tick to `c` leaves or an ancestor of it;
it is still live at `c + 1`, so `s' ≥ s + 1 − k` (Lemma 41). When `s' = s`, `e_v`'s block is likewise
`v`'s saved confirmation of slot `s` or an ancestor of it. When `s' < s`, the deadlines differ, so
`e_v`'s block passed the slow test, and Lemma 37 makes it `v`'s saved confirmation of slot `s'` on
the state its tick to `c` starts from or an ancestor of it, kept by that tick. The hypothesis on the saved confirmations at slot `s'`, the slot
`e_w`'s deadline names, makes the two saved confirmations compatible, and two ancestors-or-equal
of compatible blocks are compatible. No network assumption enters.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `v`'s lock, whose
  update runs at the support cutoff of slot `s + 1`;
- `v`, `w`: the two validators; `e_v`: `v`'s lock entry of slot `s`; `e_w`: `w`'s live lock entry;
- `s'`: the slot whose lock deadline `e_w` has; `Cv`, `Cw`: `v`'s and `w`'s saved confirmations of
  slot `s'`.

Read aloud: when `v`'s and `w`'s saved confirmations of the slot `e_w`'s deadline names are
compatible, a lock `v` makes at slot `s` that passes the slow test is compatible with the lock
`e_w` that `w` holds live just after, and so are two locks the two made at slot `s`. -/
theorem lem33_slow_lock_compatible_of_slotwise_confirmations (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s : ℕ) (v w : V) (e_v e_w : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `v` and `w` each tick to the support cutoff `c` of slot `s + 1` (T-RC5-1)
    (htick_v : x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)))
    (htick_w : x.lbl (x.tickStep w (M.supportCutoff S.C (s + 1))) = Event.tick w (M.supportCutoff S.C (s + 1)))
    -- at the slot `s'` whose lock deadline `e_w` has, the saved confirmations of slot `s'` of `v`
    -- and `w`, on the states their ticks to `c` leave, are compatible
    (hCompat : ∀ s' : ℕ, e_w.d = S.C.t_ (s' + S.C.k) + 5 * S.C.Δ → ∀ Cv Cw : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s' = some Cv →
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s' = some Cw →
      Cv.compatible Cw = true)
    -- `e_v` is a lock entry of slot `s` on the state `v`'s tick to `c` leaves
    (he_v : e_v ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries)
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- `e_w` is a lock entry on the state `w`'s tick to `c` leaves, with its deadline after `c + 1`
    (he_w : e_w ∈ (x.tickOutput w (M.supportCutoff S.C (s + 1))).lockEntries)
    (hlive_w : ((M.supportCutoff S.C (s + 1) + 1 : ℕ) : Int) < e_w.d)
    -- `e_v`'s block passes the slow test of slot `s` on the state `v`'s tick to `c` starts from, or
    -- `e_w` is a lock entry of slot `s` too
    (hSlowOrSame :
      M.slow_test S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s e_v.B = true ∨
        e_w.d = e_v.d) :
    e_v.B.compatible e_w.B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem33_slow_lock_compatible_of_slotwise_confirmations M F U)
    S A x R s v w e_v e_w E htick_v htick_w hCompat he_v hd_v he_w hlive_w hSlowOrSame

/-- **Lemma 34, a fast lock against an older lock, through the revocation.** Write `t₃` for the
vote time of slot `s + 1` and `c` for its support cutoff. In an execution that reaches every
time: when `e_v` is a lock entry with the deadline of a lock of slot
`s`, `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; `e_w` is a lock entry of
`w`'s node state after its tick to `c` whose deadline is after `c + 1` and before `e_v`'s; `w` ticks
to `t₃` (at a step `kV`); `w`'s tick at `t₃` starts from a state whose `awakeSince` is some time at most the
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `e_v`'s lock;
- `w`: the validator whose revocation is read; `e_v`: a lock entry with the deadline of a lock of
  slot `s`; `e_w`: `w`'s older live lock entry; `τ`: the time `w` has been awake since; `n'`,
`sent`: an outcome of `w`'s tick at `t₃` from an awake state, which runs the revocation; `e`: a lock
entry of `n'`.

Read aloud: a lock entry `e_v` with the deadline of a lock of slot `s` is compatible with an older
lock `w` holds live in the state its tick to the support cutoff of slot `s + 1` leaves, when `w`
ticks to the vote time of slot `s + 1`, that tick
starts with the duty test of slot `s + 1` passing, and every entry `w`'s revocation of slot `s + 1`
leaves, live then, is compatible with `e_v`'s block. -/
theorem lem34_fast_lock_compatible_of_revocation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s : ℕ) (w : V) (e_v e_w : M.LE)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `e_v` has the deadline of a lock entry of slot `s`
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- `w` ticks to the support cutoff of slot `s + 1` at the step `kC`
    (kC : ℕ) (hkC : x.lbl kC = Event.tick w (M.supportCutoff S.C (s + 1)))
    -- `e_w` is a lock entry `w` holds right after the update of slot `s`, with its deadline not
    -- yet reached
    (he_w : e_w ∈ (x.tickOutput w (M.supportCutoff S.C (s + 1))).lockEntries)
    (hlive_w : ((M.supportCutoff S.C (s + 1) + 1 : ℕ) : Int) < e_w.d)
    -- `e_w` is older: a lock entry of a slot before `s`
    (hOlder : e_w.d < e_v.d)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kV`
    (kV : ℕ) (hkV : x.lbl kV = Event.tick w (M.voteTime S.C (s + 1)))
    -- `w`'s tick then starts with `awakeSince` passing the duty test of slot `s + 1`
    (hDuty : ∃ τ : Time, (x.tickInput w (M.voteTime S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1))
    -- every lock entry live at the vote time of slot `s + 1` that `w`'s revocation of slot
    -- `s + 1` leaves is compatible with `e_v`'s block
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible e_v.B = true) :
    e_v.B.compatible e_w.B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem34_fast_lock_compatible_of_revocation M F U) S A x R s w
    e_v e_w E hd_v kC hkC he_w hlive_w hOlder kV hkV hDuty hLocks

/-- **Lemma 45, a lock whose window is after `GST` is extended by the next slot's honest votes.** In
an execution that reaches every time, with permanent corruption, blocks and Goldfish votes delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
roots naming blocks, and parents held at delivery: when `GST + max (Δ S) Δs` is at most the
view freeze of slot `s + 1 − S.C.k`; `v` is awake and honest at every time from the duty window's
start of slot `s + 1` to the support cutoff of slot `s + 1`; `w` is awake and honest at every time
from the duty window's start of slot `s + 1` to the vote time of slot `s + 1`; an outcome `n'` of
`v`'s tick at that support cutoff, which runs the confirmation update of slot `s + 1` on its node
state before that support cutoff, has `e` as a lock entry, with the deadline of a lock of slot `s`,
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; on `w`'s node state before the vote time of slot `s + 1`, the
root of the fork choice is compatible with `e`'s block; when that root is `e`'s block or an ancestor
of it, some block of `w`'s voter tree for slot `s + 1` that is `e`'s block or a descendant of it is
a viable head; and `w` put the Goldfish vote `vote` on the wire at its tick at the vote time of slot
`s + 1`: then `vote`'s head is the root of a block that is `e`'s block or a descendant of it.

Why: `e` is not an entry of the update's input, since such an entry was added by the update of its
own slot before the support cutoff (Lemma 39), and the deadline names the slot. So `e`'s block is
the saved confirmation of slot `s` or an ancestor of it, a fast block of `n'` or passing the slow
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `n'`, `sent`: an outcome
of `v`'s tick at the support cutoff of slot `s + 1`, which runs that update; `w`: the voter of slot
`s + 1`; `vote`: its Goldfish vote;
- `tree`: a voter tree of `w` for slot `s + 1`; `W`: a viable head in it; `H_w`: the block `vote`
  names.

Read aloud: once the recovery delay `max (Δ S) Δs` after `GST` has elapsed by the view freeze of slot
`s + 1 − S.C.k`, the lock `v` makes at slot
`s` is extended by the Goldfish vote every honest `w` sends at the vote time of slot `s + 1`, when
`v` is active from the duty window's start of slot `s + 1` up to its tick to its support cutoff, `w`
from that start to its vote time, `w`'s finalized block is the root of its fork choice or an
ancestor of it, that root is compatible with the lock block, and, when the root is the lock block
or an ancestor of it, some block of `w`'s voter tree that is the lock block or a descendant of it
is a viable head.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 21 and Lemma 42, which the proof calls
at slot `s`, take blocks as held up to the support cutoff of slot `s + 1`; Lemma 31 reads at an
earlier slot. -/
theorem lem45_honest_vote_extends_lock_of_post_GST_window (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (v w : V) (e : M.LE) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the support cutoff of slot `s + 1 − C.k` on
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s + 1 - S.C.k))
    -- `v` is active from the duty window's start of slot `s + 1` up to its tick to that slot's
    -- support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `w` is awake and honest from the duty window's start of slot `s + 1` to its vote time
    -- `w` ticks to the vote time of slot `s + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most `tStartW`, more than both clock bounds before the window start Lemma 42 reads; `v` and
    -- `w` are active through the sync delay after the two read times of Lemma 42's sync facts
    (tStartW : ℤ) (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.voteTime S.C (s + 1)))
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (n' : M.N) (sent : List (NamedObject V))
    -- `v`'s update of slot `s + 1` leaves `n'`, with `e` the lock entry of slot `s` it adds
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (he : e ∈ M.lockEntries n')
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the finality-gadget conditions at `w`, relative to the lock block (as Lemma 21's)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible e.B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq e.B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          e.B.AncestorEq W)
    -- `w` put `vote` on the wire at its tick at the vote time of slot `s + 1`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ e.B.AncestorEq H_w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem45_honest_vote_extends_lock_of_post_GST_window M F U)
    S A x R GST s v w e vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hv tStartW htStartW hw hv₀ hw₀ n' sent hUpdate
    hAwake he hd hF2 hF3 hSend

/-- **Lemma 43, two live locks made after `GST` are compatible.** In an execution that reaches every
time, with permanent corruption, blocks and Goldfish votes delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), roots
naming blocks, and parents held at delivery: when `GST` is at most the vote time of slot `s₁`; the
slot `s` has started by the clock value `c`; `v` and `w` are active from their ticks to a clock value
at most `tStart`, which is before the support cutoff of slot `s − S.C.k`, up to their ticks to `c`,
and active at every step at a real time in the delay before the real time `c`; `e_v` is a lock entry
of `v`'s node state at its tick to `c`, live at `c` by `v`'s clock, with a deadline at least
`S.C.t_ (s₁ + S.C.k) + 5 · S.C.Δ`, the deadline of a lock of slot `s₁`; `e_w` likewise at `w`; and
`w`'s finalized block at its tick to `c` is compatible with `e_v`'s block, and `v`'s with `e_w`'s: then
`e_v`'s block is compatible with `e_w`'s.

Every state is read at its validator's own tick to `c`: `v`'s and `w`'s node
states, their lock entries, the liveness test and the finalized blocks.

Why: the statement is symmetric in `v` and `w`; write `s' ≤ s''` for the slots of the two locks
(Lemma 39). Both are at least `s₁`, and `s' ≥ s − S.C.k − 1`, since `e_w` is live at `c`; the two
updates of slots `s' + 1` and `s'' + 1` are at the validators' ticks to the support cutoffs, before
their ticks to `c` (`clock_mono`), past the duty test. When the two slots are equal, or `e_v`'s block
passes the slow test, both blocks are ancestors-or-equal of the two validators' saved confirmations of
slot `s'` (Lemmas 37, 39, 40), which their updates of slot `s' + 1` saved compatible (Lemma 31); Lemma
31's windows come from the duty tests of those updates: a validator whose tick records that it has been
awake since a clock value `τ` ticked to `τ` after its last restart and has been active since. When
`s' < s''` and `e_v`'s block is a fast block of `v`'s update: if `e_v`'s block is an ancestor-or-equal
of `w`'s finalized block, `e_w`'s block, in `w`'s frame tree, descends from it; otherwise `w`'s tick to
the vote time of slot `s'' + 1`, inside its window and past the duty test of its own update of slot
`s' + 1`, ran the revocation of slot `s'' + 1`, whose every lock entry is compatible with `e_v`'s
fast block (Lemma 42), and `e_w` descends from one of them (Lemma 39).

The proof does not call Lemma 33: when it was written, Lemma 33's hypothesis asked the saved
confirmations to be compatible at every slot from `s'' + 1 − S.C.k` to `s''`, and a slot of that
range may be before `s₁`, where Lemma 31's synchrony hypothesis does not hold. It does not
call Lemma 34 either: the revocation's lock entries are read off `w`'s tick to the vote time of slot
`s'' + 1` directly.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`: the time from which the
  network is synchronous; `s₁`: a slot whose vote time is at or after `GST`; `s`: a slot started
  by `c`; `c`: the clock value of the read; `tStart`: the clock value the windows open at;
- `v`, `w`: the two validators; `e_v`, `e_w`: their lock entries.

Read aloud: at the clock value `c` of a slot `s` that has started, two lock entries held by `v` and `w`
at their own ticks to `c`, live at `c` by their clocks, the two validators active from their ticks to
a clock value at most `tStart` (before the support cutoff of slot `s − S.C.k`) up to their ticks to `c`
and in the delay before the real time `c`, each the lock of a slot at least `s₁`, are on compatible
blocks, when `GST` is at most the vote time of slot `s₁` and each validator's finalized block at its
tick to `c` is compatible with the other's lock block.

Roots name blocks until the real time of the later of the two ticks to `c`: Lemma 31 and Lemma 42,
which the proof calls at the slots of the two entries, take blocks as held up to ticks before those
(`lem39_lock_entry_provenance`). -/
theorem lem43_live_locks_after_GST_compatible (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s₁ s c : ℕ) (v w : V) (e_v e_w : M.LE)
    -- the execution reaches every time
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- corruption is permanent
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    -- a root names one block among what honest validators hold, until the real time of the later of
    -- `v`'s and `w`'s ticks to `c`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v c)) (x.time (x.tickStep w c))))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from `max (Δ S) Δs` before the support cutoff of slot `s₁` on
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁)
    -- slot `s` has started by the clock value `c`
    (hsc : M.slotStart S.C s ≤ c)
    -- the windows open at a clock value `tStart` before the support cutoff of slot `s − S.C.k`
    (tStart : ℕ) (htStart : tStart < M.supportCutoff S.C (s - S.C.k))
    -- `v` and `w` are active from their ticks to a value at most `tStart` up to their ticks to `c`
    (hv : v ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hw : w ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    -- `v` and `w` are active at every step at a real time in the delay before the real time `c`
    (hHoldV : v ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (hHoldW : w ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    -- `e_v` is an entry of `v`'s state at its tick to `c`, live at `c`, of a slot at least `s₁`
    (he_v : e_v ∈ (x.tickInput v c).lockEntries)
    (hlive_v : M.is_live (x.tickInput v c) (c : Int) e_v = true)
    (hd_v : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_v.d)
    -- likewise `e_w` at `w`
    (he_w : e_w ∈ (x.tickInput w c).lockEntries)
    (hlive_w : M.is_live (x.tickInput w c) (c : Int) e_w = true)
    (hd_w : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_w.d)
    -- each validator's finalized block at its tick to `c` is compatible with the other's lock block
    (hFwv : (x.tickInput w c).finalized.compatible e_v.B = true)
    (hFvw : (x.tickInput v c).finalized.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem43_live_locks_after_GST_compatible M F U) S
    A x R GST s₁ s c v w e_v e_w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hsc tStart htStart
    hv hw hHoldV hHoldW he_v hlive_v hd_v he_w hlive_w hd_w hFwv hFvw

/-- **Lemma 44, after `GST` plus `L`, every two live honest locks are compatible.** In an execution
that reaches every time, with permanent corruption, blocks and Goldfish votes delivered within `Δ`
after `GST`, roots naming blocks, and parents held at delivery: when
`GST` is at most the vote time of slot `s₁`; the clock value `c` is at or after the vote time of slot
`s₁ + S.C.k`; the slot `s` has started by `c`; `v` and `w` are active from their ticks to a clock value
at most `tStart`, which is before the support cutoff of slot `s − S.C.k`, up to their ticks to `c`,
and active at every step at a real time in the delay before the real time `c`; `e_v` is a lock entry
of `v`'s node state at its tick to `c`, live at `c` by `v`'s clock, and `e_w` likewise at `w`; and
`w`'s finalized block at its tick to `c` is compatible with `e_v`'s block, and `v`'s with `e_w`'s: then
`e_v`'s block is compatible with `e_w`'s.

Every state is read at its validator's own tick to `c`, as in Lemma 43.

Why: each entry is a lock of the slot its deadline names (Lemma 39), and a lock live at a clock value
at or after the vote time of slot `s₁ + S.C.k` is of a slot at least `s₁` (Lemma 41); so both
deadlines are at least that of a lock of slot `s₁`, and Lemma 43 applies.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`: the time from which the
  network is synchronous; `s₁`: a slot whose vote time is at or after `GST`; `s`: a slot started
  by `c`; `c`: the clock value of the read; `tStart`: the clock value the windows open at;
- `v`, `w`: the two validators; `e_v`, `e_w`: their lock entries.

Read aloud: from the vote time of slot `s₁ + S.C.k` on, at a clock value `c` of a slot `s` that has
started, any two lock entries held by `v` and `w` at their own ticks to `c`, live at `c` by their
clocks, the two validators active from their ticks to a clock value at most `tStart` (before the
support cutoff of slot `s − S.C.k`) up to their ticks to `c` and in the delay before the real time `c`,
are on compatible blocks, when `GST` is at most the vote time of slot `s₁` and each validator's
finalized block at its tick to `c` is compatible with the other's lock block.

Roots name blocks until the real time of the later of the two ticks to `c`: Lemma 43, which the proof
calls, takes blocks as held up to it. -/
theorem lem44_live_locks_compatible_from_GST_plus_L (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s₁ s c : ℕ) (v w : V) (e_v e_w : M.LE)
    -- the execution reaches every time
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- corruption is permanent
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    -- a root names one block among what honest validators hold, until the real time of the later of
    -- `v`'s and `w`'s ticks to `c`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v c)) (x.time (x.tickStep w c))))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from `max (Δ S) Δs` before the support cutoff of slot `s₁` on
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁)
    -- `c` is at or after the vote time of slot `s₁ + C.k`
    (ht : M.voteTime S.C (s₁ + S.C.k) ≤ c)
    -- slot `s` has started by `c`
    (hsc : M.slotStart S.C s ≤ c)
    -- the windows open at a clock value `tStart` before the support cutoff of slot `s − S.C.k`
    (tStart : ℕ) (htStart : tStart < M.supportCutoff S.C (s - S.C.k))
    -- `v` and `w` are active from their ticks to a value at most `tStart` up to their ticks to `c`
    (hv : v ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hw : w ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    -- `v` and `w` are active at every step at a real time in the delay before the real time `c`
    (hHoldV : v ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (hHoldW : w ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    -- `e_v` and `e_w` are entries of the two states at the ticks to `c`, live at `c`
    (he_v : e_v ∈ (x.tickInput v c).lockEntries)
    (hlive_v : M.is_live (x.tickInput v c) (c : Int) e_v = true)
    (he_w : e_w ∈ (x.tickInput w c).lockEntries)
    (hlive_w : M.is_live (x.tickInput w c) (c : Int) e_w = true)
    -- each validator's finalized block at its tick to `c` is compatible with the other's lock block
    (hFwv : (x.tickInput w c).finalized.compatible e_v.B = true)
    (hFvw : (x.tickInput v c).finalized.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem44_live_locks_compatible_from_GST_plus_L M F U)
    S A x R GST s₁ s c v w e_v e_w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST ht hsc tStart
    htStart hv hw hHoldV hHoldW he_v hlive_v he_w hlive_w hFwv hFvw

end GoldilocksCorrectness.Record.Statements.Executions

