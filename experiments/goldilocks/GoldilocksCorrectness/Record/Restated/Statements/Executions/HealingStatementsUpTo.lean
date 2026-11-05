module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42UpTo
public import GoldilocksCorrectness.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealingStatementsUpTo, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/HealingStatementsUpTo.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 42, a fast lock
clears every conflicting lock, with the delivery premises up to a bound. It is the theorem of the
same name of `Record/Restated/Proofs/Executions/Lemma42UpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked
  VotesOnceInPoolFor)
open GoldilocksCorrectness.Statements.Executions (acObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose votes `v`'s update of slot `s + 1` counts;
- `L`: the fast block; `v`: the validator whose update makes `L` fast; `w`: the validator whose
  revocation is read; `n'`: the node state `v`'s update leaves; `n''`: a node state `w`'s
  revocation may leave; `e`: a lock entry of `n''`.

Read aloud: when `v`'s update of slot `s + 1` makes `L` a fast block, every lock entry that `w`'s
revocation of slot `s + 1` leaves is on a block compatible with `L`, provided `GST` is at most
the support cutoff of slot `s`, `v` is active from `tStart` up to its tick to the support cutoff
of slot `s + 1`, `w` from `tStartW` up to its tick to the view freeze of slot `s`, and `w`'s finalized
block at its tick to the vote time of slot `s + 1` is compatible with `L`.

Read at the validators' own ticks (T-RC8-2): `v`'s update at its tick to the support cutoff of slot
`s + 1`, `w`'s revocation and finalized block at its tick to the vote time of slot `s + 1`; the holders
active for the sync delay after the read times. Roots name blocks until the latest real
time of `w`'s tick to the view freeze of slot `s`: `supporters_vote_once_in_pool_at`, which the proof
calls with `t_e := M.supportCutoff S.C s`, reads a block as delivered before that tick.

Restated with the delivery premises up to `M.supportCutoff S.C (s + 1)`:
`supporters_vote_once_in_pool_at` reads the votes due one delay after `w`'s vote time of slot
`s + 1`. -/
theorem lem42_fast_lock_clears_conflicting_locks_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (L : Block V) (v w : V) (n' : M.N)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
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
  (GoldilocksCorrectness.Record.Proofs.Executions.lem42_fast_lock_clears_conflicting_locks_upTo M F U) S
    A x R GST s L v w n' E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST tStart htStart hv tStartW
    htStartW hw hv₀ hw₀ hUpdate hFast kV hkV hF

end GoldilocksCorrectness.Record.Statements.Executions

