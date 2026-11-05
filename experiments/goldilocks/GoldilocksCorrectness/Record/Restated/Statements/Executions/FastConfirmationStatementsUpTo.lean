module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma27UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma29UpTo
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# FastConfirmationStatementsUpTo, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/FastConfirmationStatementsUpTo.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 27 and 29,
an honest confirmation update confirms, makes fast and locks a block a voter majority voted for,
with the delivery premises up to a bound. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma27UpTo.lean` or
`Record/Restated/Proofs/Executions/Lemma29UpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor EarlyVoteOnceFor)
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

/-- **Lemma 27, an honest validator's confirmation update confirms a block a voter majority voted
for.** In an execution where every time is reached, corruption is permanent, blocks and Goldfish
votes are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on
wake), a root names one block among what honest validators hold, a
block reaches a validator only once it holds the parent, and nobody votes in an honest validator's
name: if `GST` is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee,
honest through the support cutoff `t₂` of slot `s + 1`, put its slot-`s` vote for `B` on the wire
at its tick at the vote time of slot `s`, and holds `B` in its tree then; the validators with a
slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`; `B` is not the genesis block;
`v` is awake and honest at every time from the duty window's start of slot `s + 1` up to its tick to `t₂`; `v`'s
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `B`: the block their votes are for;
- `v`: the validator running the confirmation update of slot `s`.

Read aloud: if every member of `Hs` is an honest member of the slot-`s` committee that sent at the
vote time of slot `s` a vote for a non-genesis block `B` it holds, the members of `Hs` are more than
half of the validators with a slot-`s` vote in `v`'s pool before the support cutoff of slot
`s + 1`, `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to that cutoff, with
its finalized block before that cutoff `B` or an ancestor of `B`, and every lock entry live at the
vote time of slot `s + 1` that `v`'s revocation then leaves is on a block compatible with `B`, then
right after that cutoff `v` has `B` saved as the confirmation of slot `s` and its confirmed tip
advanced with `B`.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the proof takes as held by `v` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`).

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `v` by
then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem27_update_confirmation_confirms_voter_majority_block_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF1 : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    -- the block of every lock entry live at `t₃` that `v`'s revocation leaves is compatible
    -- with `B`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed =
        M.advance (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
          (x.tickInput v (M.supportCutoff S.C (s + 1))).latestConfirmed (some B) := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem27_update_confirmation_confirms_voter_majority_block_upTo M F U)
    S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hBne hv
    hF1 hLocks

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
duty window's start of slot `s + 1` up to its tick to `t₂`; and `v`'s finalized block before `t₂` is `B` or an
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
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

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the proof takes as held by `v` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`).

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `v` by
then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem29_update_confirmation_fast_locks_voter_majority_block_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    -- the slot-`s` committee is at most twice `Hs`
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF1 : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) :
    B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem29_update_confirmation_fast_locks_voter_majority_block_upTo M F U)
    S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hHalf hBne
    hv hF1

end GoldilocksCorrectness.Record.Statements.Executions

