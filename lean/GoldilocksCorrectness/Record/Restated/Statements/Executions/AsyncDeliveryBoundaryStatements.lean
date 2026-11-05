module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDeliveryBoundary
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncDeliveryBoundaryStatements, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/AsyncDeliveryBoundaryStatements.lean`
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 12 by a later
delay, the honest votes of a slot held, resolved and unique in the node state of a validator awake
and honest for one delay from a time at or after the vote time. It is the theorem of
`Record/Restated/Proofs/Executions/AsyncDeliveryBoundary.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime viewFreeze)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (acObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 12 by a later delay, the honest votes of a slot reach a validator one delay after any
time.** Under the assumptions of Lemma 12 (every time is reached, corruption is permanent, blocks
and Goldfish votes are delivered within `Δ` after `GST`, a root names one block among what honest
validators hold by `t + Δ`, a block reaches a validator only once it holds the parent, nobody votes
in an honest validator's name): if `GST` plus one delay or one sync delay is at most `t + Δ`; `t` is at or after
the vote time of slot `s`, and `t + Δ` is at most the view freeze of slot `s` and at most the clock value `c` of
`w`'s tick at step `kc`; every `u ∈ Hs` is in the slot-`s` committee, outside the adversary set at `kc`, put its
slot-`s` vote for `H u` on the wire at the tick of the vote time of slot `s`, holds `H u` in its tree then, and
is active for the sync delay from the earlier of the vote time and the read time `t + Δ − max (2 · Δ) Δs`; `w`
ticks to `t + Δ` and is active at every step from that earlier time up to that tick; and `w`'s finalized block
at its tick to `c` is `H u` or an ancestor of it — then the state `w`'s tick to `c` starts from holds `u`'s vote
for `H u` as `u`'s only slot-`s` vote, stamped and resolved strictly before `t + Δ`, with `H u` in `w`'s frame
tree.

Why: Lemma 12's proof with the delivery window `[t, t + Δ]`. The vote reaches `w` strictly before
`t + Δ`, so in slot `s` (`t + Δ` is at most the view freeze of `s`), and is admitted
(`pool_vote_at_tick_of_send`, at `w`'s tick to `t + Δ`); `H u`, held by `u` before `t`, reaches `w` by then
(`mem_T_before_add_delay` at `t`); the stamps are before `t + Δ`, and `H u`'s slot is at most `s`,
so the vote resolves at the later of the two; `u` votes once (`unique_vote_of_owner`).

Lemma 12 (`lem12_honest_vote_delivered_until`, `Statements/Executions/DeliveryStatements.lean`) is
the instance `t := M.voteTime S.C s` (its conclusion `HeldEarlyVoteFor` is `HeldEarlyVoteAt` at the
support cutoff of `s`, `heldEarlyVoteFor_iff`); it is not re-derived.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes; `t`: the
  start of the delivery window; `c`: the clock value of `w`'s tick whose input state is read; `kc`: the
  step of that tick;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for; `w`: the
  validator the votes reach.

Roots name blocks up to `w`'s own tick to `t + Δ S`: the proof takes `H u` as held by `w` at its delivery,
before that tick.

Why the receiver's window starts at the earlier of the vote time and the read time `t + Δ S − max (2 * Δ S) Δs`: the voter serves its vote's head at the vote time, and a head read
at a later time may no longer be compatible with the voter's finalized block. So each head is read at
the window's start when that is at or before the vote time, and at the vote time otherwise, and the
receiver is active from the earlier of the two; the deadline `t + Δ S` is unchanged, and the voter's
activity is asked for the sync delay `Δs` from the earlier of the two.

Read aloud: the honest votes of slot `s`, with their blocks, reach a validator awake and honest for
one delay from a time `t` at or after the vote time and at or after `GST`, strictly before `t + Δ`,
and they are in the state its tick to any clock value `c ≥ t + Δ` starts from; each vote is its voter's only
vote of the slot. -/
theorem lem12_honest_vote_delivered_by_until (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (t + Δ S))))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ t + Δ S) (htv : M.voteTime S.C s ≤ t) (htf : t + Δ S ≤ M.viewFreeze S.C s) (hc : t + Δ S ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    -- every member of `Hs` is a member of the slot-`s` committee outside the adversary set at `kc` that put its
    -- slot-`s` vote for `H u` on the wire at the tick of the vote time of `s`, holding `H u` then,
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, ⌈t₀⌉₊ + Δs]`, `t₀` the earlier
    -- of the real time of its own tick to the vote time and the sync fact's read time `t + Δ S − max (2 * Δ S) Δs`
    -- (; per voter since as amended by; the end at the clock value
    -- `⌈t₀⌉₊` the sync fact's holder window reads,, by)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x
      (min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ))
      (((⌈min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) + Δs))
    -- `w` ticks to `t + Δ S` at `kR` and is active at every step from the earlier of each voter's tick to the vote
    -- time and the sync fact's read time up to `kR` (per voter, as amended by)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (t + Δ S) ∧ ∀ u ∈ Hs,
      ∀ j : ℕ, min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j →
        j ≤ kR → w ∈ A.active j)
    -- `w`'s finalized block at its tick to `c` is `H u` or an ancestor of `H u`
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteAt M (x.tickInput w c) (((t + Δ S : ℕ) : Int)) s (H u) u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem12_honest_vote_delivered_by_until M F U) S A x R GST s t c
    Hs H w E hNet hSkew hRedeliver Sy hRoots hParent hOwner hGST htv htf hc kc hkc hHs hHold hw hF

end GoldilocksCorrectness.Record.Statements.Executions

