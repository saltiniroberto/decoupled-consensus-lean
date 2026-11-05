module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Network
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# DeliveryStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 12, an honest early
vote is held, resolved and unique in the node state of every validator awake and honest from the
vote time to the support cutoff; its two corollaries; and delivery within a delay on the delivery
premises up to the deadline. Each is the theorem of `Record/Restated/Proofs/Executions/Lemma12.lean`
or `Record/Restated/Proofs/Executions/Network.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (acObject)

open GoldilocksCorrectness.Record.Statements.Routines (EarlyVoteOnceFor VotesOnceInPoolFor)

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

/-- **Lemma 12, an honest early Goldfish vote reaches every awake honest validator.** In an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the vote time of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at the tick of the vote
time of slot `s`, and holds `H u` in its tree then; `w` is awake and honest at every time from
slot `s`'s vote time to its support cutoff; and `w`'s finalized block before the vote time of
slot `s + 1` is `H u` or an ancestor of it — then `w`'s node state before the vote time of slot
`s + 1` holds `u`'s vote for `H u` as `u`'s only slot-`s` vote, stamped and resolved strictly
before `C.t_ s + 2 · C.Δ`, with `H u` in `w`'s frame tree.





Why: the vote is on the wire at the vote time `t₁` of slot `s`, so synchrony, or catch-up on `w`'s
last wake, delivers it to `w` strictly before `t₁ + Δ`, the support cutoff; at the delivery `w`'s
clock is the delivery's time, in slot `s`, and `on_goldfish_vote` admits the vote unless `w`
already holds two slot-`s` votes of `u`, which cannot be, since every copy of a vote of `u` on the
wire descends from `u`'s own tick and a tick sends one vote. `H u` was put on the wire by `u`
before `t₁` and reaches `w` before the support cutoff too; `w` admits it, each test of
`block_admissible` passing from what `u`'s tree satisfies, from `hRoots` and `hParent`, and from
`w`'s finalized block being an ancestor of `H u`. Both stamps are the delivery times, strictly
before the support cutoff, and `H u`'s slot is at most `s`, so the vote resolves at the later of
the two.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for; `w`: the
  validator the votes reach.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the proof takes `H u` as held by `w` at its
delivery, before the support cutoff of slot `s`.

Read aloud: an honest early vote of slot `s` is held, resolved and unique in the node state before
the next vote time of every validator awake and honest from the vote time to the support cutoff.

Under T-RC6-1:
`w` is read up to its own tick to the support cutoff of slot `s`, active from `tStartW`, more than both clock
bounds before the earlier of the start of slot `s` and `supportCutoff s − max (Δ S) Δs`
(`supportCutoff s − max (2 * Δ S) Δs`); the conclusion is on the node state that tick starts from.

Read aloud (T-RC6-1): `w` is active from more than both clock bounds before the earlier of the start of slot
`s` and the time the sync fact is read at, up to its own tick to the support cutoff of slot `s`, and its
finalized block in the state that tick starts from is `H u` or an ancestor of it; then that state holds
`u`'s vote for `H u` as `HeldEarlyVoteFor` says.



Read aloud: each voter stays up and honest for one sync delay from the time the sync fact is
read at. -/
theorem lem12_honest_vote_delivered (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.supportCutoff S.C s)) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from `tStartW`, more than both clock bounds before the earlier of the start of slot `s` and
    -- one delay or one sync delay before the support cutoff, up to its own tick to the support cutoff of slot `s`
    -- (T-RC6-1:'s reader,'s bound)
    (tStartW : ℤ)
    (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.supportCutoff S.C s))
    (hF : ∀ u ∈ Hs, (x.tickInput w (M.supportCutoff S.C s)).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w (M.supportCutoff S.C s)) s (H u) u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem12_honest_vote_delivered M F U) S A x R GST s Hs H w E hNet hSkew hRedeliver Sy hΔs
     hRoots hParent hOwner hGST hHs hHold tStartW htStartW hw hF

/-- **Lemma 12 at any later time, an honest early Goldfish vote stays with every awake honest
validator.** Lemma 12 with the vote time of slot `s + 1` replaced by any time `t₃` from the support
cutoff of slot `s` on. Under the assumptions of Lemma 12 (every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block reaches a validator only
once it holds the parent, nobody votes in an honest validator's name): if `GST` is at most the vote
time of slot `s`; `t₃` is the support cutoff of slot `s` or later; every `u ∈ Hs` is in the
slot-`s` committee, honest through `t₃`, put its slot-`s` vote for `H u` on the wire at the tick of
the vote time of slot `s`, and holds `H u` in its tree then; `w` is awake and honest at every time
from slot `s`'s vote time to its support cutoff; and `w`'s finalized block before `t₃` is `H u` or
an ancestor of it — then `w`'s node state before `t₃` holds `u`'s vote for `H u` as `u`'s only
slot-`s` vote, stamped and resolved strictly before `C.t_ s + 2 · C.Δ`, with `H u` in `w`'s frame
tree.

 Lemma 12 is its instance at `t₃ := M.voteTime S.C (s + 1)`.

Why: as for Lemma 12. The vote and `H u` reach `w` strictly before the support cutoff of slot `s`,
and `w` keeps them from then to `t₃`; the vote time of slot `s + 1` entered Lemma 12's proof only as
a time at least that cutoff, up to which `u` is honest.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t₃`: the time `w`'s state is read before;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for; `w`: the
  validator the votes reach.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the proof takes `H u` as held by `w` at its
delivery, before the support cutoff of slot `s`, whatever `t₃` is.

Read aloud: an honest early vote of slot `s` reaches, by the support cutoff, every validator awake
and honest from the vote time to the support cutoff, and is held, resolved and unique in its node
state before any later `t₃` up to which the voter stays honest.

Under T-RC6-1: the time `t₃` is a clock value `c` of `w`, at least the support cutoff of slot `s`, to which
`w` ticks at the step `kc`, with no restart of `w` that loses its memory between its tick to the cutoff
and `kc`, and the voters outside the adversary set at `kc`; `w`'s window is as in Lemma 12's base form.

Read aloud (T-RC6-1): `w` ticks to a clock value `c` at least the support cutoff at the step `kc`, with
no memory-losing restart between its tick to the cutoff and `kc`, and the voters are honest at `kc`;
then the state `kc` starts from holds the vote.



Read aloud: each voter stays up and honest for one sync delay from the time the sync fact is
read at. -/
theorem lem12_honest_vote_delivered_until (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `w` ticks at `kc` to a clock value `c` at least the support cutoff of slot `s`, with no restart of `w`
    -- that loses its memory between its tick to the cutoff and `kc`
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hkeep : ∀ (l t' : ℕ), x.tickStep w (M.supportCutoff S.C s) < l → l < kc →
      x.lbl l ≠ Event.restart w t' false)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from `tStartW`, more than both clock bounds before the earlier of the start of slot `s` and
    -- one delay or one sync delay before the support cutoff, up to its own tick to the support cutoff of slot `s`
    -- (T-RC6-1:'s reader,'s bound)
    (tStartW : ℤ)
    (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.supportCutoff S.C s))
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w c) s (H u) u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem12_honest_vote_delivered_until M F U) S A x R GST s c Hs
    H w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hc kc hkc hkeep hHs hHold tStartW htStartW hw hF

omit [RootOrder] in
/-- **The delivery lemma's conclusion is what `lem8b` reads for a voter.** When `n` holds `u`'s
slot-`s` vote for `H_u` as `HeldEarlyVoteFor` says, `u` has exactly one slot-`s` vote in `n`'s
pool, its head is `H_u`'s root, and it resolves strictly before `C.t_ s + 2 · C.Δ`
(`EarlyVoteOnceFor`).

Why: the vote of `HeldEarlyVoteFor` is that vote; the stamp bound and `H_u` in the frame's tree are
not needed.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`: the node state;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: a held early vote is an early vote, the voter's only one of the slot. -/
theorem heldEarlyVoteFor_earlyVoteOnceFor (C : Config) (n : M.N) (s : Slot)
    (H_u : Block V) (u : V) (h : HeldEarlyVoteFor M C n s H_u u) :
    EarlyVoteOnceFor M C n s H_u u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.heldEarlyVoteFor_earlyVoteOnceFor M F) C n s H_u u h

omit [RootOrder] in
/-- **The delivery lemma's conclusion is what `lem5` reads for a voter.** When `n` holds `u`'s
slot-`s` vote for `H_u` as `HeldEarlyVoteFor` says, `u` has exactly one slot-`s` vote in `n`'s
pool, it resolves, and its head is the root of a block of the frame's tree that is `H_u` or a
descendant of `H_u` (`VotesOnceInPoolFor`, with `H_u` itself as that block).

Why: the vote of `HeldEarlyVoteFor` is that vote, its head is `H_u`'s root, and `H_u` is in the
frame's tree.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`: the node state;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: a held early vote is the voter's only vote of the slot in the pool, for a block of the
frame's tree. -/
theorem heldEarlyVoteFor_votesOnceInPoolFor (C : Config) (n : M.N)
    (s : Slot) (H_u : Block V) (u : V) (h : HeldEarlyVoteFor M C n s H_u u) :
    VotesOnceInPoolFor M n s H_u u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.heldEarlyVoteFor_votesOnceInPoolFor M F) C n s H_u u h

end GoldilocksCorrectness.Record.Statements.Executions

