module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ReadingPoints
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ReadingPointStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 62 to 64 over
reading points, each read at times taken as parameters. Each is the theorem of
`Record/Restated/Proofs/Executions/ReadingPoints.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (acObject)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotesAt VoterTreeAt
  VotesOnceInPoolFor ResolvesAt AnchorAt)
open GoldilocksCorrectness.Statements.Routines (WalkEnd)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotesAt VoterTreeAt
  VotesOnceInPoolFor)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (VotesOnceFor)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 62, a vote that resolved early at one validator reaches another within one delay of
the early cutoff.** In an execution where every time is reached, corruption is permanent, blocks
and Goldfish votes are delivered within `Δ` after `GST`: if `GST` plus one delay or one sync delay,
whichever is longer, is at most `t_e + Δ S`, `t_e + Δ S` is strictly before the start of slot `s + 2`,
`v₂` ticks to `t_e + Δ S` and is active at every step up to that tick whose real time is at least
`ΔClockAhead` before the earlier of `t_e + Δ S − max (Δ S) Δs` and the start of slot `s`, `v₁` is
active at every step whose real time is in the sync delay after `t_e + Δ S − max (Δ S) Δs` and ticks to
`t_e`, then every slot-`s` vote of `v₁`'s pool in the state its tick to `c₁` starts from that resolves
(in that node state) strictly before `t_e` is in `v₂`'s pool of slot `s` in the state its tick to a clock
value `c₂ ≥ t_e + Δ S` starts from, or that pool holds two distinct votes of the vote's validator.

Read at the validators' own ticks (T-RC8-2, T-RC6-1's shape): the delivery promise and the sync fact
place a delivery before the receiver's tick, at a real time that may be up to `ΔClockBehind` after the
tick's clock value; the holder `v₁` active for the sync delay after the sync fact's read time
.

Why: the vote's stamp is less than `t_e`, so `v₁` held it before its tick to `t_e` and re-sent it then;
the re-send, or the sync fact read at `t_e + Δ S − max (Δ S) Δs`, reaches `v₂` before its tick to
`t_e + Δ S`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `c₁`: the clock value of `v₁`'s tick whose state is read; `c₂`: that of
  `v₂`'s;
- `v₁`: the validator holding the vote; `v₂`: the validator it reaches; `kR`: the step of `v₂`'s tick to
  `t_e + Δ S`; `kₑ`, `k₁`, `k₂`: the steps of `v₁`'s ticks to `t_e` and `c₁` and of `v₂`'s tick to `c₂`.

Read aloud: a vote that resolved before `t_e` at `v₁` is held by `v₂` from its tick to `t_e + Δ S` on,
unless `v₂` holds two votes of its validator.

Restated with the delivery premises up to `b`, the latest deadline being `t_e + Δ S` (`v₁`'s
re-send reaching `v₂`). -/
theorem lem62_early_vote_reaches_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e c₁ c₂ b : ℕ) (v₁ v₂ : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- the network is synchronous from the sync fact's read time on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- the re-send arrives while slot-`s` votes are still admitted
    (hhi : t_e + Δ S < M.slotStart S.C (s + 2))
    -- `v₂` ticks to `t_e + Δ S` at `kR`, and is active at every step up to that tick whose real time is at least
    -- one clock-ahead bound before the earlier of `t_e + Δ S − max (Δ S) Δs` and the start of slot `s`
    (kR : ℕ) (hkR : x.lbl kR = Event.tick v₂ (t_e + Δ S))
    (hwin₂ : ∀ i : ℕ, min ((t_e + Δ S : ℝ) - max (Δ S) Δs) (M.slotStart S.C s) - ΔClockAhead ≤ x.time i →
      i ≤ kR → v₂ ∈ A.active i)
    -- `v₂`'s node state is read at its tick `k₂` to `c₂ ≥ t_e + Δ S` (T-RC8-2)
    (h02 : t_e + Δ S ≤ c₂) (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ c₂)
    -- `v₁` is active at every step whose real time is in the sync delay after the read time
    (hv₁ : v₁ ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v₁` ticks to `t_e` at `kₑ`, and its node state is read at its tick `k₁` to `c₁`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v₁ t_e) (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ c₁)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_e + Δ S ≤ b) :
    ∀ vote ∈ M.votesHeldSet (x.tickInput v₁ c₁) s,
      (∃ y : Stamp, ResolvesAt M (x.tickInput v₁ c₁) vote y ∧
        occurrenceBefore (some y) ((t_e : ℕ) : Int) = true) →
      vote ∈ M.votesHeldSet (x.tickInput v₂ c₂) s ∨
        ∃ u₁ ∈ M.votesHeldSet (x.tickInput v₂ c₂) s,
          ∃ u₂ ∈ M.votesHeldSet (x.tickInput v₂ c₂) s,
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem62_early_vote_reaches_at M F U) S A x R GST s t_e
    c₁ c₂ b v₁ v₂ E hNet hSkew hRedeliver Sy hGST hhi kR hkR hwin₂ h02 k₂ hk₂ hv₁
    kₑ hkₑ k₁ hk₁ hb

/-- **Lemma 63, the early supporters' votes and heads reach the next voter, as their only
votes.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST`, a root names one
block among what honest validators hold, and a block reaches a validator only once it holds the
parent: under the inequalities between the times listed with the hypotheses, if `w` is active from
a time `tStartW` up to its tick to `t_e + Δ S`, `v` from a time `tStart` up to its tick to
`t_w + Δ S`, each start strictly before one delay or one sync delay, whichever is longer, before
that tick's clock value, and by more than `ΔClockAhead + ΔClockBehind`, each
member of `Sup` is an early supporter of `B`'s chain on `v`'s state at its tick to `t_v` with the cutoff
`t_e` (`EarlySupporterAt`), and `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`,
then:
- each member `u` of `Sup` has a vote `vote_u` in `w`'s pool of slot `s` at its tick to `t_f`, stamped
  strictly before `t_f`; its head is the root of a block `H_u` of `w`'s tree at its tick to `t_f`, stamped
  strictly before `t_f`, that is `B` or a descendant of `B`, of slot at most `s`; and every
  slot-`s` vote of `u` that `w` holds at its tick to `t_w` is `vote_u`;
- every slot-`s` vote of a member of the slot-`s` committee that `w` holds at its tick to `t_w` is in
  `v`'s pool of slot `s` at its tick to `t_v`, or that pool holds two distinct votes of its validator.
The stamps are those of `w`'s state at its tick to `t_w`.

Why: `u`'s vote resolved at `v` before `t_e`, so `v` held it at its tick to `t_e`, re-sent it, and it
reaches `w` before `w`'s tick to `t_e + Δ S`; its head block too, held by `v` at that tick and compatible with
`w`'s finalized block (block propagation). A vote `w` holds at its tick to `t_w` reaches `v` before its tick to
`t_w + Δ S`, where `u` has one vote; so `w` holds no second vote of `u`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the clock value of `w`'s tick whose
  state is read; `t_v`: that of `v`'s tick;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block;
- `v`: the validator at which the members of `Sup` are early supporters; `w`: the voter;
- `tStart`, `tStartW`: the starts of `v`'s and `w`'s windows; `kₑ`, `k_v`: the steps of `v`'s ticks to `t_e`, `t_v`;
  `k_f`, `k_w`: those of `w`'s ticks to `t_f`, `t_w`.

Read aloud: the early supporters' votes and head blocks that `v` holds are held by `w` before
`t_f`, and `w` holds no other vote of theirs; and what `w` re-sent reaches `v` by `t_v`.

Read at the validators' own ticks (T-RC8-2, T-RC6-1's shape); roots name blocks until the latest real
time of `w`'s tick to `t_e + Δ S`. Restated with the delivery premises up to `b`, the latest deadline being `t_w + Δ S`
(`w`'s re-sends reaching `v`; the re-sends from `v` reach `w` by `t_e + Δ S ≤ t_w + Δ S`). -/
theorem lem63_supporters_counted_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup, ∃ vote_u ∈ M.votesHeldSet (x.tickInput w t_f) s, vote_u.val_index = u ∧
      (∃ τ : Stamp, (x.tickInput w t_w).voteStamp vote_u = some τ ∧
        τ < (((t_f : ℕ) : Int) : Stamp)) ∧
      (∃ H_u ∈ (x.tickInput w t_f).tree, H_u.root = vote_u.head ∧ B.AncestorEq H_u ∧
        H_u.slot ≤ s ∧
        ∃ st : Stamp, (x.tickInput w t_w).blockStamp H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
      ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index = u →
        vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
        vote' = vote_u) ∧
    (∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
      vote' ∈ M.votesHeldSet (x.tickInput v t_v) s ∨
        ∃ v₁ ∈ M.votesHeldSet (x.tickInput v t_v) s,
          ∃ v₂ ∈ M.votesHeldSet (x.tickInput v t_v) s,
            v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem63_supporters_counted_at M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w E hNet hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw tStart htStart htStartSlot hv hv₀ hw₀ kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hF hb

/-- Lemma 63 read on the sets of votes `w` counts. Under the hypotheses of Lemma 63, if moreover
the validators with a slot-`s` vote in `v`'s pool at its tick to `t_v` are fewer than twice `Sup`, and
`votes`, `support_votes` are the sets of votes the Goldfish vote of slot `s + 1` counts on `w`'s
state at its tick to `t_w` with the cutoff `t_f` (`CountedVotesAt`), then each member of `Sup` votes once
for `B`'s chain among them (`VotesOnceFor`), with its head block in `w`'s tree at its tick to `t_w` stamped
strictly before `t_f`; the validators with a vote in `votes` are fewer than twice `Sup`; and every
support vote is in `votes`.

Why: Lemma 63's vote of each member is a pool vote of `w` stamped and resolved before `t_f`, so a
counted support vote; every vote `w` counts was held by `w` at its tick to `t_w` (as a pool vote or as a
vote included in a block of its tree), so it is the member's own vote, and its validator has a
vote in `v`'s pool at its tick to `t_v`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the clock value of `w`'s tick whose
  state is read; `t_v`: that of `v`'s tick;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block;
- `v`: the validator at which the members of `Sup` are early supporters; `w`: the voter;
- `votes`, `support_votes`: the two sets `w` counts; `tStart`, `tStartW`: the starts of `v`'s and
  `w`'s windows; `kₑ`, `k_v`: the steps of `v`'s ticks to `t_e`, `t_v`;
  `k_f`, `k_w`: those of `w`'s ticks to `t_f`, `t_w`.

Read aloud: everything `v` counted as early support for `B`'s chain is counted by `w` as support
for `B`'s chain, and `w` counts no voter that `v` did not see.

Read at the validators' own ticks (T-RC8-2, T-RC6-1's shape); roots name blocks until the latest real
time of `w`'s tick to `t_e + Δ S`. Restated with the delivery premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls). -/
theorem supporters_vote_once_counted_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (votes support_votes : Finset (GoldfishVote V))
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    (hEligible : M.voters_count (M.votesHeldSet (x.tickInput v t_v) s) < 2 * Sup.card)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    (hCounted : CountedVotesAt M (x.tickInput w t_w)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup,
      VotesOnceFor (M.fg_to_ac (x.tickInput w t_w)) votes support_votes s B u ∧
      ∃ H_u ∈ (x.tickInput w t_w).tree, B.AncestorEq H_u ∧
        ∃ st : Stamp, (x.tickInput w t_w).blockStamp H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
    M.voters_count votes < 2 * Sup.card ∧ support_votes ⊆ votes :=
  (GoldilocksCorrectness.Record.Proofs.Executions.supporters_vote_once_counted_at M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w votes support_votes E hNet hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw tStart htStart htStartSlot hv hv₀ hw₀ kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hEligible hF hCounted hb

/-- Lemma 63 read on `w`'s pool. Under the hypotheses of Lemma 63, each member of `Sup` votes
once for `B`'s chain in `w`'s pool of slot `s` at its tick to `t_w` (`VotesOnceInPoolFor`).

Why: Lemma 63's vote of each member is in `w`'s pool at its tick to `t_w` and resolves there, its head block
being in `w`'s frame tree; every vote of `w`'s pool was held by `w` at its tick to `t_w`, so a vote of
the member is that one.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the clock value of `w`'s tick whose
  state is read; `t_v`: that of `v`'s tick;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block;
- `v`: the validator at which the members of `Sup` are early supporters; `w`: the validator whose
  pool is read; `tStart`, `tStartW`: the starts of `v`'s and `w`'s windows; `kₑ`, `k_v`: the steps of `v`'s ticks to `t_e`, `t_v`;
  `k_f`, `k_w`: those of `w`'s ticks to `t_f`, `t_w`.

Read aloud: each early supporter of `B`'s chain at `v` has exactly one vote in `w`'s pool, and it
supports `B`'s chain there too.

Read at the validators' own ticks (T-RC8-2, T-RC6-1's shape); roots name blocks until the latest real
time of `w`'s tick to `t_e + Δ S`. Restated with the delivery premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls). -/
theorem supporters_vote_once_in_pool_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    ∀ u ∈ Sup,
      VotesOnceInPoolFor M (x.tickInput w t_w) s B u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.supporters_vote_once_in_pool_at M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w E hNet hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw tStart htStart htStartSlot hv hv₀ hw₀ kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hF hb

/-- **Lemma 64, the next slot's Goldfish fork choice extends a block an honest validator finds
eligible.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST`, a root names one
block among what honest validators hold, and a block reaches a validator only once it holds the
parent: under the inequalities between the times listed with the hypotheses, if `w` is active from
a time `tStartW` up to its tick to `t_e + Δ S`, `v` from a time `tStart` up to its tick to
`t_w + Δ S`, each start strictly before one delay or one sync delay, whichever is longer, before
that tick's clock value, and by more than `ΔClockAhead + ΔClockBehind`; on `v`'s state at its tick to `t_v` each member of `Sup` is an early supporter of `B`'s chain with the
cutoff `t_e`, and the validators with a slot-`s` vote in `v`'s pool are fewer than twice `Sup`;
`votes`, `support_votes` are the sets the Goldfish vote of slot `s + 1` counts on `w`'s state
at its tick to `t_w` with the cutoff `t_f`, and `vbt` the voter's tree with the same cutoff; the Goldfish
walk at `t_w` from the anchor over the lock entries `E`, over the viable tree of `vbt`, counting
those sets, ends at `H_w`; on `w`'s state at its tick to `t_w`, the root of the fork choice is compatible
with `B`, and when that root is `B` or an ancestor of `B` some block of `vbt` that is `B` or a
descendant of `B` is a viable head; and the block of every lock entry of `E` live at `t_w` is
compatible with `B` — then `H_w` is `B` or a descendant of `B`.

Why: when `B` is an ancestor of `w`'s finalized block, it is an ancestor of the root of the fork
choice (Lemma 46), of the anchor and of `H_w`. Otherwise `w`'s finalized block is an ancestor of
`B`, so the members of `Sup` vote once for `B`'s chain among the counted votes, and `w`'s voters are
fewer than twice `Sup` (Lemma 63, on the counted sets); the anchor is compatible with `B` (Lemma 6)
and starts towards `B` (Lemma 7, the blocks on the path being ancestors of a supporter's head,
stamped strictly before `t_f`), so the fork choice ends at `B` or a descendant of `B` (Lemma 2).



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t_e`: the early cutoff; `t_f`: the cutoff on the stamps at `w`; `t_w`: the clock value of `w`'s tick
  running its fork choice; `t_v`: that of `v`'s tick; `tStart`, `tStartW`: the starts of `v`'s and `w`'s
  windows;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block `v` finds eligible;
- `v`: the validator that finds `B` eligible; `w`: the voter;
- `E`: the lock entries that give the anchor; `votes`, `support_votes`: the sets `w`
  counts; `vbt`: `w`'s voter tree; `H_w`: the end of `w`'s fork choice.

Read aloud: if `B` is eligible at `v` with the cutoff `t_e`, the finality-gadget conditions hold
for `B` at `w`, and no live lock entry of `E` conflicts with `B`, then `w`'s fork choice at `t_w`,
over what `w` holds by `t_f`, ends at `B` or a descendant of `B`.

Read at the validators' own ticks (T-RC8-2, T-RC6-1's shape); roots name blocks until the latest real
time of `w`'s tick to `t_e + Δ S`. Restated with the delivery premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, through `supporters_vote_once_counted_at`, which it calls). -/
theorem lem64_goldfish_vote_extends_eligible_block_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (E : Finset M.LE) (votes support_votes : Finset (GoldfishVote V))
    (vbt : Finset (Block V)) (H_w : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (Env : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    (hEligible : M.voters_count (M.votesHeldSet (x.tickInput v t_v) s) < 2 * Sup.card)
    (hCounted : CountedVotesAt M (x.tickInput w t_w)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    (hvbt : ∀ B' : Block V, B' ∈ vbt ↔
      VoterTreeAt M (x.tickInput w t_w) ((t_f : ℕ) : Int) (s + 1) B')
    (hWalk : @WalkEnd V M.tieBreak (M.viable_tree (M.fg_to_ac (x.tickInput w t_w)) vbt)
      (goldfish_score (M.fg_to_ac (x.tickInput w t_w)) votes support_votes s)
      (goldfish_eligible S.C (M.fg_to_ac (x.tickInput w t_w)) ((t_w : ℕ) : Int) votes
        support_votes s)
      (AnchorAt M (M.fg_to_ac (x.tickInput w t_w)) E ((t_w : ℕ) : Int)) H_w)
    (hF2 : (M.fg_to_ac (x.tickInput w t_w)).fc_root.compatible B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w t_w)).fc_root.AncestorEq B →
      ∃ W ∈ vbt, W ∈ (M.fg_to_ac (x.tickInput w t_w)).viable_heads ∧ B.AncestorEq W)
    (hLocks : ∀ e ∈ E,
      M.is_live (x.tickInput w t_w) ((t_w : ℕ) : Int) e = true →
        e.B.compatible B = true)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    B.AncestorEq H_w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem64_goldfish_vote_extends_eligible_block_at M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w E votes support_votes vbt H_w Env hNet hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw tStart htStart htStartSlot hv hv₀ hw₀ kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hEligible hCounted hvbt hWalk hF2 hF3 hLocks hb

end GoldilocksCorrectness.Record.Statements.Executions

