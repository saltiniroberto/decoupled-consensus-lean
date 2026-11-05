module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma17
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# NextSlotVoteStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 17, 26 and 26b, the
next slot's honest Goldfish vote extends a block a majority voted for. Each is the theorem of the
same name of `Record/Restated/Proofs/Executions/Lemma17.lean` or
`Record/Restated/Proofs/Executions/Lemma26.lean`.
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

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes AwakeFor AnchorAt VoterTree
  VoterTreeAt)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible
  occurrenceBefore_eq_true_iff)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

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

/-- **Lemma 17, the next slot's honest vote extends a block a committee majority voted for.** In
an execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the vote time `t₃` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the
vote time of slot `s`, and holds `H u`, a block that is `R` or a descendant of `R`, in its tree
then; `Hs` outnumbers the rest of the slot-`s` committee; `w` is awake and honest at every time
from the vote time of slot `s` to the support cutoff of slot `s`; on `w`'s node state before
`t₃`, the root of the fork choice is compatible with `R` (F2), and, when that root is `R` or an
ancestor of `R`, some block of `w`'s voter tree for slot `s + 1` that is `R` or a descendant of `R`
is a viable head (F3); and `w` put the Goldfish vote `vote` on the wire at its tick at `t₃` — then
`vote`'s head is the root of a block that is `R` or a descendant of `R`.



Why: `w`'s tick at `t₃` sent `vote`, so it ran the revocation of slot `s + 1` and then the
Goldfish fork choice from the anchor of the revoked AC state (Lemma 14). F2 and Lemma 46 (`w`'s
finalized block is the root of the fork choice or an ancestor of it) make `w`'s finalized block
compatible with `R`. When `R` is an ancestor of `w`'s finalized block, it is an ancestor of
the root of the fork choice, of the anchor, and so of the fork choice's end, which is the anchor
or a descendant of it. Otherwise `w`'s finalized block is an ancestor of `R`, so of every `H u`,
and the argument that follows runs. By Lemma 12 every
`u ∈ Hs` has its vote for `H u` in `w`'s pool as its only slot-`s` vote, stamped and resolved
strictly before `S.C.t_ s + 2 · S.C.Δ`, with `H u` in `w`'s frame tree. The revocation then clears
every lock entry on a block not compatible with `R` (Lemma 5), so the anchor is compatible with `R`
(Lemma 6, with F2). When the root of the fork choice is `R` or a descendant of `R`, so is the
anchor; otherwise every block after the anchor up to `R` is an ancestor of some `H u`, stamped
before the view freeze, and in `w`'s frame tree, hence in the voter tree, so the anchor starts
towards `R` in the viable tree (Lemma 7, with F3). The votes of `Hs` are counted once each, every
counted vote is from the slot-`s` committee, and `Hs` outnumbers the rest of it, so the fork
choice ends at `R` or a descendant of `R` (Lemma 3).



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `R`: the block every vote of `Hs` extends; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: if more than half of the slot-`s` committee are honest members that sent at the vote
time of slot `s` a vote for a block they hold that is `R` or a descendant of `R`, `w` is awake and
honest from the vote time of slot `s` to the support cutoff of slot `s`, F2 and F3 hold on `w`'s
state before the vote time of slot `s + 1`, and `w` sends a Goldfish vote then, that vote's head
is the root of `R` or of a descendant of `R`.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the proof takes as held by `w` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`). -/
theorem lem17_goldfish_vote_extends_majority_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (R : Block V) (w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ R.AncestorEq (H u))
    (hMajority : (S.P.committee s \ Hs).card < Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible R = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq R →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ R.AncestorEq W)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ R.AncestorEq H_w := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem17_goldfish_vote_extends_majority_block M F U) S A x Run GST
    s Hs H R w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hMajority hHold hw hF2
    hF3 hSend

/-- **Lemma 26, the next slot's honest vote extends a block a voter majority voted for.** In an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the vote time `t₃` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the
vote time of slot `s`, and holds `H u`, a block that is `R` or a descendant of `R`, in its tree
then; for every pair of sets `votes`, `support_votes` that are the slot-`s` votes and support
votes `w` counts at its slot-`(s + 1)` vote on its state before `t₃`, the validators with a vote in
`votes` are fewer than twice `Hs`; `w` is awake and honest at every time from the vote time of
slot `s` to the support cutoff of slot `s`; on `w`'s node state before `t₃`, the root of the fork
choice is compatible with `R` (F2), and, when that root is `R` or an ancestor of `R`, some block of
`w`'s voter tree for slot `s + 1` that is `R` or a descendant of `R` is a viable head (F3); for
every answer `A'` of `w`'s revocation of slot `s + 1` at `t₃`, run on `w`'s AC state before `t₃`
with its expired lock entries removed, the block of every lock entry of `A'` live at `t₃` is
compatible with `R`; and `w` put the Goldfish vote `vote` on the wire at its tick at `t₃` — then
`vote`'s head is the root of a block that is `R` or a descendant of `R`.

This is Lemma 17 with its committee majority (`Hs` outnumbers the rest of the slot-`s` committee)
replaced by the voter bound and the lock condition. The lock condition is a hypothesis because a voter majority does not make the
revocation clear a conflicting lock. The committee membership
of each `u ∈ Hs` stays: Lemma 12 needs it, since a validator admits a Goldfish vote only from a
committee member. Lemma 17 is proved from this one.

Why: as for Lemma 17, with three changes. `Hs` is not empty, since the voter bound on the sets `w`
counts gives `0 ≤ voters_count votes < 2 · |Hs|`. The lock condition, on the revocation's answer
`w`'s tick ran, gives the live lock entries compatible with `R` that Lemma 6 needs, in place of
Lemma 5. The fork choice ends at `R` or a descendant of `R` by Lemma 2 with the voter bound, in
place of Lemma 3, so the counted votes need not be shown to come from the committee.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `R`: the block every vote of `Hs` extends; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: if every member of `Hs` is an honest member of the slot-`s` committee that sent at the
vote time of slot `s` a vote for a block it holds that is `R` or a descendant of `R`, the members of
`Hs` are more than half of the validators whose slot-`s` votes `w` counts at the vote time of slot
`s + 1`, `w` is awake and honest from the vote time of slot `s` to the support cutoff of slot `s`,
F2 and F3 hold on `w`'s state before the vote time of slot `s + 1`, every lock entry live then that
`w`'s revocation leaves is on a block compatible with `R`, and `w` sends a Goldfish vote then, that
vote's head is the root of `R` or of a descendant of `R`.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the proof takes as held by `w` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`). -/
theorem lem26_goldfish_vote_extends_voter_majority_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (R : Block V) (w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ R.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible R = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq R →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ R.AncestorEq W)
    -- the block of every lock entry live at `t₃` that `w`'s revocation leaves is compatible
    -- with `R`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ R.AncestorEq H_w := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem26_goldfish_vote_extends_voter_majority_block M F U) S A
    x Run GST s Hs H R w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hVoters hHold hw
    hF2 hF3 hLocks hSend

/-- **Lemma 26b, the next slot's honest vote names a block the voter holds.** Under the hypotheses
of Lemma 26, `w`'s vote `vote` is its slot-`(s + 1)` vote for a block `H_w` of `w`'s tree before the
vote time `t₃` of slot `s + 1`, and `H_w` is `R` or a descendant of `R`. The hypotheses, in words:
every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST`, a root names one block among what honest validators hold,
a block reaches a validator only once it holds the parent, and nobody votes in an honest
validator's name; `GST` is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s`
committee, honest through `t₃`, put its slot-`s` vote for `H u` on the wire at its tick at the vote
time of slot `s`, and holds `H u`, `R` or a descendant of `R`, then; the validators with a vote
among those `w` counts at its slot-`(s + 1)` vote are fewer than twice `Hs`; `w` is awake and
honest from the vote time of slot `s` to the support cutoff of slot `s`; on `w`'s state before
`t₃`, the root of the fork choice is compatible with `R`, and, when that root is `R` or an ancestor
of `R`, some block of `w`'s voter tree for slot `s + 1` on `R`'s chain is a viable head; every lock
entry live at `t₃` that `w`'s revocation of slot `s + 1` leaves is compatible with `R`; and `w` put
`vote` on the wire at its tick at `t₃`.

Why: Lemma 26's proof, which reaches the block `H_w` the Goldfish fork choice of `w`'s tick ends
at. Lemma 14 makes `vote` the vote of the tick's validator, `w` by Lemma 11, for the slot of `t₃`,
with head `H_w`'s root; and the fork choice ends at a block of the viable tree of `w`'s voter tree,
a block of `w`'s frame tree, or at the anchor, a locked block of that tree or the root of the fork
choice, which is `w`'s justified or finalized block; all are in `w`'s tree (Lemmas 11 and 57).




The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `R`: the block every vote of `Hs` extends; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: under Lemma 26's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before the vote time of slot `s + 1` that is `R` or a descendant of `R`.

Roots name blocks until the real time of `w`'s own tick to `M.supportCutoff S.C s`: the proof takes as held by `w` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`). -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hs : Finset V)
    (H : V → Block V) (R : Block V) (w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member of `Hs` is a member of the slot-`s` committee, outside the adversary set at `w`'s tick to the vote
    -- time of slot `s + 1`, that sent its slot-`s`
    -- vote for `H u`, a block it holds that is `R` or a descendant of `R`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ R.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- on `w`'s state before `t₃`, the root of its fork choice is compatible with `R`
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible R = true)
    -- when that root is `R` or an ancestor of `R`, a block of `w`'s voter tree on `R`'s chain is
    -- a viable head
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq R →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ R.AncestorEq W)
    -- the block of every lock entry live at `t₃` that `w`'s revocation leaves is compatible
    -- with `R`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true)
    -- `w` put `vote` on the wire at its tick at `t₃`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    -- then `vote` is `w`'s slot-`(s + 1)` vote for a block it holds on `R`'s chain
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ R.AncestorEq H_w := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held M F U) S
    A x Run GST s Hs H R w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs
    hVoters hHold hw hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Record.Statements.Executions

