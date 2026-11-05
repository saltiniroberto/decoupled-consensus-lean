module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma20
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ProposalVoteStatements, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/ProposalVoteStatements.lean` over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 20, the next slot's
honest Goldfish vote names the honest proposal. It is the theorem of
`Record/Restated/Proofs/Executions/Lemma20.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (acObject)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes ProposalCountedVotes AwakeFor
  AnchorAt VoterTree)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes ProposalCountedVotes)

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

/-- **Lemma 20, the next slot's honest vote names the honest proposal.** In an execution where
every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a validator only once it
holds the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time
of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, outside the adversary set at `w`'s tick to
the vote time `t₃` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the vote
time of slot `s`, holds `H u`, a block that is `X` or a descendant of `X`, in its tree then, and is
active at every real time from the sync fact's read time `supportCutoff s − max (2 * Δ S) Δs` to one
sync delay after it; the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer
than twice `Hs`; `p` and `w` each tick to the support cutoff of slot `s` and are active at every step
from that read time up to that tick; `p` put the block `B`
on the wire at its tick at the start `t₁` of slot `s + 1`, and `w` put the Goldfish vote `vote` on
the wire at its tick at `t₃`; `w`'s tree before `t₃` holds `B`; on `p`'s node state before `t₁`,
some block of its frame's tree that is `X` or a descendant of `X` is a viable head, and its anchor
at `t₁` is `X` or an ancestor of `X`; on `w`'s node state before `t₃`, the block of every lock entry
live at `t₃` that `w`'s revocation of slot `s + 1` leaves is `B` or an ancestor of `B`, and `B` is a
viable head; and, writing a path block for a block from `X` to `B`'s parent that has the root of
`w`'s fork choice as an ancestor or is that root: every path block is a viable head at `p` exactly
when it is one at `w`; for the sets `p`'s proposal counts (`ProposalCountedVotes`) and the sets
`w`'s vote counts (`CountedVotes`), the two scores answer the same number on every child of a path
block and the two sets of votes have the same number of voters; and every child in `w`'s viable tree
of a path block, other than `B`, that `w`'s eligibility test accepts (counting those sets), is in
`p`'s viable tree — then `vote`'s head is the root of `B`.




- the hypothesis that `w`'s finalized block is each `H u` or an ancestor of it was deleted: where
  the proof needs it, `w`'s anchor is `X` or an ancestor of `X`, and it follows the same way;
- the hypothesis that `B` is the only slot-`(s + 1)` block `w` holds was deleted: the proof did not
  use it;
- the block of every live lock entry `w`'s revocation leaves is now `B`'s parent or an ancestor
  of it, where it was `X` or an ancestor of `X`;
- the scores are assumed to agree only on the children of the path blocks, where they were
  assumed on every block;
- the viable heads, the scores and the children are assumed only along the path blocks, the blocks
  from `X` to `B`'s parent that have the root of `w`'s fork choice as an ancestor (or are that
  root), where they were assumed from `X` on: that root may be a descendant of `X`, a block
  strictly between `X` and it is not a viable head at `w` while it may be one at `p`, and the proof
  reads only blocks that have `w`'s anchor as an ancestor (or are it), and the anchor has that root
  as an ancestor (or is it);
- the children assumed in `p`'s viable tree are only those `w`'s eligibility test accepts;
- `p`'s and `w`'s awake windows were narrowed from "from the start of slot `s` to `t₁`" and "from
  the start of slot `s` to `t₃`" to "from the vote time of slot `s` to its support cutoff", the
  window Lemma 12 reads;



 the committee majority gives it through the admission invariant.

Why: `p`'s tick at `t₁` sent `B`, so `B` is `p`'s proposal: its parent is the end of the Goldfish
fork choice from `p`'s anchor through `p`'s viable tree, counting `p`'s slot-`s` pool (Lemma 19).
`w`'s tick at `t₃` sent `vote`, so its head is the root of the end `H_w` of the Goldfish fork choice
from the anchor of `w`'s revoked AC state (Lemma 14). By Lemma 12 at `t₁`, every `u ∈ Hs` has its
vote for `H u` as its only slot-`s` vote in `p`'s pool, resolved. At `p` the anchor starts towards
`X` (Lemma 7, with F3), and `p` counts as many voters as `w`, fewer than twice `Hs`, so `p`'s walk
passes `X` (Lemma 2). At `w` the anchor is `B` or an ancestor of `B`
(`get_anchor_ancestorEq_of_entries`: the live lock entries are on `B` or ancestors of `B`, and the
root of `w`'s fork choice is `B` or an ancestor of it, `B` being a viable head), and so is `X`: the
anchor is an ancestor of `X`, `X`, or a descendant of `X`. When the anchor is `B`, `B` has no child
in `w`'s tree and `w`'s walk ends at `B`. Every block of `w`'s frame tree on `B`'s chain is in `w`'s
viable tree (`B` is a slot-`(s + 1)` viable head). When the anchor is `X` or an ancestor of `X`,
Lemma 12 at `t₃` gives the votes of `Hs` in `w`'s pool, the anchor starts towards `X` (Lemma 7),
`w`'s walk passes `X` (Lemma 2), and `X` is the shared block. When the anchor is a descendant of `X`
other than `B`, it is a block of `p`'s walk from `X` to `B`'s parent, `w`'s walk starts there, and
the anchor is the shared block. From the shared block on, the two walks see the same scores and the
same eligibility answers on the children of the path, `B` is eligible at `w` as a block of the
current slot and has no child in `w`'s tree, so `w`'s walk ends at `B` (Lemma 9).



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: if the honest members `Hs` of the slot-`s` committee sent at the vote time of slot `s` a
vote for a block they hold that is `X` or a descendant of `X`, and are more than half of the
validators whose votes `w` counts for its vote of slot `s + 1`; the honest proposer `p` of slot
`s + 1` put `B` on the wire at the start of slot `s + 1`, with its anchor `X` or an ancestor of `X`;
the honest voter `w` holds `B`, has every live lock on `B` or an ancestor of `B` after its
revocation, and sees `B` as a viable head; and, along the path from `X` to `B`'s parent past the
root of `w`'s fork choice, the two validators count alike on the children, agree on the viable
heads, and `p` holds every child that `w` finds eligible — then `w`'s vote of slot `s + 1` names
`B`.

Roots name blocks until the later of the real times of `p`'s and `w`'s own ticks to `M.supportCutoff S.C s`: the
proof takes as held only blocks delivered before those ticks (Lemma 12 at slot `s`, at `p` and at `w`). -/
theorem lem20_goldfish_vote_names_honest_proposal (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the later of the real times of `p`'s and `w`'s own ticks to the support cutoff of
    -- slot `s`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep p (M.supportCutoff S.C s)))
      (x.time (x.tickStep w (M.supportCutoff S.C s)))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      M.voters_count votes_w < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer `p` and the voter `w` each tick to the support cutoff of slot `s` at a step `kR` and are active at
    -- every step from the sync fact's read time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hp : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- `w` holds `B` before its vote
    (hBw : B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree)
    -- the finality-gadget condition at `p`, on its state before `slotStart S (s + 1)`
    (hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is a viable head at `w`
    (hBViable : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads)
    -- the two validators agree on the viable heads along the path from `X` to `B`'s parent, on
    -- the blocks of it that have the root of `w`'s fork choice as an ancestor (or are that root)
    (hViableAgree : ∀ Y : Block V, X.AncestorEq Y →
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      (Y ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ↔
        Y ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads))
    -- the two validators count alike: the same score on every child of a block from `X` to
    -- `B`'s parent that has the root of `w`'s fork choice as an ancestor (or is that root), the
    -- same number of voters
    (hCount : ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput p (M.slotStart S.C (s + 1))) s votes_p support_p →
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      (∀ Y : Block V, X.AncestorEq Y →
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → ∃ n : ℕ,
          goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s
            D = .ok n ∧
          goldfish_score (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes_w support_w s
            D = .ok n) ∧
      M.voters_count votes_p = M.voters_count votes_w)
    -- every child in `w`'s viable tree of a block from `X` to `B`'s parent that has the root of
    -- `w`'s fork choice as an ancestor (or is that root), other than `B`, that `w`'s eligibility
    -- test accepts, is in `p`'s viable tree
    (hChild : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      ∀ Y : Block V, X.AncestorEq Y →
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D ∈ M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1))))
            (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)),
          D.parent? = some Y → D ≠ B →
          goldfish_eligible S.C (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1))))
            ((M.voteTime S.C (s + 1) : ℕ) : Int) votes_w support_w s D = .ok true →
          D ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
            (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    vote.head = B.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem20_goldfish_vote_names_honest_proposal M F U) S A x R GST
    s Hs H X B p w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hVoters hHold hp hw hPropose hSend hBw hF3p hApX
    hLocksW hBViable hViableAgree hCount hChild

end GoldilocksCorrectness.Record.Statements.Executions

