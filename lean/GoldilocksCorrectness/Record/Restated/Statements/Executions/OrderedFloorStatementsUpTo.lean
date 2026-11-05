module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.OrderedFloorStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.OrderedFloorVotesUpTo
public import GoldilocksCorrectness.Statements.Executions.OrderedFloorStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# OrderedFloorStatementsUpTo, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/OrderedFloorStatementsUpTo.lean`, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 59 when
`head_height_floor` at the proposer is at most `head_height_floor` at the voter, with the delivery
premises up to a bound. It is the theorem of the same name of
`Record/Restated/Proofs/Executions/OrderedFloorVotesUpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AnchorAt AwakeFor CountedVotes FrameShape
  ProposalCountedVotes VoterTree)
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
open GoldilocksCorrectness.Statements.Routines (expireLocks)

/-- **Lemma 59 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 59
(`lem59_goldfish_vote_names_honest_proposal_frame`) with `w`'s frame shape at `φ_w` in place of
`φ`, and with "`B`'s chain-state height is at least `φ`" replaced by: `φ ≤ φ_w`, and `φ_w`
is at most the chain-state height of `B`'s parent — then `w`'s vote names `B`. Here `φ` is
`head_height_floor` at `p` and `φ_w` is `head_height_floor` at `w`, as the two frame shapes say.

Why: as Lemma 59, with Lemma 24 in the form `lem24le_goldfish_vote_names_honest_proposal_composed`.
`w` holds `B` (Lemmas 22a and 22) and so `B`'s parent, with its own chain state (Lemma 11), so
`B`'s parent passes `w`'s viability test (Lemma 56); the two frame shapes give the two
`head_height_floor` as `φ` and `φ_w`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s` and ends at the start of
slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: `head_height_floor` at `p`
  and at `w`.

Read aloud: when `head_height_floor` at the voter is at least at the proposer and at most the
height of the proposal's parent, the voter's vote names the proposal.



Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: Lemma 22 and
`lem24le_goldfish_vote_names_honest_proposal_composed`, which the proof calls, take blocks as
held up to `w`'s vote time of slot `s + 1`.

The activity rows: `p` and `w` are each active from a tick to
a clock value at most `tStart`, more than both clock bounds before the read time
`M.supportCutoff S.C s - max (2 * Δ S) Δs` at slot `s`, up to their own ticks to the start and to the
vote time of slot `s + 1`; each voter of `Hs` is active through the sync delay after that read time
(`hHold`), and `p` through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
(`hHoldP`); the voters of `Hs` are outside the adversary set at `w`'s tick to the vote time of slot
`s + 1`.

Restated with the delivery premises up to `M.voteTime S.C (s + 1)`: the proposal of slot `s + 1`
reaches `w` by then (`lem22_proposal_held_by_voter_upTo`,
`lem23_proposer_and_voter_count_alike_upTo`). -/
theorem lem59le_goldfish_vote_names_honest_proposal_frame_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ φ_w : Height)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.voteTime S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    --
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
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
    -- each voter of `Hs` is active through the sync delay after the read time at slot `s`
    --
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p`'s and `w`'s windows start at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the read
    -- time at slot `s`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- `p` is active from a tick to a clock value at most `tStart` up to its tick to the start of slot
    -- `s + 1`
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C (s + 1)))
    -- `p` is active through the sync delay after `max (Δ S) Δs` before the start of slot `s + 1`
    --
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from a tick to a clock value at most `tStart` up to its tick to the vote time of
    -- slot `s + 1`
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- `w`'s tree before `t₃` holds no slot-`(s + 1)` block other than `B`
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B)
    -- no block of `p`'s tree before `t₁` has `B`'s root
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` `φ`
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and `head_height_floor` `φ_w`
    (hShapeW : FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) ρ_w φ_w)
    -- `φ` is at most `φ_w`
    (hFloorLe : φ ≤ φ_w)
    -- some block of `p`'s tree that is `X` or a descendant of `X`, and `ρ_p` or a descendant of
    -- `ρ_p`, has a chain-state height at least `φ`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X)
    -- `ρ_w` is `B` or an ancestor of `B`
    (hRootW : ρ_w.AncestorEq B)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `φ_w` is at most the chain-state height of `B`'s parent
    (hParentHeight : φ_w ≤ (M.chainStateOf S.C B.parent).h) :
    vote.head = B.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem59le_goldfish_vote_names_honest_proposal_frame_upTo M F U)
    S A x R GST s Hs H X B p w vote ρ_p ρ_w φ φ_w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner
    hGST hHs hVoters hHold tStart htStart hp hHoldP hw hPropose hSend hOnly hRootNew hShapeP hShapeW hFloorLe hHeadP hApX hRootW
    hLocksW hParentHeight

end GoldilocksCorrectness.Record.Statements.Executions

