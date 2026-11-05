module
public import GoldilocksCorrectness.Statements.Executions.OrderedFloorStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.OrderedFloorVotesUpTo

@[expose] public section

/-!
# `OrderedFloorStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/OrderedFloorStatements.lean` that
name a delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound
on the deadlines. The
bound of each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads,
written in the twin's own parameters.

* `lem59le_goldfish_vote_names_honest_proposal_frame`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (FrameShape BoxOne BoxTwo BoxThree)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes)

/-- **Lemma 59 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 59
(`lem59_goldfish_vote_names_honest_proposal_frame`) with `w`'s frame shape at `φ_w` in place of
`φ`, and with "`B`'s chain-state height is at least `φ`" replaced by: `φ ≤ φ_w`, and `φ_w`
is at most the chain-state height of `B`'s parent — then `w`'s vote names `B`. Here `φ` is
`head_height_floor` at `p` and `φ_w` is `head_height_floor` at `w`, as the two frame shapes say.

Why: as Lemma 59, with Lemma 24 in the form `lem24le_goldfish_vote_names_honest_proposal_composed`.
`w` holds `B` (Lemmas 22a and 22) and so `B`'s parent, with its own chain state (Lemma 11), so
`B`'s parent passes `w`'s viability test (Lemma 56); the two frame shapes give the two
`head_height_floor` as `φ` and `φ_w`.

The variables:
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



Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and
`lem24le_goldfish_vote_names_honest_proposal_composed`, which the proof calls, take blocks as
held up to `w`'s vote time of slot `s + 1`.

Restated with the delivery premises up to `voteTime S (s + 1)`: the proposal of slot `s + 1` reaches `w` by then (`lem22_proposal_held_by_voter_upTo`, `lem23_proposer_and_voter_count_alike_upTo`). -/
theorem lem59le_goldfish_vote_names_honest_proposal_frame_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ φ_w : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    -- `p` is awake and honest from the vote time of slot `s` to `t₁`
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `w` is awake and honest from the vote time of slot `s` to `t₃`
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- `w`'s tree before `t₃` holds no slot-`(s + 1)` block other than `B`
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    -- no block of `p`'s tree before `t₁` has `B`'s root
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` `φ`
    (hShapeP : FrameShape (stateBefore x (slotStart S (s + 1)) p).S ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and `head_height_floor` `φ_w`
    (hShapeW : FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ_w)
    -- `φ` is at most `φ_w`
    (hFloorLe : φ ≤ φ_w)
    -- some block of `p`'s tree that is `X` or a descendant of `X`, and `ρ_p` or a descendant of
    -- `ρ_p`, has a chain-state height at least `φ`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    -- `ρ_w` is `B` or an ancestor of `B`
    (hRootW : ρ_w.AncestorEq B)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `φ_w` is at most the chain-state height of `B`'s parent
    (hParentHeight : φ_w ≤ (chainStateOf S.C B.parent).h) :
    vote.head = B.root :=
  GoldilocksCorrectness.Proofs.Executions.lem59le_goldfish_vote_names_honest_proposal_frame_upTo S Sched
    x GST s Hs H X B p w vote ρ_p ρ_w φ φ_w hDiv hMono hSync hCatch hRoots hParent hOwner
    hGST hHs hVoters hp hw hPropose hSend hOnly hRootNew hShapeP hShapeW hFloorLe hHeadP hApX
    hRootW hLocksW hParentHeight

end GoldilocksCorrectness.Statements.Executions

