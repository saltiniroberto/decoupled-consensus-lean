module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26Held

@[expose] public section

/-!
# NextSlotVoteHeldStatements, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/NextSlotVoteHeldStatements.lean` over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 26b with the votes
of `Hs` held by the voter as a hypothesis. It is the theorem of
`Record/Restated/Proofs/Executions/Lemma26Held.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime viewFreeze)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes AwakeFor AnchorAt VoterTree
  VoterTreeAt)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible
  occurrenceBefore_eq_true_iff)
open GoldilocksCorrectness.Record.Statements.Executions (HeldEarlyVoteAt)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

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

/-- **Lemma 26b from held votes, the next slot's honest vote names a block the voter holds.** In an
execution that reaches every time, with permanent corruption, where nobody votes in an honest
validator's name: if `tb` is at most the view freeze of slot `s`; every `u ∈ Hs` is outside the
adversary set at `w`'s tick to the vote time `t₃` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the vote
time of slot `s`, and `H u` is `R` or a descendant of `R`; in the case `w`'s finalized block before
`t₃` is `R` or an ancestor of `R`, `w`'s AC state before `t₃` holds every such vote as its voter's
only slot-`s` vote, stamped and resolved strictly before `tb`, with `H u` in `w`'s frame tree; the
validators with a vote among those `w` counts at its slot-`(s + 1)` vote are fewer than twice `Hs`;
on `w`'s state before `t₃`, the root of the fork choice is compatible with `R`, and, when that root
is `R` or an ancestor of `R`, some block of `w`'s voter tree for slot `s + 1` on `R`'s chain is a
viable head; in the same case as the votes held, every lock entry live at `t₃` that `w`'s revocation
of slot `s + 1` leaves is compatible with `R`; and `w` put `vote` on the wire at its tick at `t₃` —
then `vote` is `w`'s slot-`(s + 1)` vote for a block `H_w` of `w`'s tree before `t₃`, and `H_w` is
`R` or a descendant of `R`.

Why: Lemma 26b's proof. In the case `R` is an ancestor of `w`'s finalized block, the walk's end
descends from the root of the fork choice, which descends from the finalized block. Otherwise the
votes are held (`hHeld`), and the proof reads their stamps only against the view freeze of `s`,
which `tb` is at most; the locks are `hLocks` in the same case.


Against Lemma 26b (`Statements/Executions/NextSlotVoteStatements.lean`): `hSync`, `hCatch`,
`hRoots`, `hParent`, `hGST`, `hw` are not taken, the delivery of Lemma 12 being replaced by `hHeld`;
`htb` is added; `hLocks` is read under the case `w`'s finalized block is `R` or an ancestor of `R`.
Two conjuncts of Lemma 26b's `hHs` are not read by the proof and are deleted:
`u ∈ S.P.committee s` and `H u ∈ (stateBefore M x (M.voteTime S.C s) u).tree`, both read by Lemma
26b only through its Lemma 12 call.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s`: the slot of the votes; `tb`: the bound on their stamps and resolutions;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `R`: the block every vote of `Hs` extends; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: Lemma 26b with the delivery of the slot-`s` votes replaced by the votes held, stamped
and resolved strictly before a time at most the view freeze of `s`: whoever holds a majority's votes
on `R`'s chain votes on `R`'s chain. -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_of_held
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (s tb : ℕ) (Hs : Finset V)
    (H : V → Block V) (R : Block V) (w : V) (vote : GoldfishVote V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hOwner : VotesCastByOwner M A x)
    -- `tb` is at most the view freeze of slot `s`
    (htb : tb ≤ M.viewFreeze S.C s)
    -- every member of `Hs` is outside the adversary set at `w`'s tick to `t₃` and sent its slot-`s`
    -- vote for `H u`, which is `R` or a descendant of `R`
    (hHs : ∀ u ∈ Hs, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      R.AncestorEq (H u))
    -- in the case `w`'s finalized block is `R` or an ancestor of `R`: the slot-`s` votes held
    (hHeld : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq R →
      ∀ u ∈ Hs, HeldEarlyVoteAt M (x.tickInput w (M.voteTime S.C (s + 1))) ((tb : ℕ) : Int) s
        (H u) u)
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    -- on `w`'s state before `t₃`, the root of its fork choice is compatible with `R`
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible R = true)
    -- when that root is `R` or an ancestor of `R`, a block of `w`'s voter tree on `R`'s chain is
    -- a viable head
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq R →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ R.AncestorEq W)
    -- in the same case: the block of every lock entry live at `t₃` that `w`'s revocation leaves
    -- is compatible with `R`
    (hLocks : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq R →
      ∀ (n' : M.N) (sent : List (NamedObject V)),
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
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem26b_goldfish_vote_extends_voter_majority_block_of_held M F U)
    S A x Run s tb Hs H R w vote E hOwner htb hHs hHeld hVoters hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Record.Statements.Executions

