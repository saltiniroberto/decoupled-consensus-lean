module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.NextSlotVoteStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26UpTo
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# NextSlotVoteStatementsUpTo, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatementsUpTo.lean` over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 26b, the next
slot's honest Goldfish vote extends a block a voter majority voted for, with the delivery premises
up to a bound. It is the theorem of `Record/Restated/Proofs/Executions/Lemma26UpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
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
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`).

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `w` by
then (`lem12_honest_vote_delivered_upTo`). -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_held_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hs : Finset V)
    (H : V → Block V) (R : Block V) (w : V) (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member of `Hs` is an honest member of the slot-`s` committee that sent its slot-`s`
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
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo M F U) S
    A x Run GST s Hs H R w vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs
    hVoters hHold hw hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Record.Statements.Executions

