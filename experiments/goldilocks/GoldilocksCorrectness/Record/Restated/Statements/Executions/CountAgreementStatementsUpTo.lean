module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.CountAgreementStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma23UpTo
public import GoldilocksCorrectness.Statements.Executions.CountAgreementStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# CountAgreementStatementsUpTo, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/CountAgreementStatementsUpTo.lean`
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 23, an honest
proposer and the next slot's honest voter count alike, with the delivery premises up to a bound. It
is the theorem of `Record/Restated/Proofs/Executions/Lemma23UpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (acObject)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes ProposalCountedVotes ResolvesAt)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes ProposalCountedVotes)

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

/-- **Lemma 23, an honest proposer and the next slot's honest voter count alike.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches a
validator only once it holds the parent: if `GST` is at most the vote time of slot `s`; `p` is awake
and honest at every time from the view freeze of slot `s` to the start `t₁` of slot `s + 1`, and
`w` at every time from `t₁` to the vote time `t₃` of slot `s + 1`; `p` put its block `B` on the
wire at its tick at `t₁`; and on `w`'s node state before `t₃`, `B` is in the frame tree and is the
only slot-`(s + 1)` block of the FG tree — then, for the sets `votes_p`, `support_p` `p`'s proposal
counts (`ProposalCountedVotes`) and the sets `votes_w`, `support_w` `w`'s vote counts
(`CountedVotes`), the Goldfish scores of every block `D` that has `p`'s finalized block before `t₁`
and `w`'s finalized block before `t₃` as ancestors (or is one of them) answer one number at both,
and the two voter counts are equal.

 `hOnly` is judgement J38's hypothesis, the
unforgeability of blocks.

 `p`'s awake window was narrowed from "from the
start of slot `s`" to "from the view freeze of slot `s`", and `w`'s from "from the start of slot
`s`" to "from `t₁`", the windows the proof uses (`w`'s honesty at the view freeze follows from its
honesty at `t₁`, corruption being permanent).

Why: by Lemma 19, `B`'s votes are `p`'s pool of slot `s` and its support votes those that resolve
at `p`; by `hOnly` the votes `w` counts as included in a slot-`(s + 1)` block are exactly those. A
vote `w` holds stamped before the view freeze was re-sent by `w` and reached `p` before `t₁`, so
it is in `p`'s pool, or `p` holds two votes of its validator. Hence the equivocators agree, the
participants agree, and the one counted vote of a validator that does not equivocate is the same
at both. A vote supports a block `D` only through a head block that is `D` or a descendant of
`D`; when `D` has both finalized blocks as ancestors, so does that head block, which, when one
validator resolves it, reaches the other within a delay and is in the other's frame tree, so the
vote resolves at both; roots name one block across the two honest trees, so the vote supports `D`
at both. The score of a block is the number of equivocators plus the number of its supporters, so
the scores of such a `D` agree.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes;
- `B`: the proposal of slot `s + 1`; `p`: its proposer; `w`: the voter of slot `s + 1`;
- `votes_p`, `support_p`: the sets `p`'s proposal counts; `votes_w`, `support_w`: the sets `w`'s
  vote counts.

Read aloud: after `GST`, an honest proposer and an honest voter of the next slot give every block
that descends from both their finalized blocks the same Goldfish score, and count the same voters,
when the voter holds the proposal and no other block of its slot.

Roots name blocks until the real time of `w`'s tick to `M.voteTime S.C (s + 1)`: the proof compares the
blocks `w` holds at that tick with those `p` holds at its tick to the start `t₁` of slot `s + 1`, and takes
blocks `p` holds at its tick as held by `w` at its tick (`block_at_tick_of_held_tick`).

 each is
active at every step from the first one whose time is `ΔClockAhead` before `t₁ − max (Δ S) Δs` up to that
tick, and in every configuration in force at a real time of `[t₁ − max (Δ S) Δs, t₁ − max (Δ S) Δs + Δs]` (the
holder clause of the sync fact); what `w` stamped before the view freeze of slot `s` reaches `p` by its tick
(`pool_vote_reaches_at_tick_steps`, `block_at_tick_of_held_tick`).

Restated with the delivery premises up to `M.voteTime S.C (s + 1)`: the votes and blocks `p` and `w`
exchange around slot `s + 1` reach them by then.

`w`'s tree, pool, finalized block and scores are read at the state its own tick to the vote time of slot `s + 1`
starts from (`x.tickInput w (M.voteTime S.C (s + 1))`; rule R3, finding F-50-5), as Lemma 24, the proof's
caller, reads them. -/
theorem lem23_proposer_and_voter_count_alike_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (B : Block V) (p w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.voteTime S.C (s + 1)))
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.slotStart S.C (s + 1))
    -- `p` ticks to the start of slot `s + 1` at a step `kP` and is active after every step from the first one
    -- whose time is `ΔClockAhead` before `M.slotStart S.C (s + 1) - max (Δ S) Δs` up to `kP`
    (hp : ∃ kP : ℕ, x.lbl kP = Event.tick p (M.slotStart S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kP →
        p ∈ A.active j)
    -- `w` ticks to the vote time of slot `s + 1` at a step `kW` and is active after every step from the same
    -- first one up to `kW`
    (hw : ∃ kW : ℕ, x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kW →
        w ∈ A.active j)
    -- `p` and `w` are active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the
    -- window's start `M.slotStart S.C (s + 1) - max (Δ S) Δs` (:'s holder clause)
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldW : w ∈ A.activeThroughout x ((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hBw : B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree)
    (hOnly : ∀ B' ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree, B'.slot = s + 1 → B' = B) :
    ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput p (M.slotStart S.C (s + 1))) s votes_p support_p →
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes_w support_w →
      (∀ D : Block V, (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq D →
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq D → ∃ n : ℕ,
          goldfish_score (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s
            D = .ok n ∧
          goldfish_score (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes_w support_w s
            D = .ok n) ∧
      M.voters_count votes_p = M.voters_count votes_w := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem23_proposer_and_voter_count_alike_upTo M F U) S A x R GST s B
    p w E hNet hSkew hRedeliver Sy hRoots hParent hGST hp hw hHoldP hHoldW hPropose hBw hOnly

end GoldilocksCorrectness.Record.Statements.Executions

