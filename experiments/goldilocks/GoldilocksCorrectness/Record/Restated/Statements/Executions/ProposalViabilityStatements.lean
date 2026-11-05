module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalViability

@[expose] public section

/-!
# ProposalViabilityStatements, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/ProposalViabilityStatements.lean` over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: an honest proposal is
viable at its proposer. It is the theorem of
`Record/Restated/Proofs/Executions/ProposalViability.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (slotStart)

namespace GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Corollary of Lemma 58, an honest proposal is viable at its proposer.** When `p` put the block
`B` on the wire at its tick at the start of slot `s + 1`, and `B`'s parent is in the viable tree of
the frame of `p`'s state before that start, `B`'s chain-state height is at least
`head_height_floor` (the least chain-state height a viable block may have) of `p`'s FG state before that start.

Why: `B`'s parent is the head `p`'s fork choice answered at that tick (Lemma 19); a head in the
viable tree is a viable head (Lemma 58); a viable head's height is at least `head_height_floor`; and `B`'s
height is at least its parent's (Lemma 47 (b)).



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `B`: the block proposed; `p`: its proposer.

Read aloud: an honest proposal's height is at least `head_height_floor` at its proposer. -/
theorem proposal_viable (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p : V)
    -- `p`'s tick at the start of slot `s + 1` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in the viable tree of `p`'s frame before the start of slot `s + 1`
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) ≤
      (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.proposal_viable M F U) S A x R E s B p hPropose
    hParentIn

end GoldilocksCorrectness.Record.Statements.Executions

