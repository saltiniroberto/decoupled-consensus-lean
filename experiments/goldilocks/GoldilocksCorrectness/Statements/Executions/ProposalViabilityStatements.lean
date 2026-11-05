module
public import GoldilocksCorrectness.Proofs.Executions.ProposalViability

@[expose] public section

/-!
# The statement that an honest proposal is viable at its proposer

The audited statement `proposal_viable`, a corollary of Lemma 58, proved in
`GoldilocksCorrectness/Proofs/Executions/ProposalViability.lean`.


-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (slotStart)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Corollary of Lemma 58, an honest proposal is viable at its proposer.** When `p` put the block
`B` on the wire at its tick at the start of slot `s + 1`, and `B`'s parent is in the viable tree of
the frame of `p`'s state before that start, `B`'s chain-state height is at least
`head_height_floor` (the least chain-state height a viable block may have) of `p`'s FG state before that start.

Why: `B`'s parent is the head `p`'s fork choice answered at that tick (Lemma 19); a head in the
viable tree is a viable head (Lemma 58); a viable head's height is at least `head_height_floor`; and `B`'s
height is at least its parent's (Lemma 47 (b)).



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `B`: the block proposed; `p`: its proposer.

Read aloud: an honest proposal's height is at least `head_height_floor` at its proposer. -/
theorem proposal_viable (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p : V)
    -- `p`'s tick at the start of slot `s + 1` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before the start of slot `s + 1`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    head_height_floor (stateBefore x (slotStart S (s + 1)) p).S ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.proposal_viable S Sched x s B p hPropose hParentIn

end GoldilocksCorrectness.Statements.Executions
