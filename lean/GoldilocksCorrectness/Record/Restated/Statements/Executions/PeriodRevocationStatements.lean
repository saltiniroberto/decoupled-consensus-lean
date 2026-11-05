module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodRevocation
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements

@[expose] public section

/-!
# PeriodRevocationStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PeriodRevocationStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: after the
revocation against a delivered majority on `B`'s chain, no live lock entry conflicts with `B`; it is
the theorem of the same name of `Record/Restated/Proofs/Executions/PeriodRevocation.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (LocksRevoked)

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

/-- **Execution fact: after the revocation against a delivered majority on `B`'s chain, no lock
entry conflicts with `B`.** When the votes of a set `Hs` of more than half of the committee of slot
`σ` are held by `u` before the vote time `t₃` of slot `σ + 1`, each `u' ∈ Hs`'s vote for a block
`H u'` that is `B` or a descendant of `B`, held as `u'`'s only slot-`σ` vote, resolved, with `H u'`
in `u`'s frame tree: then for every answer `A'` of `u`'s revocation of slot `σ + 1` at `t₃` (on
`u`'s AC state before `t₃` with its expired entries removed), every lock entry of `A'` live at `t₃`
is on a block compatible with `B`.

Why: every entry of `A'` was moved by `moved_entry` to a block of `u`'s frame tree with fewer than
half of the committee of `σ` opposing it (`moved_entry_opponents_lt`). A block conflicting with `B`
is opposed by every voter of `Hs`: its vote is in `u`'s pool of slot `σ`, which the removal of the
expired entries keeps, it resolves, its head names `H u'` in the frame tree, `H u'` conflicts with
that block (`B` is an ancestor of `H u'`), and `u'` is no equivocator (its only slot-`σ` vote in the
pool is that one). So its opponents are at least `Hs`, more than half of the committee.


Against the brief's template: the hypotheses "every `u' ∈ Hs` is in `S.P.committee σ`", "honest at
`M.voteTime S.C (σ + 1)`" and the slot bound `σ ≥ s + 1` are not read by the proof and are not
taken.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot of the votes; `tb`: the
  bound on their stamps; `u`: the revoking validator; `Hs`: the voters; `H`: the block each
  voter's vote is for; `B`: the block.

Read aloud: after the revocation against a delivered majority on `B`'s chain, no live lock
conflicts with `B`. -/
theorem revoked_entries_compatible_of_majority (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (σ tb : ℕ) (u : V) (Hs : Finset V) (H : V → Block V)
    (B : Block V)
    -- `Hs` is more than half of the committee of slot `σ`
    (hcard : |S.P.committee σ| < 2 * |Hs|)
    -- every vote of `Hs` is for `B` or a descendant of `B`
    (hHB : ∀ u' ∈ Hs, B.AncestorEq (H u'))
    -- `u` holds the votes of `Hs` before the vote time of slot `σ + 1`
    (hHeld : ∀ u' ∈ Hs, HeldEarlyVoteAt M (x.stateBefore (M.voteTime S.C (σ + 1)) u)
        ((tb : ℕ) : Int) σ (H u') u') :
    ∀ n' : M.N, LocksRevoked M S.P (x.stateBefore (M.voteTime S.C (σ + 1)) u)
        ((M.voteTime S.C (σ + 1) : ℕ) : Int) (σ + 1) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.stateBefore (M.voteTime S.C (σ + 1)) u)
          ((M.voteTime S.C (σ + 1) : ℕ) : Int) e = true → e.B.compatible B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.revoked_entries_compatible_of_majority M F) S
    A x R E σ tb u Hs H B hcard hHB hHeld

end GoldilocksCorrectness.Record.Statements.Executions

