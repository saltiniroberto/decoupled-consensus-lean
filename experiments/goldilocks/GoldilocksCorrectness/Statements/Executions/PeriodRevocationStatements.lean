module
public import GoldilocksCorrectness.Proofs.Executions.PeriodRevocation
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements

@[expose] public section

/-! two kit statements, new, no landed statement changes. Proved in
`GoldilocksCorrectness/Proofs/Executions/PeriodRevocation.lean`.

- `moved_entry_opponents_lt`: the block an entry is moved to has fewer than half of the committee
  opposing it;
- `revoked_entries_compatible_of_majority`: after the revocation against a delivered majority on
  `B`'s chain, no lock entry conflicts with `B`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

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
`voteTime S (σ + 1)`" and the slot bound `σ ≥ s + 1` are not read by the proof and are not taken.


The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot of the votes; `tb`: the
  bound on their stamps; `u`: the revoking validator; `Hs`: the voters; `H`: the block each
  voter's vote is for; `B`: the block.

Read aloud: after the revocation against a delivered majority on `B`'s chain, no live lock
conflicts with `B`. -/
theorem revoked_entries_compatible_of_majority (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (σ tb : ℕ) (u : V) (Hs : Finset V) (H : V → Block V)
    (B : Block V)
    -- `Hs` is more than half of the committee of slot `σ`
    (hcard : |S.P.committee σ| < 2 * |Hs|)
    -- every vote of `Hs` is for `B` or a descendant of `B`
    (hHB : ∀ u' ∈ Hs, B.AncestorEq (H u'))
    -- `u` holds the votes of `Hs` before the vote time of slot `σ + 1`
    (hHeld : ∀ u' ∈ Hs, HeldEarlyVoteAt (stateBefore x (voteTime S (σ + 1)) u).A
      (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S) ((tb : ℕ) : Int) σ (H u') u') :
    ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (σ + 1)) u).A
        ((voteTime S (σ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S)
        ((voteTime S (σ + 1) : ℕ) : Int) (σ + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S)
          ((voteTime S (σ + 1) : ℕ) : Int) e = true → e.B.compatible B = true :=
  GoldilocksCorrectness.Proofs.Executions.revoked_entries_compatible_of_majority S Sched x σ tb u
    Hs H B hcard hHB hHeld

end GoldilocksCorrectness.Statements.Executions
