module
public import GoldilocksCorrectness.Proofs.Executions.PeriodHolders
public import GoldilocksCorrectness.Statements.Executions.DeliveryDefs
public import GoldilocksCorrectness.Proofs.Routines.Confirmation

@[expose] public section

/-! two kit statements, new. The audited statements are in
`Statements/Executions/PeriodRevocationStatements.lean`.

- `moved_entry_opponents_lt`, a routine fact: the block `moved_entry` moves an entry to is a block
  of the frame's tree, the entry's block or an ancestor of it, whose opponents, counted twice, are
  fewer than the committee; the deadline is kept;
- `revoked_entries_compatible_of_majority`, an execution fact: when a validator holds the
  slot-`σ` votes of a set `Hs` of more than half of the committee of `σ`, each vote for a block on
  `B`'s chain, every lock entry its revocation of slot `σ + 1` leaves is on a block compatible with
  `B`. A block conflicting with `B` has every voter of `Hs` among its opponents, so it is never a
  candidate of `moved_entry`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)

open GoldilocksCorrectness.Proofs.Routines (moved_entry_opponents_lt)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes mem_opponents_of_eq_ok
  mem_votes_by_iff pool_of_keepsVotes revoke_locks_entry_opponents_lt tau_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff conflicts_iff
  ancestorEq_compatible dre_bind_eq_ok mem_of_filterM_eq_ok_iff mem_of_imageM_eq_ok present_mem_iff
  deepest?_mem opposes_eq_ok mem_equivocators_iff dre_bind_ok)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Execution fact: after the revocation against a delivered majority on `B`'s chain, no lock
entry conflicts with `B`.** The proof; the audited statement is in
`Statements/Executions/PeriodRevocationStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot of the votes; `tb`: the
  bound on their stamps; `u`: the revoking validator; `Hs`: the voters; `H`: the block each voter's
  vote is for; `B`: the block. -/
theorem revoked_entries_compatible_of_majority (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (σ tb : ℕ) (u : V) (Hs : Finset V) (H : V → Block V)
    (B : Block V)
    (hcard : |S.P.committee σ| < 2 * |Hs|)
    (hHB : ∀ u' ∈ Hs, B.AncestorEq (H u'))
    (hHeld : ∀ u' ∈ Hs, HeldEarlyVoteAt (stateBefore x (voteTime S (σ + 1)) u).A
      (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S) ((tb : ℕ) : Int) σ (H u') u') :
    ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (σ + 1)) u).A
        ((voteTime S (σ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S)
        ((voteTime S (σ + 1) : ℕ) : Int) (σ + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S)
          ((voteTime S (σ + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro A' hRev e he _
  have hR : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ u
  obtain ⟨opp, hopp, hlt⟩ :=
    revoke_locks_entry_opponents_lt (s := σ + 1) (Nat.succ_ne_zero σ) hRev e he
  simp only [Nat.add_sub_cancel] at hopp hlt
  rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at hopp
  by_contra hc
  -- every voter of `Hs` opposes `e.B`
  have hsub : Hs ⊆ opp := by
    intro u' hu'
    obtain ⟨hp, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u' hu'
    -- the vote's voter is no equivocator
    have hneq : u' ∉ equivocators ((stateBefore x (voteTime S (σ + 1)) u).A.pool σ) := by
      rw [mem_equivocators_iff]
      intro h2
      have h1 : (votes_by ((stateBefore x (voteTime S (σ + 1)) u).A.pool σ) u').card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        rw [mem_votes_by_iff] at ha hb
        rw [huniq a ha.1 ha.2, huniq b hb.1 hb.2]
      omega
    -- the vote's block conflicts with `e.B`
    have hconf : (H u').conflicts e.B = true := by
      rw [conflicts_iff, compatible_iff]
      rintro (h | h)
      · exact hc ((compatible_iff _ _).2 (Or.inr (ancestorEq_trans (hHB u' hu') h)))
      · exact hc ((compatible_iff _ _).2 (ancestorEq_compatible h (hHB u' hu')))
    have hopp' : opposes (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S) e.B
        (GoldfishVote.mk u' σ (H u').root) = .ok true := by
      rw [opposes_eq_ok hR]
      simp only [Except.ok.injEq, decide_eq_true_eq]
      exact ⟨H u', hHΦ, rfl, hconf⟩
    have hy' : (expireLocks (stateBefore x (voteTime S (σ + 1)) u).A
        ((voteTime S (σ + 1) : ℕ) : Int)).tau (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S)
        (GoldfishVote.mk u' σ (H u').root) = .ok (some y) :=
      (tau_of_keepsVotes (expireLocks_keepsVotes _ _) _ _).trans hy
    exact mem_opponents_of_eq_ok hopp hp rfl hneq hy' hopp'
  have hle := Finset.card_le_card hsub
  omega

end GoldilocksCorrectness.Proofs.Executions
