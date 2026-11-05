module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodHolders
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Executions.PeriodHolders
public import GoldilocksCorrectness.Statements.Executions.DeliveryDefs
public import GoldilocksCorrectness.Proofs.Routines.Confirmation

@[expose] public section

/-!
# PeriodRevocation, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodRevocation.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the revocation against a delivered
majority. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)

open GoldilocksCorrectness.Proofs.Routines (moved_entry_opponents_lt)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes mem_opponents_of_eq_ok
  tau_of_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions

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
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff conflicts_iff
  ancestorEq_compatible dre_bind_eq_ok mem_of_filterM_eq_ok_iff mem_of_imageM_eq_ok
  present_mem_iff deepest?_mem opposes_eq_ok dre_bind_ok)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Execution fact: after the revocation against a delivered majority on `B`'s chain, no lock
entry conflicts with `B`.** The proof; the audited statement is in
`Statements/Executions/PeriodRevocationStatements.lean`. The revocation's answer is read as the
record's `LocksRevoked` from `u`'s state before the vote time of slot `σ + 1`, as in
`locks_clause_of_votes`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot of the votes; `tb`: the
  bound on their stamps; `u`: the revoking validator; `Hs`: the voters; `H`: the block each voter's
  vote is for; `B`: the block.

Read aloud: after the revocation against a delivered majority on `B`'s chain, no live lock conflicts
with `B`. -/
theorem revoked_entries_compatible_of_majority (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (σ tb : ℕ) (u : V) (Hs : Finset V) (H : V → Block V)
    (B : Block V)
    (hcard : |S.P.committee σ| < 2 * |Hs|)
    (hHB : ∀ u' ∈ Hs, B.AncestorEq (H u'))
    (hHeld : ∀ u' ∈ Hs, HeldEarlyVoteAt M (x.stateBefore (M.voteTime S.C (σ + 1)) u)
        ((tb : ℕ) : Int) σ (H u') u') :
    ∀ n' : M.N, LocksRevoked M S.P (x.stateBefore (M.voteTime S.C (σ + 1)) u)
        ((M.voteTime S.C (σ + 1) : ℕ) : Int) (σ + 1) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.stateBefore (M.voteTime S.C (σ + 1)) u)
          ((M.voteTime S.C (σ + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro n' hRev e he _
  have hR : RootsNameBlocksIn (M.fg_to_ac (x.stateBefore (M.voteTime S.C (σ + 1)) u)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ u
  obtain ⟨opp, hopp, hlt⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_opponents_lt (s := σ + 1) (Nat.succ_ne_zero σ) hRev e he
  simp only [Nat.add_sub_cancel] at hopp hlt
  by_contra hc
  -- every voter of `Hs` opposes `e.B`
  have hsub : Hs ⊆ opp := by
    intro u' hu'
    obtain ⟨hp, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u' hu'
    -- the vote's voter is no equivocator: its one vote of slot `σ` is the only one `u` holds
    have hneq : u' ∉ M.equivocators (M.votesHeldSet (x.stateBefore (M.voteTime S.C (σ + 1)) u) σ) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_equivocators_iff_two M F)]
      rintro ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩
      exact hne ((huniq v₁ hv₁ h1).trans (huniq v₂ hv₂ h2).symm)
    -- the vote's block conflicts with `e.B`
    have hconf : (H u').conflicts e.B = true := by
      rw [conflicts_iff, compatible_iff]
      rintro (h | h)
      · exact hc ((compatible_iff _ _).2 (Or.inr (ancestorEq_trans (hHB u' hu') h)))
      · exact hc ((compatible_iff _ _).2 (ancestorEq_compatible h (hHB u' hu')))
    -- the vote resolves and opposes `e.B`: `u'` is among the opponents
    exact (hopp u').2 ⟨hneq, _, hp, rfl, ⟨y, hy⟩, ⟨H u', hHΦ, rfl, hconf⟩⟩
  have hle := Finset.card_le_card hsub
  omega

end GoldilocksCorrectness.Record.Proofs.Executions

