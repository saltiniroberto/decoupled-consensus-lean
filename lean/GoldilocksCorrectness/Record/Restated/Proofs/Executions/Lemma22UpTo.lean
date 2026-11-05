module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma22
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalPropagationUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma22
public import GoldilocksCorrectness.Proofs.Executions.ProposalPropagationUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma22UpTo, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma22UpTo.lean` over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 22 with the delivery premises up to
a bound, an honest proposal reaches every validator awake and honest for the next delay. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible compatible_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 22, an honest proposal reaches the next slot's voter.** The proof; the audited
statement is in `Statements/Executions/ProposalPropagationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer;
  `w`: the voter of slot `s + 1`.

Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`, the step the
delivery of `B` to `w` comes before. The proposer's honesty is read at its own tick
`i` (`tick_active`); no honesty of `p` at a real time is asked.

Restated with the delivery premises up to `M.voteTime S.C (s + 1)`: the proposal of slot `s + 1`
reaches `w` by then (`mem_T_before_of_send_upTo`).

Read aloud: after `GST`, an honest proposal of slot `s + 1` is held by the vote time of slot `s + 1`
by every validator awake and honest from the slot's start to its vote time whose finalized block is
compatible with it, the delivery premises read up to that vote time. -/
theorem lem22_proposal_held_by_voter_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s i : ℕ) (B : Block V) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ M.voteTime S.C s)
    -- `w` ticks to the vote time of slot `s + 1` at a step `kR` and is active after every step from the first one
    -- whose time is `ΔClockAhead` before the start of slot `s + 1` up to `kR` (, T-K1)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, (M.slotStart S.C (s + 1) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, put `B` on the wire, and left
    -- `p` holding `B`
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hBp : B ∈ (x.st (i + 1) p).tree)
    -- `w`'s finalized block before its vote is compatible with `B`
    (hF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible B = true) :
    B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
  -- the deadline `max (x.time (i + 1)) GST + ΔNet` is at most the vote time (so the promise up to it
  -- covers `p`'s send) and leaves `ΔClockAhead` before it: `p`'s tick is at most `ΔClockBehind` after the
  -- slot's start, `GST` is at most the slot's start, and `hNet`
  have hvt : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s ≤ M.slotStart S.C (s + 1) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s,
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      Nat.mul_add, Nat.mul_one]
    have := one_le_Δ S
    omega
  have hGSTR : (GST : ℝ) ≤ M.slotStart S.C (s + 1) := by exact_mod_cast hGST.trans hv₁
  have hvtR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = (M.slotStart S.C (s + 1) : ℝ) + Δ S := by
    rw [hvt]; push_cast; ring
  have hTi1 := ((time_of_lbl_tick M) x R E hl).2.2
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hmax : max (x.time (i + 1)) (GST : ℝ) ≤ (M.slotStart S.C (s + 1) : ℝ) + ΔClockBehind :=
    max_le hTi1 (by linarith)
  have hb : max (x.time (i + 1)) (GST : ℝ) + (ΔNet : ℝ) ≤ ((M.voteTime S.C (s + 1) : ℕ) : ℝ) := by
    rw [hvtR]; linarith
  exact (proposal_held_by_voter_of_deadline M F U) S A x R s i B p w E hSkew hRedeliver hRoots hParent hw hl
    hsent hBp (GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨hb, rfl⟩)
    (by rw [hvtR]; linarith) hF

end GoldilocksCorrectness.Record.Proofs.Executions

