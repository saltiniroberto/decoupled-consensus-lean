module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# ProposalPropagation, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/ProposalPropagation.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: a block a validator holds before `t`
has a slot at most the slot of `t − 1`, and block propagation from a given send. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A block a validator holds before the time `t` has a slot at most the slot of some clock value `c`
that is less than `t + ΔClockAhead`, or is `0`, the initial clock: it entered the validator's tree at
a step whose time is less than `t`, with the validator's clock value then in a slot at least the
block's (`tree_block_relayed_before`), and that clock value is at most the step's real time plus
`ΔClockAhead`, or `0` (`clockValue_le_time_add_ahead`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `t`: the time; `v`: the validator;
- `B`: the block; `c`: the clock value.

Read aloud: a block `v` holds before `t` has a slot at most the slot of a clock value less than
`t + ΔClockAhead`, or of the initial clock. -/
theorem slot_lt_of_mem_T_before (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v : V) (B : Block V)
    (hB : B ∈ (x.stateBefore t v).tree) :
    ∃ c : ℕ, (c = 0 ∨ (c : ℝ) < (t : ℝ) + ΔClockAhead) ∧ B.slot ≤ S.C.slot (c : Int) := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact ⟨0, Or.inl rfl, Nat.zero_le _⟩
  obtain ⟨i, hi, -, -, hslot⟩ := (tree_block_relayed_before M F R) E hB hg
  have hlt : x.time (i + 1) < t := ((lt_stepBefore_iff M) x R E).1 hi
  refine ⟨x.clockValue (i + 1) v, ?_, ?_⟩
  · have hc := (clockValue_le_time_add_ahead M F) x R E (i + 1) v
    rcases le_total (x.time (i + 1) + ΔClockAhead) 0 with h0 | h0
    · left
      rw [max_eq_left h0] at hc
      exact_mod_cast le_antisymm hc (Nat.cast_nonneg _)
    · right
      rw [max_eq_right h0] at hc
      linarith
  · rw [(clock_eq_clockValue M F) x R (i + 1) v] at hslot
    exact hslot

end GoldilocksCorrectness.Record.Proofs.Executions

