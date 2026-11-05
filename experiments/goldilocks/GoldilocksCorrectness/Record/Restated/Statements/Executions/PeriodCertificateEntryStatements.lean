module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodCertificateEntry

@[expose] public section

/-!
# PeriodCertificateEntryStatements, over a model

The statements of
`GoldilocksCorrectness/Statements/Executions/PeriodCertificateEntryStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the certified entry of a
progress certificate on an honest-held chain is held by its honest attester; the theorem of the same
name of `Record/Restated/Proofs/Executions/PeriodCertificateEntry.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)

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

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Kit fact K1: the certified entry is held by an honest attester at its tick.** Take a block
`Y` that `w`, outside the adversary set at the time after `j` steps, holds after `j` steps, and a
progress certificate on the chain of `Y` at the height `h` naming the block `T`, an ancestor of
`Y` or `Y`. When fewer than a quorum of validators have been in the adversary set up to that time,
and roots name blocks among the blocks honest validators hold by then: some validator `uₐ` is an
updater of some slot `sₐ`, outside the adversary set at `M.supportCutoff S.C (sₐ + 1)`, a time at
most the time after `j` steps; some fast block `F` of the state right after `uₐ`'s tick at that time
has `T` as an ancestor or is `T`; and `uₐ` held `T` in its FG tree before that tick.

Why: some member `u` of the certificate's quorum is honest up to the time after `j` steps; its
attestation is in its record (Lemma 74), so its tick sent an attestation with that content at an
earlier step (`record_content_sent_step`). That tick is at `M.supportCutoff S.C (sₐ + 1)` for an
updater `u` of `sₐ`, and the attestation names, by root, the entry `E` of the chain state of a
fast block `F` of that update, with `E` an ancestor of `F` and `F` held before the tick
(`attest_source_fast_block_updater_inTree`). `E` and `T` have one root and are held by honest
validators by the time after `j` steps, so `E = T`.

 every
hypothesis is read. The height `h` is not compared with a threshold here (`cert_entry_at_slot`'s
`hOld` is not taken).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `j`: the step; `w`: the holder;
  `Y`: the held block; `T`: the block the certificate names; `h`: its height.

Read aloud: a progress certificate on a chain an honest validator holds has an honest attester that
ran the update of a slot `sₐ` awake and honest from that slot's duty window up to its own tick to
`M.supportCutoff S.C (sₐ + 1)`, a step before the step `j`, and is outside
the adversary set after every step whose time is at most the time after `j` steps; that
tick sent it; the certified block `T` is an ancestor of that update's fast block `F`, or `F`,
and the attester held `T` before that tick. -/
theorem cert_entry_held_by_attester (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (j : ℕ) (w : V) (Y T : Block V) (h : Height)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- what honest validators sign is never forged
    -- fewer than a quorum have been in the adversary set up to the time after `j` steps
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time j))
    -- roots name blocks among the blocks honest validators hold by that time
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    -- `w` is outside the adversary set at that time
    (hw : w ∉ A.corrupted j)
    -- `w` holds `Y` after `j` steps
    (hY : Y ∈ (x.st j w).tree) (hTY : T.AncestorEq Y) (hJ : ProgressCertOn M Y h T) :
    ∃ (sₐ : ℕ) (uₐ : V) (F : Block V), x.tickStep uₐ (M.supportCutoff S.C (sₐ + 1)) < j ∧
      uₐ ∈ A.activeThroughoutToTick x (duty_window_start S.C (sₐ + 1)) (M.supportCutoff S.C (sₐ + 1)) ∧
      uₐ ∉ A.corruptedAtTime x (x.time j) ∧
      F ∈ (x.tickOutput uₐ (M.supportCutoff S.C (sₐ + 1))).fastBlocks ∧ T.AncestorEq F ∧
      T ∈ (x.tickInput uₐ (M.supportCutoff S.C (sₐ + 1))).tree :=
  (GoldilocksCorrectness.Record.Proofs.Executions.cert_entry_held_by_attester M F U Fx) S A x R j
    w Y T h E hAdvQ hRoots hw hY hTY hJ

end GoldilocksCorrectness.Record.Statements.Executions

