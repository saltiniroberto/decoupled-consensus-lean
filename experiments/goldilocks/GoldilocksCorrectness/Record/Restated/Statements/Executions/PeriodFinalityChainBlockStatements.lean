module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFinalityChainBlock
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceChainBlockDefs
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceChainBlockDefs

@[expose] public section

/-!
# PeriodFinalityChainBlockStatements, over a model

The statements of
`GoldilocksCorrectness/Statements/Executions/PeriodFinalityChainBlockStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the step lemmas of Lemmas 103
and 106 over the copied certificate clause, the caches staying compatible with `B` and a held block
two heights past `B` descending from `B`; each is the theorem of the same name of
`Record/Restated/Proofs/Executions/PeriodFinalityChainBlock.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith)

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

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- **Lemma 103, the step: the caches stay compatible with `B`.** When `u`'s caches at step `j`
are compatible with `B` (`J` compatible with `B`, an entry at the height `h_j > H`, `F` an ancestor
of `J`), `u` is honest at step `j + 1`, and the copied certificate clause holds at `j + 1`, then
`u`'s caches at `j + 1` are compatible with `B`.

Why: Lemma 84's step with the family "compatible with `B`" (`update_finality_cachesOnChainWith`
through `reaction_tick_cachesFrom` and `receive_cachesFrom`): the justified block moves only to the
justified block of a held chain's state at a justification height at least the old one, so
greater than `H`; that block is an ancestor of the chain's block, its justification certificate on
the chain (Lemma 66) is a progress certificate, so the copied certificate clause makes it
compatible with `B`; it is an entry (Lemma 47f) at that height (Lemma 66). The finalized block
moves only to an ancestor of the justified block.

Rendering note. The probe's `caches_step`
(`scratch/goldilocks_async/probe_lanes_1.lean:705`) over the original clause
`CertificatesCompatibleWithAt` is false as worded and was never landed. The probe's `hRoots : RootsNameBlocks M S Sched x` is not
taken (the copied clause names the chain's own block; no root comparison is made), and the probe's
`hMono` is not taken either (not read: the caches at `j` are a hypothesis). Read aloud: the step of Lemma 103 over the certificate clause that speaks
of the chain's own block.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step; `u`: the validator;
- `hu`: `u` is honest at step `j + 1`; `hC`: `u`'s caches at `j` are compatible with `B`; `hCert`:
  the copied certificate clause at `j + 1`.

Read aloud: a delivery or a tick moves the caches only along certificates, and every certificate
that counts is for a block on `B`'s side. -/
theorem caches_step_ofChainBlock (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {H : ℕ} {B : Block V} (j : ℕ) (u : V)
    (hu : u ∉ A.corrupted (j + 1))
    (hC : CachesCompatibleWith M S B H (x.st j u))
    (hCert : CertificatesCompatibleWithAtOfChainBlock M A x H B (j + 1)) :
    CachesCompatibleWith M S B H (x.st (j + 1) u) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.caches_step_ofChainBlock M F Fx) S A x R E j u hu
    hC hCert

/-- **Lemma 106 at a step: a held block two heights past `B` descends from `B`.** When the copied
certificate clause holds at step `j` and `H < h(B)`, every block `D` a validator honest at `j`
holds with `h(D) ≥ h(B) + 2` is `B` or a descendant of `B`.

Why: Lemma 67 at the height `h(B) + 1`: `D`'s chain holds a progress certificate at `h(B) + 1 > H`
for its own entry `T'` at that height, a block of `D`'s chain; the copied certificate clause makes
`T'` compatible with `B`; its height `h(B) + 1` rules out `T'` being `B` or an ancestor of `B`, so
`B` is an ancestor of `T'`, hence of `D`.

Rendering note. The probe's `blocksTwoPastDescend_at`
(`scratch/goldilocks_async/probe_lanes_1.lean:721`) over the original clause is false as worded
 and was never landed. The
probe's `hRoots : RootsNameBlocks M S Sched x` is not taken (not read). Read aloud: the step of Lemma 106 over the
certificate clause that speaks of the chain's own block.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step;
- `hHB`: `H` is less than `B`'s chain-state height; `hCert`: the copied certificate clause at `j`.

Read aloud: a chain conflicting with `B` gains at most one height past `B`'s. -/
theorem blocksTwoPastDescend_at_ofChainBlock (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) {H : ℕ} {B : Block V} (j : ℕ)
    (hHB : H < (M.chainStateOf S.C B).h)
    (hCert : CertificatesCompatibleWithAtOfChainBlock M A x H B j) :
    ∀ (w : V) (D : Block V), w ∉ A.corrupted j → D ∈ (x.st j w).tree →
      (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D :=
  (GoldilocksCorrectness.Record.Proofs.Executions.blocksTwoPastDescend_at_ofChainBlock M F Fx) S
    A x j hHB hCert

end GoldilocksCorrectness.Record.Statements.Executions

