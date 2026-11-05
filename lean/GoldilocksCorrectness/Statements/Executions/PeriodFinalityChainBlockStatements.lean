module
public import GoldilocksCorrectness.Proofs.Executions.PeriodFinalityChainBlock
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceChainBlockDefs

@[expose] public section

/-!
- `blocksTwoPastDescend_at_ofChainBlock`, Lemma 106's step: a held block two heights past `B`
  descends from `B`.

 The probe's statements
(`scratch/goldilocks_async/probe_lanes_1.lean:705`, `:721`) over the original clause are false
as worded and are not landed.
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

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
`CertificatesCompatibleWithAt` is false as worded and was never landed. The probe's `hRoots : RootsNameBlocks S Sched x` is not
taken (the copied clause names the chain's own block; no root comparison is made), and the probe's
`hMono` is not taken either (not read: the caches at `j` are a hypothesis). Read aloud: the step of Lemma 103 over the certificate clause that speaks
of the chain's own block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step; `u`: the validator;
- `hu`: `u` is honest at step `j + 1`; `hC`: `u`'s caches at `j` are compatible with `B`; `hCert`:
  the copied certificate clause at `j + 1`.

Read aloud: a delivery or a tick moves the caches only along certificates, and every certificate
that counts is for a block on `B`'s side. -/
theorem caches_step_ofChainBlock {H : ℕ} {B : Block V} (j : ℕ) (u : V)
    (hu : u ∉ Sched.adv (x[j + 1].time : Int))
    (hC : CachesCompatibleWith S B H (x[j][u].st))
    (hCert : CertificatesCompatibleWithAtOfChainBlock S Sched x H B (j + 1)) :
    CachesCompatibleWith S B H (x[j + 1][u].st) :=
  GoldilocksCorrectness.Proofs.Executions.caches_step_ofChainBlock S Sched x j u hu hC hCert

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
probe's `hRoots : RootsNameBlocks S Sched x` is not taken (not read). Read aloud: the step of Lemma 106 over the
certificate clause that speaks of the chain's own block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step;
- `hHB`: `H` is less than `B`'s chain-state height; `hCert`: the copied certificate clause at `j`.

Read aloud: a chain conflicting with `B` gains at most one height past `B`'s. -/
theorem blocksTwoPastDescend_at_ofChainBlock {H : ℕ} {B : Block V} (j : ℕ)
    (hHB : H < (chainStateOf S.C B).h)
    (hCert : CertificatesCompatibleWithAtOfChainBlock S Sched x H B j) :
    ∀ (w : V) (D : Block V), w ∉ Sched.adv (x[j].time : Int) → D ∈ (x[j][w].st).S.T →
      (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D :=
  GoldilocksCorrectness.Proofs.Executions.blocksTwoPastDescend_at_ofChainBlock S Sched x j hHB
    hCert

end GoldilocksCorrectness.Statements.Executions
