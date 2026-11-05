module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalityLivenessKit

@[expose] public section

/-!
# FinalityLivenessKitStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/FinalityLivenessKitStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the justification
and finalization heights never decrease along a chain, and no honest timeout after healing. Each is
the theorem of the same name of `Record/Restated/Proofs/Routines/ChainStateOf.lean` or
`Record/Restated/Proofs/Executions/FinalityLivenessKit.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (RecordConsistent)

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

omit [RootOrder] in
/-- **The justification and finalization heights never decrease along a chain.** When `A` is an
ancestor of `B` or `B` itself, the chain state of `B` has a justification height at least `A`'s
and a finalization height at least `A`'s.

Why: a block's justification height is its parent's, or its parent's height, which is greater;
every pending justification of a chain state is at a height greater than its finalization height,
so the loop over them in `process_height_events` leaves a finalization height at least the
parent's; then an induction on the ancestry.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `A`: the ancestor; `B`: the descendant.

Read aloud: along a chain, `h_j` and `h_F` only rise.

 -/
theorem chainStateOf_h_j_h_F_mono (C : Config) (A B : Block V) (hAB : A.AncestorEq B) :
    (M.chainStateOf C A).h_j ≤ (M.chainStateOf C B).h_j ∧
      (M.chainStateOf C A).h_F ≤ (M.chainStateOf C B).h_F :=
  (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_h_j_h_F_mono M F) C A B hAB

/-- **No honest timeout after healing.** In an execution where every time is reached, corruption
is permanent and the honest confirmations form a chain from slot `s₀`, and where every attestation
an honest awake validator put on the wire at a tick before the support cutoff of slot `s₀ + 1` has
height at most `H`: an attestation `a` that the validator `v`, awake and outside the adversary set
at the time `t`, puts on the wire at the tick of step `i` at `t`, with `t` at or after that support
cutoff and `a.h > H`, is a target (`a.τ = false`).

Why: `create_attestation` builds a timeout at the source's height `h_c` only when the record holds
a timeout at `h_c` or a target at `h_c` for a block other than the source's `T_h`; by the record's
consistency, `v` sent that attestation earlier, at a tick, awake and honest then. Sent before the
support cutoff, its height would be at most `H`; sent from then on, a timeout is excluded by
induction on the step, and a target names the honest chain's entry block at `h_c` (Lemma 82), as
`a` does, and two entry blocks of the honest chain at one height are one block, so it names the
source's `T_h`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the bound
  on the heights of the honest attestations sent before the healed round's action time;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation.

Read aloud: after healing, honest validators only vote targets at new heights.

 -/
theorem no_honest_timeout_after_healing (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i t : ℕ) (v : V) (a : Attestation V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain M S A x s₀)
    -- every honest attestation sent before the support cutoff of slot `s₀ + 1` has height at most
    -- `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = Event.tick v t) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ t)
    (hHon : v ∉ A.corruptedAtTime x t)
    -- the step `i` put `v`'s attestation `a` on the wire
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    -- `a`'s height is greater than `H`
    (hH : H < a.h) :
    a.τ = false :=
  (GoldilocksCorrectness.Record.Proofs.Executions.no_honest_timeout_after_healing M F U) S A x R
    s₀ H i t v a E hChain hOld hl ht₀ hHon hSent hH

end GoldilocksCorrectness.Record.Statements.Executions

