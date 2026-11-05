module
public import GoldilocksCorrectness.Proofs.Executions.FinalityLivenessKit

@[expose] public section

/-!
# The finality-liveness kit: no honest timeout after healing, and the monotonicity of the
justification and finalization heights

The audited statements proved in `GoldilocksCorrectness/Proofs/Executions/FinalityLivenessKit.lean`:

- `no_honest_timeout_after_healing`: from the healed round's action time on, an attestation an
  honest awake validator puts on the wire at a height greater than `H` is a target;
- `chainStateOf_h_j_h_F_mono`: along a chain, the justification height and the finalization height
  of the chain state never decrease.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **The justification and finalization heights never decrease along a chain.** When `A` is an
ancestor of `B` or `B` itself, the chain state of `B` has a justification height at least `A`'s
and a finalization height at least `A`'s.

Why: a block's justification height is its parent's, or its parent's height, which is greater;
every pending justification of a chain state is at a height greater than its finalization height,
so the loop over them in `process_height_events` leaves a finalization height at least the
parent's; then an induction on the ancestry.

The variables:
- `C`: the parameters; `A`: the ancestor; `B`: the descendant.

Read aloud: along a chain, `h_j` and `h_F` only rise.

 -/
theorem chainStateOf_h_j_h_F_mono (C : Config) (A B : Block V)
    -- `A` is an ancestor of `B`, or `B` itself
    (hAB : A.AncestorEq B) :
    (chainStateOf C A).h_j ≤ (chainStateOf C B).h_j ∧
      (chainStateOf C A).h_F ≤ (chainStateOf C B).h_F :=
  GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono C A B hAB

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the bound
  on the heights of the honest attestations sent before the healed round's action time;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation.

Read aloud: after healing, honest validators only vote targets at new heights.

 -/
theorem no_honest_timeout_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i t : ℕ) (v : V) (a : Attestation V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- every honest attestation sent before the support cutoff of slot `s₀ + 1` has height at most
    -- `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- `t` is at or after the support cutoff of slot `s₀ + 1`
    (ht₀ : supportCutoff S (s₀ + 1) ≤ t)
    -- `v` is awake at `t`
    (hAwake : v ∈ Sched.awake (t : Int))
    -- `v` is outside the adversary set at `t`
    (hHon : v ∉ Sched.adv (t : Int))
    -- the step `i` put `v`'s attestation `a` on the wire
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    -- `a`'s height is greater than `H`
    (hH : H < a.h) :
    a.τ = false :=
  GoldilocksCorrectness.Proofs.Executions.no_honest_timeout_after_healing S Sched x s₀ H i t v a
    hDiv hMono hChain hOld hl ht₀ hAwake hHon hSent hH

end GoldilocksCorrectness.Statements.Executions
