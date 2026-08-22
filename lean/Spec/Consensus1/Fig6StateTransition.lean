import Spec.Consensus1.Notation

/-!
# Figure 6 — the deterministic finality-gadget state transition

Definition 4's chain state and Figure 6's four routines: `state_transition`,
`process_attestation`, `process_height_events` and `advance_height`. Every block is evaluated
from its parent's immutable post-state, `σ[B] = state_transition(σ[B.parent], B)`, and the
result is a deterministic function of the chain ending at `B`.

The `-- line n` comments use Figure 6's own line numbering, in the draft as of 2026-08-22.
The routines appear callee-first, because Lean wants a definition before its use; the
figure's order is `state_transition`, `process_attestation`, `process_height_events`,
`advance_height`.

**It comes before the store in the import order**, though it is Figure 6 of seven: the store
holds `Σ.σ[·]`, a map into the chain state, so Definition 4 has to exist first. The file
names keep the draft's figure numbers; the import order is dependency order.

## Four things to know while reading

**The transition is total.** Every routine returns a state; there is no `invalid`. Whether a
block is accepted at all is the store's business (Figure 7), not this figure's.

**`σ` on a right-hand side is the state at that statement.** The assignment macros expand to
`σ := { σ with … }`, so consecutive lines read each other's effects, exactly as the figure's
imperative text does.

**`σ.L` is still the parent block while attestations are processed.** Line 5 writes `σ.L ← B`
only after the loop, so an attestation is classified against the height and target the
*parent's* post-state carried — which is what makes a block's own attestations unable to use
that block as evidence.

**`nj` is a stored field.** The draft computes it on entry into a height, "after the same
transition has applied any finalization", and keeps it until the height changes: `advance
height` writes it at line 29, and the justify event reads it at line 20. The previous draft
recomputed the same test inline at the justify event, which is not the same rule — this one
reads the `h_F` of the height's *entry*, not of the moment the justification fires.

## `(K ∣ h)` is written `h % K = 0`

The draft writes the divisibility as `(K | h)`. Lean's `∣` reads as a pipe to anyone who has
not met it, so this subtree writes `h % Params.K = 0`, as the previous rendering did.
-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots]

/-! ## Definition 4 — the chain state -/

/-- The chain state (Definition 4 of the draft), in the draft's field order:
    `σ = (L, s, h, T_h, nj, target_participation, progress, finalize, J, h_j, F, h_F)`.

    The three arrays hold one bit per validator; the quorum sets `Qtarget`, `Qprog` and
    `Qfinality` below are derived from them when used. -/
structure ChainState (Validator : Type) where
  /-- `L`, the latest block. -/
  L : Block Validator
  /-- `s`, the current slot; the draft notes `s = L.slot`. -/
  s : Nat
  /-- `h`, the current height — the finality counter, separate from slot. It advances by
      exactly one, at a justification or a progress event. -/
  h : Nat
  /-- `T_h`, the block that carried the transition into height `h` — genesis for height 1.
      Always a block, never `⊥`: the genesis state names genesis, and every advance names
      the advancing block. -/
  T_h : Block Validator
  /-- `nj`, computed when the chain enters `h` and fixed until the height changes: the
      height is *nonjustifiable*. See the module header on why it is stored. -/
  nj : Bool
  /-- `target_participation[i]`: `i` attested the exact pair `(h, T_h)`. -/
  targetParticipation : Validator → Bool
  /-- `progress[i]`: `i` made a current-height attestation that proves progress. -/
  progress : Validator → Bool
  /-- `finalize[i]`: `i`'s finality pair matched the latest justification `(h_j, J)`. -/
  finalize : Validator → Bool
  /-- `J`, the latest justification on the chain. -/
  J : Block Validator
  /-- `h_j`, its height. -/
  h_j : Nat
  /-- `F`, the latest finalization. -/
  F : Block Validator
  /-- `h_F`, its height. -/
  h_F : Nat

/-- The initial chain state: `L = T_h = J = F = B_gen`, `s = 0`, `h = 1`,
    `h_j = h_F = 0`, `nj = false`, and every array entry false. Genesis "is justified and
    finalized at height 0, and every chain starts at height 1". -/
def ChainState.gen : ChainState Validator where
  L := .genesis
  s := 0
  h := 1
  T_h := .genesis
  nj := false
  targetParticipation _ := false
  progress _ := false
  finalize _ := false
  J := .genesis
  h_j := 0
  F := .genesis
  h_F := 0

section QuorumSets
variable [DecidableEq Validator] [Electorate Validator]

/-- `Q_target(σ) = {i : σ.target_participation[i]}`, intersected with the electorate, since
    only `V`'s weights are ever summed. -/
def ChainState.Qtarget (σ : ChainState Validator) : Finset Validator :=
  {i ∈ Electorate.V | σ.targetParticipation i}

/-- `Q_prog(σ) = {i : σ.progress[i]}`, likewise. -/
def ChainState.Qprog (σ : ChainState Validator) : Finset Validator :=
  {i ∈ Electorate.V | σ.progress i}

/-- `Q_finality(σ) = {i : σ.finalize[i]}`, likewise. -/
def ChainState.Qfinality (σ : ChainState Validator) : Finset Validator :=
  {i ∈ Electorate.V | σ.finalize i}

end QuorumSets

/-! ## The four routines -/

section Routines
variable [DecidableEq Validator] [Electorate Validator] [Params]

open Params

/-- `process_attestation(σ, a)` (Figure 6, lines 7–16): classify one attestation and set the
    bits it earns.

    The finality test wants three things at once (line 9): an unfinalized justification,
    `σ.F ⪯ σ.J`, and a finality pair naming that justification exactly.

    The height tests are an `if`/`else if`, and the first branch sets **both** bits: an exact
    target vote proves progress as well, `T_h` being on the chain by construction. An exact
    empty-target vote proves only progress.

    `σ.L` is the including block's parent here; see the module header. -/
def processAttestation (σ : ChainState Validator) (a : Attestation Validator) :
    ChainState Validator := Id.run do
  let mut σ := σ
  let i := a.validator                                        -- line 8
  -- line 9
  if σ.h_j > σ.h_F ∧ σ.F ⪯ σ.J ∧ a.finalityPair = .pair σ.h_j σ.J then
    σ.finalize[i] ← true                                      -- line 10
  if a.heightPair = .target σ.h σ.T_h then                    -- line 11
    σ.targetParticipation[i] ← true                           -- line 12
    σ.progress[i] ← true                                      -- line 13
  else if a.heightPair = .emptyTarget σ.h then                -- line 14
    σ.progress[i] ← true                                      -- line 15
  return σ                                                    -- line 16

/-- `advance_height(σ)` (Figure 6, lines 27–31): increment the height, record the advancing
    block — `σ.L`, already the block being processed — recompute `nj` for the height just
    entered, and clear both height-participation arrays.

    The `finalize` array is *not* cleared here: the justify event clears it before calling
    this, at line 22, and the progress event does not clear it at all. -/
def advanceHeight (σ : ChainState Validator) : ChainState Validator := Id.run do
  let mut σ := σ
  σ.h ← σ.h + 1                                               -- line 28
  σ.T_h ← σ.L
  -- line 29: `σ.nj ← (K ∣ σ.h) ∧ (σ.h − σ.h_F > D)`; the divisibility is `% = 0`
  σ.nj ← σ.h % K = 0 ∧ σ.h - σ.h_F > D
  σ.targetParticipation, σ.progress ← fun _ => false          -- line 30: `false^V`
  return σ                                                    -- line 31

/-- `process_height_events(σ)` (Figure 6, lines 17–26): after a block's attestations are
    folded in, the height events are checked once, in order — *finalize*, then *justify*,
    then *progress*.

    Justification therefore wins whenever both height thresholds are present, and a
    nonjustifiable height can still be passed through the progress event. The finalize event
    is not exclusive with the other two: it fires and falls through, so one transition can
    finalize and then advance.

    `σ.nj` is read, not recomputed — see the module header. -/
def processHeightEvents (σ : ChainState Validator) : ChainState Validator := Id.run do
  let mut σ := σ
  -- line 18
  if σ.h_j > σ.h_F ∧ σ.F ⪯ σ.J ∧ w(σ.Qfinality)≥q then
    σ.F ← σ.J                                                 -- line 19: `(σ.F, σ.h_F) ← (σ.J, σ.h_j)`
    σ.h_F ← σ.h_j
  if ¬ σ.nj ∧ w(σ.Qtarget)≥q then                             -- line 20
    σ.J ← σ.T_h                                               -- line 21: `(σ.J, σ.h_j) ← (σ.T_h, σ.h)`
    σ.h_j ← σ.h
    σ.finalize ← fun _ => false                               -- line 22: `false^V`
    return advanceHeight σ                                    -- line 23
  if w(σ.Qprog)≥q then                                        -- line 24
    return advanceHeight σ                                    -- line 25
  return σ                                                    -- line 26

/-- `state_transition(σ, B)` (Figure 6, lines 1–6), with `σ = σ[B.parent]`: fold `B`'s
    attestations into the parent's post-state, install `B` as the latest block, and check the
    height events once. The *state height* of `B` is `σ[B].h`, which is what Definition 5's
    viability and Figure 7's height filter read. -/
def stateTransition (σ : ChainState Validator) (B : Block Validator) :
    ChainState Validator := Id.run do
  let mut σ := σ
  σ.s ← B.slot                                                -- line 2
  for a in B.attestations do                                  -- line 3
    σ ← processAttestation σ a                                -- line 4
  σ.L ← B                                                     -- line 5
  return processHeightEvents σ                                -- line 6

end Routines

end Consensus1
