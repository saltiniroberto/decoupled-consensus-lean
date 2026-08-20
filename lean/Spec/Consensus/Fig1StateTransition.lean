import Spec.Consensus.Notation

/-!
# Figure 1 — State transition

The draft's per-block transition: `state_transition`, `process_attestation`,
`process_height_events` and `advance_height`, over the chain state of Definition 6. The
post-state of a block `B` is `stateTransition σ[B.parent] B`, a deterministic function of
`B`'s chain.

The `-- line n` comments use Figure 1's own line numbering, in the draft as of 2026-08-19.
The routines appear callee-first because Lean wants a definition before its use; the
figure's order is the reverse.

## Five things to know while reading

**The transition is total.** Every routine returns a state; there is no `invalid`. Whether
a block is accepted at all is the store's business (the draft's Section 3), not this
figure's.

**`σ` on a right-hand side is the state at that statement.** The assignment macros expand
to `σ := { σ with … }`, so consecutive lines read each other's effects, exactly as the
figure's imperative text does.

**`σ.L` is still the parent block while attestations are processed.** The figure writes
`σ.L ← B` only after the loop, so `process_attestation`'s progress test `T ⪯ σ.L` bounds
targets by the chain *up to `B`'s parent* — a block's own attestations cannot use `B`
itself as evidence.

**Prestate classification.** The draft says every attestation in a block is classified
against the block's prestate, while the figure folds them one after another. The two agree
here because the fields `process_attestation` *reads* — `h`, `T_h`, `h_j`, `J`, `L` — are
disjoint from the ones it *writes*, which are the three bit arrays. That is an observation
about this rendering, not a proved lemma.

**`σ.` is written out.** The figure's `PROCESS_ATTESTATION` elides nothing, but a future
figure may; either way, every field write here is `σ.field ← …`, because the assignment
macro cannot know which bare identifiers are fields of the state record.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator : Type}

/-! ## Definition 6 — the chain state -/

/-- The chain state (Definition 6 of the draft), in the draft's field order:
    `σ = (L, s, h, T_h, target_participation, progress, finalize, J, h_j, F, h_F)`.

    The three arrays hold one bit per validator; the quorum sets `Qtarget`, `Qprog` and
    `Qfinality` below are derived from them when used. -/
structure ChainState (Validator : Type) where
  /-- `L`, the latest block. -/
  L : Block Validator
  /-- `s`, the current slot. -/
  s : Nat
  /-- `h`, the current height — the finality counter, separate from slot. It advances by
      exactly one, at a justification or a progress event. -/
  h : Nat
  /-- `T_h`, the current height's *target*: the block that carried the transition into `h`
      — genesis for height 1. Always a block, never `⊥`: the genesis state names genesis,
      and every advance names the advancing block. -/
  T_h : Block Validator
  /-- `target_participation[i]`: `i` attested the exact pair `(h, T_h)`. -/
  targetParticipation : Validator → Bool
  /-- `progress[i]`: `i` made a current-height attestation that proves progress. -/
  progress : Validator → Bool
  /-- `finalize[i]`: `i`'s finality pair matched the latest justification `(h_j, J)`. -/
  finalize : Validator → Bool
  /-- `J`, the latest justified block. -/
  J : Block Validator
  /-- `h_j`, its height. -/
  h_j : Nat
  /-- `F`, the latest finalized block. -/
  F : Block Validator
  /-- `h_F`, its height. -/
  h_F : Nat

/-- The genesis state: `L = T_h = B_gen`, `s = 0`, `h = 1`,
    `(J, h_j) = (F, h_F) = (B_gen, 0)`, and every bit false. Genesis counts as justified
    and finalized at height 0, and every chain begins at height 1. -/
def ChainState.gen : ChainState Validator where
  L := .genesis
  s := 0
  h := 1
  T_h := .genesis
  targetParticipation _ := false
  progress _ := false
  finalize _ := false
  J := .genesis
  h_j := 0
  F := .genesis
  h_F := 0

section QuorumSets
variable [Electorate Validator]

/-- `Q_target(σ) = {i : σ.target_participation[i]}`, intersected with the electorate,
    since only `V`'s weights are ever summed. -/
def ChainState.Qtarget (σ : ChainState Validator) : Finset Validator :=
  Electorate.V.filter fun i => σ.targetParticipation i

/-- `Q_prog(σ) = {i : σ.progress[i]}`, likewise. -/
def ChainState.Qprog (σ : ChainState Validator) : Finset Validator :=
  Electorate.V.filter fun i => σ.progress i

/-- `Q_finality(σ) = {i : σ.finalize[i]}`, likewise. -/
def ChainState.Qfinality (σ : ChainState Validator) : Finset Validator :=
  Electorate.V.filter fun i => σ.finalize i

end QuorumSets

/-! ## The four routines -/

section Routines
variable [DecidableEq Validator] [Electorate Validator] [Params]

open Params

/-- `process_attestation(σ, a)` (Figure 1, lines 7–15): classify one attestation and set
    the bits it earns. The three tests are independent, so an exact target vote sets both
    the target-participation and the progress bit — the exact target `T_h` lies on `σ.L`'s
    chain.

    `σ.L` is the including block's parent here; see the module header. -/
def processAttestation (σ : ChainState Validator) (a : Attestation Validator) :
    ChainState Validator := Id.run do
  let mut σ := σ
  let i := a.validator                                        -- line 8
  if a.finalityPair = .pair σ.h_j σ.J then                    -- line 9
    σ.finalize[i] ← true                                      -- line 10
  if a.heightPair = .target σ.h σ.T_h then                    -- line 11
    σ.targetParticipation[i] ← true                           -- line 12
  -- line 13: `if a's height pair = (σ.h, ⊥), or = (σ.h, T) with T ⪯ σ.L`
  match a.heightPair with
  | .emptyTarget hh => if hh = σ.h then σ.progress[i] ← true  -- line 14
  | .target hh T => if hh = σ.h ∧ T ⪯ σ.L then σ.progress[i] ← true
  | .empty => pure ()
  return σ                                                    -- line 15

/-- `advance_height(σ)` (Figure 1, lines 25–28): increment the height, record the advancing
    block — `σ.L`, already the block being processed — as the new height's target, and
    clear both height-participation arrays. The `finalize` array is *not* cleared here; the
    justify event clears it before calling this. -/
def advanceHeight (σ : ChainState Validator) : ChainState Validator := Id.run do
  let mut σ := σ
  σ.h ← σ.h + 1                                               -- line 26
  σ.T_h ← σ.L
  σ.targetParticipation, σ.progress ← fun _ => false          -- line 27: `false^V`
  return σ                                                    -- line 28

/-- `process_height_events(σ)` (Figure 1, lines 16–24): after a block's attestations are
    folded in, the height events are checked once, in order — *finalize*, then *justify*,
    then *progress*. Justification therefore wins whenever both height thresholds are
    present, and a nonjustifiable height — `(K ∣ h) ∧ (h − h_F > D)`, tested inline against
    the possibly-just-updated `h_F` — can still be passed through the progress event. -/
def processHeightEvents (σ : ChainState Validator) : ChainState Validator := Id.run do
  let mut σ := σ
  if σ.h_j > σ.h_F ∧ w(σ.Qfinality)≥q then                    -- line 17
    σ.F ← σ.J                                                 -- line 18: `(σ.F, σ.h_F) ← (σ.J, σ.h_j)`
    σ.h_F ← σ.h_j
  if ¬ (σ.h % K = 0 ∧ σ.h - σ.h_F > D) ∧ w(σ.Qtarget)≥q then  -- line 19: `(K ∣ σ.h)` is `σ.h % K = 0`
    σ.J ← σ.T_h                                               -- line 20: `(σ.J, σ.h_j) ← (σ.T_h, σ.h)`
    σ.h_j ← σ.h
    σ.finalize ← fun _ => false                               -- line 20: `σ.finalize ← false^V`
    return advanceHeight σ                                    -- line 21
  if w(σ.Qprog)≥q then                                        -- line 22
    return advanceHeight σ                                    -- line 23
  return σ                                                    -- line 24

/-- `state_transition(σ, B)` (Figure 1, lines 1–6), with `σ = σ[B.parent]`: fold `B`'s
    attestations into the parent's post-state, install `B` as the latest block, and check
    the height events once. The block's post-state is `σ[B] = stateTransition σ[B.parent] B`,
    and the *state-height* of `B` is `σ[B].h`. -/
def stateTransition (σ : ChainState Validator) (B : Block Validator) :
    ChainState Validator := Id.run do
  let mut σ := σ
  σ.s ← B.slot                                                -- line 2
  for a in B.attestations do                                  -- line 3
    σ ← processAttestation σ a                                -- line 4
  σ.L ← B                                                     -- line 5
  return processHeightEvents σ                                -- line 6

end Routines

end Consensus
