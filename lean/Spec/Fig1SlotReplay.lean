import Spec.Fig2AttestationProcessing

/-!
# Figure 1 (`alg:state-replay`) — deterministic slot replay

`height_filter_healing.tex`, Figure 1 (`alg:state-replay`), lines 711–746: `state_transition`,
`process_slots` and `process_slot`. The figure's **Genesis** block is `ChainState.gen`, in
`Spec/Defs/Basic.lean` beside Definition 13 (`def:chain-state`), which states the same
values.

Figure 1 calls into Figure 2 (`alg:attestation-processing`) twice, `process_block` and
`process_height_events`, and Figure 2 never calls back.

All notation comes from `Spec/Defs/Notation.lean`; read that first.

## The `while` is Lean's own

`process_slots` is written as the figure writes it, with no bound and no macro. That it
*terminates* is not an obligation Lean imposes on a `while` in `Id`. That it does what the
figure means is visible instead in `process_slot`, which ends with `s ← s + 1` on every
path, so each turn advances `s` by one.

## Two deviations from the figure's own spelling

**`σ.` is written out**, for the reason given in
`Spec/Fig2AttestationProcessing.lean`.

**`process_slots`' second parameter is `target`, not the figure's `slot`.** `Blk.slot` is a
projection, so `B.slot` is the figure's own spelling; a parameter named `slot` would shadow
it inside this one routine.
-/

set_option autoImplicit false

namespace Decoupled

open Framework.StsMultisetLog

variable {Node Root : Type}

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- `process_slot(σ)` (Figure 1, `alg:state-replay`, lines 738–746). Closes the slot at `s`:
    it may record the current height's target now that the latest block's root can be named,
    runs the height check when the slot is empty on this chain, and increments `s`.

    The emptiness test is `L.slot < s`. When `s` still names the latest block's own slot, that block's post-state already contains its height check, and
    Definition 17 (`def:direct-height-position`) is explicit that this call must not repeat
    it. -/
def processSlot (σ : ChainState Node Root) : ChainState Node Root := Id.run do
  let mut σ := σ
  if σ.T_h = ⊥ ∧ σ.L.slot ≥ σ.s_h then                        -- line 739
    σ.T_h ← some σ.L                                          -- line 740
  if σ.L.slot < σ.s then                                      -- line 742: empty on this chain
    σ ← processHeightEvents σ σ.s                             -- line 743
  σ.s ← σ.s + 1                                               -- line 745
  return σ

/-- `process_slots(σ, slot)` (Figure 1, `alg:state-replay`, lines 731–736). -/
def processSlots (σ : ChainState Node Root) (target : Time)
    : ChainState Node Root := Id.run do
  let mut σ := σ
  while σ.s < target do                                       -- line 732
    σ ← processSlot σ                                         -- line 733
  return σ                                                    -- line 735

/-- `state_transition(σ, B)` (Figure 1, `alg:state-replay`, lines 718–729). Rejects a block
    that does not extend the state's latest block, or that sits at or before `s`;
    otherwise closes the slots up to the block's own, processes the block, and runs the
    height events directly after this block's attestations, as
    Definition 17 (`def:direct-height-position`) requires. -/
def stateTransition (σ : ChainState Node Root) (B : Blk Node Root)
    : TransitionResult Node Root := Id.run do
  let mut σ := σ
  if B.parent ≠ some σ.L ∨ B.slot ≤ σ.s then                  -- line 719
    return invalid                                            -- line 720
  σ ← processSlots σ B.slot                                   -- line 722
  match processBlock σ B with                                 -- line 723
  | invalid => return invalid                                 -- lines 724–726
  | .state σ' => σ ← σ'
  -- Directly after this block's attestations.
  return processHeightEvents σ B.slot                         -- line 727

end

end Decoupled
