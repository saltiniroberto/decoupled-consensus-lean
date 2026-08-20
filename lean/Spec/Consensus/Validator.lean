import Spec.Consensus.Fig6TimedStore

/-!
# The honest validator

The draft's Section 6, which the pdf marks `[To be drafted.]` — so unlike the figure
files, nothing here renders existing text. The semantics are fixed by Roberto's dictation,
rule by rule (decided 2026-08-20), and the Lean is the primary artifact; the paper's
Section 6 can follow it. No figure, hence no figure number in the filename and no
`-- line n` comments.

What Sections 1–4 already fix, and this file calls rather than redefines: the SG/FG
action happens at `a_r` (Definition 9) and its outputs are anchored at `Σ.action_root[r]`
(Definition 15); the opening proposer's proposal root comes from `get_proposal_root`
(Definition 13); each Goldfish fork choice starts from the walk root (Definition 14).

Pure functions first: what to sign or build at each instant, as functions of the timed
store. The lean-sts execution wiring — sends, receipts, the network — is a later, separate
step.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator : Type}

section Actions
variable [DecidableEq Validator] [Electorate Validator] [Params] [Omega Validator]

/-- Validator `i`'s SG and FG action for round `r`, performed at `a_r`: the one combined
    attestation of the round, its SG half the head, its FG half the two pairs.

    The precondition is an autoparam: a call site where `S.t = actionTime r` is in
    context — `onTick`'s `a_r` branch, or a statement's hypothesis — discharges it
    silently, and anywhere else it must be proved. A statement supplying it must hold it
    as a *named* hypothesis: `assumption` does not see anonymous arrow binders during
    statement elaboration (measured on `lemChainTargetFirstBlock`).

    **The body is a skeleton, not a rule.** Every line marked `skeleton:` is a
    placeholder decision awaiting Roberto's dictation, 2026-08-20:

    * the anchor is the stored action root, with the fork-choice root standing in when
      the entry is unset — unreachable on schedule, where `on_tick` wrote it at this very
      instant;
    * the FG halves are read from the anchor's own post-state, and are unconditionally
      the exact target vote and the latest-justification commitment — no empty-target
      rule, no condition on committing;
    * the head is the anchor itself, standing in for Section 5's confirmed head;
    * an anchor the state map misses signs the all-empty attestation;
    * no signing history is consulted. -/
def onSGFGVotingAction (i : Validator) (S : Store Validator) (r : Nat)
    (_ : S.t = actionTime r := by assumption) :
    Attestation Validator := Id.run do
  -- the anchor (Definition 15): the root `on_tick` stored at `a_r`
  let A := (S.actionRoot r).getD (forkChoiceRoot S)  -- skeleton: fallback for the unset case
  if _ : A ∈ S.σ then
    let σ := S.σ[A]
    return {
      validator := i
      round := r
      head := some A                       -- skeleton: stands in for §5's confirmed head
      heightPair := .target σ.h σ.T_h      -- skeleton: always the exact target vote
      finalityPair := .pair σ.h_j σ.J }    -- skeleton: always commit `(h_j, J)`
  -- skeleton: an anchor the state map misses signs the all-empty attestation
  return { validator := i, round := r, head := ⊥, heightPair := .empty, finalityPair := .empty }

end Actions

end Consensus
