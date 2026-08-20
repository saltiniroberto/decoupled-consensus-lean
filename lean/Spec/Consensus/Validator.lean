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
variable [DecidableEq Validator] [Electorate Validator] [Params]

/-- The round's Goldfish confirmation, from a walk start (Roberto's rule, 2026-08-20):
    filter the tree from `walkStart` — keep the blocks of the candidate tree `C(Σ)` that
    descend from it and that the veto does not exclude — then run the Goldfish fork choice
    from `walkStart` over exactly the blocks that survive; `none` when nothing does.

    The walk itself is the draft's Section 5, undrafted, so the store's `Ω` stands for
    "run Goldfish from `walkStart` over this set": the membership proof it carries is what
    gives the result the three filter properties — in `C(Σ)`, descending from `walkStart`,
    unvetoed. When Section 5 lands, the `Ω` application becomes the vote-driven walk. -/
def goldfishConfirmation (S : Store Validator) (walkStart : Block Validator)
    (vetoed : Block Validator → Prop) [DecidablePred vetoed] :
    Option (Block Validator) :=
  let candidates := (candidateTree S).filter fun B => walkStart ⪯ B ∧ ¬ vetoed B
  if h : candidates.Nonempty then some (S.Ω candidates h).val else none

/-- Validator `i`'s SG and FG action for round `r`, performed at `a_r`: the one combined
    attestation of the round, its SG half the head, its FG half the two pairs.

    The precondition is an autoparam: a call site where `S.t = actionTime r` is in
    context — `onTick`'s `a_r` branch, or a statement's hypothesis — discharges it
    silently, and anywhere else it must be proved. A statement supplying it must hold it
    as a *named* hypothesis: `assumption` does not see anonymous arrow binders during
    statement elaboration (measured on `lemChainTargetFirstBlock`).

    **The body is a skeleton, not a rule.** The pipeline as dictated so far, 2026-08-20,
    with the remaining inventions marked `skeleton:`. What it does:

    * anchor at the stored action root `A`, fork-choice root standing in when the entry is
      unset — unreachable on schedule, where `on_tick` wrote it at this very instant;
    * derive the round's confirmation with `goldfishConfirmation` from `A`, under the veto
      "some accepted block on the finalized chain, conflicting with the candidate, might
      still hold majority support" — `G0`, playing the role the old paper's strong G0
      check gave it;
    * with a confirmation `C`: head is `C`, and the current-height pair is read off `C`'s
      post-state — the exact target vote at a justifiable height, the empty-target
      (progress-only) vote at a nonjustifiable one, the same test Figure 1's justify event
      applies on receipt;
    * without one: no head, no current-height pair;
    * the finality half is independent of the confirmation, as in the old paper: read off
      the anchor's post-state, commit the latest justification `(h_j, J)` while it is
      unfinalized — heights in the two pairs always differ (`h_j < h`), so one honest
      attestation cannot trip slashing condition E1 against itself.

    Still consciously dropped from the old pipeline, each a decision to re-make: the
    source-proposal branch — the old rule prefers the graded proposal's state over the
    confirmation's — and the signing history, which the old rule filters every pair
    through. -/
def onSGFGVotingAction (i : Validator) (S : Store Validator) (r : Nat)
    (_ : S.t = actionTime r := by assumption) :
    Attestation Validator := Id.run do
  -- the anchor (Definition 15): the root `on_tick` stored at `a_r`
  let A := (S.actionRoot r).getD (forkChoiceRoot S)  -- skeleton: fallback for the unset case
  -- skeleton: the finality half, independent of the confirmation, off the anchor's state
  let finalityPair : FinalityPair Validator :=
    if _ : A ∈ S.σ then
      let σ := S.σ[A]
      if σ.h_j > σ.h_F then .pair σ.h_j σ.J else .empty
    else .empty
  -- the confirmation from `A`; skeleton: the veto is `G0` on a conflicting block over `Σ.F`
  let C? := goldfishConfirmation S A fun Q => ∃ B ∈ S.T, S.F ⪯ B ∧ ¬ B ∼ Q ∧ G0 S r B
  if hC : C?.isSome then
    let C := C?.get hC
    if _ : C ∈ S.σ then
      let σ := S.σ[C]
      -- skeleton: the current-height half, off the confirmation's state, no history
      let heightPair : HeightPair Validator :=
        if σ.h % Params.K = 0 ∧ σ.h - σ.h_F > Params.D then .emptyTarget σ.h
        else .target σ.h σ.T_h
      return {
        validator := i
        round := r
        head := some C
        heightPair := heightPair
        finalityPair := finalityPair }
  -- no confirmation (or one the state map misses — skeleton): no head, no height pair;
  -- the finality half still goes out
  return { validator := i, round := r, head := ⊥, heightPair := .empty
           finalityPair := finalityPair }

end Actions

end Consensus
