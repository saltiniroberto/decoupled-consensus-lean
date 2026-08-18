import StsMultisetLog.Spec.Protocol
import Spec.Receive

/-!
# The node protocol, in the framework

This file renders no figure — it renders Figure 5 (`alg:recovery-action`,
lines 2081–2125), the
paper's own one-round summary, as the `Framework.StsMultisetLog.Protocol` instance for
one node: the execution layer's entry point, where the framework's events meet the store
and the recovery machinery of `Spec/Defs/Recovery.lean`.

What the framework supplies, and what this file owes it (from
`StsMultisetLog/Spec/Protocol.lean`, read 2026-08-16): a protocol reacts to events and to
nothing else — `tick` (its own clock advanced), `recv m` (a message delivered, already in
the view), `wake`, and `custom` events of its own choosing. The instance owes four fields:
`init`, a relational `step`, `total` (a reaction always exists — Event-B's FIS), and
`enabled` for the custom events.

## What the node keeps

`ValidatorState`: the store; Definition 12's durable signing history; the store held at
the previous action cutoff (`storeAtPrevSGFGVote` — Definition 30's activation filter and
Definition 31's aging witnesses both key on `a_{r−1}`); the received attestations, raw
Goldfish votes and proposals (the pools the schedule's snapshots read — the healing store's evidence
retention, played by the validator so the grade views are locally computable); the
previous round's accepted proposal block (Definition 47's source); the pre-round `X⁻`
snapshot; and the current round's records, `RoundState`.

## What the node does at each reading (Definition 28's schedule)

* `recv` — a block folds into the store through `receive`; an attestation, raw vote or
  proposal is filed in its pool and the store is untouched.
* `t = d_r` — derive the selection state `Σ_sel` under the activation filter, snapshot
  `X⁰`, open the round's records. The proposer branch (Figure 5, `alg:recovery-action`,
  steps 5–7)
  is not rendered — block production is outside what this project has modelled — so
  proposals only arrive as messages.
* `t = d_r + Δ` — snapshot `X¹`; run Definition 43's recognition wrapper over the received
  proposals (`ProposerSelection` picks the local winner; two distinct signed round
  proposals from its signer discard both); merge an accepted proposal's carried view;
  derive `Σ_vote`; fix the lower root (Definition 40) and the stable root (Definition 41);
  cast the first slot's raw Goldfish vote (Definition 45) from that root in the aged tree
  with the proposal-path exemption, if this validator is in the slot's committee.
* `t = d_r + 2Δ` — snapshot `X²` (the grade-0 view), freeze the first slot's support view
  `V⁻` (Definition 38), and record the finalized evidence processed by the freeze, which
  Definition 46's veto reads.
* slot-view freezes (`+3Δ` of each slot) — snapshot the frozen slot view the next vote
  merges into.
* later slot boundaries — Definition 29's re-derivation of an ungraded (or
  grade-deactivated) stable root.
* later vote phases — ordinary Goldfish with the round's fixed root on the current
  candidate tree (Definition 32's walk-standing; Remark 10, `rem:aged-scope`).
* `t = a_r` — the round's SG/FG action: `castSGFGVote` (Definitions 42, 46, 47 and 50
  assembled), the history updated before the send; then this store becomes the next
  round's activation cutoff `storeAtPrevSGFGVote`, and the round's accepted proposal
  becomes the next action's source.
* `t = d_{r+1} − Δ` — the `X⁻` snapshot for the next round, taken as a pre-update so it
  composes with whatever phase this reading also is.

## Deviations, all from the same cause

The store records no receipt times, so the paper's strict-receipt refinements collapse to
pool membership at the reading: Definition 28's strict selection cutoff (the boundary
exception), Definition 41's timeliness test, and Definition 51's retransmission policy
are not separately representable. Each is noted where it would bite. Everything a
validator has received by a tick is in its pools at that tick; nothing else is.
## Glossary: the paper's symbols in this module

| Paper | Here | Meaning |
| --- | --- | --- |
| `d_r` | `Rounds.start r` | round `r`'s first proposal time |
| `Δ` | `Rounds.Δ` | the network-delivery bound |
| `a_r` | `Rounds.SGFGVotingTime r` | the round's SG/FG action time, `d_r + 6Δ` |
| `X_u^-` | `attsAtRoundStartMinusΔ` | SG-grade snapshot at `d_r − Δ` |
| `X_u^0` | `attsAtRoundStart` | SG-grade snapshot at `d_r` |
| `X_u^1` | `attsAtRoundStartPlusΔ` | SG-grade snapshot at `d_r + Δ` |
| `X_u^2` | `attsAtRoundStartPlus2Δ` | SG-grade snapshot at `d_r + 2Δ`, the grade-0 view |
| `V_u^-` | `votesAtSupportFreeze` | the first slot's support-freeze view |
| `Σ_{u,sel}^r` | `selSnap` | the selection state |
| `Σ_{u,vote}^r` | `voteSnap` | the vote state |
| `Σ_{u,act}^r` | `filteredStoreAtSGFGVote` | the action state, derived at the `castSGFGVote` call |
| `R` (Fig. 2) | `Store.walkStartFromFGVotes` | the walk-from block; the paper's Simplex root |
| `R_{u,vote}^r` | `goldfishWalkStart` | the vote-time stable walk-start — Definition 41 |
| `C⁻_u(Σ)` | `candidateTreeBackedByPrevSGFGVote` | the aged candidate tree — Definition 31 |
| `H_i` | `hist` | the durable signing history |

The convention is `CLAUDE.md`'s: a symbol may become a word; the docstring opens with the
symbol; a word the paper defines keeps its name. Rows still showing a symbolic name are
renames not yet made.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type}

/-- One round's records, fixed by the schedule's snapshots and read by the later phases.
    All fields start empty at the round's opening except the frozen slot view, which
    persists across the boundary — the receipt buffer is not merged before a freeze
    (Definition 28, `def:recovery-timing`, lines 208–220). -/
structure RoundState (Node Root : Type) where
  /-- The round number these records belong to. -/
  r : Nat
  /-- `X_u^-`, the SG-grade snapshot at `d_r − Δ` (Definition 28, `def:recovery-timing`,
      lines 180–186): the whole received pool, cut to the preceding round's SG-head batch
      by its readers (`eligibleBatch`). Feeds `G3`, with `X_u^1`. -/
  attsAtRoundStartMinusΔ : Finset (Attestation Node Root)
  /-- `X_u^0`, the SG-grade snapshot at `d_r`, the round's start. Feeds `G2`. -/
  attsAtRoundStart : Finset (Attestation Node Root)
  /-- `X_u^1`, the SG-grade snapshot at `d_r + Δ`, the first slot's vote time. Feeds `G1`,
      and `G3`'s equivocation cross-check. -/
  attsAtRoundStartPlusΔ : Finset (Attestation Node Root)
  /-- `X_u^2`, the SG-grade snapshot at `d_r + 2Δ` — the grade-0 view. Feeds `G0`. -/
  attsAtRoundStartPlus2Δ : Finset (Attestation Node Root)
  /-- `Σ_{u,sel}^r`, the selection state (activation-filtered). -/
  selSnap : Store Node Root
  /-- `Σ_{u,vote}^r`, the vote state (activation-filtered, after the proposal merge). -/
  voteSnap : Store Node Root
  /-- `V_u^-`, the first slot's support-freeze view (Definition 38, `f_r = d_r + 2Δ`). -/
  votesAtSupportFreeze : Finset (GoldfishVote Node Root)
  /-- The current frozen slot view, snapshotted at each slot-view freeze (`+3Δ`). -/
  frozen : Finset (GoldfishVote Node Root)
  /-- `R_{u,vote}^r`, the paper's "stable root", named here for its primary consumer: the
      round's Goldfish walks start from it. Fixed at the vote time (Definition 41),
      re-derived at slot boundaries when Definition 29 says so; the SG/FG vote reuses it
      through Definition 42's admission rather than deriving its own. The dual text is at
      `goldfishWalkStart`'s definition in `Spec/Defs/Recovery.lean`. -/
  goldfishWalkStart : Blk Node Root
  /-- The root's classification for Definition 29: `false` exactly when it is the vote
      state's own Simplex selection. -/
  graded : Bool
  /-- The accepted distinguished proposal, `none` on every failure path. -/
  acceptedProposal : Option (RecoveryProposal Node Root)
  /-- The finalized roots whose evidence was processed by the grade-0 freeze — what
      Definition 46's veto counts. -/
  processedFinalizedAtFreeze : Finset (Blk Node Root)

/-- What one validator keeps. See the module header for each field's role. -/
structure ValidatorState (Node Root : Type) where
  /-- The fork-choice store. -/
  store : Store Node Root
  /-- The durable signing history `H_i` (Definition 12, `def:signing-history`). -/
  hist : SigningHistory Node Root
  /-- The store held at the previous action cutoff `a_{r−1}` — Definition 30's activation
      filter and Definition 31's aging witnesses. Genesis before the first action, which
      is Definition 30's base case at the relay point. -/
  storeAtPrevSGFGVote : Store Node Root
  /-- Every attestation received (or signed) so far — the grade snapshots read this. -/
  atts : Finset (Attestation Node Root)
  /-- Every raw Goldfish vote received (or cast) so far — the TSQ views read this. -/
  gvotes : Finset (GoldfishVote Node Root)
  /-- Every round proposal received so far. -/
  proposals : Finset (RecoveryProposal Node Root)
  /-- The previous round's accepted proposal block — Definition 47's source proposal for
      the current action. -/
  prevRoundProposal : Option (Blk Node Root)
  /-- `X_u^-` for the round about to open, staged at `d_{r+1} − Δ`; it lands in
      `attsAtRoundStartMinusΔ` when the round's records are built. -/
  nextAttsAtRoundStartMinusΔ : Finset (Attestation Node Root)
  /-- The current round's records. -/
  round : RoundState Node Root

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root] [Omega Node Root] [Rounds] [Committees Node]
  [ProposerSelection Node Root]

/-- One node's reaction to one event: the schedule of Definition 28, phase by phase — see
    the module header for the map. The exact-time phases are tested first; the modular
    phases (slot-view freeze, slot boundary, later votes) after them, so each reading
    runs exactly one phase, except the pre-round `X⁻` snapshot, which is a pre-update
    composing with whatever else its reading is. -/
def reaction (i : Node) (t : Time) (st : ValidatorState Node Root)
    (e : Event Node (StoreMsg Node Root) Empty) :
    NodeStepResult (ValidatorState Node Root) (StoreMsg Node Root) :=
  match e with
  | .recv m =>
      let st := { st with store := receive st.store m.msg }
      match m.msg with
      | .block _ => { state := st, send := ∅ }
      | .attestation a => { state := { st with atts := insert a st.atts }, send := ∅ }
      | .gVote v => { state := { st with gvotes := insert v st.gvotes }, send := ∅ }
      | .proposal p => { state := { st with proposals := insert p st.proposals }, send := ∅ }
  | .tick =>
      match Rounds.roundAt t with
      | some r =>
          let roundStart := Rounds.start r
          let Δ := Rounds.Δ
          -- the X⁻ snapshot for round r + 1, one bound before its proposal time
          -- (Definition 28, `def:recovery-timing`, lines 180–186); a pre-update,
          -- because its reading may also
          -- be a freeze, boundary or vote phase of the current round
          let st := if t + Δ = Rounds.start (r + 1)
            then { st with nextAttsAtRoundStartMinusΔ := st.atts } else st
          if t = roundStart then
            -- the round opens: Σ_sel under the activation filter (Definition 30), the
            -- X⁰ snapshot, fresh records. The proposer branch (`alg:recovery-action`
            -- lines 5–7) is not rendered — module header. The strict selection cutoff
            -- (Definition 28's boundary exception) is the pool at this reading.
            let sel := st.store.withJustificationAndFinalityFrom st.storeAtPrevSGFGVote
            { state := { st with round :=
                { r := r,
                  attsAtRoundStartMinusΔ := st.nextAttsAtRoundStartMinusΔ,
                  attsAtRoundStart := st.atts,
                  selSnap := sel,
                  voteSnap := sel,
                  attsAtRoundStartPlusΔ := ∅,
                  attsAtRoundStartPlus2Δ := ∅,
                  votesAtSupportFreeze := ∅,
                  frozen := st.round.frozen,
                  goldfishWalkStart := sel.walkStartFromFGVotes,
                  graded := false,
                  acceptedProposal := none,
                  processedFinalizedAtFreeze := ∅ } },
              send := ∅ }
          else if t = roundStart + Δ then
            -- the first slot's vote time (Figure 5, `alg:recovery-action`, steps 8–12)
            let attsAtRoundStartPlusΔ := st.atts
            -- Definition 31's aging witnesses
            let treeAtPrevSGFGVote := st.storeAtPrevSGFGVote.T
            -- Definition 43's wrapper: the locally winning well-formed proposal,
            -- discarded when its signer has two distinct round proposals in this view;
            -- timeliness is pool membership at this reading (module header)
            let cands := st.proposals.filter fun p => p.wellFormed r
            let prop :=
              match ProposerSelection.winner cands with
              | some p =>
                  if ∃ p' ∈ cands, p'.proposer = p.proposer ∧ p' ≠ p then none
                  else some p
              | none => none
            -- "merge only the accepted proposal's ordinary Goldfish view": the proposal
            -- block's own ancestry, parent-first, through on_block, and its carried
            -- votes; other carried blocks re-arrive as ordinary messages under honest
            -- relay, so nothing else is folded here
            let store' :=
              match prop with
              | some p => ((ancestors p.block).reverse).foldl onBlock st.store
              | none => st.store
            let gv' := match prop with
              | some p => st.gvotes ∪ p.carriedGoldfishVotes
              | none => st.gvotes
            let Svote := store'.withJustificationAndFinalityFrom st.storeAtPrevSGFGVote
            let pf := processedFinalized store'
            -- `L_u^r`, Definition 40
            let lowerWalkStart := lowerWalkStart st.round.selSnap Svote treeAtPrevSGFGVote
              st.round.attsAtRoundStartMinusΔ attsAtRoundStartPlusΔ r pf
            let vr := goldfishWalkStart Svote treeAtPrevSGFGVote lowerWalkStart
              attsAtRoundStartPlusΔ r pf prop
            -- Definition 45: the frozen slot view merged with the carried view, the
            -- preceding vote phase's votes counted, the walk in the aged tree with the
            -- proposal-path exemption
            let view := match prop with
              | some p => st.round.frozen ∪ p.carriedGoldfishVotes
              | none => st.round.frozen
            let counted := view.filter fun v => v.slot + 4 * Δ = t
            let tree := candidateTreeBackedByPrevSGFGVoteOrOnProposalPath Svote treeAtPrevSGFGVote
              (vr.acceptedProposal.map fun p => p.block)
            let st' := { st with
              store := store', gvotes := gv',
              round := { st.round with
                attsAtRoundStartPlusΔ := attsAtRoundStartPlusΔ, voteSnap := Svote,
                goldfishWalkStart := vr.walkStart,
                graded := vr.graded, acceptedProposal := vr.acceptedProposal } }
            if i ∈ Committees.committee t then
              let v := recoveryGoldfishVote i t counted tree vr.walkStart
              { state := { st' with gvotes := insert v st'.gvotes },
                send := {.gVote v} }
            else { state := st', send := ∅ }
          else if t = roundStart + 2 * Δ then
            -- the grade-0 freeze and the support freeze (Definition 28,
            -- `def:recovery-timing`, line 187; Definition 38, `def:tsq-views`): X², V⁻,
            -- and the finalized evidence processed by the freeze, which Definition 46's
            -- veto counts
            { state := { st with round := { st.round with
                attsAtRoundStartPlus2Δ := st.atts, votesAtSupportFreeze := st.gvotes,
                processedFinalizedAtFreeze := processedFinalized st.store } },
              send := ∅ }
          else if t = Rounds.SGFGVotingTime r then
            -- the round's SG/FG action (Figure 5, `alg:recovery-action`, steps 15–21)
            let (a, H') := castSGFGVote
              (i := i) (r := r) (t := t)
              (filteredStoreAtSGFGVote :=
                st.store.withJustificationAndFinalityFrom st.storeAtPrevSGFGVote)
              (latestGoldfishWalkStart := st.round.goldfishWalkStart)
              (acceptedProposal := st.round.acceptedProposal)
              (prevRoundProposal := st.prevRoundProposal)
              (committee := Committees.committee (roundStart + Δ))
              (firstSlotVoteTime := roundStart + Δ)
              (votesAtSupportFreeze := st.round.votesAtSupportFreeze)
              (votesAtSGFGVote := st.gvotes) -- V⁺: every delivery due by a_r is processed
              (attsAtRoundStartPlusΔ := st.round.attsAtRoundStartPlusΔ)
              (attsAtRoundStartPlus2Δ := st.round.attsAtRoundStartPlus2Δ)
              (processedFinalizedAtFreeze := st.round.processedFinalizedAtFreeze)
              (processedFinalizedAtSGFGVote := processedFinalized st.store)
              (history := st.hist)
            { state := { st with
                hist := H',
                atts := insert a st.atts,  -- its own head is in its own later views
                storeAtPrevSGFGVote := st.store,          -- the next round's activation cutoff
                prevRoundProposal := st.round.acceptedProposal.map fun p => p.block
              },
              send := {.attestation a} }
          else if (t - roundStart) % (4 * Δ) = 3 * Δ then
            -- a slot-view freeze (Definition 28, `def:recovery-timing`, lines 171–177)
            { state := { st with round := { st.round with frozen := st.gvotes } },
              send := ∅ }
          else if (t - roundStart) % (4 * Δ) = 0 then
            -- a later slot boundary (t = roundStart was caught above): Definition 29's
            -- re-derivation
            let cur := st.store.withJustificationAndFinalityFrom st.storeAtPrevSGFGVote
            let (walkStart', g') := rederive cur (processedFinalized st.store)
              st.round.goldfishWalkStart st.round.graded
            { state := { st with round :=
                { st.round with goldfishWalkStart := walkStart', graded := g' } },
              send := ∅ }
          else if Rounds.isGoldfishVoteTime r t then
            -- a later slot's vote (Definition 28, `def:recovery-timing`,
            -- lines 190–192): ordinary Goldfish with the round's fixed root on the
            -- current candidate tree (Definition 32, `def:walk-standing`; Remark 10,
            -- `rem:aged-scope`)
            if i ∈ Committees.committee t then
              let cur := st.store.withJustificationAndFinalityFrom st.storeAtPrevSGFGVote
              let counted := st.round.frozen.filter fun v => v.slot + 4 * Δ = t
              let v := recoveryGoldfishVote i t counted (candidateTree cur)
                st.round.goldfishWalkStart
              { state := { st with gvotes := insert v st.gvotes }, send := {.gVote v} }
            else { state := st, send := ∅ }
          else { state := st, send := ∅ }
      | none => { state := st, send := ∅ }
  | .wake => { state := st, send := ∅ }
  | .custom ev => ev.elim

/-- The node protocol: state is `ValidatorState`, behaviour is `reaction`, lifted into
    the framework's relational `step` as its documentation prescribes for a deterministic
    protocol. -/
def protocol : Protocol Node (StoreMsg Node Root) (ValidatorState Node Root) Empty where
  init _ :=
    { store := Store.gen, hist := .gen, storeAtPrevSGFGVote := Store.gen,
      atts := ∅, gvotes := ∅, proposals := ∅, prevRoundProposal := none,
      nextAttsAtRoundStartMinusΔ := ∅,
      round := { r := 0, attsAtRoundStartMinusΔ := ∅, attsAtRoundStart := ∅,
                 attsAtRoundStartPlusΔ := ∅, attsAtRoundStartPlus2Δ := ∅,
                 selSnap := Store.gen, voteSnap := Store.gen, votesAtSupportFreeze := ∅,
                 frozen := ∅,
                 goldfishWalkStart := .genesis, graded := false, acceptedProposal := none,
                 processedFinalizedAtFreeze := ∅ } }
  step i t _ st e res := res = reaction i t st e
  total i t _ st e := ⟨reaction i t st e, rfl⟩
  enabled _ _ ev := ev.elim

end

end Decoupled
