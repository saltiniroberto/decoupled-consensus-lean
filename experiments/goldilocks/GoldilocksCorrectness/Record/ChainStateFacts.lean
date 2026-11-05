module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateDefs

@[expose] public section

/-!
# The facts of the chain state of a block

`ChainStateFacts M` holds, for a model `M`, what the chain state of a block, `M.chainStateOf C B`,
guarantees: each field is a theorem of the library about the spec's chain states, with the model's
members in place of the spec's (`M.chainStateOf C B`, `σ.h` for `M.cs_h σ`, `M.valid_attestation`,
`M.on_chain`, `M.quorumAt B` for the count that advances a chain state on the block `B`). Each
library theorem over the state transition from the chain state `σ` of a block's parent,
`state_transition C σ B`, is a field about a block `B` that is not the genesis block: the state
transition is the chain state of `B`, `M.chainStateOf C B`, and `σ` is the chain state of its
parent, `M.chainStateOf C B.parent`. The certificates of Lemmas 66 and 67 (b) are the record's
(`JustificationCertOn M`, `ProgressCertOn M`, `FinalityCertOn M`): a set of validators reaching
the quorum at some block `X`, `B` or an ancestor of `B`, with its votes included on `X`'s chain.
Four fields are written for the record: the defining equations of the readers `newest` and
`is_pending`, the last pending pair named by its readers, and the readers of the genesis block's
chain state. A theorem of the family whose proof only combines these is not a field: it is
restated over the record on the pages of `Record/Restated/`.
-/

set_option autoImplicit false
-- the hypotheses of the fields are named, as in the theorems the fields restate
set_option linter.unusedVariables false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Block Attestation FinalityPair Height Slot BlockId)
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry JustificationCertOn ProgressCertOn
  FinalityCertOn)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the chain state of a block, `M.chainStateOf C B`.

Read aloud: the model `M`'s chain states of blocks behave as the spec's do in every way the
proofs use. -/
structure ChainStateFacts (M : GoldilocksModel V) : Prop where
  /-- The landed `GoldilocksCorrectness.Proofs.Routines.lem47a_state_transition_bounds`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:267`),
      over the chain state of a block `B` that is not the genesis block: the landed
      `state_transition C σ B` is `M.chainStateOf C B`, and the parent's chain state `σ` is
      `M.chainStateOf C B.parent`.

      Read aloud: along a block, the justification height stays less than the height, the
      finalization height stays at most the justification height, and every pending
      justification stays at a height at most the justification height. -/
  lem47a_state_transition_bounds : ∀ (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    (hj : (M.chainStateOf C B.parent).h_j < (M.chainStateOf C B.parent).h)
        (hF : (M.chainStateOf C B.parent).h_F ≤ (M.chainStateOf C B.parent).h_j)
    (hpend : ∀ e ∈ (M.chainStateOf C B.parent).pending_finality,
        e.j ≤ (M.chainStateOf C B.parent).h_j),
      1 ≤ (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_j < (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B).h_j ∧
      ∀ e ∈ (M.chainStateOf C B).pending_finality, e.j ≤ (M.chainStateOf C B).h_j

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.lem47b_state_transition_height`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:297`),
      over the chain state of a block `B` that is not the genesis block: the landed
      `state_transition C σ B` is `M.chainStateOf C B`, and the parent's chain state `σ` is
      `M.chainStateOf C B.parent`.

      Read aloud: a block's height is its parent's, or one more. -/
  lem47b_state_transition_height : ∀ (C : Config) (B : Block V) (hB : B ≠ Block.genesis),
      (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∨
          (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.lem47c_state_transition_T_h`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:310`),
      over the chain state of a block `B` that is not the genesis block: the landed
      `state_transition C σ B` is `M.chainStateOf C B`, and the parent's chain state `σ` is
      `M.chainStateOf C B.parent`.

      Read aloud: `T_h` changes exactly when the height does, and then to the block that raised
      it. -/
  lem47c_state_transition_T_h : ∀ (C : Config) (B : Block V) (hB : B ≠ Block.genesis),
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h →
          (M.chainStateOf C B).T_h = (M.chainStateOf C B.parent).T_h) ∧
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 → (M.chainStateOf C B).T_h = B)

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.state_transition_justification`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:324`),
      over the chain state of a block `B` that is not the genesis block: the landed
      `state_transition C σ B` is `M.chainStateOf C B`, and the parent's chain state `σ` is
      `M.chainStateOf C B.parent`.

      Read aloud: a block keeps its parent's justification, or justifies its parent's `T_h` at its
      parent's height. -/
  state_transition_justification : ∀ (C : Config) (B : Block V) (hB : B ≠ Block.genesis),
      ((M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h_j ∧
          (M.chainStateOf C B).J = (M.chainStateOf C B.parent).J) ∨
      ((M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h ∧
          (M.chainStateOf C B).J = (M.chainStateOf C B.parent).T_h)

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_height`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:398`).

      Read aloud: a vote for the chain's current height and block may be included. -/
  valid_attestation_of_height : ∀ (σ : M.CS) (a : Attestation V)
    (hh : a.h = σ.h) (hT : a.T = σ.T_h.root),
      M.valid_attestation σ a = true

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.state_transition_h_F_mono`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:553`),
      over the chain state of a block `B` that is not the genesis block: the landed
      `state_transition C σ B` is `M.chainStateOf C B`, and the parent's chain state `σ` is
      `M.chainStateOf C B.parent`.

      Read aloud: when every pending justification is higher than the finalization, a block's
      finalization height is at least its parent's. -/
  state_transition_h_F_mono : ∀ (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    -- every pending justification of the parent is at a height greater than its finalization
    -- height
    (habove : ∀ e ∈ (M.chainStateOf C B.parent).pending_finality,
        (M.chainStateOf C B.parent).h_F < e.j),
      (M.chainStateOf C B.parent).h_F ≤ (M.chainStateOf C B).h_F

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.quorum_certificate_with_counted`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:594`),
      over the chain state of a block `B` that is not the genesis block: the landed
      `state_transition C σ B` is `M.chainStateOf C B`, and the parent's chain state `σ` is
      `M.chainStateOf C B.parent`.

      Read aloud: a quorum counted in the parent or voting in the block is a certificate. -/
  quorum_certificate_with_counted : ∀ (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    (Q : Finset V)
    (hQ : M.quorumAt B ≤ Q.card)
    (hAtts : ∀ v ∈ Q, v ∈ (M.chainStateOf C B.parent).progress ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = (M.chainStateOf C B.parent).h ∧
        a.T = (M.chainStateOf C B.parent).T_h.root),
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 ∨
        ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∧
            Q ⊆ (M.chainStateOf C B).progress ∧
          B.slot < (M.chainStateOf C B.parent).T_h.slot + C.δt)) ∧
      ((∀ v ∈ Q, v ∈ (M.chainStateOf C B.parent).target_participation ∨
          ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = (M.chainStateOf C B.parent).h ∧
            a.T = (M.chainStateOf C B.parent).T_h.root ∧
            a.τ = false) →
        (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 ∧
            (M.chainStateOf C B).J = (M.chainStateOf C B.parent).T_h ∧
          (M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h)

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.valid_attestation_cases`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:639`).

      Read aloud: an attestation a chain state accepts votes for its current height and block, or
      is at a lesser height. -/
  valid_attestation_cases : ∀ (σ : M.CS) (a : Attestation V)
    (h : M.valid_attestation σ a = true),
      (a.h = σ.h ∧ a.T = σ.T_h.root) ∨ a.h < σ.h

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_pending`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainState.lean:684`).

      Read aloud: an attestation finalizing a pending justification, at a height between the
      pair's and the chain's, is accepted. -/
  valid_attestation_of_pending : ∀ (σ : M.CS) (a : Attestation V) (p : FinalityPair)
    (hp : a.finality_pair = some p) (hpend : M.is_pending σ p = true) (h1 : p.hf < a.h)
    (h2 : a.h < σ.h),
      M.valid_attestation σ a = true

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_bounds`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean:66`).

      Read aloud: every chain state has height at least `1`, justification height less than its
      height, finalization height at most its justification height, and every pending
      justification at most its justification height. -/
  chainStateOf_bounds : ∀ (C : Config) (B : Block V),
      1 ≤ (M.chainStateOf C B).h ∧ (M.chainStateOf C B).h_j < (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B).h_j ∧
      ∀ e ∈ (M.chainStateOf C B).pending_finality, e.j ≤ (M.chainStateOf C B).h_j

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_pending_above`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean:284`).

      Read aloud: every pending justification of a block's chain state is higher than its
      finalization. -/
  chainStateOf_pending_above : ∀ (C : Config) (B : Block V),
      ∀ e ∈ (M.chainStateOf C B).pending_finality, (M.chainStateOf C B).h_F < e.j

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.counted_kept_of_same_height`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean:344`).

      Read aloud: along a chain at one height, the counted validators are kept. -/
  counted_kept_of_same_height : ∀ (C : Config) {Y D : Block V} (hYD : Y.AncestorEq D)
    (hh : (M.chainStateOf C Y).h = (M.chainStateOf C D).h),
      (M.chainStateOf C Y).progress ⊆ (M.chainStateOf C D).progress ∧
      (M.chainStateOf C Y).target_participation ⊆ (M.chainStateOf C D).target_participation

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_h`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean:598`).

      Read aloud: the genesis block's chain is at the height one. -/
  chainStateOf_genesis_h : ∀ (C : Config),
      (M.chainStateOf C (Block.genesis : Block V)).h = 1

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_T_h`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean:608`).

      Read aloud: the genesis block's chain entered its height at the genesis block. -/
  chainStateOf_genesis_T_h : ∀ (C : Config),
      (M.chainStateOf C (Block.genesis : Block V)).T_h = Block.genesis

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_J`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean:620`).

      Read aloud: the genesis block's chain has the genesis block justified, at the height zero. -/
  chainStateOf_genesis_J : ∀ (C : Config),
      (M.chainStateOf C (Block.genesis : Block V)).J = Block.genesis ∧
      (M.chainStateOf C (Block.genesis : Block V)).h_j = 0

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.pending_pair_step`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateCertified.lean:62`),
      over the chain state of a block `B` that is not the genesis block: the landed
      `state_transition C σ B` is `M.chainStateOf C B`, and the parent's chain state `σ` is
      `M.chainStateOf C B.parent`.

      Read aloud: one block either finalizes at least the pending pair's height, or keeps the pair
      pending, keeps its counted validators, and counts the block's finality pairs for
      it. -/
  pending_pair_step : ∀ (C : Config) (B : Block V) (hB : B ≠ Block.genesis) (e₀ : M.PP)
    (h : Height)
    (hshape : ∃ l₁ l₂ : List (M.PP), (M.chainStateOf C B.parent).pending_finality = l₁ ++ e₀ :: l₂ ∧
      (l₂ = [] ∨ (l₂.length = 1 ∧ h + 1 ≤ (M.chainStateOf C B.parent).h)))
    (hj₀ : e₀.j < h) (hh : h ≤ (M.chainStateOf C B.parent).h)
    (hJ : (M.chainStateOf C B).h_j ≤ h),
      e₀.j ≤ (M.chainStateOf C B).h_F ∨
      ((∃ l₁ l₂ : List (M.PP), (M.chainStateOf C B).pending_finality = l₁ ++ e₀ :: l₂ ∧
        (l₂ = [] ∨ (l₂.length = 1 ∧ h + 1 ≤ (M.chainStateOf C B).h))) ∧
      (∀ v ∈ (M.chainStateOf C B.parent).finality_participation e₀.j,
        v ∈ (M.chainStateOf C B).finality_participation e₀.j) ∧
      (∀ a ∈ B.attestations, a.finality_pair = some (FinalityPair.mk e₀.j e₀.T.root) →
        a.val_index ∈ (M.chainStateOf C B).finality_participation e₀.j))

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.first_advance_justified_or_timeout`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateCertified.lean:172`).

      Read aloud: the first block past the height `h` on a chain was raised by a justification at
      `h`, or by a timeout. -/
  first_advance_justified_or_timeout : ∀ (C : Config) (B : Block V) (h : Height)
    (h1 : 1 ≤ h) (hlt : h < (M.chainStateOf C B).h),
      ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (M.chainStateOf C Y.parent).h = h ∧ (M.chainStateOf C Y).h = h + 1 ∧
      ((M.chainStateOf C Y).h_j = h ∨ (M.chainStateOf C Y.parent).T_h.slot + C.δt ≤ Y.slot)

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.justification_witness_of_finalized`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/Certificates.lean:482`).

      Read aloud: a chain that finalized `F` at `h_F` passed through a state that had just
      justified `F` at `h_F`. -/
  justification_witness_of_finalized : ∀ (C : Config) (D : Block V)
    -- the finalization height of `D`'s chain state is at least `1`
    (h1 : 1 ≤ (M.chainStateOf C D).h_F),
      ∃ Y : Block V, Y.AncestorEq D ∧ (M.chainStateOf C Y).h_j = (M.chainStateOf C D).h_F ∧
      (M.chainStateOf C Y).J = (M.chainStateOf C D).F

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.lem66_chain_state_certified`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/Certificates.lean:522`).

      Read aloud: the justified block, every pending justification and the finalized block of a
      chain state each have their certificates included on the chain, and each is a
      block of the chain whose own chain state is at the height named. -/
  lem66_chain_state_certified : ∀ (C : Config) (B : Block V),
      (1 ≤ (M.chainStateOf C B).h_j →
        JustificationCertOn M B (M.chainStateOf C B).h_j (M.chainStateOf C B).J ∧
        (M.chainStateOf C B).J.AncestorEq B ∧
        (M.chainStateOf C (M.chainStateOf C B).J).h = (M.chainStateOf C B).h_j) ∧
      (∀ e ∈ (M.chainStateOf C B).pending_finality,
        JustificationCertOn M B e.j e.T ∧ e.T.AncestorEq B ∧ (M.chainStateOf C e.T).h = e.j) ∧
      (1 ≤ (M.chainStateOf C B).h_F →
        JustificationCertOn M B (M.chainStateOf C B).h_F (M.chainStateOf C B).F ∧
        FinalityCertOn M B (M.chainStateOf C B).h_F (M.chainStateOf C B).F ∧
        (M.chainStateOf C B).F.AncestorEq B ∧
        (M.chainStateOf C (M.chainStateOf C B).F).h = (M.chainStateOf C B).h_F)

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.lem67b_first_advance_cases`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/Certificates.lean:685`).

      Read aloud: a height was left by a quorum of targets, or by a progress quorum once the
      timeout had passed. -/
  lem67b_first_advance_cases : ∀ (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (M.chainStateOf C B).h),
      ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (M.chainStateOf C Y.parent).h = h ∧ (M.chainStateOf C Y).h = h + 1 ∧
      (M.chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn M Y h (M.chainStateOf C Y.parent).T_h ∧
      (JustificationCertOn M Y h (M.chainStateOf C Y.parent).T_h ∨
        (M.chainStateOf C Y.parent).T_h.slot + C.δt ≤ Y.slot)

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/Accountable.lean:98`).

      Read aloud: a chain state with finalization height `0` has the genesis block finalized. -/
  chainStateOf_F_genesis : ∀ (C : Config) (B : Block V)
    -- the finalization height of the chain state of `B` is `0`
    (h0 : (M.chainStateOf C B).h_F = 0),
      (M.chainStateOf C B).F = Block.genesis

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.round_justified_of_spacing3`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOfCertified.lean:55`).

      Read aloud: a later block on the chain, within `δt` slots of the entry's slot, has inherited
      the justification at the entry's height. -/
  round_justified_of_spacing3 : ∀ (C : Config) (B B' : Block V)
    (hBB' : B.AncestorEq B') (hh : (M.chainStateOf C B).h + 1 ≤ (M.chainStateOf C B').h)
    (hslot : B'.slot ≤ (M.chainStateOf C B).T_h.slot + C.δt)
    (hanc : ∀ Y : Block V, Y.AncestorEq B' → Y ≠ B' → Y.slot < B'.slot)
    (hJ : (M.chainStateOf C B'.parent).h = (M.chainStateOf C B).h →
      (M.chainStateOf C B').h_j = (M.chainStateOf C B).h ∧
      (M.chainStateOf C B').J = (M.chainStateOf C B).T_h),
      (M.chainStateOf C B).h ≤ (M.chainStateOf C B').h_j

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.lem93_block_finalizes_pending`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/FinalityPair.lean:275`).

      Read aloud: a block that brings a quorum of finality pairs for a pending justification
      finalizes it. -/
  lem93_block_finalizes_pending : ∀ (C : Config) (B H' : Block V) (j : Height) (T : Block V)
    (Q : Finset V)
    (hParent : B.parent = H')
    (hPending : ∃ e ∈ (M.chainStateOf C H').pending_finality, e.j = j ∧ e.T = T)
    (hQ : M.quorumAt B ≤ |Q|)
    (hAtts : ∀ v ∈ Q, v ∈ (M.chainStateOf C H').finality_participation j ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.finality_pair = some (FinalityPair.mk j T.root)),
      j ≤ (M.chainStateOf C B).h_F

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.on_chain_counted`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/FGStateReaders.lean:178`).

      Read aloud: an attestation included on a chain, at the chain's height, is counted in the
      chain state's progress set, and in its target participation when it is a target
      vote. -/
  on_chain_counted : ∀ (C : Config) (H : Block V) (a : Attestation V)
    (hon : M.on_chain a H = true)
    (hValid : ∀ Y : Block V, Y.AncestorEq H → Y ≠ Block.genesis →
      ∀ a' ∈ Y.attestations, M.valid_attestation (M.chainStateOf C Y.parent) a' = true)
    (hh : a.h = (M.chainStateOf C H).h),
      a.val_index ∈ (M.chainStateOf C H).progress ∧
      (a.τ = false → a.val_index ∈ (M.chainStateOf C H).target_participation)

  /-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_pending_last`
      (`experiments/goldilocks/GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean:476`), with
      the pending pair `PendingPair.mk (chainStateOf C X).h_j (chainStateOf C X).J` named by its
      readers: a pair `e` with `e.j` the justification height and `e.T` the justified block.

      Read aloud: when the finalization height of a block's chain state is less than its
      justification height, the last pending pair of that chain state has the justification
      height and the justified block. -/
  chainStateOf_pending_last : ∀ (C : Config) (X : Block V)
    (hlt : (M.chainStateOf C X).h_F < (M.chainStateOf C X).h_j),
      ∃ (l : List M.PP) (e : M.PP), (M.chainStateOf C X).pending_finality = l ++ [e] ∧
        e.j = (M.chainStateOf C X).h_j ∧ e.T = (M.chainStateOf C X).J

  /-- The readers of the genesis block's chain state (the spec's `ChainState.initial`).

      Read aloud: the genesis block's chain state has the genesis block as its latest block, the
      slot `0`, the height `1` entered at the genesis block, nobody counted, nothing pending, the
      genesis block justified at the height `0` and finalized at the height `0`. -/
  cs_initial_eq : ∀ (C : Config),
      (M.chainStateOf C Block.genesis).L = Block.genesis ∧
      (M.chainStateOf C Block.genesis).s = 0 ∧
      (M.chainStateOf C Block.genesis).h = 1 ∧
      (M.chainStateOf C Block.genesis).T_h = Block.genesis ∧
      (M.chainStateOf C Block.genesis).target_participation = ∅ ∧
      (M.chainStateOf C Block.genesis).progress = ∅ ∧
      (M.chainStateOf C Block.genesis).pending_finality = [] ∧
      (∀ j : Height, (M.chainStateOf C Block.genesis).finality_participation j = ∅) ∧
      (M.chainStateOf C Block.genesis).J = Block.genesis ∧
      (M.chainStateOf C Block.genesis).h_j = 0 ∧
      (M.chainStateOf C Block.genesis).F = Block.genesis ∧
      (M.chainStateOf C Block.genesis).h_F = 0

  /-- The definition of the reader `newest` (the spec's `Goldilocks.newest`).

      Read aloud: `newest K_W l` is the last `K_W` elements of `l`, or the whole of `l` when it has
      at most `K_W` elements. -/
  newest_eq : ∀ (K_W : ℕ) (l : List M.PP), M.newest K_W l = l.drop (l.length - K_W)

  /-- The definition of the reader `is_pending` (the spec's `Goldilocks.is_pending`).

      Read aloud: `is_pending σ p` answers whether some pending justification of `σ` is at the
      height `p.hf` and names a block whose root is `p.Tf`. -/
  is_pending_eq : ∀ (σ : M.CS) (p : FinalityPair),
      M.is_pending σ p = decide (∃ e ∈ σ.pending_finality, e.j = p.hf ∧ e.T.root = p.Tf)

end GoldilocksCorrectness.Record
