module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Statements.Routines.ChainStateStatements

@[expose] public section

/-!
# ChainStateStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Routines/ChainStateStatements.lean` over a model
`M` whose facts `F` hold: Lemma 47, the certificate (Lemmas 51 and 51b), and the kit fact
`valid_attestation_of_height`.

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry JustificationCertOn ProgressCertOn FinalityCertOn)
open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedOnChainWith)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 47 (a), the bounds on the heights, over the state transition.** When the parent's
chain state `σ` has its justification height less than its height, its finalization height at
most its justification height, and every pending justification at a height at most its
justification height, so does the chain state of `B`; and its height is at least `1`.

Why: counting the attestations keeps the heights and the pending justifications; the loop over
the pending justifications sets `h_F` to `σ.h_F` or to a pending height, both at most `σ.h_j`; the
justification branch sets `h_j` to `σ.h`, appends a pending justification at `σ.h`, and raises the
height to `σ.h + 1`; the timeout branch raises the height; otherwise the heights stay.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `hB`: `B` is not the genesis block; `σ`, in this text, is `M.chainStateOf C B.parent`, the chain state of `B`'s parent; `B`: the block.

Read aloud: along a block, the justification height stays less than the height, the finalization
height stays at most the justification height, and every pending justification stays at a height
at most the justification height.

 -/
theorem lem47a_state_transition_bounds (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    -- the parent's justification height is less than its height
    (hj : (M.chainStateOf C B.parent).h_j < (M.chainStateOf C B.parent).h)
    -- the parent's finalization height is at most its justification height
    (hF : (M.chainStateOf C B.parent).h_F ≤ (M.chainStateOf C B.parent).h_j)
    -- every pending justification of the parent is at a height at most its justification height
    (hpend : ∀ e ∈ (M.chainStateOf C B.parent).pending_finality,
        e.j ≤ (M.chainStateOf C B.parent).h_j) :
    1 ≤ (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_j < (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B).h_j ∧
      ∀ e ∈ (M.chainStateOf C B).pending_finality, e.j ≤ (M.chainStateOf C B).h_j :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem47a_state_transition_bounds M F) C B hB hj hF hpend

/-- **Lemma 47 (b), the height rises by at most one, over the state transition.** The chain
state of `B` has the parent's height, or the parent's height plus one.

Why: only `advance_height` writes the height, and at most once.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `hB`: `B` is not the genesis block; `σ`, in this text, is `M.chainStateOf C B.parent`, the chain state of `B`'s parent; `B`: the block.

Read aloud: a block's height is its parent's, or one more.

 -/
theorem lem47b_state_transition_height (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∨
        (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem47b_state_transition_height M F) C B hB

/-- **Lemma 47 (c), the block that took the chain into its height, over the state transition.**
When the chain state of `B` keeps the parent's height, it keeps the parent's `T_h`; when it
raises the height by one, its `T_h` is `B`.

Why: counting the attestations makes `B` the latest block; `advance_height` writes `T_h` from the
latest block; otherwise `T_h` is kept.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `hB`: `B` is not the genesis block; `σ`, in this text, is `M.chainStateOf C B.parent`, the chain state of `B`'s parent; `B`: the block.

Read aloud: `T_h` changes exactly when the height does, and then to the block that raised it.

 -/
theorem lem47c_state_transition_T_h (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h →
        (M.chainStateOf C B).T_h = (M.chainStateOf C B.parent).T_h) ∧
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 → (M.chainStateOf C B).T_h = B) :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem47c_state_transition_T_h M F) C B hB

/-- **Lemma 51, a quorum of votes at the parent's height is a certificate.** When the block `B`
includes, for every member of a quorum `Q`, an attestation of that member at the parent's height
`σ.h` naming `σ.T_h`, the chain state of `B` has the height `σ.h + 1`, or keeps `σ.h` with `Q`
counted in its progress set and `B`'s slot less than `δt` slots after `σ.T_h`'s; and when every
one of those attestations is a target, the chain state of `B` has the height `σ.h + 1`, the
justified block `σ.T_h` and the justification height `σ.h`.

Why: counting the attestations keeps `σ.h` and `σ.T_h` and adds each member of `Q` to the
progress set, and to the target participation when its attestation is a target; then the
justification branch runs when the targets are a quorum, else the timeout branch when the
progress set is a quorum and the slot condition holds; when neither, the height stays, and the
slot condition is what failed.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `hB`: `B` is not the genesis block; `σ`, in this text, is `M.chainStateOf C B.parent`, the chain state of `B`'s parent; `B`: the block;
- `Q`: the validators whose attestations `B` includes.

Read aloud: a quorum of votes for `(σ.h, σ.T_h)` in one block is a certificate: targets justify
`σ.T_h` and raise the height; mixed votes fill the progress set and raise the height once the
block's slot is `δt` past `σ.T_h`'s.

 -/
theorem lem51_quorum_is_certificate (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    (Q : Finset V)
    -- `Q` is a quorum
    (hQ : M.quorumAt B ≤ Q.card)
    -- `B` includes, for every member of `Q`, an attestation of it at the height `(M.chainStateOf C B.parent).h` naming
    -- `(M.chainStateOf C B.parent).T_h`
    (hAtts : ∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧
        a.h = (M.chainStateOf C B.parent).h ∧ a.T = (M.chainStateOf C B.parent).T_h.root) :
    ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 ∨
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∧ Q ⊆ (M.chainStateOf C B).progress ∧
        B.slot < (M.chainStateOf C B.parent).T_h.slot + C.δt)) ∧
    ((∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = (M.chainStateOf C B.parent).h ∧
        a.T = (M.chainStateOf C B.parent).T_h.root ∧
        a.τ = false) →
      (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 ∧
          (M.chainStateOf C B).J = (M.chainStateOf C B.parent).T_h ∧
        (M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h) :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem51_quorum_is_certificate M F) C B hB Q hQ hAtts

/-- **Lemma 51b, the progress quorum advances the height at the timeout slot.** When the parent's
chain state has a quorum in its progress set and `B`'s slot is at least `δt` slots after
`σ.T_h`'s, the chain state of `B` has the height `σ.h + 1`, whatever `B` includes.

Why: counting the attestations only adds to the progress set, and keeps `σ.T_h`; then either the
justification branch or the timeout branch raises the height.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `hB`: `B` is not the genesis block; `σ`, in this text, is `M.chainStateOf C B.parent`, the chain state of `B`'s parent; `B`: the block.

Read aloud: once a progress quorum is on chain, the first block of a late enough slot raises the
height, honest or not.

 -/
theorem lem51b_progress_quorum_advances (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    -- the parent's progress set is a quorum
    (hQ : M.quorumAt B ≤ (M.chainStateOf C B.parent).progress.card)
    -- `B`'s slot is at least `δt` slots after the slot of `(M.chainStateOf C B.parent).T_h`
    (hSlot : (M.chainStateOf C B.parent).T_h.slot + C.δt ≤ B.slot) :
    (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem51b_progress_quorum_advances M F) C B hB hQ hSlot

/-- **Kit fact, an attestation at the parent's height naming its `T_h` is valid.** An attestation
at the height `σ.h` naming `σ.T_h` is valid against the chain state `σ`.

Why: the first case of `valid_attestation`.

The variables:
- `M`: the model; `F`: its facts;
- `σ`: the chain state; `a`: the attestation.

Read aloud: a vote for the chain's current height and block may be included.

 -/
theorem valid_attestation_of_height (σ : M.CS) (a : Attestation V)
    -- `a` is at the height `σ.h`
    (hh : a.h = σ.h)
    -- `a` names `σ.T_h`
    (hT : a.T = σ.T_h.root) :
    M.valid_attestation σ a = true :=
  (GoldilocksCorrectness.Record.Proofs.Routines.valid_attestation_of_height M F) σ a hh hT

/-- **Lemma 47, the chain-state facts.** For the chain states `chainStateOf C B` and
`chainStateOf C D`:
(a) the height is at least `1`, the justification height is less than the height, and the
finalization height is at most the justification height;
(b) a non-genesis block's height is its parent's or its parent's plus one;
(c) a non-genesis block that keeps its parent's height keeps its parent's `T_h`, and a block that
raises the height has itself as `T_h`;
(d) when `B` is an ancestor of `D` or `D` itself, `B`'s height is at most `D`'s;
(e) when moreover the two heights are equal, the two `T_h` are equal.

Why: `chainStateOf` is the state transition from the parent's chain state, so (a) to (c) are
Lemma 47 (a) to (c) over the state transition, (a) by induction on the block from the genesis
block's chain state (height `1`, justification and finalization heights `0`, nothing pending);
(d) and (e) are inductions on the ancestry from `D` down to `B`, over (b) and (c).

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`, `D`: the blocks.

Read aloud: along a chain the height rises by at most one per block, `T_h` changes exactly when
the height does, and two blocks of one chain at the same height have the same `T_h`.

 -/
theorem lem47_chain_state_heights (C : Config) (B D : Block V) :
    (1 ≤ (M.chainStateOf C B).h ∧ (M.chainStateOf C B).h_j < (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B).h_j) ∧
    (B ≠ Block.genesis →
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∨
        (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1)) ∧
    (B ≠ Block.genesis →
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h →
        (M.chainStateOf C B).T_h = (M.chainStateOf C B.parent).T_h) ∧
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 → (M.chainStateOf C B).T_h = B)) ∧
    (B.AncestorEq D → (M.chainStateOf C B).h ≤ (M.chainStateOf C D).h) ∧
    (B.AncestorEq D → (M.chainStateOf C B).h = (M.chainStateOf C D).h →
      (M.chainStateOf C B).T_h = (M.chainStateOf C D).T_h) :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) C B D

/-- **Lemma 47 (f), the justified block is the entry block of its height.** When `D`'s chain state
has the justification height `H` and `1 ≤ H`, some block `Y` that is an ancestor of `D` or `D`
itself has the height `H`, and `Y`'s `T_h` is the justified block of `D`'s chain state.

Why: the justification of a chain state is its parent's, or the parent's height with the parent's
`T_h`; the genesis block's justification height is `0`, so a justification height `H ≥ 1` was
written at an ancestor-or-self of `D` whose parent has the height `H`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block whose justification is read; `H`: its justification height.

Read aloud: the justified block of a chain is the entry block of its justification height on that
chain, the genesis block excepted.

 -/
theorem lem47f_justified_is_entry (C : Config) (D : Block V) (H : Height)
    -- `D`'s chain state has the justification height `H`
    (hH : (M.chainStateOf C D).h_j = H)
    -- `H` is at least `1`
    (h1 : 1 ≤ H) :
    ∃ Y : Block V, Y.AncestorEq D ∧ (M.chainStateOf C Y).h = H ∧
      (M.chainStateOf C Y).T_h = (M.chainStateOf C D).J :=
  (GoldilocksCorrectness.Record.Proofs.Routines.exists_ancestor_of_h_j M F) C D H hH h1

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem47a_state_transition_bounds`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47a_state_transition_bounds` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem47a_state_transition_bounds_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem47a_state_transition_bounds V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem47a_state_transition_bounds Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem47b_state_transition_height`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47b_state_transition_height` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem47b_state_transition_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem47b_state_transition_height V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem47b_state_transition_height Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem47c_state_transition_T_h`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47c_state_transition_T_h` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem47c_state_transition_T_h_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem47c_state_transition_T_h V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem47c_state_transition_T_h Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem51_quorum_is_certificate`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem51_quorum_is_certificate` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem51_quorum_is_certificate_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem51_quorum_is_certificate V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem51_quorum_is_certificate Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem51b_progress_quorum_advances`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem51b_progress_quorum_advances` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem51b_progress_quorum_advances_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem51b_progress_quorum_advances V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem51b_progress_quorum_advances Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Statements.Routines.valid_attestation_of_height`,
recovered from its record form at the spec's model.

Read aloud: the landed `valid_attestation_of_height` holds, as the record's theorem at the spec's
model. -/
theorem valid_attestation_of_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.valid_attestation_of_height V) := by
  exact valid_attestation_of_height Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem47_chain_state_heights`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47_chain_state_heights` holds, as the record's theorem at the spec's
model. -/
theorem lem47_chain_state_heights_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem47_chain_state_heights V _ _) := by
  exact lem47_chain_state_heights Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem47f_justified_is_entry`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47f_justified_is_entry` holds, as the record's theorem at the spec's
model. -/
theorem lem47f_justified_is_entry_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem47f_justified_is_entry V _ _) := by
  exact lem47f_justified_is_entry Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Statements.Routines
