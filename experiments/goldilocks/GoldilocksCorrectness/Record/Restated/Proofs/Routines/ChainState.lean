module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateDefs

@[expose] public section

/-!
# ChainState, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/ChainState.lean` over a model `M` whose facts
`F` hold: Lemma 47, parts (a) to (c), over the model's state transition, the certificate (Lemmas 51
and 51b), and the kit facts on the attestations a chain state accepts.

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry JustificationCertOn ProgressCertOn FinalityCertOn)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 47 (a), over the state transition.** The proof; the audited statement is in
`Statements/Routines/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: along a block, the justification height stays less than the height, the finalization height stays at most the justification height, and every pending justification stays at a height at most the justification height. -/
theorem lem47a_state_transition_bounds (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    (hj : (M.chainStateOf C B.parent).h_j < (M.chainStateOf C B.parent).h)
        (hF : (M.chainStateOf C B.parent).h_F ≤ (M.chainStateOf C B.parent).h_j)
    (hpend : ∀ e ∈ (M.chainStateOf C B.parent).pending_finality,
        e.j ≤ (M.chainStateOf C B.parent).h_j) :
    1 ≤ (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_j < (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B).h_j ∧
      ∀ e ∈ (M.chainStateOf C B).pending_finality, e.j ≤ (M.chainStateOf C B).h_j :=
  F.cs.lem47a_state_transition_bounds C B hB hj hF hpend

/-- **Lemma 47 (b), over the state transition.** The proof; the audited statement is in
`Statements/Routines/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: a block's height is its parent's, or one more. -/
theorem lem47b_state_transition_height (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∨
        (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 :=
  F.cs.lem47b_state_transition_height C B hB

/-- **Lemma 47 (c), over the state transition.** The proof; the audited statement is in
`Statements/Routines/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: `T_h` changes exactly when the height does, and then to the block that raised it. -/
theorem lem47c_state_transition_T_h (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h →
        (M.chainStateOf C B).T_h = (M.chainStateOf C B.parent).T_h) ∧
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 → (M.chainStateOf C B).T_h = B) :=
  F.cs.lem47c_state_transition_T_h C B hB

/-- The justification of the state transition: the parent's justification is kept, or the
justified block becomes the parent's `T_h` at the parent's height.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: a block keeps its parent's justification, or justifies its parent's `T_h` at its parent's height. -/
theorem state_transition_justification (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    ((M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h_j ∧
        (M.chainStateOf C B).J = (M.chainStateOf C B.parent).J) ∨
      ((M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h ∧
          (M.chainStateOf C B).J = (M.chainStateOf C B.parent).T_h) :=
  F.cs.state_transition_justification C B hB

/-- **Kit fact, an attestation at the parent's height naming its `T_h` is valid.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `σ`: the chain state; `a`: the attestation.

Read aloud: a vote for the chain's current height and block may be included. -/
theorem valid_attestation_of_height (σ : M.CS) (a : Attestation V)
    (hh : a.h = σ.h) (hT : a.T = σ.T_h.root) :
    M.valid_attestation σ a = true :=
  F.cs.valid_attestation_of_height σ a hh hT

/-- When every pending justification of the parent's chain state is at a height greater than its
finalization height, the chain state of `B` has a finalization height at least the parent's.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: when every pending justification is higher than the finalization, a block's finalization height is at least its parent's. -/
theorem state_transition_h_F_mono (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    -- every pending justification of the parent is at a height greater than its finalization
    -- height
    (habove : ∀ e ∈ (M.chainStateOf C B.parent).pending_finality,
        (M.chainStateOf C B.parent).h_F < e.j) :
    (M.chainStateOf C B.parent).h_F ≤ (M.chainStateOf C B).h_F :=
  F.cs.state_transition_h_F_mono C B hB habove

/-- When the parent's justification height is less than its height, the chain state of `B` has a
justification height at least the parent's.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: a block's justification height is at least its parent's. -/
theorem state_transition_h_j_mono (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    -- the parent's justification height is less than its height
    (hj : (M.chainStateOf C B.parent).h_j < (M.chainStateOf C B.parent).h) :
    (M.chainStateOf C B.parent).h_j ≤ (M.chainStateOf C B).h_j := by
  rcases (state_transition_justification M F) C B hB with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  exact le_of_lt hj

/-- **Kit fact, Lemma 51 with votes already counted.** When `quorum V ≤ |Q|` and every member of
`Q` is in the parent's progress set or has an attestation in `B` at the height `σ.h` naming
`σ.T_h`, the chain state of `B` has height `σ.h + 1`, or keeps `σ.h` with `Q` in its progress set
and `B`'s slot less than `δt` after `σ.T_h`'s; and when every member is in the parent's target
participation or has a target vote in `B` at that height naming `σ.T_h`, the chain state of `B`
has height `σ.h + 1`, justified block `σ.T_h` and justification height `σ.h`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block; `Q`: the quorum.

Read aloud: a quorum counted in the parent or voting in the block is a certificate.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block. -/
theorem quorum_certificate_with_counted (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    (Q : Finset V)
    (hQ : M.quorumAt B ≤ Q.card)
    (hAtts : ∀ v ∈ Q, v ∈ (M.chainStateOf C B.parent).progress ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = (M.chainStateOf C B.parent).h ∧
        a.T = (M.chainStateOf C B.parent).T_h.root) :
    ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 ∨
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∧ Q ⊆ (M.chainStateOf C B).progress ∧
        B.slot < (M.chainStateOf C B.parent).T_h.slot + C.δt)) ∧
    ((∀ v ∈ Q, v ∈ (M.chainStateOf C B.parent).target_participation ∨
        ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = (M.chainStateOf C B.parent).h ∧
          a.T = (M.chainStateOf C B.parent).T_h.root ∧
          a.τ = false) →
      (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 ∧
          (M.chainStateOf C B).J = (M.chainStateOf C B.parent).T_h ∧
        (M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h) :=
  F.cs.quorum_certificate_with_counted C B hB Q hQ hAtts

/-- **Lemma 51, a quorum of votes at the parent's height is a certificate.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block; `Q`: the quorum.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: a quorum of votes for `(σ.h, σ.T_h)` in one block is a certificate: targets justify `σ.T_h` and raise the height; mixed votes fill the progress set and raise the height once the block's slot is `δt` past `σ.T_h`'s. -/
theorem lem51_quorum_is_certificate (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    (Q : Finset V)
    (hQ : M.quorumAt B ≤ Q.card)
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
        (M.chainStateOf C B).h_j = (M.chainStateOf C B.parent).h) := by
  have h := quorum_certificate_with_counted M F C B hB Q hQ (fun v hv => Or.inr (hAtts v hv))
  exact ⟨h.1, fun hT => h.2 (fun v hv => Or.inr (hT v hv))⟩

/-- **Lemma 51b, the progress quorum advances the height at the timeout slot.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: once a progress quorum is on chain, the first block of a late enough slot raises the height. -/
theorem lem51b_progress_quorum_advances (C : Config) (B : Block V) (hB : B ≠ Block.genesis)
    (hQ : M.quorumAt B ≤ (M.chainStateOf C B.parent).progress.card)
    (hSlot : (M.chainStateOf C B.parent).T_h.slot + C.δt ≤ B.slot) :
    (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 := by
  obtain ⟨h, -⟩ := quorum_certificate_with_counted M F C B hB
    (M.chainStateOf C B.parent).progress hQ (fun v hv => Or.inl hv)
  rcases h with h | ⟨-, -, hlt⟩
  · exact h
  · exfalso
    omega_nat

/-- A valid attestation is at the chain state's height naming its `T_h`, or at a lesser height.

The variables:
- `M`: the model; `F`: its facts;
- `σ`: the chain state; `a`: the attestation.

Read aloud: an attestation a chain state accepts votes for its current height and block, or is at a lesser height. -/
theorem valid_attestation_cases (σ : M.CS) (a : Attestation V)
    (h : M.valid_attestation σ a = true) :
    (a.h = σ.h ∧ a.T = σ.T_h.root) ∨ a.h < σ.h :=
  F.cs.valid_attestation_cases σ a h

/-- `newest K l₁ ++ l₂`, when `l₂` has at most `K` elements, keeps all of `l₂`: it is a suffix of
`l₁` followed by `l₂`.

The variables:
- `M`: the model; `F`: its facts;
- `K`: the bound; `l₁`, `l₂`: the two parts of the list.

Read aloud: keeping the newest `K` pairs of a list whose last part has at most `K` pairs keeps that last part. -/
theorem newest_append_of_length_le (K : Nat) (l₁ l₂ : List (M.PP))
    (h : l₂.length ≤ K) :
    M.newest K (l₁ ++ l₂) = l₁.drop (l₁.length + l₂.length - K) ++ l₂ := by
  rw [F.cs.newest_eq, List.length_append]
  exact List.drop_append_of_le_length (by omega)

/-- An attestation whose finality pair names a pending justification of `σ`, at a height greater
than the pair's and less than `σ.h`, is valid against `σ` (the second case of
`valid_attestation`).

The variables:
- `M`: the model; `F`: its facts;
- `σ`: the chain state; `a`: the attestation; `p`: its finality pair.

Read aloud: an attestation finalizing a pending justification, at a height between the pair's and the chain's, is accepted. -/
theorem valid_attestation_of_pending (σ : M.CS) (a : Attestation V) (p : FinalityPair)
    (hp : a.finality_pair = some p) (hpend : M.is_pending σ p = true) (h1 : p.hf < a.h)
    (h2 : a.h < σ.h) :
    M.valid_attestation σ a = true :=
  F.cs.valid_attestation_of_pending σ a p hp hpend h1 h2

/-- `is_pending σ p` answers `true` exactly when some pending justification `e` of `σ` is at the
height `p.hf` and names a block whose root is `p.Tf`.

The variables:
- `M`: the model; `F`: its facts;
- `σ`: the chain state; `p`: the finality pair.

Read aloud: a finality pair is pending in `σ` when it names the height and the block root of one
of `σ`'s pending justifications. -/
theorem is_pending_iff (σ : M.CS) (p : FinalityPair) :
    M.is_pending σ p = true ↔ ∃ e ∈ σ.pending_finality, e.j = p.hf ∧ e.T.root = p.Tf := by
  simp only [F.cs.is_pending_eq, decide_eq_true_eq]

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem47a_state_transition_bounds`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47a_state_transition_bounds` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem47a_state_transition_bounds_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem47a_state_transition_bounds V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem47a_state_transition_bounds Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem47b_state_transition_height`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47b_state_transition_height` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem47b_state_transition_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem47b_state_transition_height V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem47b_state_transition_height Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem47c_state_transition_T_h`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47c_state_transition_T_h` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem47c_state_transition_T_h_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem47c_state_transition_T_h V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem47c_state_transition_T_h Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.state_transition_justification`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `state_transition_justification` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem state_transition_justification_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.state_transition_justification V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact state_transition_justification Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_height`,
recovered from its record form at the spec's model.

Read aloud: the landed `valid_attestation_of_height` holds, as the record's theorem at the spec's
model. -/
theorem valid_attestation_of_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_height V) := by
  exact valid_attestation_of_height Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.state_transition_h_F_mono`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `state_transition_h_F_mono` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem state_transition_h_F_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.state_transition_h_F_mono V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact state_transition_h_F_mono Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.state_transition_h_j_mono`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `state_transition_h_j_mono` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem state_transition_h_j_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.state_transition_h_j_mono V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact state_transition_h_j_mono Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.quorum_certificate_with_counted`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `quorum_certificate_with_counted` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem quorum_certificate_with_counted_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.quorum_certificate_with_counted V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact quorum_certificate_with_counted Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem51_quorum_is_certificate`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem51_quorum_is_certificate` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem51_quorum_is_certificate_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem51_quorum_is_certificate V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem51_quorum_is_certificate Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem51b_progress_quorum_advances`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `lem51b_progress_quorum_advances` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem lem51b_progress_quorum_advances_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem51b_progress_quorum_advances V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact lem51b_progress_quorum_advances Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.valid_attestation_cases`,
recovered from its record form at the spec's model.

Read aloud: the landed `valid_attestation_cases` holds, as the record's theorem at the spec's
model. -/
theorem valid_attestation_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.valid_attestation_cases V) := by
  exact valid_attestation_cases Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.newest_append_of_length_le`,
recovered from its record form at the spec's model.

Read aloud: the landed `newest_append_of_length_le` holds, as the record's theorem at the spec's
model. -/
theorem newest_append_of_length_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.newest_append_of_length_le V) := by
  exact newest_append_of_length_le Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_pending`,
recovered from its record form at the spec's model.

Read aloud: the landed `valid_attestation_of_pending` holds, as the record's theorem at the spec's
model. -/
theorem valid_attestation_of_pending_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_pending V) := by
  exact valid_attestation_of_pending Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.is_pending_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `is_pending_iff` holds, as the record's theorem at the spec's
model. -/
theorem is_pending_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.is_pending_iff V) := by
  exact is_pending_iff Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
