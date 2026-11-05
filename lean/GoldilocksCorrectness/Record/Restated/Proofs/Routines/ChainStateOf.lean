module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOfDefs
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# ChainStateOf, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean` over a model `M` whose
facts `F` hold: the bounds and heights of the chain state of a block, the block that took the chain
into each height, the justified block, Lemma 47, and the facts on two compatible chains.

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
open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedOnChainWith)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_genesis_iff ancestorEq_node_iff
  ancestorEq_refl ancestorEq_trans compatible_iff)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- Part (a) of Lemma 47 with the bound on the pending justifications: the height is at least
`1`, the justification height less than the height, the finalization height at most the
justification height, and every pending justification at a height at most the justification
height.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block.

Read aloud: every chain state has height at least `1`, justification height less than its height, finalization height at most its justification height, and every pending justification at most its justification height. -/
theorem chainStateOf_bounds (C : Config) (B : Block V) :
    1 ≤ (M.chainStateOf C B).h ∧ (M.chainStateOf C B).h_j < (M.chainStateOf C B).h ∧
      (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B).h_j ∧
      ∀ e ∈ (M.chainStateOf C B).pending_finality, e.j ≤ (M.chainStateOf C B).h_j :=
  F.cs.chainStateOf_bounds C B

/-- Part (b) of Lemma 47 over `chainStateOf`: a non-genesis block's height is its parent's or
its parent's plus one.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block.

Read aloud: a non-genesis block's height is its parent's, or one more. -/
theorem chainStateOf_height (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h ∨
      (M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 := by
  exact F.cs.lem47b_state_transition_height C B hB

/-- Part (c) of Lemma 47 over `chainStateOf`: a non-genesis block that keeps its parent's
height keeps its parent's `T_h`, and one that raises it has itself as `T_h`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block.

Read aloud: a non-genesis block keeps its parent's `T_h` when it keeps the height, and is its own `T_h` when it raises it. -/
theorem chainStateOf_T_h (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h →
        (M.chainStateOf C B).T_h = (M.chainStateOf C B.parent).T_h) ∧
      ((M.chainStateOf C B).h = (M.chainStateOf C B.parent).h + 1 → (M.chainStateOf C B).T_h = B) := by
  exact F.cs.lem47c_state_transition_T_h C B hB

/-- Part (d) of Lemma 47: the heights are monotone along ancestry.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the ancestor; `D`: the descendant.

Read aloud: along a chain, the height never decreases. -/
theorem chainStateOf_height_mono (C : Config) {B D : Block V} (hBD : B.AncestorEq D) :
    (M.chainStateOf C B).h ≤ (M.chainStateOf C D).h := by
  induction D with
  | genesis =>
      rw [(ancestorEq_genesis_iff B).1 hBD]
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hBD with h | h
      · rw [h]
      · have h1 := ih h
        have h2 := (chainStateOf_height M F) C (.node p s r votes support ats v) (by intro h; cases h)
        change _ = (M.chainStateOf C p).h ∨ _ = (M.chainStateOf C p).h + 1 at h2
        rcases h2 with h2 | h2 <;> omega_nat

/-- Part (e) of Lemma 47: two blocks of one chain at the same height have the same `T_h`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the ancestor; `D`: the descendant.

Read aloud: two blocks of one chain at one height have one `T_h`. -/
theorem chainStateOf_T_h_of_same_height (C : Config) {B D : Block V} (hBD : B.AncestorEq D)
    (hh : (M.chainStateOf C B).h = (M.chainStateOf C D).h) :
    (M.chainStateOf C B).T_h = (M.chainStateOf C D).T_h := by
  induction D with
  | genesis =>
      rw [(ancestorEq_genesis_iff B).1 hBD]
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hBD with h | h
      · rw [h]
      · have hle := (chainStateOf_height_mono M F) C h
        have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
        have h2 := (chainStateOf_height M F) C _ hne
        have h3 := ((chainStateOf_T_h M F) C _ hne).1
        change _ = (M.chainStateOf C p).h ∨ _ = (M.chainStateOf C p).h + 1 at h2
        change _ = (M.chainStateOf C p).h → _ = (M.chainStateOf C p).T_h at h3
        rcases h2 with h2 | h2
        · rw [h3 h2]
          exact ih h (hh.trans h2)
        · exfalso
          omega_nat

/-- A justification height `H ≥ 1` of a block's chain state is the height of an ancestor of the
block, or the block itself, whose `T_h` is the justified block.

Why: the justification is the parent's, or the parent's `T_h` at the parent's height; the genesis
block's justification height is `0`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block; `H`: the justification height.

Read aloud: a justification height of at least `1` is the height of a block of the chain whose `T_h` is the justified block. -/
theorem exists_ancestor_of_h_j (C : Config) (D : Block V) (H : Height)
    (hH : (M.chainStateOf C D).h_j = H) (h1 : 1 ≤ H) :
    ∃ Y : Block V, Y.AncestorEq D ∧ (M.chainStateOf C Y).h = H ∧
      (M.chainStateOf C Y).T_h = (M.chainStateOf C D).J := by
  induction D with
  | genesis =>
      exfalso
      have h0 : (M.chainStateOf C (Block.genesis : Block V)).h_j = 0 :=
        (F.cs.chainStateOf_genesis_J C).2
      rw [h0] at hH
      omega_nat
  | node p s r votes support ats v ih =>
      have hp : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      have hst := F.cs.state_transition_justification C (.node p s r votes support ats v)
        (by intro h; cases h)
      simp only [Block.parent] at hst
      rcases hst with ⟨hj, hJ⟩ | ⟨hj, hJ⟩
      · obtain ⟨Y, hY, hYh, hYT⟩ := ih (hj.symm.trans hH)
        exact ⟨Y, ancestorEq_trans hY hp, hYh, hYT.trans hJ.symm⟩
      · exact ⟨p, hp, hj.symm.trans hH, hJ.symm⟩

/-- A block's `T_h` is an ancestor of the block, or the block itself, and has the block's height.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block.

Read aloud: a block's `T_h` is on its chain, at its height. -/
theorem chainStateOf_T_h_spec (C : Config) (D : Block V) :
    (M.chainStateOf C D).T_h.AncestorEq D ∧
      (M.chainStateOf C (M.chainStateOf C D).T_h).h = (M.chainStateOf C D).h := by
  induction D with
  | genesis =>
      rw [F.cs.chainStateOf_genesis_T_h C]
      exact ⟨ancestorEq_refl _, rfl⟩
  | node p s r votes support ats v ih =>
      have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
      have hp : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      have h2 := (chainStateOf_height M F) C _ hne
      have h3 := (chainStateOf_T_h M F) C _ hne
      change _ = (M.chainStateOf C p).h ∨ _ = (M.chainStateOf C p).h + 1 at h2
      change (_ = (M.chainStateOf C p).h → _ = (M.chainStateOf C p).T_h) ∧ _ at h3
      rcases h2 with h2 | h2
      · rw [h3.1 h2]
        exact ⟨ancestorEq_trans ih.1 hp, ih.2.trans h2.symm⟩
      · rw [h3.2 h2]
        exact ⟨ancestorEq_refl _, rfl⟩

/-- A block's justified block is an ancestor of the block, or the block itself; it is the
genesis block when the justification height is `0`; and it has the justification height as its
height when that is at least `1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block.

Read aloud: a block's justified block is on its chain; it is the genesis block at justification height `0`, and otherwise has the justification height as its height. -/
theorem chainStateOf_J_spec (C : Config) (D : Block V) :
    (M.chainStateOf C D).J.AncestorEq D ∧
      ((M.chainStateOf C D).h_j = 0 → (M.chainStateOf C D).J = Block.genesis) ∧
      (1 ≤ (M.chainStateOf C D).h_j →
        (M.chainStateOf C (M.chainStateOf C D).J).h = (M.chainStateOf C D).h_j) := by
  have h0 : ∀ D : Block V, (M.chainStateOf C D).h_j = 0 → (M.chainStateOf C D).J = Block.genesis := by
    intro D
    induction D with
    | genesis => intro _; exact (F.cs.chainStateOf_genesis_J C).1
    | node p s r votes support ats v ih =>
        intro hj0
        have hst := F.cs.state_transition_justification C (.node p s r votes support ats v)
          (by intro h; cases h)
        simp only [Block.parent] at hst
        rcases hst with ⟨hj, hJ⟩ | ⟨hj, -⟩
        · rw [hJ]
          exact ih (hj.symm.trans hj0)
        · exfalso
          have := ((chainStateOf_bounds M F) C p).1
          omega_nat
  refine ⟨?_, h0 D, fun h1 => ?_⟩
  · by_cases hj : (M.chainStateOf C D).h_j = 0
    · rw [h0 D hj]
      exact GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq D
    · obtain ⟨Y, hYD, -, hYT⟩ :=
        (exists_ancestor_of_h_j M F) C D _ rfl (Nat.one_le_iff_ne_zero.mpr hj)
      rw [← hYT]
      exact ancestorEq_trans ((chainStateOf_T_h_spec M F) C Y).1 hYD
  · obtain ⟨Y, -, hYh, hYT⟩ := (exists_ancestor_of_h_j M F) C D _ rfl h1
    rw [← hYT, ((chainStateOf_T_h_spec M F) C Y).2, hYh]

/-- **Lemma 47, the chain-state facts, parts (a) to (e).** The proof; the audited statement is in
`Statements/Executions/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`, `D`: the blocks.

Read aloud: along a chain the height rises by at most one per block, `T_h` changes exactly when the height does, and two blocks of one chain at the same height have the same `T_h`. -/
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
      (M.chainStateOf C B).T_h = (M.chainStateOf C D).T_h) := by
  obtain ⟨a1, a2, a3, -⟩ := (chainStateOf_bounds M F) C B
  exact ⟨⟨a1, a2, a3⟩, (chainStateOf_height M F) C B, (chainStateOf_T_h M F) C B,
    (chainStateOf_height_mono M F) C, (chainStateOf_T_h_of_same_height M F) C⟩

/-- Every pending justification of a block's chain state is at a height greater than its
finalization height.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block.

Read aloud: every pending justification of a block's chain state is higher than its finalization. -/
theorem chainStateOf_pending_above (C : Config) (B : Block V) :
    ∀ e ∈ (M.chainStateOf C B).pending_finality, (M.chainStateOf C B).h_F < e.j :=
  F.cs.chainStateOf_pending_above C B

/-- A block's chain state has a justification height and a finalization height at least its
parent's.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `p`: the parent; the rest: the block's fields.

Read aloud: a block's justification and finalization heights are at least its parent's. -/
theorem chainStateOf_h_j_h_F_mono_parent (C : Config) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V) :
    (M.chainStateOf C p).h_j ≤ (M.chainStateOf C (.node p s r votes support ats v)).h_j ∧
      (M.chainStateOf C p).h_F ≤ (M.chainStateOf C (.node p s r votes support ats v)).h_F := by
  have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
  exact ⟨(state_transition_h_j_mono M F) C _ hne ((chainStateOf_bounds M F) C p).2.1,
    F.cs.state_transition_h_F_mono C _ hne (F.cs.chainStateOf_pending_above C p)⟩

/-- **The monotonicity of the justification and finalization heights along a chain.** The proof;
the audited statement is in `Statements/Executions/FinalityLivenessKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `A`: the ancestor; `B`: the descendant.

Read aloud: along a chain, the justification and finalization heights never decrease. -/
theorem chainStateOf_h_j_h_F_mono (C : Config) (A B : Block V) (hAB : A.AncestorEq B) :
    (M.chainStateOf C A).h_j ≤ (M.chainStateOf C B).h_j ∧
      (M.chainStateOf C A).h_F ≤ (M.chainStateOf C B).h_F := by
  induction B with
  | genesis =>
      rw [(ancestorEq_genesis_iff A).1 hAB]
      exact ⟨le_refl _, le_refl _⟩
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hAB with h | h
      · rw [h]; exact ⟨le_refl _, le_refl _⟩
      · obtain ⟨h1, h2⟩ := ih h
        obtain ⟨h3, h4⟩ := (chainStateOf_h_j_h_F_mono_parent M F) C p s r votes support ats v
        exact ⟨le_trans h1 h3, le_trans h2 h4⟩

/-- Along a chain at one height, the progress set and the target participation only grow.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `Y`: the ancestor; `D`: the descendant.

Read aloud: along a chain at one height, the counted validators are kept. -/
theorem counted_kept_of_same_height (C : Config) {Y D : Block V} (hYD : Y.AncestorEq D)
    (hh : (M.chainStateOf C Y).h = (M.chainStateOf C D).h) :
    (M.chainStateOf C Y).progress ⊆ (M.chainStateOf C D).progress ∧
      (M.chainStateOf C Y).target_participation ⊆ (M.chainStateOf C D).target_participation :=
  F.cs.counted_kept_of_same_height C hYD hh

/-- **Kit fact, the block that took a chain into its height is an entry block.** The proof; the
audited statement is in `Statements/Executions/HealedAttestationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block.

Read aloud: a block's `T_h` is an entry block, at the block's height, on its chain. -/
theorem isEntry_T_h (C : Config) (D : Block V) :
    IsEntry M C (M.chainStateOf C D).T_h ∧
      (M.chainStateOf C (M.chainStateOf C D).T_h).h = (M.chainStateOf C D).h ∧
      (M.chainStateOf C D).T_h.AncestorEq D := by
  obtain ⟨h1, h2⟩ := (chainStateOf_T_h_spec M F) C D
  exact ⟨((lem47_chain_state_heights M F) C _ D).2.2.2.2 h1 h2, h2, h1⟩

/-- Two entry blocks of one height on one chain are one block.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: two entry blocks of one height on one chain are one block. -/
theorem entry_eq_of_compatible (C : Config) {E E' : Block V} (hE : IsEntry M C E)
    (hE' : IsEntry M C E') (hh : (M.chainStateOf C E).h = (M.chainStateOf C E').h)
    (hc : E.compatible E' = true) :
    E = E' := by
  rcases (compatible_iff _ _).1 hc with h | h
  · have := ((lem47_chain_state_heights M F) C E E').2.2.2.2 h hh
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this
  · have := ((lem47_chain_state_heights M F) C E' E).2.2.2.2 h hh.symm
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this.symm

/-- Copied from `scratch/goldilocks_async/probe_ar3_false.lean:73`.
An entry block `E` compatible with `B`, at a chain-state height at most `B`'s, is `B` or an
ancestor of `B`.

Why: when `B` is an ancestor of `E`, the heights are equal, so `B`'s `T_h` is `E`'s, which is `E`
itself (an entry), and a `T_h` is an ancestor of its block.

Read aloud: `B`'s chain has one entry per height, so an entry at or before `B`'s height that does
not conflict with `B` is on `B`'s chain.

The variables:
- `M`: the model; `F`: its facts. -/
theorem ancestorEq_of_entry_compatible_le (C : Config) {B E : Block V}
    (hE : IsEntry M C E) (hc : E.AncestorEq B ∨ B.AncestorEq E)
    (hh : (M.chainStateOf C E).h ≤ (M.chainStateOf C B).h) :
    E.AncestorEq B := by
  rcases hc with h | h
  · exact h
  · have hle := (chainStateOf_height_mono M F) C h
    have heq : (M.chainStateOf C B).h = (M.chainStateOf C E).h := le_antisymm hle hh
    have hT := (chainStateOf_T_h_of_same_height M F) C h heq
    unfold IsEntry at hE
    rw [hE] at hT
    rw [← hT]
    exact ((chainStateOf_T_h_spec M F) C B).1

/-- A block compatible with `B` whose chain-state height is greater than `B`'s descends from `B`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `E`: the block compatible with `B`.

Read aloud: a block on `B`'s side that is higher than `B` is `B` or a descendant of `B`. -/
theorem descends_of_compatible_higher (C : Config) {B E : Block V}
    (hc : E.AncestorEq B ∨ B.AncestorEq E)
    (hh : (M.chainStateOf C B).h < (M.chainStateOf C E).h) :
    B.AncestorEq E := by
  rcases hc with h | h
  · have := (chainStateOf_height_mono M F) C h
    omega_nat
  · exact h

/-- The chain state of the genesis block has the height `1`: it is the spec's initial chain state
`ChainState.initial`, whose height is `1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters.

Read aloud: the genesis block's chain is at the height one. -/
theorem chainStateOf_genesis_h (C : Config) :
    (M.chainStateOf C (Block.genesis : Block V)).h = 1 :=
  F.cs.chainStateOf_genesis_h C

/-- The chain state of the genesis block took its chain into its height at the genesis block: it is
the spec's initial chain state `ChainState.initial`, whose `T_h` is the genesis block.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters.

Read aloud: the genesis block's chain entered its height at the genesis block. -/
theorem chainStateOf_genesis_T_h (C : Config) :
    (M.chainStateOf C (Block.genesis : Block V)).T_h = Block.genesis :=
  F.cs.chainStateOf_genesis_T_h C

/-- The chain state of the genesis block has the genesis block as its justified block and the
justification height `0`: it is the spec's initial chain state `ChainState.initial`. Added by the
record migration, step 1f.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters.

Read aloud: the genesis block's chain has the genesis block justified, at the height zero. -/
theorem chainStateOf_genesis_J (C : Config) :
    (M.chainStateOf C (Block.genesis : Block V)).J = Block.genesis ∧
      (M.chainStateOf C (Block.genesis : Block V)).h_j = 0 :=
  F.cs.chainStateOf_genesis_J C

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_bounds`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_bounds` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_bounds_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_bounds V _ _) := by
  exact chainStateOf_bounds Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_height`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_height` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_height V _ _) := by
  exact chainStateOf_height Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_T_h`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_T_h` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_T_h_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_T_h V _ _) := by
  exact chainStateOf_T_h Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_height_mono`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_height_mono` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_height_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_height_mono V _ _) := by
  exact chainStateOf_height_mono Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_T_h_of_same_height`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_T_h_of_same_height` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_T_h_of_same_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_T_h_of_same_height V _ _) := by
  exact chainStateOf_T_h_of_same_height Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.exists_ancestor_of_h_j`,
recovered from its record form at the spec's model.

Read aloud: the landed `exists_ancestor_of_h_j` holds, as the record's theorem at the spec's
model. -/
theorem exists_ancestor_of_h_j_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.exists_ancestor_of_h_j V _ _) := by
  exact exists_ancestor_of_h_j Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_T_h_spec`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_T_h_spec` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_T_h_spec_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_T_h_spec V _ _) := by
  exact chainStateOf_T_h_spec Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_J_spec`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_J_spec` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_J_spec_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_J_spec V _ _) := by
  exact chainStateOf_J_spec Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem47_chain_state_heights`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem47_chain_state_heights` holds, as the record's theorem at the spec's
model. -/
theorem lem47_chain_state_heights_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem47_chain_state_heights V _ _) := by
  exact lem47_chain_state_heights Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_pending_above`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_pending_above` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_pending_above_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_pending_above V _ _) := by
  exact chainStateOf_pending_above Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono_parent`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_h_j_h_F_mono_parent` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_h_j_h_F_mono_parent_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono_parent V _ _) := by
  exact chainStateOf_h_j_h_F_mono_parent Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_h_j_h_F_mono` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_h_j_h_F_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono V _ _) := by
  exact chainStateOf_h_j_h_F_mono Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.counted_kept_of_same_height`,
recovered from its record form at the spec's model.

Read aloud: the landed `counted_kept_of_same_height` holds, as the record's theorem at the spec's
model. -/
theorem counted_kept_of_same_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.counted_kept_of_same_height V _ _) := by
  exact counted_kept_of_same_height Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.isEntry_T_h`,
recovered from its record form at the spec's model.

Read aloud: the landed `isEntry_T_h` holds, as the record's theorem at the spec's
model. -/
theorem isEntry_T_h_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.isEntry_T_h V _ _) := by
  simp only [record_goldilocks]
  exact isEntry_T_h Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.entry_eq_of_compatible`,
recovered from its record form at the spec's model.

Read aloud: the landed `entry_eq_of_compatible` holds, as the record's theorem at the spec's
model. -/
theorem entry_eq_of_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.entry_eq_of_compatible V _ _) := by
  simp only [record_goldilocks]
  exact entry_eq_of_compatible Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_entry_compatible_le`,
recovered from its record form at the spec's model.

Read aloud: the landed `ancestorEq_of_entry_compatible_le` holds, as the record's theorem at the spec's
model. -/
theorem ancestorEq_of_entry_compatible_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_entry_compatible_le V _ _) := by
  simp only [record_goldilocks]
  exact ancestorEq_of_entry_compatible_le Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.descends_of_compatible_higher`,
recovered from its record form at the spec's model.

Read aloud: the landed `descends_of_compatible_higher` holds, as the record's theorem at the spec's
model. -/
theorem descends_of_compatible_higher_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.descends_of_compatible_higher V _ _) := by
  exact descends_of_compatible_higher Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_h`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_genesis_h` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_genesis_h_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_h V _ _) := by
  exact chainStateOf_genesis_h Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_T_h`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_genesis_T_h` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_genesis_T_h_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_T_h V _ _) := by
  exact chainStateOf_genesis_T_h Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_J`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_genesis_J` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_genesis_J_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_genesis_J V _ _) := by
  exact chainStateOf_genesis_J Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
