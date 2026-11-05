module
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Statements.Routines.ChainStateDefs
import all Goldilocks.FG.ChainState

@[expose] public section

/-!
# The chain state of a block

The theorems about `chainStateOf C B`, the chain state of the block `B` (the initial chain state
for the genesis block, and for any other block the state transition from its parent's): its
bounds and heights (`chainStateOf_bounds`, `chainStateOf_height`, `chainStateOf_height_mono`),
the block `T_h` that took the chain into each height (`chainStateOf_T_h`, `chainStateOf_T_h_spec`,
`chainStateOf_T_h_of_same_height`, `isEntry_T_h`), the justified block (`chainStateOf_J_spec`,
`exists_ancestor_of_h_j`, `entry_eq_of_compatible`), the pending pairs (`chainStateOf_pending_above`,
`chainStateOf_pending_last`), Lemma 47 (`lem47_chain_state_heights`), and the facts on two
compatible chains (`ancestorEq_of_entry_compatible_le`, `descends_of_compatible_higher`,
`counted_kept_of_same_height`).

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- The chain state of a non-genesis block is the state transition from its parent's. -/
theorem chainStateOf_node (C : Config) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V) :
    chainStateOf C (.node p s r votes support ats v) =
      state_transition C (chainStateOf C p) (.node p s r votes support ats v) := by rfl

omit [RootOrder] in
/-- Part (a) of Lemma 47 with the bound on the pending justifications: the height is at least
`1`, the justification height less than the height, the finalization height at most the
justification height, and every pending justification at a height at most the justification
height.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem chainStateOf_bounds (C : Config) (B : Block V) :
    1 ≤ (chainStateOf C B).h ∧ (chainStateOf C B).h_j < (chainStateOf C B).h ∧
      (chainStateOf C B).h_F ≤ (chainStateOf C B).h_j ∧
      ∀ e ∈ (chainStateOf C B).pending_finality, e.j ≤ (chainStateOf C B).h_j := by
  induction B with
  | genesis =>
      refine ⟨le_refl 1, Nat.zero_lt_one, le_refl 0, fun e he => absurd he List.not_mem_nil⟩
  | node p s r votes support ats v ih =>
      rw [chainStateOf_node]
      exact lem47a_state_transition_bounds C _ _ ih.2.1 ih.2.2.1 ih.2.2.2

omit [RootOrder] in
/-- Part (b) of Lemma 47 over `chainStateOf`: a non-genesis block's height is its parent's or
its parent's plus one.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem chainStateOf_height (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    (chainStateOf C B).h = (chainStateOf C B.parent).h ∨
      (chainStateOf C B).h = (chainStateOf C B.parent).h + 1 := by
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      rw [chainStateOf_node]
      exact lem47b_state_transition_height C _ _

omit [RootOrder] in
/-- Part (c) of Lemma 47 over `chainStateOf`: a non-genesis block that keeps its parent's
height keeps its parent's `T_h`, and one that raises it has itself as `T_h`.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem chainStateOf_T_h (C : Config) (B : Block V) (hB : B ≠ Block.genesis) :
    ((chainStateOf C B).h = (chainStateOf C B.parent).h →
        (chainStateOf C B).T_h = (chainStateOf C B.parent).T_h) ∧
      ((chainStateOf C B).h = (chainStateOf C B.parent).h + 1 → (chainStateOf C B).T_h = B) := by
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      rw [chainStateOf_node]
      exact lem47c_state_transition_T_h C _ _

omit [RootOrder] in
/-- Part (d) of Lemma 47: the heights are monotone along ancestry.

The variables:
- `C`: the parameters; `B`: the ancestor; `D`: the descendant. -/
theorem chainStateOf_height_mono (C : Config) {B D : Block V} (hBD : B.AncestorEq D) :
    (chainStateOf C B).h ≤ (chainStateOf C D).h := by
  induction D with
  | genesis =>
      rw [(ancestorEq_genesis_iff B).1 hBD]
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hBD with h | h
      · rw [h]
      · have h1 := ih h
        have h2 := chainStateOf_height C (.node p s r votes support ats v) (by intro h; cases h)
        change _ = (chainStateOf C p).h ∨ _ = (chainStateOf C p).h + 1 at h2
        rcases h2 with h2 | h2 <;> omega_nat

omit [RootOrder] in
/-- Part (e) of Lemma 47: two blocks of one chain at the same height have the same `T_h`.

The variables:
- `C`: the parameters; `B`: the ancestor; `D`: the descendant. -/
theorem chainStateOf_T_h_of_same_height (C : Config) {B D : Block V} (hBD : B.AncestorEq D)
    (hh : (chainStateOf C B).h = (chainStateOf C D).h) :
    (chainStateOf C B).T_h = (chainStateOf C D).T_h := by
  induction D with
  | genesis =>
      rw [(ancestorEq_genesis_iff B).1 hBD]
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hBD with h | h
      · rw [h]
      · have hle := chainStateOf_height_mono C h
        have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
        have h2 := chainStateOf_height C _ hne
        have h3 := (chainStateOf_T_h C _ hne).1
        change _ = (chainStateOf C p).h ∨ _ = (chainStateOf C p).h + 1 at h2
        change _ = (chainStateOf C p).h → _ = (chainStateOf C p).T_h at h3
        rcases h2 with h2 | h2
        · rw [h3 h2]
          exact ih h (hh.trans h2)
        · exfalso
          omega_nat

omit [RootOrder] in
/-- A justification height `H ≥ 1` of a block's chain state is the height of an ancestor of the
block, or the block itself, whose `T_h` is the justified block.

Why: the justification is the parent's, or the parent's `T_h` at the parent's height; the genesis
block's justification height is `0`.

The variables:
- `C`: the parameters; `D`: the block; `H`: the justification height. -/
theorem exists_ancestor_of_h_j (C : Config) (D : Block V) (H : Height)
    (hH : (chainStateOf C D).h_j = H) (h1 : 1 ≤ H) :
    ∃ Y : Block V, Y.AncestorEq D ∧ (chainStateOf C Y).h = H ∧
      (chainStateOf C Y).T_h = (chainStateOf C D).J := by
  induction D with
  | genesis =>
      exfalso
      have h0 : (chainStateOf C (Block.genesis : Block V)).h_j = 0 := rfl
      rw [h0] at hH
      omega_nat
  | node p s r votes support ats v ih =>
      have hp : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      rw [chainStateOf_node] at hH ⊢
      rcases state_transition_justification C (chainStateOf C p) (.node p s r votes support ats v)
        with ⟨hj, hJ⟩ | ⟨hj, hJ⟩
      · obtain ⟨Y, hY, hYh, hYT⟩ := ih (hj.symm.trans hH)
        exact ⟨Y, ancestorEq_trans hY hp, hYh, hYT.trans hJ.symm⟩
      · exact ⟨p, hp, hj.symm.trans hH, hJ.symm⟩

omit [RootOrder] in
/-- A block's `T_h` is an ancestor of the block, or the block itself, and has the block's height.

The variables:
- `C`: the parameters; `D`: the block. -/
theorem chainStateOf_T_h_spec (C : Config) (D : Block V) :
    (chainStateOf C D).T_h.AncestorEq D ∧
      (chainStateOf C (chainStateOf C D).T_h).h = (chainStateOf C D).h := by
  induction D with
  | genesis => exact ⟨ancestorEq_refl _, rfl⟩
  | node p s r votes support ats v ih =>
      have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
      have hp : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      have h2 := chainStateOf_height C _ hne
      have h3 := chainStateOf_T_h C _ hne
      change _ = (chainStateOf C p).h ∨ _ = (chainStateOf C p).h + 1 at h2
      change (_ = (chainStateOf C p).h → _ = (chainStateOf C p).T_h) ∧ _ at h3
      rcases h2 with h2 | h2
      · rw [h3.1 h2]
        exact ⟨ancestorEq_trans ih.1 hp, ih.2.trans h2.symm⟩
      · rw [h3.2 h2]
        exact ⟨ancestorEq_refl _, rfl⟩

omit [RootOrder] in
/-- A block's justified block is an ancestor of the block, or the block itself; it is the
genesis block when the justification height is `0`; and it has the justification height as its
height when that is at least `1`.

The variables:
- `C`: the parameters; `D`: the block. -/
theorem chainStateOf_J_spec (C : Config) (D : Block V) :
    (chainStateOf C D).J.AncestorEq D ∧
      ((chainStateOf C D).h_j = 0 → (chainStateOf C D).J = Block.genesis) ∧
      (1 ≤ (chainStateOf C D).h_j →
        (chainStateOf C (chainStateOf C D).J).h = (chainStateOf C D).h_j) := by
  have h0 : ∀ D : Block V, (chainStateOf C D).h_j = 0 → (chainStateOf C D).J = Block.genesis := by
    intro D
    induction D with
    | genesis => intro _; rfl
    | node p s r votes support ats v ih =>
        intro hj0
        rw [chainStateOf_node] at hj0 ⊢
        rcases state_transition_justification C (chainStateOf C p)
          (.node p s r votes support ats v) with ⟨hj, hJ⟩ | ⟨hj, -⟩
        · rw [hJ]
          exact ih (hj.symm.trans hj0)
        · exfalso
          have := (chainStateOf_bounds C p).1
          omega_nat
  refine ⟨?_, h0 D, fun h1 => ?_⟩
  · by_cases hj : (chainStateOf C D).h_j = 0
    · rw [h0 D hj]
      exact GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq D
    · obtain ⟨Y, hYD, -, hYT⟩ :=
        exists_ancestor_of_h_j C D _ rfl (Nat.one_le_iff_ne_zero.mpr hj)
      rw [← hYT]
      exact ancestorEq_trans (chainStateOf_T_h_spec C Y).1 hYD
  · obtain ⟨Y, -, hYh, hYT⟩ := exists_ancestor_of_h_j C D _ rfl h1
    rw [← hYT, (chainStateOf_T_h_spec C Y).2, hYh]

omit [RootOrder] in
/-- **Lemma 47, the chain-state facts, parts (a) to (e).** The proof; the audited statement is in
`Statements/Executions/ChainStateStatements.lean`.

The variables:
- `C`: the parameters; `B`, `D`: the blocks. -/
theorem lem47_chain_state_heights (C : Config) (B D : Block V) :
    (1 ≤ (chainStateOf C B).h ∧ (chainStateOf C B).h_j < (chainStateOf C B).h ∧
      (chainStateOf C B).h_F ≤ (chainStateOf C B).h_j) ∧
    (B ≠ Block.genesis →
      ((chainStateOf C B).h = (chainStateOf C B.parent).h ∨
        (chainStateOf C B).h = (chainStateOf C B.parent).h + 1)) ∧
    (B ≠ Block.genesis →
      ((chainStateOf C B).h = (chainStateOf C B.parent).h →
        (chainStateOf C B).T_h = (chainStateOf C B.parent).T_h) ∧
      ((chainStateOf C B).h = (chainStateOf C B.parent).h + 1 → (chainStateOf C B).T_h = B)) ∧
    (B.AncestorEq D → (chainStateOf C B).h ≤ (chainStateOf C D).h) ∧
    (B.AncestorEq D → (chainStateOf C B).h = (chainStateOf C D).h →
      (chainStateOf C B).T_h = (chainStateOf C D).T_h) := by
  obtain ⟨a1, a2, a3, -⟩ := chainStateOf_bounds C B
  exact ⟨⟨a1, a2, a3⟩, chainStateOf_height C B, chainStateOf_T_h C B,
    chainStateOf_height_mono C, chainStateOf_T_h_of_same_height C⟩

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- Every pending justification of a block's chain state is at a height greater than its
finalization height.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem chainStateOf_pending_above (C : Config) (B : Block V) :
    ∀ e ∈ (chainStateOf C B).pending_finality, (chainStateOf C B).h_F < e.j := by
  cases B with
  | genesis => intro e he; exact absurd he List.not_mem_nil
  | node p s r votes support ats v =>
      obtain ⟨-, hj, hF, hpend⟩ := chainStateOf_bounds C p
      rw [chainStateOf_node]
      exact state_transition_pending_above C _ _ hj hF hpend

omit [RootOrder] in
/-- A block's chain state has a justification height and a finalization height at least its
parent's.

The variables:
- `C`: the parameters; `p`: the parent; the rest: the block's fields. -/
theorem chainStateOf_h_j_h_F_mono_parent (C : Config) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V) :
    (chainStateOf C p).h_j ≤ (chainStateOf C (.node p s r votes support ats v)).h_j ∧
      (chainStateOf C p).h_F ≤ (chainStateOf C (.node p s r votes support ats v)).h_F := by
  rw [chainStateOf_node]
  exact ⟨state_transition_h_j_mono C _ _ (chainStateOf_bounds C p).2.1,
    state_transition_h_F_mono C _ _ (chainStateOf_pending_above C p)⟩

omit [RootOrder] in
/-- **The monotonicity of the justification and finalization heights along a chain.** The proof;
the audited statement is in `Statements/Executions/FinalityLivenessKitStatements.lean`.

The variables:
- `C`: the parameters; `A`: the ancestor; `B`: the descendant. -/
theorem chainStateOf_h_j_h_F_mono (C : Config) (A B : Block V) (hAB : A.AncestorEq B) :
    (chainStateOf C A).h_j ≤ (chainStateOf C B).h_j ∧
      (chainStateOf C A).h_F ≤ (chainStateOf C B).h_F := by
  induction B with
  | genesis =>
      rw [(ancestorEq_genesis_iff A).1 hAB]
      exact ⟨le_refl _, le_refl _⟩
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hAB with h | h
      · rw [h]; exact ⟨le_refl _, le_refl _⟩
      · obtain ⟨h1, h2⟩ := ih h
        obtain ⟨h3, h4⟩ := chainStateOf_h_j_h_F_mono_parent C p s r votes support ats v
        exact ⟨le_trans h1 h3, le_trans h2 h4⟩

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Along a chain at one height, the progress set and the target participation only grow.

The variables:
- `C`: the parameters; `Y`: the ancestor; `D`: the descendant. -/
theorem counted_kept_of_same_height (C : Config) {Y D : Block V} (hYD : Y.AncestorEq D)
    (hh : (chainStateOf C Y).h = (chainStateOf C D).h) :
    (chainStateOf C Y).progress ⊆ (chainStateOf C D).progress ∧
      (chainStateOf C Y).target_participation ⊆ (chainStateOf C D).target_participation := by
  induction D with
  | genesis =>
      rw [(ancestorEq_genesis_iff Y).1 hYD]
      exact ⟨subset_refl _, subset_refl _⟩
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hYD with h | h
      · rw [h]
        exact ⟨subset_refl _, subset_refl _⟩
      · have hle := chainStateOf_height_mono C h
        have hle' := chainStateOf_height_mono C
          ((ancestorEq_node_iff p p s r votes support ats v).2 (Or.inr (ancestorEq_refl p)))
        have hpD : (chainStateOf C p).h = (chainStateOf C (.node p s r votes support ats v)).h := by
          unfold Height at *
          omega
        obtain ⟨h1, h2⟩ := ih h (hh.trans hpD.symm)
        rw [chainStateOf_node] at hpD ⊢
        obtain ⟨tp, pr, fp, F', h_F', htp, hpr, -, -, hc⟩ :=
          state_transition_cases C (chainStateOf C p) (.node p s r votes support ats v)
        rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩
        · rw [hR] at hpD
          exact absurd hpD (by dsimp only; unfold Height; omega)
        · rw [hR] at hpD
          exact absurd hpD (by dsimp only; unfold Height; omega)
        · rw [hR]
          exact ⟨h1.trans hpr, h2.trans htp⟩

end

end

section

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **Kit fact, the block that took a chain into its height is an entry block.** The proof; the
audited statement is in `Statements/Executions/HealedAttestationStatements.lean`.

The variables:
- `C`: the parameters; `D`: the block. -/
theorem isEntry_T_h (C : Config) (D : Block V) :
    IsEntry C (chainStateOf C D).T_h ∧
      (chainStateOf C (chainStateOf C D).T_h).h = (chainStateOf C D).h ∧
      (chainStateOf C D).T_h.AncestorEq D := by
  obtain ⟨h1, h2⟩ := chainStateOf_T_h_spec C D
  exact ⟨(lem47_chain_state_heights C _ D).2.2.2.2 h1 h2, h2, h1⟩

end

end

section

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `JustifiedOnChainWith C H OnChain B`: when the justification height of the chain state of `B`
is greater than `H`, its justified block satisfies `OnChain`, is an entry block and has that
justification height as its chain-state height.

The variables:
- `C`: the parameters; `H`: the threshold; `OnChain`: the set of blocks; `B`: the block. -/
def JustifiedOnChainWith (C : Config) (H : ℕ) (OnChain : Block V → Prop) (B : Block V) : Prop :=
  H < (chainStateOf C B).h_j →
    OnChain (chainStateOf C B).J ∧ IsEntry C (chainStateOf C B).J ∧
      (chainStateOf C (chainStateOf C B).J).h = (chainStateOf C B).h_j

end

end

section

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- Two entry blocks of one height on one chain are one block. -/
theorem entry_eq_of_compatible (C : Config) {E E' : Block V} (hE : IsEntry C E)
    (hE' : IsEntry C E') (hh : (chainStateOf C E).h = (chainStateOf C E').h)
    (hc : E.compatible E' = true) : E = E' := by
  rcases (compatible_iff _ _).1 hc with h | h
  · have := (lem47_chain_state_heights C E E').2.2.2.2 h hh
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this
  · have := (lem47_chain_state_heights C E' E).2.2.2.2 h hh.symm
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this.symm

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- When a block's chain state has its finalization height less than its justification height,
the justification `(h_j, J)` is the last pending justification.

Why: by induction on the block. The justification branch appends `(σ.h, σ.T_h)`, the new
`(h_j, J)`, and `newest` keeps the last pair (`K_W ≥ 2`); otherwise `(h_j, J)` is the parent's,
the finalization height the loop leaves is at least the parent's, so the parent's is less than
`h_j` and its last pair is `(h_j, J)`, which the filter keeps.

The variables:
- `C`: the parameters; `X`: the block. -/
theorem chainStateOf_pending_last (C : Config) (X : Block V)
    (hlt : (chainStateOf C X).h_F < (chainStateOf C X).h_j) :
    ∃ l : List (PendingPair V), (chainStateOf C X).pending_finality =
      l ++ [PendingPair.mk (chainStateOf C X).h_j (chainStateOf C X).J] := by
  induction X with
  | genesis => exact absurd hlt (lt_irrefl 0)
  | node p s r votes support ats v ih =>
      have habove := chainStateOf_pending_above C p
      rw [chainStateOf_node, state_transition_eq] at hlt ⊢
      obtain ⟨tp, pr, fp, h1, -, -, -⟩ := process_attestations_eq (chainStateOf C p)
        (.node p s r votes support ats v) (Block.node p s r votes support ats v).attestations
      obtain ⟨F', h_F', hh, hc⟩ := process_height_events_cases C
        (process_attestations (chainStateOf C p) (.node p s r votes support ats v)
          (Block.node p s r votes support ats v).attestations)
      rw [h1] at hh hc
      have hge : (chainStateOf C p).h_F ≤ h_F' := by
        rcases hh with h | ⟨e, he, h⟩
        · rw [h]
        · have := habove e he; rw [h]; exact le_of_lt this
      rw [h1] at hlt ⊢
      rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR] at hlt ⊢
      · simp only [advance_height_eq]
        rw [newest_append_of_length_le _ _ _ (by simp; have := C.K_W_ge_two; omega)]
        exact ⟨_, rfl⟩
      · simp only [advance_height_eq] at hlt ⊢
        obtain ⟨l, hl⟩ := ih (lt_of_le_of_lt hge hlt)
        refine ⟨l.filter (fun e : PendingPair V => decide (h_F' < e.j)), ?_⟩
        show List.filter _ (chainStateOf C p).pending_finality = _
        rw [hl, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
        rw [if_pos hlt]
      · obtain ⟨l, hl⟩ := ih (lt_of_le_of_lt hge hlt)
        refine ⟨l.filter (fun e : PendingPair V => decide (h_F' < e.j)), ?_⟩
        show List.filter _ (chainStateOf C p).pending_finality = _
        rw [hl, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
        rw [if_pos hlt]

end

end

section

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- Copied from `scratch/goldilocks_async/probe_ar3_false.lean:73`.
An entry block `E` compatible with `B`, at a chain-state height at most `B`'s, is `B` or an
ancestor of `B`.

Why: when `B` is an ancestor of `E`, the heights are equal, so `B`'s `T_h` is `E`'s, which is `E`
itself (an entry), and a `T_h` is an ancestor of its block.

Read aloud: `B`'s chain has one entry per height, so an entry at or before `B`'s height that does
not conflict with `B` is on `B`'s chain. -/
theorem ancestorEq_of_entry_compatible_le (C : Config) {B E : Block V}
    (hE : IsEntry C E) (hc : E.AncestorEq B ∨ B.AncestorEq E)
    (hh : (chainStateOf C E).h ≤ (chainStateOf C B).h) : E.AncestorEq B := by
  rcases hc with h | h
  · exact h
  · have hle := chainStateOf_height_mono C h
    have heq : (chainStateOf C B).h = (chainStateOf C E).h := le_antisymm hle hh
    have hT := chainStateOf_T_h_of_same_height C h heq
    unfold IsEntry at hE
    rw [hE] at hT
    rw [← hT]
    exact (chainStateOf_T_h_spec C B).1

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)
set_option linter.unusedSectionVars false

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block compatible with `B` whose chain-state height is greater than `B`'s descends from `B`.

The variables:
- `C`: the parameters; `B`: the block; `E`: the block compatible with `B`.

Read aloud: a block on `B`'s side that is higher than `B` is `B` or a descendant of `B`. -/
theorem descends_of_compatible_higher (C : Config) {B E : Block V}
    (hc : E.AncestorEq B ∨ B.AncestorEq E)
    (hh : (chainStateOf C B).h < (chainStateOf C E).h) : B.AncestorEq E := by
  rcases hc with h | h
  · have := chainStateOf_height_mono C h
    omega_nat
  · exact h

end

end

/-! ## The genesis block's chain state (record migration, step 1c: a theorem the execution proof
`handover_after_fast_block` calls instead of reading `chainStateOf`'s first case) -/

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The chain state of the genesis block has the height `1`: it is the spec's initial chain state
`ChainState.initial`, whose height is `1`.

The variables:
- `C`: the parameters.

Read aloud: the genesis block's chain is at the height one. -/
theorem chainStateOf_genesis_h (C : Config) : (chainStateOf C (Block.genesis : Block V)).h = 1 :=
  by rfl

/-- The chain state of the genesis block took its chain into its height at the genesis block: it is
the spec's initial chain state `ChainState.initial`, whose `T_h` is the genesis block.

The variables:
- `C`: the parameters.

Read aloud: the genesis block's chain entered its height at the genesis block. -/
theorem chainStateOf_genesis_T_h (C : Config) :
    (chainStateOf C (Block.genesis : Block V)).T_h = Block.genesis :=
  by rfl

/-- The chain state of the genesis block has the genesis block as its justified block and the
justification height `0`: it is the spec's initial chain state `ChainState.initial`. Added by the
record migration, step 1f.

The variables:
- `C`: the parameters.

Read aloud: the genesis block's chain has the genesis block justified, at the height zero. -/
theorem chainStateOf_genesis_J (C : Config) :
    (chainStateOf C (Block.genesis : Block V)).J = Block.genesis ∧
      (chainStateOf C (Block.genesis : Block V)).h_j = 0 :=
  ⟨rfl, rfl⟩

end

end GoldilocksCorrectness.Proofs.Routines
