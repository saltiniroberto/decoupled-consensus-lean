module
public import GoldilocksCorrectness.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# What the readers of the FG state answer

The theorems about the readers of an FG state `S`: the fork-choice root `get_fc_root S`
(`get_fc_root_cases`, `root_cases`, `fc_root_eq`, `F_ancestorEq_get_fc_root`,
`fc_root_ancestorEq_of_tall`, `fc_root_compatible`), `head_height_floor S`, the least chain-state
height a viable block may have (`floor_cases`, `floor_le_h_max`, `floor_of_root_ne_J`,
`h_max_sub_one_le_floor`, `h_max_le_floor_add_one`, `h_j_lt_floor_of_root_F`,
`floor_of_boxOne_or_boxThree`, `head_height_floor_le_h_max`), the contest test `fg_contest S`
(`fg_contest_spec`, `fg_contest_true_of`, `h_max_of_contested`, `justified_past_of_contested`,
`not_contested_or_two_past`), the viable heads and the viable descendants (`mem_viable_heads_iff`,
`mem_viable_heads_of`, `has_viable_descendant_of`, `viable_head_descends_of_justified_past`), the
tree of `fg_to_ac S` (`mem_fg_to_ac_tree`), and the attestations of a chain (`on_chain_iff`,
`exists_of_on_chain`, `on_chain_counted`, `pending_pair_along_chain`).

They read an FG state alone: no node state, no execution.

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

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- No attestation is included on the chain of the genesis block: the genesis block includes none
and has no ancestor. Added by the record migration, step 1f.

The variables:
- `a`: the attestation.

Read aloud: nothing is on the genesis block's chain. -/
theorem on_chain_genesis (a : Attestation V) : on_chain a (Block.genesis : Block V) = false := by
  simp [on_chain, attestations_on_chain]

omit [Fintype V] [RootOrder] in
/-- An attestation is included on the chain of `B` exactly when some block that is `B` or an
ancestor of `B` includes it.

The variables:
- `a`: the attestation; `B`: the block. -/
theorem on_chain_iff (a : Attestation V) (B : Block V) :
    on_chain a B = true ↔ ∃ X : Block V, X.AncestorEq B ∧ a ∈ X.attestations := by
  induction B with
  | genesis =>
      constructor
      · intro h
        simp [on_chain, attestations_on_chain] at h
      · rintro ⟨X, hX, ha⟩
        rw [(ancestorEq_genesis_iff X).1 hX] at ha
        exact absurd ha List.not_mem_nil
  | node p s r votes support ats v ih =>
      constructor
      · intro h
        simp only [on_chain, attestations_on_chain, decide_eq_true_eq, List.mem_append] at h
        rcases h with h | h
        · exact ⟨_, ancestorEq_refl _, h⟩
        · obtain ⟨X, hX, ha⟩ := ih.1 (by simp only [on_chain, decide_eq_true_eq]; exact h)
          exact ⟨X, (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr hX), ha⟩
      · rintro ⟨X, hX, ha⟩
        rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hX with rfl | hX
        · exact on_chain_node_of_mem a p s r votes support ats v ha
        · exact on_chain_node_of_parent a p s r votes support ats v (ih.2 ⟨X, hX, ha⟩)

end

section

open GoldilocksCorrectness.Statements.Routines (FinalizedAncestorJustified)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A block is in the tree of the frame the FG state gives the available chain exactly when it is
in the FG state's tree and the finalized block is an ancestor of it, or it.

The variables:
- `S`: the FG state; `B`: the block. -/
theorem mem_fg_to_ac_tree (S : FGState V) (B : Block V) :
    B ∈ (fg_to_ac S).tree ↔ B ∈ S.T ∧ S.F.AncestorEq B := by
  simp [fg_to_ac, Block.AncestorEq]

omit [Fintype V] in
/-- When the finalized block is the justified block or an ancestor of it, the finalized block is
the root of the fork choice `get_fc_root S` or an ancestor of it: that root is the justified block
or the finalized block.

The variables:
- `S`: the FG state.

 -/
theorem F_ancestorEq_get_fc_root (S : FGState V)
    -- the finalized block of `S` is the justified block of `S` or an ancestor of it
    (h : FinalizedAncestorJustified S) :
    S.F.AncestorEq (get_fc_root S) := by
  simp only [get_fc_root, Id.run]
  split
  · exact h
  · exact ancestorEq_refl _

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- An attestation on the chain of `H` is included in `H` or in an ancestor of `H`, other than
the genesis block.

The variables:
- `a`: the attestation; `H`: the block. -/
theorem exists_of_on_chain (a : Attestation V) (H : Block V) (h : on_chain a H = true) :
    ∃ Y : Block V, Y.AncestorEq H ∧ Y ≠ Block.genesis ∧ a ∈ Y.attestations := by
  induction H with
  | genesis =>
      simp [on_chain, attestations_on_chain] at h
  | node p s r votes support ats v ih =>
      simp only [on_chain, attestations_on_chain, decide_eq_true_eq, List.mem_append] at h
      rcases h with h | h
      · exact ⟨_, ancestorEq_refl _, (fun h' => by cases h'), h⟩
      · obtain ⟨Y, hY, hne, ha⟩ := ih (by simpa [on_chain] using h)
        exact ⟨Y, (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr hY), hne, ha⟩

/-- **Kit fact, an attestation on a chain is counted.** When the attestation `a` is on the chain
of `H`, every attestation a non-genesis block of that chain includes is valid against its parent's
chain state, and `a` is at the height of `H`'s chain state, then `a`'s validator is in the progress
set of `H`'s chain state, and in its target participation when `a` is a target.

Why: the block that includes `a` has a parent at height at least `a.h` by validity, hence exactly
`a.h`, the height of `H`; that block counts `a`, and the chain keeps its counts up to `H` at that
height.

The variables:
- `C`: the parameters; `H`: the block; `a`: the attestation.

Read aloud: a vote at the chain's height already included on the chain is already counted. -/
theorem on_chain_counted (C : Config) (H : Block V) (a : Attestation V)
    (hon : on_chain a H = true)
    (hValid : ∀ Y : Block V, Y.AncestorEq H → Y ≠ Block.genesis →
      ∀ a' ∈ Y.attestations, valid_attestation (chainStateOf C Y.parent) a' = true)
    (hh : a.h = (chainStateOf C H).h) :
    a.val_index ∈ (chainStateOf C H).progress ∧
      (a.τ = false → a.val_index ∈ (chainStateOf C H).target_participation) := by
  obtain ⟨Y, hYH, hne, ha⟩ := exists_of_on_chain a H hon
  cases Y with
  | genesis => exact absurd rfl hne
  | node p s r votes support ats v =>
      have hpY : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff p p s r votes support ats v).2 (Or.inr (ancestorEq_refl p))
      have h1 := chainStateOf_height_mono C hpY
      have h2 := chainStateOf_height_mono C hYH
      have hvalid := hValid _ hYH hne a ha
      have hpar : (Block.node p s r votes support ats v).parent = p := rfl
      rw [hpar] at hvalid
      rcases valid_attestation_cases _ a hvalid with ⟨hh', hT'⟩ | hlt
      · have hpH : (chainStateOf C p).h = (chainStateOf C H).h := hh'.symm.trans hh
        have hYeq : (chainStateOf C (.node p s r votes support ats v)).h =
            (chainStateOf C H).h := by
          unfold Height at *
          omega
        obtain ⟨k1, k2⟩ := counted_kept_of_same_height C hYH hYeq
        have hYp : (chainStateOf C (.node p s r votes support ats v)).h =
            (chainStateOf C p).h := hYeq.trans hpH.symm
        rw [chainStateOf_node] at hYp k1 k2
        obtain ⟨tp, pr, fp, F', h_F', -, -, hmem, -, hc⟩ :=
          state_transition_cases C (chainStateOf C p) (.node p s r votes support ats v)
        have hm := hmem a ha hh' hT'
        rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩
        · rw [hR] at hYp
          exact absurd hYp (by dsimp only; unfold Height; omega)
        · rw [hR] at hYp
          exact absurd hYp (by dsimp only; unfold Height; omega)
        · rw [hR] at k1 k2
          exact ⟨k1 hm.1, fun hτ => k2 (hm.2 hτ)⟩
      · exfalso
        unfold Height at *
        omega

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- The `head_height_floor` of an FG state is at most its `h_max`.

The variables:
- `S`: the FG state. -/
theorem floor_le_h_max (S : FGState V) : (head_height_floor S : ℕ) ≤ (S.h_max : ℕ) := by
  simp only [head_height_floor, Id.run]
  split
  · exact Nat.le_refl _
  · exact Nat.sub_le _ _

omit [Fintype V] [RootOrder] in
/-- **A root that is not the justified block puts `head_height_floor` past the cache `h_j`.** In
an FG state `S` with `S.h_j + 1 ≤ S.h_max`, when `get_fc_root S` is not `S.J`,
`head_height_floor S` is at least `S.h_j + 1`.

Why: the root is `S.J` exactly when `S.h_max = S.h_j + 1` and `S` is not contested
(`get_fc_root`). Contested, `head_height_floor S` is `S.h_max = S.h_j + 1` (Lemma 56, box 3). Not
contested with `S.h_max ≠ S.h_j + 1`, `head_height_floor S` is `S.h_max − 1 ≥ S.h_j + 1`.

The variables:
- `S`: the FG state.

Read aloud: a validator whose root is its finalized block finds no block viable at a height at most
its justification height. -/
theorem floor_of_root_ne_J (S : FGState V) (hm : S.h_j + 1 ≤ S.h_max)
    (hroot : get_fc_root S ≠ S.J) : S.h_j + 1 ≤ head_height_floor S := by
  by_cases hc : fg_contest S = true
  · -- box 3: `head_height_floor` is `h_max`
    have hsh := (GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree S hc).2.2
    rw [hsh]
    exact hm
  · have hcf : fg_contest S = false := by simpa using hc
    by_cases hm' : S.h_max = S.h_j + 1
    · -- box 2: the root is `S.J`, against `hroot`
      exact absurd (GoldilocksCorrectness.Statements.Routines.frameShape_of_boxTwo S S.J
        ⟨hm', hcf, rfl⟩).1 hroot
    · -- box 1: `head_height_floor` is `h_max − 1`, and `h_max ≥ h_j + 2`
      have hfl : head_height_floor S = S.h_max - 1 := by
        simp [head_height_floor, hcf]
      rw [hfl]
      unfold Height at *
      omega

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- A contested FG state has `h_max = h_j + 1` and a held block, a descendant of the finalized
block or the finalized block itself, of chain-state height `h_max`, of which the justified block is
not an ancestor (`fg_contest`).

The variables:
- `S`: the FG state. -/
theorem fg_contest_spec (S : FGState V) (h : fg_contest S = true) :
    S.h_max = S.h_j + 1 ∧ ∃ B ∈ S.T, S.F.AncestorEq B ∧ (S.σ B).h = S.h_max ∧
      ¬ S.J.AncestorEq B := by
  simp only [fg_contest, Id.run] at h
  split at h
  · cases h
  · rename_i hne
    refine ⟨Decidable.of_not_not hne, ?_⟩
    exact of_decide_eq_true h

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- A root of an FG state is `L` or an ancestor of `L` when the state holds `L` at the height
`h_max`, on its finalized block's chain.

Why: the root is the justified block only when `h_max` is `h_j + 1` and the state is not
contested; `L`, of height `h_max` on the finalized block's chain, contests it unless the justified
block is `L` or an ancestor of `L`. Otherwise the root is the finalized block.

The variables:
- `St`: the FG state; `L`: the block. -/
theorem fc_root_ancestorEq_of_tall (St : FGState V) (L : Block V) (hLT : L ∈ St.T)
    (hFL : St.F.AncestorEq L) (hLh : (St.σ L).h = St.h_max) :
    (get_fc_root St).AncestorEq L := by
  simp only [get_fc_root, Id.run]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨hbox, hcon⟩ := hc
    by_contra hJL
    have : fg_contest St = true := by
      simp only [fg_contest, Id.run]
      rw [if_neg (by rw [hbox]; exact fun h => h rfl)]
      exact decide_eq_true ⟨L, hLT, hFL, hLh, hJL⟩
    rw [hcon] at this
    exact Bool.false_ne_true this
  · exact hFL

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- The fork-choice root is the justified block, with `h_max = h_j + 1` and the state not
contested; or it is the finalized block, with the state contested or `h_max ≠ h_j + 1`
(`get_fc_root`).

The variables:
- `S`: the FG state. -/
theorem root_cases (S : FGState V) :
    (get_fc_root S = S.J ∧ S.h_max = S.h_j + 1 ∧ fg_contest S = false) ∨
      (get_fc_root S = S.F ∧ (fg_contest S = true ∨ S.h_max ≠ S.h_j + 1)) := by
  by_cases hc : fg_contest S = true
  · right
    refine ⟨?_, Or.inl hc⟩
    simp only [get_fc_root, Id.run, hc]
    simp
    rfl
  · have hcf : fg_contest S = false := by simpa using hc
    by_cases hm : S.h_max = S.h_j + 1
    · left
      refine ⟨?_, hm, hcf⟩
      simp only [get_fc_root, Id.run, hcf, hm]
      simp
      rfl
    · right
      refine ⟨?_, Or.inr hm⟩
      simp only [get_fc_root, Id.run, hm]
      simp
      rfl

omit [Fintype V] [RootOrder] in
/-- A contested FG state has `h_max = h_j + 1` and `head_height_floor = h_max`; one not contested
has `head_height_floor = h_max − 1` (Lemma 56).

The variables:
- `S`: the FG state. -/
theorem floor_cases (S : FGState V) :
    (fg_contest S = true ∧ S.h_max = S.h_j + 1 ∧ head_height_floor S = S.h_max) ∨
      (fg_contest S = false ∧ head_height_floor S = S.h_max - 1) := by
  by_cases hc : fg_contest S = true
  · left
    obtain ⟨he, -, hfl⟩ := GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree S hc
    exact ⟨hc, he, hfl⟩
  · have hcf : fg_contest S = false := by simpa using hc
    right
    refine ⟨hcf, ?_⟩
    simp [head_height_floor, hcf]

omit [Fintype V] [RootOrder] in
/-- `head_height_floor` is at least `h_max − 1`.

The variables:
- `S`: the FG state. -/
theorem h_max_sub_one_le_floor (S : FGState V) : S.h_max - 1 ≤ head_height_floor S := by
  rcases floor_cases S with ⟨-, -, h⟩ | ⟨-, h⟩ <;> rw [h]
  exact Nat.sub_le _ _

omit [Fintype V] [RootOrder] in
/-- **The `head_height_floor` of an FG state that is not contested.** When `fg_contest S` is
`false`, `head_height_floor S`, the least chain-state height a viable block of `S` may have, is
`S.h_max − 1`.

Why: the second case of `floor_cases`; its first case has `fg_contest S = true`.

The variables:
- `S`: the FG state.

Read aloud: when the FG state is not contested, the least chain-state height a viable block may
have is one less than the greatest chain-state height `S.h_max`.

Added by the record migration, step 1d, for the execution proofs that opened
`head_height_floor` with `simp only [head_height_floor, Id.run, …]`. -/
theorem head_height_floor_of_not_contested (S : FGState V) (hc : fg_contest S = false) :
    head_height_floor S = S.h_max - 1 := by
  rcases floor_cases S with ⟨h, -, -⟩ | ⟨-, h⟩
  · rw [hc] at h
    cases h
  · exact h

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- In the second case of `get_fc_root` (the root the finalized block: contested, or
`h_max ≠ h_j + 1`), `head_height_floor` is greater than the cache `h_j`, given `h_j < h_max`.

The variables:
- `S`: the FG state. -/
theorem h_j_lt_floor_of_root_F (S : FGState V) (hm : S.h_j < S.h_max)
    (hor : fg_contest S = true ∨ S.h_max ≠ S.h_j + 1) : S.h_j < head_height_floor S := by
  rcases floor_cases S with ⟨-, hme, hfl1⟩ | ⟨hcf, hfl1⟩
  · rw [hfl1, hme]
    exact Nat.lt_succ_self _
  · rcases hor with hc | hne
    · rw [hcf] at hc
      cases hc
    · rw [hfl1]
      unfold Height at *
      omega

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- An FG state with `h_max = h_j + 1` and a held block, a descendant of the finalized block or the
finalized block itself, of chain-state height `h_max` that is not a descendant of the justified
block nor the justified block, is contested.

The variables:
- `S`: the FG state; `B`: the block. -/
theorem fg_contest_true_of (S : FGState V) (B : Block V) (hm : S.h_max = S.h_j + 1)
    (hB : B ∈ S.T) (hFB : S.F.AncestorEq B) (hh : (S.σ B).h = S.h_max)
    (hJB : ¬ S.J.AncestorEq B) : fg_contest S = true := by
  simp only [fg_contest, Id.run]
  rw [if_neg (by rw [hm]; exact fun h => h rfl)]
  exact decide_eq_true ⟨B, hB, hFB, hh, hJB⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- The root of the frame's fork choice is `get_fc_root`.

The variables:
- `S`: the FG state. -/
theorem fc_root_eq (S : FGState V) : (fg_to_ac S).fc_root = get_fc_root S := by rfl

omit [Fintype V] [RootOrder] in
/-- **The finalized block of `fg_to_ac S` is the FG state's.** The record `fg_to_ac S` carries
the finalized block `S.F` of the FG state `S` unchanged.

Why: `fg_to_ac` builds its record with `F := S.F`.

The variables:
- `S`: the FG state.

Read aloud: the finalized block of the record `fg_to_ac S` is the finalized block of `S`.

Added by the record migration, step 1d, for the execution proofs that read
`(fg_to_ac S).F` as `S.F` through the body of `fg_to_ac`. -/
theorem fg_to_ac_F (S : FGState V) : (fg_to_ac S).F = S.F := by rfl

omit [Fintype V] [RootOrder] in
/-- The root of the fork choice is the justified block or the finalized block.

The variables:
- `S`: the FG state. -/
theorem get_fc_root_cases (S : FGState V) : get_fc_root S = S.J ∨ get_fc_root S = S.F := by
  simp only [get_fc_root, Id.run]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **Kit theorem, a pending justification along a chain.** When `h_F(B) < h_j(B)`, `B` is `X` or
an ancestor of `X`, and every block from `B` to `X` has a justification height at most `h(B)`:
the chain state of `X` finalizes at a height at least `h_j(B)`, or keeps the pair
`(h_j(B), J(B))` pending, with at most one pending pair after it, and counts at `h_j(B)` the
validator of every attestation with the finality pair `(h_j(B), J(B))` on `X`'s chain and not on
`B`'s.

Why: by induction on `X`. At `B`, the pair is the last pending one (`chainStateOf_pending_last`);
each transition after `B` keeps it, or finalizes at least its height (`pending_pair_step`), the
height staying at least `h(B)` (Lemma 47 (d)); a block's attestations are on its chain, the
others on its parent's; and the finalization height only rises.

The variables:
- `C`: the parameters; `B`: the first block; `X`: its descendant. -/
theorem pending_pair_along_chain (C : Config) (B X : Block V) (hBX : B.AncestorEq X)
    (hlt : (chainStateOf C B).h_F < (chainStateOf C B).h_j)
    (hbound : ∀ Y : Block V, B.AncestorEq Y → Y.AncestorEq X →
      (chainStateOf C Y).h_j ≤ (chainStateOf C B).h) :
    (chainStateOf C B).h_j ≤ (chainStateOf C X).h_F ∨
      ((∃ l₁ l₂ : List (PendingPair V), (chainStateOf C X).pending_finality =
          l₁ ++ PendingPair.mk (chainStateOf C B).h_j (chainStateOf C B).J :: l₂ ∧
          (l₂ = [] ∨ (l₂.length = 1 ∧ (chainStateOf C B).h + 1 ≤ (chainStateOf C X).h))) ∧
        ∀ a : Attestation V,
          a.finality_pair = some (FinalityPair.mk (chainStateOf C B).h_j (chainStateOf C B).J.root) →
          on_chain a X = true →
          on_chain a B = true ∨
            a.val_index ∈ (chainStateOf C X).finality_participation (chainStateOf C B).h_j) := by
  -- the case `X = B`
  have hbase : (chainStateOf C B).h_j ≤ (chainStateOf C B).h_F ∨
      ((∃ l₁ l₂ : List (PendingPair V), (chainStateOf C B).pending_finality =
          l₁ ++ PendingPair.mk (chainStateOf C B).h_j (chainStateOf C B).J :: l₂ ∧
          (l₂ = [] ∨ (l₂.length = 1 ∧ (chainStateOf C B).h + 1 ≤ (chainStateOf C B).h))) ∧
        ∀ a : Attestation V,
          a.finality_pair = some (FinalityPair.mk (chainStateOf C B).h_j (chainStateOf C B).J.root) →
          on_chain a B = true →
          on_chain a B = true ∨
            a.val_index ∈ (chainStateOf C B).finality_participation (chainStateOf C B).h_j) := by
    obtain ⟨l, hl⟩ := chainStateOf_pending_last C B hlt
    exact Or.inr ⟨⟨l, [], hl, Or.inl rfl⟩, fun a _ ha => Or.inl ha⟩
  induction X with
  | genesis =>
      rw [(ancestorEq_genesis_iff B).1 hBX] at hbase ⊢
      exact hbase
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hBX with heq | hBp
      · rw [← heq]; exact hbase
      have hpX : p.AncestorEq (Block.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      have hmonoF := (chainStateOf_h_j_h_F_mono_parent C p s r votes support ats v).2
      rcases ih hBp (fun Y h1 h2 => hbound Y h1 (ancestorEq_trans h2 hpX)) with hle | ⟨hshape, hpart⟩
      · exact Or.inl (le_trans hle hmonoF)
      have hBh := (lem47_chain_state_heights C B B).1
      have hhp := (lem47_chain_state_heights C B p).2.2.2.1 hBp
      have hJX := hbound _ hBX (ancestorEq_refl _)
      rw [chainStateOf_node] at hJX ⊢
      rcases pending_pair_step C (chainStateOf C p) (.node p s r votes support ats v)
          (PendingPair.mk (chainStateOf C B).h_j (chainStateOf C B).J) (chainStateOf C B).h
          hshape hBh.2.1 hhp hJX with hle | ⟨hshape', hmono, hadd⟩
      · exact Or.inl hle
      refine Or.inr ⟨hshape', fun a hp hon => ?_⟩
      simp only [on_chain, attestations_on_chain, decide_eq_true_eq, List.mem_append] at hon
      rcases hon with hin | hin
      · exact Or.inr (hadd a hin hp)
      · rcases hpart a hp (by simpa [on_chain] using hin) with h | h
        · exact Or.inl h
        · exact Or.inr (hmono _ h)

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- `head_height_floor` is at most the greatest chain-state height. -/
theorem head_height_floor_le_h_max (S : FGState V) : head_height_floor S ≤ S.h_max := by
  simp only [head_height_floor, Id.run]
  split
  · exact le_refl S.h_max
  · exact Nat.sub_le S.h_max 1

omit [Fintype V] [RootOrder] in
/-- A block of the tree at a chain-state height at least `S.h_max` is a viable descendant of each
of its ancestors. -/
theorem has_viable_descendant_of (S : FGState V) (B X : Block V) (hX : X ∈ S.T)
    (hBX : B.AncestorEq X) (hh : S.h_max ≤ (S.σ X).h) : has_viable_descendant S B = true := by
  simp only [has_viable_descendant, decide_eq_true_eq]
  refine ⟨X, hX, hBX, ?_⟩
  simp only [is_viable, decide_eq_true_eq]
  exact le_trans (head_height_floor_le_h_max S) hh

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section

open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)

omit [RootOrder] in
/-- **Not contested, or `h_max` at least `h(B) + 2`.** Copied from
`scratch/goldilocks_async/probe_ar3_false.lean:127`. At an FG state `n` whose chain states are
computed, whose justified block `n.J` is compatible with `B`, is an entry, has the chain-state
height `n.h_j`, with `H < n.h_j`; when, for every held block `D`, every progress certificate on
`D`'s chain at a height `h > H` for a block `T` of `D`'s chain at height `h` has `T` compatible
with `B`: `fg_contest n = false`, or `h(B) + 2 ≤ n.h_max`.

Why: contested means `h_max = h_j + 1` and a held block `D` at height `h_max` of which `J` is not
an ancestor. When `h_j ≥ h(B) + 1`, `h_max ≥ h(B) + 2`. Otherwise `h_j ≤ h(B)`: `D`'s chain
passed height `h_j`, so (Lemma 67) it holds a progress certificate at `h_j` for its own entry `T'`
at `h_j`, an ancestor of `D`; the certificate clause makes `T'` compatible with `B`; `T'` and `J`
are then two entries compatible with `B` at one height at most `h(B)`, so one block
(`entry_eq_of_compatible_le`), and `J = T'` is an ancestor of `D`: not contested.

Read aloud: inside and after the period, a contest can only be between two descendants of `B`,
and then the block at the top height is a descendant of `B`. -/
theorem not_contested_or_two_past (C : Config) (n : FGState V) (B : Block V) (H : ℕ)
    (hσ : ChainStatesComputed C n)
    (hJ : n.J.AncestorEq B ∨ B.AncestorEq n.J) (hJE : IsEntry C n.J)
    (hJh : (chainStateOf C n.J).h = n.h_j) (hHj : H < n.h_j)
    (hCert : ∀ D ∈ n.T, ∀ (h : Height) (T : Block V), T.AncestorEq D →
      ProgressCertOn D h T → H < h → (chainStateOf C T).h = h →
      (T.AncestorEq B ∨ B.AncestorEq T)) :
    fg_contest n = false ∨ (chainStateOf C B).h + 2 ≤ n.h_max := by
  by_cases hmax : n.h_max = n.h_j + 1
  swap
  · left
    simp only [fg_contest, Id.run]
    rw [if_pos hmax]
    rfl
  by_cases hB : (chainStateOf C B).h + 1 ≤ n.h_j
  · right
    omega_nat
  left
  simp only [fg_contest, Id.run]
  rw [if_neg (by rw [hmax]; exact fun h => h rfl)]
  refine decide_eq_false ?_
  rintro ⟨D, hD, _, hDh, hJD⟩
  apply hJD
  show n.J.AncestorEq D
  change (n.σ D).h = n.h_max at hDh
  rw [hσ D hD, hmax] at hDh
  have h1 : 1 ≤ n.h_j := by omega_nat
  obtain ⟨Y, hYD, -, hYph, -, hTY, hcert⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem67_first_advance C D n.h_j h1
      (by rw [hDh]; omega_nat)
  have hT'D : (chainStateOf C Y.parent).T_h.AncestorEq D := ancestorEq_trans hTY hYD
  have hT'h : (chainStateOf C (chainStateOf C Y.parent).T_h).h = n.h_j := by
    rw [(GoldilocksCorrectness.Proofs.Routines.isEntry_T_h C Y.parent).2.1, hYph]
  -- the certificate on `Y`'s chain is on `D`'s chain
  have hcertD : ProgressCertOn D n.h_j (chainStateOf C Y.parent).T_h := by
    obtain ⟨A, hA, hv⟩ := hcert
    refine ⟨A, hA, fun v hvA => ?_⟩
    obtain ⟨a, h1, h2, h3, h4⟩ := hv v hvA
    exact ⟨a, h1, h2, h3, on_chain_mono a hYD h4⟩
  have hT'B := hCert D hD n.h_j _ hT'D hcertD hHj hT'h
  have hT'E : IsEntry C (chainStateOf C Y.parent).T_h := (GoldilocksCorrectness.Proofs.Routines.isEntry_T_h C Y.parent).1
  have hEq : (chainStateOf C Y.parent).T_h = n.J :=
    entry_eq_of_compatible_le C hT'E hJE hT'B hJ (by rw [hT'h, hJh])
      (by rw [hT'h]; omega_nat)
  rw [← hEq]
  exact hT'D

end

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- A block of an FG state's tree that descends from its finalized block and from the root of
its fork choice, at a chain-state height at least `head_height_floor`, is a viable head of its
frame, when the chain states are computed.

The variables:
- `C`: the parameters; `n`: the FG state; `W`: the block. -/
theorem mem_viable_heads_of (C : Config) (n : FGState V) (W : Block V)
    (hσ : ChainStatesComputed C n) (hWT : W ∈ n.T) (hFW : n.F.AncestorEq W)
    (hrW : (get_fc_root n).AncestorEq W) (hfl : head_height_floor n ≤ (chainStateOf C W).h) :
    W ∈ (fg_to_ac n).viable_heads := by
  have hWΦ : W ∈ (fg_to_ac n).tree := (mem_fg_to_ac_tree _ _).2 ⟨hWT, hFW⟩
  show W ∈ ({D ∈ (fg_to_ac n).tree | (get_fc_root n).ancestorEq D && is_viable n D} :
    Finset (Block V))
  rw [Finset.mem_filter]
  refine ⟨hWΦ, ?_⟩
  have h1 : (get_fc_root n).ancestorEq W = true := hrW
  have h2 : is_viable n W = true := by
    simp only [is_viable, decide_eq_true_eq]
    show head_height_floor n ≤ (n.σ W).h
    rw [hσ W hWT]
    exact hfl
  rw [h1, h2]
  rfl

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)
set_option linter.unusedSectionVars false
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A contested FG state has `h_max = h_j + 1`.

The variables:
- `n`: the FG state.

Read aloud: an FG state is contested only when its greatest height is one past its justification
height. -/
theorem h_max_of_contested (n : FGState V) (hc : fg_contest n = true) :
    n.h_max = n.h_j + 1 := by
  by_contra hne
  simp only [fg_contest, Id.run] at hc
  rw [if_pos hne] at hc
  exact absurd hc (by decide)

/-- At an FG state whose chain states are computed, whose justified block is compatible with `B`
and has the chain-state height `h_j`, whose held blocks two heights past `B` descend from `B`,
with `h_j < h_max` and `h(B) + 1 ≤ h_j`: every viable head of its frame descends from `B`.

The variables:
- `C`: the parameters; `n`: the FG state; `B`: the block.

Read aloud: at a state justified past `B` whose caches are compatible with `B`, every viable head
is `B` or a descendant of `B`. -/
theorem viable_head_descends_of_justified_past (C : Config) (n : FGState V) (B : Block V)
    (hσ : ChainStatesComputed C n)
    (hJ : n.J.AncestorEq B ∨ B.AncestorEq n.J)
    (hJh : (chainStateOf C n.J).h = n.h_j)
    (hTwo : ∀ D ∈ n.T, (chainStateOf C B).h + 2 ≤ (chainStateOf C D).h → B.AncestorEq D)
    (hjmax : n.h_j < n.h_max)
    (hSafe : (chainStateOf C B).h + 1 ≤ n.h_j) :
    ∀ W ∈ (fg_to_ac n).viable_heads, B.AncestorEq W := by
  intro W hW
  have hW' : W ∈ {X ∈ {X ∈ n.T | n.F.ancestorEq X} |
      (get_fc_root n).ancestorEq X && is_viable n X} := hW
  rw [Finset.mem_filter, Bool.and_eq_true] at hW'
  obtain ⟨hWT', hroot, hv⟩ := hW'
  have hWT : W ∈ n.T := (Finset.mem_filter.1 hWT').1
  simp only [is_viable, decide_eq_true_eq] at hv
  change head_height_floor n ≤ (n.σ W).h at hv
  rw [hσ W hWT] at hv
  by_cases hc : fg_contest n = true
  · have hfl : head_height_floor n = n.h_max := by simp [head_height_floor, hc]
    have hm := h_max_of_contested n hc
    rw [hfl] at hv
    exact hTwo W hWT (by omega_nat)
  · have hc' : fg_contest n = false := by
      cases h : fg_contest n
      · rfl
      · exact absurd h hc
    have hfl : head_height_floor n = n.h_max - 1 := by simp [head_height_floor, hc']
    rw [hfl] at hv
    by_cases hm : n.h_max = n.h_j + 1
    · have hr : get_fc_root n = n.J := by simp [get_fc_root, hm, hc']
      rw [hr] at hroot
      have hBJ := GoldilocksCorrectness.Proofs.Routines.descends_of_compatible_higher C hJ (by rw [hJh]; omega_nat)
      exact ancestorEq_trans hBJ hroot
    · exact hTwo W hWT (by omega_nat)

/-- The root of the fork choice is compatible with `B` when the justified block is, and the
finalized block is an ancestor of the justified block.

The variables:
- `n`: the FG state; `B`: the block.

Read aloud: the fork choice starts from a block compatible with `B` when the caches are. -/
theorem fc_root_compatible (n : FGState V) (B : Block V)
    (hJ : n.J.AncestorEq B ∨ B.AncestorEq n.J) (hFJ : n.F.AncestorEq n.J) :
    (get_fc_root n).compatible B = true := by
  have hF : n.F.compatible B = true := by
    rcases hJ with h | h
    · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ h))
    · exact (compatible_iff _ _).2 (ancestorEq_compatible hFJ h)
  by_cases h : (n.h_max = n.h_j + 1 && !fg_contest n) = true
  · have hr : get_fc_root n = n.J := by simp only [get_fc_root, Id.run]; rw [if_pos h]; rfl
    rw [hr]
    exact (compatible_iff _ _).2 hJ
  · have hr : get_fc_root n = n.F := by simp only [get_fc_root, Id.run]; rw [if_neg h]; rfl
    rw [hr]
    exact hF

/-- Under the hypotheses of the landed `not_contested_or_two_past`, a contested FG state has a
justification height at least `h(B) + 1`.

The variables:
- `C`: the parameters; `n`: the FG state; `B`: the block; `H`: the height threshold.

Read aloud: inside and after the period, only a state justified past `B` can be contested. -/
theorem justified_past_of_contested (C : Config) (n : FGState V) (B : Block V) (H : ℕ)
    (hσ : ChainStatesComputed C n)
    (hJ : n.J.AncestorEq B ∨ B.AncestorEq n.J) (hJE : IsEntry C n.J)
    (hJh : (chainStateOf C n.J).h = n.h_j) (hHj : H < n.h_j)
    (hCert : ∀ D ∈ n.T, ∀ (h : Height) (T : Block V), T.AncestorEq D →
      GoldilocksCorrectness.Statements.Routines.ProgressCertOn D h T → H < h →
      (chainStateOf C T).h = h → (T.AncestorEq B ∨ B.AncestorEq T))
    (hc : fg_contest n = true) : (chainStateOf C B).h + 1 ≤ n.h_j := by
  have hm := h_max_of_contested n hc
  rcases not_contested_or_two_past C n B H hσ hJ hJE hJh hHj hCert with h | h
  · rw [hc] at h; exact absurd h (by decide)
  · omega_nat

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- The cache `h_max` is at most `head_height_floor` plus one: `head_height_floor` is `h_max` or `h_max − 1`.

The variables:
- `S`: the FG state. -/
theorem h_max_le_floor_add_one (S : FGState V) : S.h_max ≤ head_height_floor S + 1 := by
  simp only [head_height_floor, Id.run]
  split
  · exact Nat.le_succ _
  · exact Nat.le_add_of_sub_le le_rfl

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (BoxOne BoxThree frameShape_of_boxOne
  frameShape_of_boxThree)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- **Kit fact, the frame of an FG state in box 1 or box 3 from bounds on `h_max`.** When the
state is in box 1 with `lo ≤ h_max − 1` and `h_max ≤ hi + 1`, or in box 3 with `lo ≤ h_max` and
`h_max ≤ hi`: its fork-choice root is its finalized block, its `head_height_floor` is between `lo`
and `hi`, and its cache `h_j` is less than `hi`.

Why: Lemma 56's box forms; in box 1 `h_j + 1 < h_max`, in box 3 `h_max = h_j + 1`.

The variables:
- `St`: the FG state; `lo`, `hi`: the bounds. -/
theorem floor_of_boxOne_or_boxThree (St : FGState V) (lo hi : ℕ)
    (h : (BoxOne St ∧ lo ≤ St.h_max - 1 ∧ St.h_max ≤ hi + 1) ∨
      (BoxThree St ∧ lo ≤ St.h_max ∧ St.h_max ≤ hi)) :
    get_fc_root St = St.F ∧ lo ≤ head_height_floor St ∧ head_height_floor St ≤ hi ∧
      St.h_j < hi := by
  rcases h with ⟨hb, hlo, hhi⟩ | ⟨hb, hlo, hhi⟩
  · have hS := frameShape_of_boxOne St hb
    have hb' : St.h_j + 1 < St.h_max := hb
    refine ⟨hS.2.1, ?_, ?_, ?_⟩
    · rw [hS.2.2]; exact hlo
    · rw [hS.2.2]; unfold Height at *; omega
    · unfold Height at *; omega
  · have hS := frameShape_of_boxThree St hb
    refine ⟨hS.2.1, ?_, ?_, ?_⟩
    · rw [hS.2.2]; exact hlo
    · rw [hS.2.2]; exact hhi
    · have := hS.1; unfold Height at *; omega

end

section

open Goldilocks
variable {V : Type} [DecidableEq V]

/-- A block is a viable head of the frame the FG state gives the available chain exactly when it
is in the FG state's tree, the finalized block is an ancestor of it or it, the frame's fork-choice
root is an ancestor of it or it, and its chain-state height is at least
`head_height_floor S`.

The variables:
- `S`: the FG state; `B`: the block. -/
theorem mem_viable_heads_iff (S : FGState V) (B : Block V) :
    B ∈ (fg_to_ac S).viable_heads ↔
      B ∈ S.T ∧ S.F.AncestorEq B ∧ (fg_to_ac S).fc_root.AncestorEq B ∧
        head_height_floor S ≤ (S.σ B).h := by
  simp [fg_to_ac, is_viable, Block.AncestorEq, and_assoc]
  -- `S.σ[B]` is the bracket read of `funGetElem`, `S.σ B` by definition
  exact fun _ _ _ => Iff.rfl

end

section

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **The viability test of a block, as a condition.** `is_viable S B` answers `true` exactly when
the chain-state height `S` holds for `B` is at least `head_height_floor S`, the least chain-state
height a viable block may have.

The variables:
- `S`: the FG state; `B`: the block.

Read aloud: a block is viable when its chain-state height is at least `head_height_floor S`. -/
theorem is_viable_iff (S : FGState V) (B : Block V) :
    is_viable S B = true ↔ head_height_floor S ≤ (S.σ B).h := by
  simp only [is_viable, decide_eq_true_eq]
  rfl

end

end GoldilocksCorrectness.Proofs.Routines
