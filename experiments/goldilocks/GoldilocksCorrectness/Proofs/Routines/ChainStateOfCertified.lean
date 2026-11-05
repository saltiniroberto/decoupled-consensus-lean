module
public import GoldilocksCorrectness.Proofs.Routines.Accountable
public import GoldilocksCorrectness.Statements.Routines.ChainStateStatements

@[expose] public section

/-!
# The chain state of a block, with the certificates

The theorems about `chainStateOf` whose proofs read the certificate facts of
`Proofs/Routines/Certificates.lean` or `Proofs/Routines/Accountable.lean`: the finalized block of a
chain state is an ancestor of its justified block (`chainStateOf_F_ancestorEq`,
`chainStateOf_F_ancestorEq_J`), the justified block is an entry block (`chainStateOf_J_isEntry`,
`entry_eq_of_compatible_le`), and `round_justified_of_spacing3`.

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
/-- **C5, the next opening within `δt` of the entry inherits the justification.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`. Why: the block `Y`, `B'`
or an ancestor of `B'`, that took `B'`'s chain from `B`'s height `h` to `h + 1` (Lemma 67) has its
parent at `B`'s entry's height on `B'`'s chain, so the parent's `T_h` is `B`'s; its height events
took the justification branch, which sets `h_j` to `h`, or the timeout branch, whose test
`T_h.slot + δt ≤ Y.slot` fails for a strict ancestor of `B'` (its slot is less than `B'`'s); and
when `Y` is `B'`, `B'`'s parent is at `h`, and the justification clause gives `h_j(B') = h`. The
justification height never decreases along a chain (`chainStateOf_h_j_h_F_mono`). -/
theorem round_justified_of_spacing3 (C : Config) (B B' : Block V)
    (hBB' : B.AncestorEq B') (hh : (chainStateOf C B).h + 1 ≤ (chainStateOf C B').h)
    (hslot : B'.slot ≤ (chainStateOf C B).T_h.slot + C.δt)
    (hanc : ∀ Y : Block V, Y.AncestorEq B' → Y ≠ B' → Y.slot < B'.slot)
    (hJ : (chainStateOf C B'.parent).h = (chainStateOf C B).h →
      (chainStateOf C B').h_j = (chainStateOf C B).h ∧
      (chainStateOf C B').J = (chainStateOf C B).T_h) :
    (chainStateOf C B).h ≤ (chainStateOf C B').h_j := by
  have h1 : 1 ≤ (chainStateOf C B).h := (lem47_chain_state_heights C B B).1.1
  obtain ⟨Y, hYB', hYg, hYp, hYh, -, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem67_first_advance C B' (chainStateOf C B).h h1
      (by unfold Height at *; omega)
  cases Y with
  | genesis => exact absurd rfl hYg
  | node p s r votes support ats v =>
    change (chainStateOf C p).h = (chainStateOf C B).h at hYp
    have hpY : p.AncestorEq (Block.node p s r votes support ats v) :=
      (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
    have hpB' : p.AncestorEq B' := ancestorEq_trans hpY hYB'
    have hT : (chainStateOf C p).T_h = (chainStateOf C B).T_h := by
      rcases ancestorEq_compatible hpB' hBB' with h | h
      · exact (lem47_chain_state_heights C p B).2.2.2.2 h hYp
      · exact ((lem47_chain_state_heights C B p).2.2.2.2 h hYp.symm).symm
    have hmono := (chainStateOf_h_j_h_F_mono C _ B' hYB').1
    obtain ⟨tp, pr, fp, F', h_F', -, -, -, -, hc⟩ :=
      state_transition_cases C (chainStateOf C p) (Block.node p s r votes support ats v)
    rw [chainStateOf_node] at hYh hmono
    rcases hc with ⟨-, hR⟩ | ⟨-, -, hδ, hR⟩ | ⟨-, -, hR⟩
    · rw [hR] at hmono
      change (chainStateOf C p).h ≤ (chainStateOf C B').h_j at hmono
      rw [hYp] at hmono
      exact hmono
    · by_cases hYeq : Block.node p s r votes support ats v = B'
      · subst hYeq
        exact le_of_eq (hJ hYp).1.symm
      · have hlt := hanc _ hYB' hYeq
        change (chainStateOf C p).T_h.slot + C.δt ≤ s at hδ
        change s < B'.slot at hlt
        rw [hT] at hδ
        unfold Slot at *
        omega
    · rw [hR] at hYh
      change (chainStateOf C p).h = (chainStateOf C B).h + 1 at hYh
      unfold Height at *
      omega

end

end

section

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf lem47f_justified_is_entry)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (lem66_chain_state_certified)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- A block's finalized block is the block or an ancestor of it. -/
theorem chainStateOf_F_ancestorEq (C : Config) (D : Block V) :
    (chainStateOf C D).F.AncestorEq D := by
  by_cases h0 : (chainStateOf C D).h_F = 0
  · rw [GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis C D h0]
    exact genesis_ancestorEq D
  exact ((lem66_chain_state_certified C D).2.2 (by omega_nat)).2.2.1

omit [RootOrder] in
/-- A block's justified block, at a justification height at least `1`, is its own `T_h`. -/
theorem chainStateOf_J_isEntry (C : Config) (D : Block V)
    (h1 : 1 ≤ (chainStateOf C D).h_j) : IsEntry C (chainStateOf C D).J := by
  obtain ⟨Y, -, -, hY⟩ := lem47f_justified_is_entry C D _ rfl h1
  rw [← hY]
  exact (isEntry_T_h C Y).1

omit [RootOrder] in
/-- A block's finalized block is its justified block or an ancestor of it.

Why: both are the block or ancestors of it; when the justified block is an ancestor of the
finalized one, their heights `h_j ≥ h_F` force one height, and both are entries
(`justification_witness_of_finalized`, Lemma 47 (f)), so they are one block. -/
theorem chainStateOf_F_ancestorEq_J (C : Config) (D : Block V) :
    (chainStateOf C D).F.AncestorEq (chainStateOf C D).J := by
  by_cases h0 : (chainStateOf C D).h_F = 0
  · rw [GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis C D h0]
    exact genesis_ancestorEq _
  have h1 : 1 ≤ (chainStateOf C D).h_F := by omega_nat
  obtain ⟨-, -, hFD, hFh⟩ := (lem66_chain_state_certified C D).2.2 h1
  have hb := (lem47_chain_state_heights C D D).1
  have hj1 : 1 ≤ (chainStateOf C D).h_j := le_trans h1 hb.2.2
  obtain ⟨-, hJD, hJh⟩ := (lem66_chain_state_certified C D).1 hj1
  rcases ancestorEq_compatible hFD hJD with hFJ | hJF
  · exact hFJ
  · have hle := (lem47_chain_state_heights C _ _).2.2.2.1 hJF
    have heq : (chainStateOf C (chainStateOf C D).J).h =
        (chainStateOf C (chainStateOf C D).F).h := by
      rw [hJh, hFh] at hle ⊢
      exact le_antisymm hle hb.2.2
    have hT := (lem47_chain_state_heights C _ _).2.2.2.2 hJF heq
    have hJe := chainStateOf_J_isEntry C D hj1
    obtain ⟨Y, -, hYj, hYJ⟩ :=
      GoldilocksCorrectness.Proofs.Routines.justification_witness_of_finalized C D h1
    have hFe : IsEntry C (chainStateOf C D).F := by
      have h := chainStateOf_J_isEntry C Y (by rw [hYj]; exact h1)
      rw [hYJ] at h
      exact h
    unfold IsEntry at hJe hFe
    rw [hJe, hFe] at hT
    rw [hT]
    exact ancestorEq_refl _

end

end

section

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- Copied from `scratch/goldilocks_async/probe_ar3_false.lean:90`.
Two entry blocks compatible with `B`, at one chain-state height at most `B`'s, are one block.

Read aloud: at a height at most `B`'s, there is one entry that does not conflict with `B`. -/
theorem entry_eq_of_compatible_le (C : Config) {B E E' : Block V}
    (hE : IsEntry C E) (hE' : IsEntry C E')
    (hc : E.AncestorEq B ∨ B.AncestorEq E) (hc' : E'.AncestorEq B ∨ B.AncestorEq E')
    (hh : (chainStateOf C E).h = (chainStateOf C E').h)
    (hle : (chainStateOf C E).h ≤ (chainStateOf C B).h) : E = E' := by
  have h1 := ancestorEq_of_entry_compatible_le C hE hc hle
  have h2 := ancestorEq_of_entry_compatible_le C hE' hc' (by rw [← hh]; exact hle)
  rcases ancestorEq_compatible h1 h2 with h | h
  · have := (GoldilocksCorrectness.Statements.Routines.lem47_chain_state_heights C E E').2.2.2.2
      h hh
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this
  · have := (GoldilocksCorrectness.Statements.Routines.lem47_chain_state_heights C E' E).2.2.2.2
      h hh.symm
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this.symm

end

end

end GoldilocksCorrectness.Proofs.Routines
