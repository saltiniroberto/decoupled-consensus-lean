module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Accountable
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified

@[expose] public section

/-!
# ChainStateOfCertified, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/ChainStateOfCertified.lean` over a model `M`
whose facts `F` hold: the justification inherited within `δt` of an entry, the finalized block an
ancestor of the block and of the justified block, the justified block an entry block, and two entry
blocks compatible with a block at one height are one.

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_compatible ancestorEq_refl
  genesis_ancestorEq)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **C5, the next opening within `δt` of the entry inherits the justification.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`. Why: the block `Y`, `B'`
or an ancestor of `B'`, that took `B'`'s chain from `B`'s height `h` to `h + 1` (Lemma 67) has its
parent at `B`'s entry's height on `B'`'s chain, so the parent's `T_h` is `B`'s; its height events
took the justification branch, which sets `h_j` to `h`, or the timeout branch, whose test
`T_h.slot + δt ≤ Y.slot` fails for a strict ancestor of `B'` (its slot is less than `B'`'s); and
when `Y` is `B'`, `B'`'s parent is at `h`, and the justification clause gives `h_j(B') = h`. The
justification height never decreases along a chain (`chainStateOf_h_j_h_F_mono`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a later block on the chain, within `δt` slots of the entry's slot, has inherited the justification at the entry's height. -/
theorem round_justified_of_spacing3 (C : Config) (B B' : Block V)
    (hBB' : B.AncestorEq B') (hh : (M.chainStateOf C B).h + 1 ≤ (M.chainStateOf C B').h)
    (hslot : B'.slot ≤ (M.chainStateOf C B).T_h.slot + C.δt)
    (hanc : ∀ Y : Block V, Y.AncestorEq B' → Y ≠ B' → Y.slot < B'.slot)
    (hJ : (M.chainStateOf C B'.parent).h = (M.chainStateOf C B).h →
      (M.chainStateOf C B').h_j = (M.chainStateOf C B).h ∧
      (M.chainStateOf C B').J = (M.chainStateOf C B).T_h) :
    (M.chainStateOf C B).h ≤ (M.chainStateOf C B').h_j :=
  F.cs.round_justified_of_spacing3 C B B' hBB' hh hslot hanc hJ

/-- A block's finalized block is the block or an ancestor of it.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a block's finalized block is the block or an ancestor of it. -/
theorem chainStateOf_F_ancestorEq (C : Config) (D : Block V) :
    (M.chainStateOf C D).F.AncestorEq D := by
  by_cases h0 : (M.chainStateOf C D).h_F = 0
  · rw [(chainStateOf_F_genesis M F) C D h0]
    exact genesis_ancestorEq D
  exact (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) C D).2.2 (by omega_nat)).2.2.1

/-- A block's justified block, at a justification height at least `1`, is its own `T_h`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a justified block at a height at least `1` is an entry block. -/
theorem chainStateOf_J_isEntry (C : Config) (D : Block V)
    (h1 : 1 ≤ (M.chainStateOf C D).h_j) :
    IsEntry M C (M.chainStateOf C D).J := by
  obtain ⟨Y, -, -, hY⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem47f_justified_is_entry M F) C D _ rfl h1
  rw [← hY]
  exact ((isEntry_T_h M F) C Y).1

/-- A block's finalized block is its justified block or an ancestor of it.

Why: both are the block or ancestors of it; when the justified block is an ancestor of the
finalized one, their heights `h_j ≥ h_F` force one height, and both are entries
(`justification_witness_of_finalized`, Lemma 47 (f)), so they are one block.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a block's finalized block is its justified block or an ancestor of it. -/
theorem chainStateOf_F_ancestorEq_J (C : Config) (D : Block V) :
    (M.chainStateOf C D).F.AncestorEq (M.chainStateOf C D).J := by
  by_cases h0 : (M.chainStateOf C D).h_F = 0
  · rw [(chainStateOf_F_genesis M F) C D h0]
    exact genesis_ancestorEq _
  have h1 : 1 ≤ (M.chainStateOf C D).h_F := by omega_nat
  obtain ⟨-, -, hFD, hFh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) C D).2.2 h1
  have hb := ((lem47_chain_state_heights M F) C D D).1
  have hj1 : 1 ≤ (M.chainStateOf C D).h_j := le_trans h1 hb.2.2
  obtain ⟨-, hJD, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) C D).1 hj1
  rcases ancestorEq_compatible hFD hJD with hFJ | hJF
  · exact hFJ
  · have hle := ((lem47_chain_state_heights M F) C _ _).2.2.2.1 hJF
    have heq : (M.chainStateOf C (M.chainStateOf C D).J).h =
        (M.chainStateOf C (M.chainStateOf C D).F).h := by
      rw [hJh, hFh] at hle ⊢
      exact le_antisymm hle hb.2.2
    have hT := ((lem47_chain_state_heights M F) C _ _).2.2.2.2 hJF heq
    have hJe := (chainStateOf_J_isEntry M F) C D hj1
    obtain ⟨Y, -, hYj, hYJ⟩ :=
      (justification_witness_of_finalized M F) C D h1
    have hFe : IsEntry M C (M.chainStateOf C D).F := by
      have h := (chainStateOf_J_isEntry M F) C Y (by rw [hYj]; exact h1)
      rw [hYJ] at h
      exact h
    unfold IsEntry at hJe hFe
    rw [hJe, hFe] at hT
    rw [hT]
    exact ancestorEq_refl _

/-- Copied from `scratch/goldilocks_async/probe_ar3_false.lean:90`.
Two entry blocks compatible with `B`, at one chain-state height at most `B`'s, are one block.

Read aloud: at a height at most `B`'s, there is one entry that does not conflict with `B`.

The variables:
- `M`: the model; `F`: its facts. -/
theorem entry_eq_of_compatible_le (C : Config) {B E E' : Block V}
    (hE : IsEntry M C E) (hE' : IsEntry M C E')
    (hc : E.AncestorEq B ∨ B.AncestorEq E) (hc' : E'.AncestorEq B ∨ B.AncestorEq E')
    (hh : (M.chainStateOf C E).h = (M.chainStateOf C E').h)
    (hle : (M.chainStateOf C E).h ≤ (M.chainStateOf C B).h) :
    E = E' := by
  have h1 := (ancestorEq_of_entry_compatible_le M F) C hE hc hle
  have h2 := (ancestorEq_of_entry_compatible_le M F) C hE' hc' (by rw [← hh]; exact hle)
  rcases ancestorEq_compatible h1 h2 with h | h
  · have := ((GoldilocksCorrectness.Record.Statements.Routines.lem47_chain_state_heights M F) C E E').2.2.2.2
      h hh
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this
  · have := ((GoldilocksCorrectness.Record.Statements.Routines.lem47_chain_state_heights M F) C E' E).2.2.2.2
      h hh.symm
    unfold IsEntry at hE hE'
    rw [hE, hE'] at this
    exact this.symm

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.round_justified_of_spacing3`,
recovered from its record form at the spec's model.

Read aloud: the landed `round_justified_of_spacing3` holds, as the record's theorem at the spec's
model. -/
theorem round_justified_of_spacing3_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.round_justified_of_spacing3 V _ _) := by
  exact round_justified_of_spacing3 Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_ancestorEq`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_F_ancestorEq` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_F_ancestorEq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_ancestorEq V _ _) := by
  exact chainStateOf_F_ancestorEq Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_J_isEntry`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_J_isEntry` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_J_isEntry_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_J_isEntry V _ _) := by
  simp only [record_goldilocks]
  exact chainStateOf_J_isEntry Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_ancestorEq_J`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_F_ancestorEq_J` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_F_ancestorEq_J_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_ancestorEq_J V _ _) := by
  exact chainStateOf_F_ancestorEq_J Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.entry_eq_of_compatible_le`,
recovered from its record form at the spec's model.

Read aloud: the landed `entry_eq_of_compatible_le` holds, as the record's theorem at the spec's
model. -/
theorem entry_eq_of_compatible_le_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.entry_eq_of_compatible_le V _ _) := by
  simp only [record_goldilocks]
  exact entry_eq_of_compatible_le Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
