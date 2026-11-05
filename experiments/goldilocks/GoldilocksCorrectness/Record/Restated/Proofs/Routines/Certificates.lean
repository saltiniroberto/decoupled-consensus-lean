module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.Certificates

@[expose] public section

/-!
# Certificates, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Certificates.lean` over a model `M` whose
facts `F` hold: the justification behind a finalization, two pending justifications of one height in
a sorted list, quorum intersection (Lemma 65, with fixed validators), the certificates behind a
chain state (Lemma 66) and the first advance past a height (Lemma 67 and its part (b)).

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
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- Two pending justifications of a list in strictly increasing order of heights, at one height,
are one.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in a list sorted by strictly increasing height, two pending pairs at one height are one. -/
theorem eq_of_pairwise_j {l : List (M.PP)}
    -- the heights of `l` are strictly increasing
    (hl : l.Pairwise (fun e e' => e.j < e'.j))
    {e e' : M.PP}
    -- both are in `l`, at one height
    (he : e ∈ l) (he' : e' ∈ l) (hj : e.j = e'.j) :
    e = e' := by
  induction l with
  | nil => exact absurd he List.not_mem_nil
  | cons x l ih =>
      rw [List.pairwise_cons] at hl
      rcases List.mem_cons.mp he with h1 | h1 <;> rcases List.mem_cons.mp he' with h2 | h2
      · exact h1.trans h2.symm
      · have := hl.1 e' h2; rw [h1] at hj; omega_nat
      · have := hl.1 e h1; rw [h2] at hj; omega_nat
      · exact ih hl.2 h1 h2

/-- **The finalized block was justified by a block of the chain.** When the chain state of `D` has
finalization height at least `1`, some block `Y`, `D` or an ancestor of `D`, has a chain state
whose justification height is that finalization height and whose justified block is `D`'s
finalized block.

Why: `justificationWitnessed_chainStateOf`, its second conjunct.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block.

Read aloud: a chain that finalized `F` at `h_F` passed through a state that had just justified `F`
at `h_F`. -/
theorem justification_witness_of_finalized (C : Config) (D : Block V)
    -- the finalization height of `D`'s chain state is at least `1`
    (h1 : 1 ≤ (M.chainStateOf C D).h_F) :
    ∃ Y : Block V, Y.AncestorEq D ∧ (M.chainStateOf C Y).h_j = (M.chainStateOf C D).h_F ∧
      (M.chainStateOf C Y).J = (M.chainStateOf C D).F :=
  F.cs.justification_witness_of_finalized C D h1

/-- **Lemma 65, quorum intersection, over a model with fixed validators.** A set `A` reaching
the quorum at the block `X` and a set `A'` reaching the quorum at the block `X'` share at least
`2 * quorum V - validator_count V` validators.

Why: with fixed validators the quorum at every block is `quorum V` (`quorumAt_eq_quorum`), and
two quorums share that many validators.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `X`, `X'`: the two blocks; `A`, `A'`: the two sets of validators.

Read aloud: with fixed validators, a set reaching the quorum at `X` and a set reaching the
quorum at `X'` share at least `2 * quorum V - validator_count V` validators. -/
theorem lem65_quorum_intersection (Fx : FixedValidators M.toSlotLayout) (X X' : Block V)
    (A A' : Finset V)
    -- `A` reaches the quorum at `X`
    (hA : M.quorumAt X ≤ |A|)
    -- `A'` reaches the quorum at `X'`
    (hA' : M.quorumAt X' ≤ |A'|) :
    2 * quorum V - validator_count V ≤ |A ∩ A'| := by
  rw [quorumAt_eq_quorum Fx F.sched X] at hA
  rw [quorumAt_eq_quorum Fx F.sched X'] at hA'
  exact GoldilocksCorrectness.Proofs.Routines.lem65_quorum_intersection A A' hA hA'

/-- **Lemma 66, the certificates behind a chain state.** The proof; the audited statement is in
`Statements/Routines/CertificateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block.

Read aloud: the justified block, every pending justification and the finalized block of a chain state each have their certificates included on the chain, and each is a block of the chain whose own chain state is at the height named. -/
theorem lem66_chain_state_certified (C : Config) (B : Block V) :
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
      (M.chainStateOf C (M.chainStateOf C B).F).h = (M.chainStateOf C B).h_F) :=
  F.cs.lem66_chain_state_certified C B

/-- **Lemma 67, the first advance past a height.** The proof; the audited statement is in
`Statements/Routines/CertificateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `h`: the height.

Read aloud: a chain whose height passed `h` has a block that raised the height from `h` to `h + 1`, carrying a quorum of votes at `h` naming the entry of height `h`, which is an ancestor of that block. -/
theorem lem67_first_advance (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (M.chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (M.chainStateOf C Y.parent).h = h ∧ (M.chainStateOf C Y).h = h + 1 ∧
      (M.chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn M Y h (M.chainStateOf C Y.parent).T_h := by
  obtain ⟨Y, hY1, hY2, hY3, hY4, hY5, hY6, -⟩ := F.cs.lem67b_first_advance_cases C B h h1 hlt
  exact ⟨Y, hY1, hY2, hY3, hY4, hY5, hY6⟩

/-- **Lemma 67 (b), the first advance past a height, with its branch.** The proof; the audited
statement is in `Statements/Routines/CertificateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `h`: the height.

Read aloud: a height was left by a quorum of targets, or by a progress quorum once the timeout had passed. -/
theorem lem67b_first_advance_cases (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (M.chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (M.chainStateOf C Y.parent).h = h ∧ (M.chainStateOf C Y).h = h + 1 ∧
      (M.chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn M Y h (M.chainStateOf C Y.parent).T_h ∧
      (JustificationCertOn M Y h (M.chainStateOf C Y.parent).T_h ∨
        (M.chainStateOf C Y.parent).T_h.slot + C.δt ≤ Y.slot) :=
  F.cs.lem67b_first_advance_cases C B h h1 hlt

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.eq_of_pairwise_j`,
recovered from its record form at the spec's model.

Read aloud: the landed `eq_of_pairwise_j` holds, as the record's theorem at the spec's
model. -/
theorem eq_of_pairwise_j_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.eq_of_pairwise_j V) := by
  exact eq_of_pairwise_j Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.justification_witness_of_finalized`,
recovered from its record form at the spec's model.

Read aloud: the landed `justification_witness_of_finalized` holds, as the record's theorem at the spec's
model. -/
theorem justification_witness_of_finalized_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.justification_witness_of_finalized V _ _) := by
  exact justification_witness_of_finalized Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem65_quorum_intersection`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem65_quorum_intersection` holds, as the record's theorem at the spec's
model. -/
theorem lem65_quorum_intersection_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem65_quorum_intersection V _ _) := by
  exact lem65_quorum_intersection Model.goldilocks goldilocksFacts fixedValidators_goldilocks Block.genesis Block.genesis

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem66_chain_state_certified`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem66_chain_state_certified` holds, as the record's theorem at the spec's
model. -/
theorem lem66_chain_state_certified_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem66_chain_state_certified V _ _) := by
  simp only [record_goldilocks]
  exact lem66_chain_state_certified Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem67_first_advance`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem67_first_advance` holds, as the record's theorem at the spec's
model. -/
theorem lem67_first_advance_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem67_first_advance V _ _) := by
  simp only [record_goldilocks]
  exact lem67_first_advance Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem67b_first_advance_cases`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem67b_first_advance_cases` holds, as the record's theorem at the spec's
model. -/
theorem lem67b_first_advance_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem67b_first_advance_cases V _ _) := by
  simp only [record_goldilocks]
  exact lem67b_first_advance_cases Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
