module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Certificates
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements

@[expose] public section

/-!
# CertificateStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Routines/CertificateStatements.lean` over a
model `M` whose facts `F` hold: quorum intersection (Lemma 65, with fixed validators), the
certificates behind a chain state (Lemma 66), the first advance past a height (Lemma 67 and its part
(b)).

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
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

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
  exact GoldilocksCorrectness.Record.Proofs.Routines.lem65_quorum_intersection M F Fx X X' A A' hA hA'

/-- **Lemma 66, the certificates behind a chain state.** For the chain state of `B`: when its
justification height is at least `1`, its justified block has a justification certificate at that
height on `B`'s chain, is `B` or an ancestor of `B`, and has its own chain state at that height;
every pending justification likewise; and when its finalization height is at least `1`, its
finalized block has a justification and a finality certificate at that height on `B`'s chain, is
`B` or an ancestor of `B`, and has its own chain state at that height.

Why: by induction on `B`, every validator a chain state counts has its attestation included on
the chain; a justification is written from a quorum of target votes, a finalization from a
pending justification whose finality participation is a quorum, and the pending heights are
strictly increasing, so that participation is read against one pending justification.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block.

Read aloud: the justified block, every pending justification and the finalized block of a chain
state each have their certificates included on the chain, and each is a block of the chain whose
own chain state is at the height named.

 -/
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
  (GoldilocksCorrectness.Record.Proofs.Routines.lem66_chain_state_certified M F) C B

/-- **Lemma 67, the first advance past a height.** When `1 ≤ h` and the chain state of `B` has a
height greater than `h`, some block `Y`, `B` or an ancestor of `B` and not the genesis block, has
a parent at the height `h` and is itself at the height `h + 1`; the parent's `T_h` is an ancestor
of `Y`, and `Y`'s chain holds a progress certificate at `h` for the parent's `T_h`.

Why: the height rises by at most one per block from `1` at the genesis block, so the chain has a
block whose parent is at `h` and that is at `h + 1`; that block raised the height through the
justification branch or the timeout branch, so a quorum of its pre-event target participation or
progress set voted at `h` naming the parent's `T_h`, each vote included on its chain.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `h`: the height.

Read aloud: a chain whose height passed `h` has a block that raised the height from `h` to
`h + 1`, carrying a quorum of votes at `h` naming the entry of height `h`, which is an ancestor of
that block.

 -/
theorem lem67_first_advance (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (M.chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (M.chainStateOf C Y.parent).h = h ∧ (M.chainStateOf C Y).h = h + 1 ∧
      (M.chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn M Y h (M.chainStateOf C Y.parent).T_h :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem67_first_advance M F) C B h h1 hlt

/-- **Lemma 67 (b), the first advance past a height, with its branch.** Lemma 67's conclusion
(`lem67_first_advance`): when `1 ≤ h` and the chain state of `B` has a height greater than `h`,
some block `Y`, `B` or an ancestor of `B` and not the genesis block, has a parent at the height
`h` and is itself at the height `h + 1`; the parent's `T_h` is an ancestor of `Y`, and `Y`'s chain
holds a progress certificate at `h` for the parent's `T_h`; and in addition, `Y`'s chain holds a
justification certificate at `h` for the parent's `T_h`, or `Y`'s slot is at least `δt` after the
slot of the parent's `T_h`.

Why: Lemma 67's proof; at the block that raised the height, the height events took the
justification branch, whose quorum is of target votes, or the timeout branch, whose test is
`T_h.slot + δt ≤ s` at the block's slot.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `h`: the height.

Read aloud: a height was left by a quorum of targets, or by a progress quorum once the timeout
had passed.

 -/
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
  (GoldilocksCorrectness.Record.Proofs.Routines.lem67b_first_advance_cases M F) C B h h1 hlt

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem65_quorum_intersection`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem65_quorum_intersection` holds, as the record's theorem at the spec's
model. -/
theorem lem65_quorum_intersection_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem65_quorum_intersection V _ _) := by
  exact lem65_quorum_intersection Model.goldilocks goldilocksFacts fixedValidators_goldilocks Block.genesis Block.genesis

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem66_chain_state_certified` holds, as the record's theorem at the spec's
model. -/
theorem lem66_chain_state_certified_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified V _ _) := by
  simp only [record_goldilocks]
  exact lem66_chain_state_certified Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem67_first_advance`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem67_first_advance` holds, as the record's theorem at the spec's
model. -/
theorem lem67_first_advance_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem67_first_advance V _ _) := by
  simp only [record_goldilocks]
  exact lem67_first_advance Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem67b_first_advance_cases`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem67b_first_advance_cases` holds, as the record's theorem at the spec's
model. -/
theorem lem67b_first_advance_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem67b_first_advance_cases V _ _) := by
  simp only [record_goldilocks]
  exact lem67b_first_advance_cases Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Statements.Routines
