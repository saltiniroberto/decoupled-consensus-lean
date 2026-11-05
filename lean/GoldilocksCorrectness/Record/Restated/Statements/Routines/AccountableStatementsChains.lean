module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.AccountableChains
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements

@[expose] public section

/-!
# AccountableStatementsChains, over a model

The statements of `GoldilocksCorrectness/Statements/Routines/AccountableStatements.lean` that
compare two chains, over a model `M` whose facts `F` hold and whose validators are fixed (`Fx`):
past finalized (Lemma 68), finalized chain (Lemma 69), accountable safety at the chain level
(Lemma 70) and one justification per height (Lemma 71). Each takes
`Fx : FixedValidators M.toSlotLayout`, which quorum intersection (Lemma 65) needs. (The page's
statement on the anti-slashing record is restated on
`AccountableStatementsValidatorClient.lean`.)

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks`, its facts `goldilocksFacts` and its fixed validators
`fixedValidators_goldilocks`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (E1 E2 RootCollisionOn)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 68, past finalized, over a model with fixed validators.** When the height of the
chain state of `B'` is greater than the finalization height of the chain state of `B`, the
finalized block of `B`'s chain state is `B'` or an ancestor of `B'`; or at least
`2 * quorum V - validator_count V` validators each signed an attestation with that finality pair
included on the chain of `B` and a vote at its height for another block included on the chain of
`B'`; or two different blocks of the two chains share a root.

Why: the landed proof, over the model's readers; the certificates' votes, included on the chain of
a block `X` that is `B` or an ancestor of `B`, are carried to the chain of `B` by `on_chain_mono`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: a chain whose height passed the height at which another chain finalized a block holds
that block, or at least `2q − n` validators each signed an E1 pair across the two chains, or two
different blocks of the two chains share a root. -/
theorem lem68_past_finalized (Fx : FixedValidators M.toSlotLayout) (C : Config) (B B' : Block V)
    -- the height of the chain state of `B'` is greater than the finalization height of `B`'s
    (hlt : (M.chainStateOf C B).h_F < (M.chainStateOf C B').h) :
    (M.chainStateOf C B).F.AncestorEq B' ∨
      (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          M.on_chain a B = true ∧ M.on_chain a' B' = true ∧ E1 a a') ∨
      RootCollisionOn B B' :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem68_past_finalized M F Fx C B B' hlt

/-- **Lemma 69, finalized chain, over a model with fixed validators.** When the finalization
height of the chain state of `B` is at most that of `B'`, the finalized block of `B`'s chain state
is that of `B'`'s or an ancestor of it; or at least `2 * quorum V - validator_count V` validators
each signed an attestation included on the chain of `B` and one included on the chain of `B'` that
together meet E1 or E2; or two different blocks of the two chains share a root.

Why: the landed proof, over the model's readers, with the certificates' votes carried as in
Lemma 68.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: when the first chain's finalization height is at most the second's, the first chain's
finalized block is the second's or an ancestor of it, or at least `2q − n` validators each signed
an E1 or E2 pair across the two chains, or two different blocks of the two chains share a root. -/
theorem lem69_finalized_chain (Fx : FixedValidators M.toSlotLayout) (C : Config) (B B' : Block V)
    -- the finalization height of `B`'s chain state is at most `B'`'s
    (hle : (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B').h_F) :
    (M.chainStateOf C B).F.AncestorEq (M.chainStateOf C B').F ∨
      (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          M.on_chain a B = true ∧ M.on_chain a' B' = true ∧ (E1 a a' ∨ E2 a a')) ∨
      RootCollisionOn B B' :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem69_finalized_chain M F Fx C B B' hle

/-- **Lemma 70, accountable safety at the chain level, over a model with fixed validators.** When
the finalized blocks of the chain states of `B` and `B'` are not compatible (neither is the other
or an ancestor of the other), `SlashableBetween M B B'` holds, or two different blocks of the two
chains share a root.

Why: Lemma 69 in the order of the two finalization heights; its first disjunct makes the two
finalized blocks compatible.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: when the blocks two chains finalized conflict, at least `2q − n` validators each signed
two attestations, one included on each chain, meeting E1 or E2, or two different blocks of the two
chains share a root. -/
theorem lem70_accountable_safety_chain (Fx : FixedValidators M.toSlotLayout) (C : Config)
    (B B' : Block V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (M.chainStateOf C B).F.compatible (M.chainStateOf C B').F = false) :
    SlashableBetween M B B' ∨ RootCollisionOn B B' :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem70_accountable_safety_chain M F Fx C B B'
    hConflict

/-- **Lemma 71, one justification per height, over a model with fixed validators.** A
justification certificate at the height `h` for `T` on the chain of `B` and one for `T'` on the
chain of `B'` leave at least `2 * quorum V - validator_count V` validators each with a target vote
at `h` included on the chain of `B` and one included on the chain of `B'`, for different blocks; or
`T` and `T'` have the same root.

Why: the two quorums meet in `2q − n` validators (Lemma 65, with fixed validators), and each of
them voted at `h` for `T`'s root on one chain and for `T'`'s on the other.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `B`, `B'`: the two blocks whose chains hold the certificates; `h`: the height; `T`, `T'`: the
  blocks the certificates name.

Read aloud: two justification certificates at one height, on two chains, for `T` and `T'`: at
least `2q − n` validators each signed an E2 pair across the two chains, or `T` and `T'` have the
same root. -/
theorem lem71_one_justification_per_height (Fx : FixedValidators M.toSlotLayout) (B B' : Block V)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B`
    (hJ : JustificationCertOn M B h T)
    -- a justification certificate at `h` for `T'` on the chain of `B'`
    (hJ' : JustificationCertOn M B' h T') :
    (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
      ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
        M.on_chain a B = true ∧ M.on_chain a' B' = true ∧ E2 a a') ∨
      T.root = T'.root :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem71_one_justification_per_height M F Fx B B' h T T'
    hJ hJ'

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem68_past_finalized`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem68_past_finalized` holds, as the record's theorem at the spec's
model. -/
theorem lem68_past_finalized_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem68_past_finalized V _ _) := by
  simp only [record_goldilocks]
  exact lem68_past_finalized Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem69_finalized_chain`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem69_finalized_chain` holds, as the record's theorem at the spec's
model. -/
theorem lem69_finalized_chain_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem69_finalized_chain V _ _) := by
  simp only [record_goldilocks]
  exact lem69_finalized_chain Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem70_accountable_safety_chain`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem70_accountable_safety_chain` holds, as the record's theorem at the
spec's model. -/
theorem lem70_accountable_safety_chain_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem70_accountable_safety_chain V _ _) := by
  simp only [record_goldilocks]
  exact lem70_accountable_safety_chain Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem71_one_justification_per_height`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem71_one_justification_per_height` holds, as the record's theorem at the
spec's model. -/
theorem lem71_one_justification_per_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem71_one_justification_per_height V _ _) := by
  simp only [record_goldilocks]
  exact lem71_one_justification_per_height Model.goldilocks goldilocksFacts
    fixedValidators_goldilocks

end GoldilocksCorrectness.Record.Statements.Routines
