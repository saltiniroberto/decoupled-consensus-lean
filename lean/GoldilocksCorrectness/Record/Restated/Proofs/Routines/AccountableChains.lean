module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Accountable
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.AccountableFGState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Certificates
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableDefs
public import GoldilocksCorrectness.Proofs.Routines.Accountable

@[expose] public section

/-!
# AccountableChains, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Accountable.lean` that compare two chains,
over a model `M` whose facts `F` hold and whose validators are fixed (`Fx`): the helpers under
`RootsNameBlocksOn B B'` (`e2_of_two_justifications`, `past_finalized_of_roots`,
`finalized_chain_of_roots`, `accountable_chain_of_roots`) and Lemmas 68 to 71.

Each takes `Fx : FixedValidators M.toSlotLayout`, because each calls quorum intersection (Lemma 65,
`lem65_quorum_intersection`), which compares two quorums at two blocks. A certificate of the record
(`JustificationCertOn M B h T`, `ProgressCertOn M`, `FinalityCertOn M`) holds its votes on the chain
of a block `X` that is `B` or an ancestor of `B`; the proofs carry each vote from `X`'s chain to
`B`'s by `on_chain_mono`. The statements are the landed ones with the model's readers `M.on_chain`
and `M.chainStateOf C`; `E1`, `E2`, `RootsNameBlocksOn` and `RootCollisionOn` name no member and are
shared, as are `rootsNameBlocksOn_or_collision` and `rootsNameBlocksOn_symm`.

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks`, its facts `goldilocksFacts` and its fixed validators
`fixedValidators_goldilocks`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn ProgressCertOn
  FinalityCertOn SlashableBetween)
open GoldilocksCorrectness.Statements.Routines (E1 E2 RootsNameBlocksOn RootCollisionOn)
open GoldilocksCorrectness.Proofs.Routines (rootsNameBlocksOn_or_collision rootsNameBlocksOn_symm
  ancestorEq_compatible ancestorEq_refl ancestorEq_trans compatible_iff genesis_ancestorEq)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-! ## The helpers under `RootsNameBlocksOn` -/

/-- Two justification certificates at one height, on two chains, for blocks of different roots
leave at least `2 * quorum V - validator_count V` validators each with a target vote at that
height included on the first chain and one included on the second, for different blocks.

Why: the two certificates hold their votes on the chains of `X ⪯ B` and `X' ⪯ B'`; their quorums
meet in `2q − n` validators (Lemma 65, with fixed validators), and each vote is carried to the
chain of `B` or `B'` by `on_chain_mono`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `B`, `B'`: the two blocks whose chains hold the certificates; `h`: the height; `T`, `T'`: the
  blocks the certificates name.

Read aloud: two justification certificates at one height, on two chains, for blocks of different
roots leave at least `2q − n` validators each with an E2 pair across the two chains. -/
theorem e2_of_two_justifications (Fx : FixedValidators M.toSlotLayout) (B B' : Block V) (h : Height)
    (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B`
    (hJ : JustificationCertOn M B h T)
    -- a justification certificate at `h` for `T'` on the chain of `B'`
    (hJ' : JustificationCertOn M B' h T')
    -- `T` and `T'` have different roots
    (hne : T.root ≠ T'.root) :
    ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
      ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
        M.on_chain a B = true ∧ M.on_chain a' B' = true ∧ E2 a a' := by
  obtain ⟨X₁, hX₁, A₁, hA₁, hv₁⟩ := hJ
  obtain ⟨X₂, hX₂, A₂, hA₂, hv₂⟩ := hJ'
  refine ⟨A₁ ∩ A₂, lem65_quorum_intersection M F Fx X₁ X₂ A₁ A₂ hA₁ hA₂, fun v hv => ?_⟩
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ := hv₁ v (Finset.mem_inter.1 hv).1
  obtain ⟨a', hb1, hb2, hb3, hb4, hb5⟩ := hv₂ v (Finset.mem_inter.1 hv).2
  refine ⟨a, a', ha1, hb1, on_chain_mono M F a hX₁ ha5, on_chain_mono M F a' hX₂ hb5, ?_, ha4,
    hb4, ?_⟩
  · rw [ha2, hb2]
  · rw [ha3, hb3]
    exact hne

/-- Lemma 68 under `RootsNameBlocksOn B B'`: a chain whose height passed the finalization height
of the chain state of `B` holds its finalized block, or at least `2 * quorum V - validator_count V`
validators each hold an E1 pair, the finality pair on the chain of `B` and the vote on the chain
of `B'`.

Why: at finalization height `0` the finalized block is the genesis block. Otherwise the finality
certificate of Lemma 66 holds its votes on the chain of a block `X₁ ⪯ B`, and the block `Y` of
`B'`'s chain that raised the height past the finalization height has a progress certificate on the
chain of a block `X₂ ⪯ Y` (Lemma 67); the two quorums meet (Lemma 65), and each vote is carried to
the chain of `B` or `B'` by `on_chain_mono`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: under distinct roots, a chain whose height passed another chain's finalization height
holds that chain's finalized block, or at least `2q − n` validators each signed an E1 pair across
the two chains. -/
theorem past_finalized_of_roots (Fx : FixedValidators M.toSlotLayout) (C : Config) (B B' : Block V)
    -- no two different blocks of the two chains share a root
    (hRoots : RootsNameBlocksOn B B')
    -- the height of the chain state of `B'` is greater than the finalization height of `B`'s
    (hlt : (M.chainStateOf C B).h_F < (M.chainStateOf C B').h) :
    (M.chainStateOf C B).F.AncestorEq B' ∨
      ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          M.on_chain a B = true ∧ M.on_chain a' B' = true ∧ E1 a a' := by
  by_cases h0 : (M.chainStateOf C B).h_F = 0
  · left
    rw [chainStateOf_F_genesis M F C B h0]
    exact genesis_ancestorEq B'
  have h1 : 1 ≤ (M.chainStateOf C B).h_F := by omega_nat
  obtain ⟨-, ⟨X₁, hX₁, A₁, hA₁, hv₁⟩, hFB, -⟩ := (F.cs.lem66_chain_state_certified C B).2.2 h1
  obtain ⟨Y, hYB', -, -, -, hTY, ⟨X₂, hX₂, A₂, hA₂, hv₂⟩⟩ := lem67_first_advance M F C B' _ h1 hlt
  by_cases hTF : (M.chainStateOf C Y.parent).T_h.root = (M.chainStateOf C B).F.root
  · left
    have hT := hRoots _ _ (Or.inr (ancestorEq_trans hTY hYB')) (Or.inl hFB) hTF
    rw [← hT]
    exact ancestorEq_trans hTY hYB'
  · right
    refine ⟨A₁ ∩ A₂, lem65_quorum_intersection M F Fx X₁ X₂ A₁ A₂ hA₁ hA₂, fun v hv => ?_⟩
    obtain ⟨a, ha1, ha2, ha3⟩ := hv₁ v (Finset.mem_inter.1 hv).1
    obtain ⟨a', hb1, hb2, hb3, hb4⟩ := hv₂ v (Finset.mem_inter.1 hv).2
    refine ⟨a, a', ha1, hb1, on_chain_mono M F a hX₁ ha3,
      on_chain_mono M F a' (ancestorEq_trans hX₂ hYB') hb4, ⟨_, ha2, hb2, ?_⟩⟩
    rw [hb3]
    exact hTF

/-- Lemma 69 under `RootsNameBlocksOn B B'`: when the finalization height of the chain state of
`B` is at most that of `B'`, the finalized block of `B`'s is that of `B'`'s or an ancestor of it,
or at least `2 * quorum V - validator_count V` validators each hold an E1 or E2 pair, the first
attestation on the chain of `B` and the second on the chain of `B'`.

Why: as the landed proof: by `past_finalized_of_roots` when the finalization heights differ, by
`e2_of_two_justifications` when they are equal and the finalized blocks differ.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: under distinct roots, when the first chain's finalization height is at most the
second's, the first chain's finalized block is the second's or an ancestor of it, or at least
`2q − n` validators each signed an E1 or E2 pair across the two chains. -/
theorem finalized_chain_of_roots (Fx : FixedValidators M.toSlotLayout) (C : Config)
    (B B' : Block V)
    -- no two different blocks of the two chains share a root
    (hRoots : RootsNameBlocksOn B B')
    -- the finalization height of `B`'s chain state is at most `B'`'s
    (hle : (M.chainStateOf C B).h_F ≤ (M.chainStateOf C B').h_F) :
    (M.chainStateOf C B).F.AncestorEq (M.chainStateOf C B').F ∨
      ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          M.on_chain a B = true ∧ M.on_chain a' B' = true ∧ (E1 a a' ∨ E2 a a') := by
  by_cases h0 : (M.chainStateOf C B).h_F = 0
  · left
    rw [chainStateOf_F_genesis M F C B h0]
    exact genesis_ancestorEq _
  have h1 : 1 ≤ (M.chainStateOf C B).h_F := by omega_nat
  obtain ⟨hJB, -, hFB, hFh⟩ := (F.cs.lem66_chain_state_certified C B).2.2 h1
  have h1' : 1 ≤ (M.chainStateOf C B').h_F := by omega_nat
  obtain ⟨hJB', -, hF'B', hF'h⟩ := (F.cs.lem66_chain_state_certified C B').2.2 h1'
  by_cases hlt : (M.chainStateOf C B).h_F < (M.chainStateOf C B').h_F
  · have hb := chainStateOf_bounds M F C B'
    have hlt' : (M.chainStateOf C B).h_F < (M.chainStateOf C B').h := by omega_nat
    rcases past_finalized_of_roots M F Fx C B B' hRoots hlt' with hFB' | ⟨A, hA, hv⟩
    · rcases ancestorEq_compatible hFB' hF'B' with hanc | hanc
      · exact Or.inl hanc
      · exfalso
        have hmono := chainStateOf_height_mono M F C hanc
        rw [hFh, hF'h] at hmono
        omega_nat
    · right
      refine ⟨A, hA, fun v hvA => ?_⟩
      obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
      exact ⟨a, a', e1, e2, e3, e4, Or.inl e5⟩
  · have heq : (M.chainStateOf C B').h_F = (M.chainStateOf C B).h_F := by omega_nat
    by_cases hFF : (M.chainStateOf C B).F = (M.chainStateOf C B').F
    · left
      rw [hFF]
      exact ancestorEq_refl _
    · rw [heq] at hJB'
      by_cases hr : (M.chainStateOf C B).F.root = (M.chainStateOf C B').F.root
      · exact absurd (hRoots _ _ (Or.inl hFB) (Or.inr hF'B') hr) hFF
      · right
        obtain ⟨A, hA, hv⟩ := e2_of_two_justifications M F Fx B B' _ _ _ hJB hJB' hr
        refine ⟨A, hA, fun v hvA => ?_⟩
        obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
        exact ⟨a, a', e1, e2, e3, e4, Or.inr e5⟩

/-- Lemma 70 under `RootsNameBlocksOn B B'`: when the finalized blocks of the chain states of `B`
and `B'` are not compatible, `SlashableBetween M B B'`.

Why: `finalized_chain_of_roots` in the order of the two finalization heights; its first disjunct
makes the two finalized blocks compatible.

The variables:
- `M`: the model; `F`: its facts; `Fx`: every block of `M` has every validator;
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: under distinct roots, when the blocks two chains finalized conflict, at least `2q − n`
validators each signed two attestations, one included on each chain, meeting E1 or E2. -/
theorem accountable_chain_of_roots (Fx : FixedValidators M.toSlotLayout) (C : Config)
    (B B' : Block V)
    -- no two different blocks of the two chains share a root
    (hRoots : RootsNameBlocksOn B B')
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (M.chainStateOf C B).F.compatible (M.chainStateOf C B').F = false) :
    SlashableBetween M B B' := by
  rcases le_total (M.chainStateOf C B).h_F (M.chainStateOf C B').h_F with hle | hle
  · rcases finalized_chain_of_roots M F Fx C B B' hRoots hle with hanc | ⟨A, hA, hv⟩
    · rw [(compatible_iff _ _).2 (Or.inl hanc)] at hConflict
      cases hConflict
    · refine ⟨A, hA, fun v hvA => ?_⟩
      obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
      exact ⟨a, a', e1, e2, Or.inl ⟨e3, e4⟩, e5⟩
  · rcases finalized_chain_of_roots M F Fx C B' B (rootsNameBlocksOn_symm hRoots) hle with
      hanc | ⟨A, hA, hv⟩
    · rw [(compatible_iff _ _).2 (Or.inr hanc)] at hConflict
      cases hConflict
    · refine ⟨A, hA, fun v hvA => ?_⟩
      obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
      exact ⟨a, a', e1, e2, Or.inr ⟨e4, e3⟩, e5⟩

/-! ## The page lemmas -/

/-- **Lemma 68, past finalized, over a model with fixed validators.** The proof; the audited
statement is in `Record/Restated/Statements/Routines/AccountableStatementsChains.lean`.

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
      RootCollisionOn B B' := by
  rcases rootsNameBlocksOn_or_collision B B' with hR | hC
  · rcases past_finalized_of_roots M F Fx C B B' hR hlt with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hC)

/-- **Lemma 69, finalized chain, over a model with fixed validators.** The proof; the audited
statement is in `Record/Restated/Statements/Routines/AccountableStatementsChains.lean`.

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
      RootCollisionOn B B' := by
  rcases rootsNameBlocksOn_or_collision B B' with hR | hC
  · rcases finalized_chain_of_roots M F Fx C B B' hR hle with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hC)

/-- **Lemma 70, accountable safety at the chain level, over a model with fixed validators.** The
proof; the audited statement is in
`Record/Restated/Statements/Routines/AccountableStatementsChains.lean`.

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
    SlashableBetween M B B' ∨ RootCollisionOn B B' := by
  rcases rootsNameBlocksOn_or_collision B B' with hR | hC
  · exact Or.inl (accountable_chain_of_roots M F Fx C B B' hR hConflict)
  · exact Or.inr hC

/-- **Lemma 71, one justification per height, over a model with fixed validators.** The proof;
the audited statement is in `Record/Restated/Statements/Routines/AccountableStatementsChains.lean`.

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
      T.root = T'.root := by
  by_cases hr : T.root = T'.root
  · exact Or.inr hr
  · exact Or.inl (e2_of_two_justifications M F Fx B B' h T T' hJ hJ' hr)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.e2_of_two_justifications`,
recovered from its record form at the spec's model.

Read aloud: the landed `e2_of_two_justifications` holds, as the record's theorem at the spec's
model. -/
theorem e2_of_two_justifications_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.e2_of_two_justifications V _ _) := by
  simp only [record_goldilocks]
  exact e2_of_two_justifications Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.past_finalized_of_roots`,
recovered from its record form at the spec's model.

Read aloud: the landed `past_finalized_of_roots` holds, as the record's theorem at the spec's
model. -/
theorem past_finalized_of_roots_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.past_finalized_of_roots V _ _) := by
  simp only [record_goldilocks]
  exact past_finalized_of_roots Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.finalized_chain_of_roots`,
recovered from its record form at the spec's model.

Read aloud: the landed `finalized_chain_of_roots` holds, as the record's theorem at the spec's
model. -/
theorem finalized_chain_of_roots_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.finalized_chain_of_roots V _ _) := by
  simp only [record_goldilocks]
  exact finalized_chain_of_roots Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.accountable_chain_of_roots`,
recovered from its record form at the spec's model.

Read aloud: the landed `accountable_chain_of_roots` holds, as the record's theorem at the spec's
model. -/
theorem accountable_chain_of_roots_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.accountable_chain_of_roots V _ _) := by
  simp only [record_goldilocks]
  exact accountable_chain_of_roots Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem68_past_finalized`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem68_past_finalized` holds, as the record's theorem at the spec's
model. -/
theorem lem68_past_finalized_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem68_past_finalized V _ _) := by
  simp only [record_goldilocks]
  exact lem68_past_finalized Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem69_finalized_chain`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem69_finalized_chain` holds, as the record's theorem at the spec's
model. -/
theorem lem69_finalized_chain_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem69_finalized_chain V _ _) := by
  simp only [record_goldilocks]
  exact lem69_finalized_chain Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem70_accountable_safety_chain`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem70_accountable_safety_chain` holds, as the record's theorem at the
spec's model. -/
theorem lem70_accountable_safety_chain_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem70_accountable_safety_chain V _ _) := by
  simp only [record_goldilocks]
  exact lem70_accountable_safety_chain Model.goldilocks goldilocksFacts fixedValidators_goldilocks

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem71_one_justification_per_height`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem71_one_justification_per_height` holds, as the record's theorem at the
spec's model. -/
theorem lem71_one_justification_per_height_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem71_one_justification_per_height V _ _) := by
  simp only [record_goldilocks]
  exact lem71_one_justification_per_height Model.goldilocks goldilocksFacts
    fixedValidators_goldilocks

end GoldilocksCorrectness.Record.Proofs.Routines
