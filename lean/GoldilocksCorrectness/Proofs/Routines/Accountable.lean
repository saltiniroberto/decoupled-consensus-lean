module
public import GoldilocksCorrectness.Statements.Routines.AccountableDefs
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Statements.Routines.RecordDefs
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State

@[expose] public section

/-!
# Accountable safety at the chain level

The proofs of the statements of
`GoldilocksCorrectness/Statements/Routines/AccountableStatements.lean`: a consistent record forbids
the slashing conditions (`no_slashable_of_consistent`), past finalized (Lemma 68), finalized chain
(Lemma 69), accountable safety at the chain level (Lemma 70) and one justification per height
(Lemma 71).

The route: each of Lemmas 68 to 70 is first proved under the hypothesis `RootsNameBlocksOn B B'`
(the helpers `past_finalized_of_roots`, `finalized_chain_of_roots`,
`accountable_chain_of_roots`), from the certificates of Lemmas 66 and 67 and quorum intersection
(Lemma 65); the page lemma then splits on `rootsNameBlocksOn_or_collision`, the other case being
the disjunct `RootCollisionOn B B'`.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (E1 E2 RootsNameBlocksOn RootCollisionOn
  SlashableBetween RecordConsistent JustificationCertOn)
open GoldilocksCorrectness.Proofs.Routines (chainStateOf_bounds chainStateOf_height_mono)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The kit -/

omit [Fintype V] in
/-- Either no two different blocks of the two chains ending at `B` and `B'` share a root, or two
different ones do.

The variables:
- `B`, `B'`: the two blocks whose chains are read. -/
theorem rootsNameBlocksOn_or_collision (B B' : Block V) :
    RootsNameBlocksOn B B' ∨ RootCollisionOn B B' := by
  by_cases h : RootsNameBlocksOn B B'
  · exact Or.inl h
  · right
    simp only [RootsNameBlocksOn, not_forall] at h
    obtain ⟨X, Y, hX, hY, hr, hne⟩ := h
    exact ⟨X, Y, hX, hY, hr, hne⟩

omit [Fintype V] in
/-- `RootsNameBlocksOn` is symmetric in the two blocks.

The variables:
- `B`, `B'`: the two blocks whose chains are read. -/
theorem rootsNameBlocksOn_symm {B B' : Block V}
    -- no two different blocks of the two chains share a root
    (h : RootsNameBlocksOn B B') : RootsNameBlocksOn B' B :=
  fun X Y hX hY hr => h X Y hX.symm hY.symm hr

omit [Fintype V] in
/-- An attestation included on the chain of `Y` is included on the chain of every block of which
`Y` is an ancestor, or which is `Y`.

The variables:
- `a`: the attestation; `Y`: the block whose chain includes it; `B`: the descendant. -/
theorem on_chain_mono (a : Attestation V) {Y B : Block V}
    -- `Y` is `B` or an ancestor of `B`
    (hYB : Y.AncestorEq B)
    -- `a` is included on the chain of `Y`
    (h : on_chain a Y = true) : on_chain a B = true := by
  induction B with
  | genesis =>
      rw [(ancestorEq_genesis_iff Y).1 hYB] at h
      exact h
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hYB with hY | hY
      · rw [hY] at h
        exact h
      · exact on_chain_node_of_parent a p s r votes support ats v (ih hY)

/-- A chain state with finalization height `0` has the genesis block as its finalized block.

The variables:
- `C`: the parameters; `B`: the block. -/
theorem chainStateOf_F_genesis (C : Config) (B : Block V)
    -- the finalization height of the chain state of `B` is `0`
    (h0 : (chainStateOf C B).h_F = 0) : (chainStateOf C B).F = Block.genesis := by
  induction B with
  | genesis => rfl
  | node p s r votes support ats v ih =>
      obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ChainState V,
          σ₁ = process_attestations (chainStateOf C p) (.node p s r votes support ats v) ats :=
        ⟨_, rfl⟩
      obtain ⟨tp, pr, fp, heq, -⟩ :=
        process_attestations_eq (chainStateOf C p) (.node p s r votes support ats v) ats
      have hF : σ₁.F = (chainStateOf C p).F := by rw [hσ₁, heq]
      have hhF : σ₁.h_F = (chainStateOf C p).h_F := by rw [hσ₁, heq]
      have hpend : σ₁.pending_finality = (chainStateOf C p).pending_finality := by
        rw [hσ₁, heq]
      have hB : chainStateOf C (.node p s r votes support ats v) = process_height_events C σ₁ := by
        rw [hσ₁]; rfl
      obtain ⟨F', h_F', hcase, hb⟩ := process_height_events_branches C σ₁
      have hfields : (chainStateOf C (.node p s r votes support ats v)).F = F' ∧
          (chainStateOf C (.node p s r votes support ats v)).h_F = h_F' := by
        rw [hB]
        rcases hb with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR] <;> exact ⟨rfl, rfl⟩
      rw [hfields.1]
      rw [hfields.2] at h0
      rcases hcase with ⟨hF', hh'⟩ | ⟨e, he, -, hh', -⟩
      · rw [hF', hF]
        apply ih
        rw [← hhF, ← hh']
        exact h0
      · exfalso
        rw [hpend] at he
        have h66 := (lem66_chain_state_certified C p).2.1 e he
        have hb1 := (chainStateOf_bounds C e.T).1
        rw [h66.2.2] at hb1
        rw [hh'] at h0
        omega_nat

/-! ## The anti-slashing record -/

omit [DecidableEq V] [Fintype V] in
/-- Two attestations whose contents a consistent anti-slashing record holds form no E1 and no E2
pair.

The variables:
- `Λ`: the record; `a`, `a'`: the two attestations. -/
theorem no_slashable_of_consistent (Λ : SigningHistory) (hΛ : RecordConsistent Λ)
    (a a' : Attestation V)
    -- the record holds the content of `a`
    (ha : a.content ∈ Λ.sent)
    -- the record holds the content of `a'`
    (ha' : a'.content ∈ Λ.sent) :
    ¬ E1 a a' ∧ ¬ E2 a a' := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, hh, hT⟩
    exact hT (hΛ.lockKept a.content ha p hp a'.content ha' hh)
  · rintro ⟨hh, hτ, hτ', hT⟩
    exact hT (hΛ.oneTarget a.content ha a'.content ha' hh hτ hτ')

/-! ## The helpers under `RootsNameBlocksOn` -/

/-- Two justification certificates at one height, on two chains, for blocks of different roots
leave at least `2 * quorum V - validator_count V` validators each with a target vote at that
height included on the first chain and one included on the second, for different blocks.

The variables:
- `B`, `B'`: the two blocks whose chains hold the certificates; `h`: the height; `T`, `T'`: the
  blocks the certificates name. -/
theorem e2_of_two_justifications (B B' : Block V) (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B`
    (hJ : JustificationCertOn B h T)
    -- a justification certificate at `h` for `T'` on the chain of `B'`
    (hJ' : JustificationCertOn B' h T')
    -- `T` and `T'` have different roots
    (hne : T.root ≠ T'.root) :
    ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
      ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
        on_chain a B = true ∧ on_chain a' B' = true ∧ E2 a a' := by
  obtain ⟨A₁, hA₁, hv₁⟩ := hJ
  obtain ⟨A₂, hA₂, hv₂⟩ := hJ'
  refine ⟨A₁ ∩ A₂, lem65_quorum_intersection A₁ A₂ hA₁ hA₂, fun v hv => ?_⟩
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ := hv₁ v (Finset.mem_inter.1 hv).1
  obtain ⟨a', hb1, hb2, hb3, hb4, hb5⟩ := hv₂ v (Finset.mem_inter.1 hv).2
  refine ⟨a, a', ha1, hb1, ha5, hb5, ?_, ha4, hb4, ?_⟩
  · rw [ha2, hb2]
  · rw [ha3, hb3]
    exact hne

/-- Lemma 68 under `RootsNameBlocksOn B B'`: a chain whose height passed the finalization height
of the chain state of `B` holds its finalized block, or at least `2 * quorum V - validator_count V`
validators each hold an E1 pair, the finality pair on the chain of `B` and the vote on the chain
of `B'`.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks. -/
theorem past_finalized_of_roots (C : Config) (B B' : Block V)
    -- no two different blocks of the two chains share a root
    (hRoots : RootsNameBlocksOn B B')
    -- the height of the chain state of `B'` is greater than the finalization height of `B`'s
    (hlt : (chainStateOf C B).h_F < (chainStateOf C B').h) :
    (chainStateOf C B).F.AncestorEq B' ∨
      ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          on_chain a B = true ∧ on_chain a' B' = true ∧ E1 a a' := by
  by_cases h0 : (chainStateOf C B).h_F = 0
  · left
    rw [chainStateOf_F_genesis C B h0]
    exact genesis_ancestorEq B'
  have h1 : 1 ≤ (chainStateOf C B).h_F := by omega_nat
  obtain ⟨-, ⟨A₁, hA₁, hv₁⟩, hFB, -⟩ := (lem66_chain_state_certified C B).2.2 h1
  obtain ⟨Y, hYB', -, -, -, hTY, ⟨A₂, hA₂, hv₂⟩⟩ := lem67_first_advance C B' _ h1 hlt
  by_cases hTF : (chainStateOf C Y.parent).T_h.root = (chainStateOf C B).F.root
  · left
    have hT := hRoots _ _ (Or.inr (ancestorEq_trans hTY hYB')) (Or.inl hFB) hTF
    rw [← hT]
    exact ancestorEq_trans hTY hYB'
  · right
    refine ⟨A₁ ∩ A₂, lem65_quorum_intersection A₁ A₂ hA₁ hA₂, fun v hv => ?_⟩
    obtain ⟨a, ha1, ha2, ha3⟩ := hv₁ v (Finset.mem_inter.1 hv).1
    obtain ⟨a', hb1, hb2, hb3, hb4⟩ := hv₂ v (Finset.mem_inter.1 hv).2
    refine ⟨a, a', ha1, hb1, ha3, on_chain_mono a' hYB' hb4, ⟨_, ha2, hb2, ?_⟩⟩
    rw [hb3]
    exact hTF

/-- Lemma 69 under `RootsNameBlocksOn B B'`: when the finalization height of the chain state of
`B` is at most that of `B'`, the finalized block of `B`'s is that of `B'`'s or an ancestor of it,
or at least `2 * quorum V - validator_count V` validators each hold an E1 or E2 pair, the first
attestation on the chain of `B` and the second on the chain of `B'`.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks. -/
theorem finalized_chain_of_roots (C : Config) (B B' : Block V)
    -- no two different blocks of the two chains share a root
    (hRoots : RootsNameBlocksOn B B')
    -- the finalization height of `B`'s chain state is at most `B'`'s
    (hle : (chainStateOf C B).h_F ≤ (chainStateOf C B').h_F) :
    (chainStateOf C B).F.AncestorEq (chainStateOf C B').F ∨
      ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          on_chain a B = true ∧ on_chain a' B' = true ∧ (E1 a a' ∨ E2 a a') := by
  by_cases h0 : (chainStateOf C B).h_F = 0
  · left
    rw [chainStateOf_F_genesis C B h0]
    exact genesis_ancestorEq _
  have h1 : 1 ≤ (chainStateOf C B).h_F := by omega_nat
  obtain ⟨hJB, -, hFB, hFh⟩ := (lem66_chain_state_certified C B).2.2 h1
  have h1' : 1 ≤ (chainStateOf C B').h_F := by omega_nat
  obtain ⟨hJB', -, hF'B', hF'h⟩ := (lem66_chain_state_certified C B').2.2 h1'
  by_cases hlt : (chainStateOf C B).h_F < (chainStateOf C B').h_F
  · have hb := chainStateOf_bounds C B'
    have hlt' : (chainStateOf C B).h_F < (chainStateOf C B').h := by omega_nat
    rcases past_finalized_of_roots C B B' hRoots hlt' with hFB' | ⟨A, hA, hv⟩
    · rcases ancestorEq_compatible hFB' hF'B' with hanc | hanc
      · exact Or.inl hanc
      · exfalso
        have hmono := chainStateOf_height_mono C hanc
        rw [hFh, hF'h] at hmono
        omega_nat
    · right
      refine ⟨A, hA, fun v hvA => ?_⟩
      obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
      exact ⟨a, a', e1, e2, e3, e4, Or.inl e5⟩
  · have heq : (chainStateOf C B').h_F = (chainStateOf C B).h_F := by omega_nat
    by_cases hFF : (chainStateOf C B).F = (chainStateOf C B').F
    · left
      rw [hFF]
      exact ancestorEq_refl _
    · rw [heq] at hJB'
      by_cases hr : (chainStateOf C B).F.root = (chainStateOf C B').F.root
      · exact absurd (hRoots _ _ (Or.inl hFB) (Or.inr hF'B') hr) hFF
      · right
        obtain ⟨A, hA, hv⟩ := e2_of_two_justifications B B' _ _ _ hJB hJB' hr
        refine ⟨A, hA, fun v hvA => ?_⟩
        obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
        exact ⟨a, a', e1, e2, e3, e4, Or.inr e5⟩

/-- Lemma 70 under `RootsNameBlocksOn B B'`: when the finalized blocks of the chain states of `B`
and `B'` are not compatible, `SlashableBetween B B'`.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks. -/
theorem accountable_chain_of_roots (C : Config) (B B' : Block V)
    -- no two different blocks of the two chains share a root
    (hRoots : RootsNameBlocksOn B B')
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (chainStateOf C B).F.compatible (chainStateOf C B').F = false) :
    SlashableBetween B B' := by
  rcases le_total (chainStateOf C B).h_F (chainStateOf C B').h_F with hle | hle
  · rcases finalized_chain_of_roots C B B' hRoots hle with hanc | ⟨A, hA, hv⟩
    · rw [(compatible_iff _ _).2 (Or.inl hanc)] at hConflict
      cases hConflict
    · refine ⟨A, hA, fun v hvA => ?_⟩
      obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
      exact ⟨a, a', e1, e2, Or.inl ⟨e3, e4⟩, e5⟩
  · rcases finalized_chain_of_roots C B' B (rootsNameBlocksOn_symm hRoots) hle with
      hanc | ⟨A, hA, hv⟩
    · rw [(compatible_iff _ _).2 (Or.inr hanc)] at hConflict
      cases hConflict
    · refine ⟨A, hA, fun v hvA => ?_⟩
      obtain ⟨a, a', e1, e2, e3, e4, e5⟩ := hv v hvA
      exact ⟨a, a', e1, e2, Or.inr ⟨e4, e3⟩, e5⟩

/-! ## The page lemmas -/

/-- **Lemma 68, past finalized.** The proof; the audited statement is in
`Statements/Routines/AccountableStatements.lean`.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks. -/
theorem lem68_past_finalized (C : Config) (B B' : Block V)
    -- the height of the chain state of `B'` is greater than the finalization height of `B`'s
    (hlt : (chainStateOf C B).h_F < (chainStateOf C B').h) :
    (chainStateOf C B).F.AncestorEq B' ∨
      (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          on_chain a B = true ∧ on_chain a' B' = true ∧ E1 a a') ∨
      RootCollisionOn B B' := by
  rcases rootsNameBlocksOn_or_collision B B' with hR | hC
  · rcases past_finalized_of_roots C B B' hR hlt with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hC)

/-- **Lemma 69, finalized chain.** The proof; the audited statement is in
`Statements/Routines/AccountableStatements.lean`.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks. -/
theorem lem69_finalized_chain (C : Config) (B B' : Block V)
    -- the finalization height of `B`'s chain state is at most `B'`'s
    (hle : (chainStateOf C B).h_F ≤ (chainStateOf C B').h_F) :
    (chainStateOf C B).F.AncestorEq (chainStateOf C B').F ∨
      (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          on_chain a B = true ∧ on_chain a' B' = true ∧ (E1 a a' ∨ E2 a a')) ∨
      RootCollisionOn B B' := by
  rcases rootsNameBlocksOn_or_collision B B' with hR | hC
  · rcases finalized_chain_of_roots C B B' hR hle with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hC)

/-- **Lemma 70, accountable safety at the chain level.** The proof; the audited statement is in
`Statements/Routines/AccountableStatements.lean`.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks. -/
theorem lem70_accountable_safety_chain (C : Config) (B B' : Block V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (chainStateOf C B).F.compatible (chainStateOf C B').F = false) :
    SlashableBetween B B' ∨ RootCollisionOn B B' := by
  rcases rootsNameBlocksOn_or_collision B B' with hR | hC
  · exact Or.inl (accountable_chain_of_roots C B B' hR hConflict)
  · exact Or.inr hC

/-- **Lemma 71, one justification per height.** The proof; the audited statement is in
`Statements/Routines/AccountableStatements.lean`.

The variables:
- `B`, `B'`: the two blocks whose chains hold the certificates; `h`: the height; `T`, `T'`: the
  blocks the certificates name. -/
theorem lem71_one_justification_per_height (B B' : Block V) (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B`
    (hJ : JustificationCertOn B h T)
    -- a justification certificate at `h` for `T'` on the chain of `B'`
    (hJ' : JustificationCertOn B' h T') :
    (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
      ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
        on_chain a B = true ∧ on_chain a' B' = true ∧ E2 a a') ∨
      T.root = T'.root := by
  by_cases hr : T.root = T'.root
  · exact Or.inr hr
  · exact Or.inl (e2_of_two_justifications B B' h T T' hJ hJ' hr)

end GoldilocksCorrectness.Proofs.Routines
