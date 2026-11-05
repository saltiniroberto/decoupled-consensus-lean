module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Certificates
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# FGStateReaders, over a model: the contest test and the progress certificates

The two theorems of `GoldilocksCorrectness/Proofs/Routines/FGStateReaders.lean` that read the
contest test `fg_contest` together with the progress certificates on the chains of the tree,
`not_contested_or_two_past` and `justified_past_of_contested`, over a model `M` whose facts `F`
hold. Each is stated for a node state `n` satisfying the model's node invariant
`M.nodeInv C P X n` (the readers' facts `F.ndAdded` hold under it), with the greatest chain-state
height of the tree `hMax M C n` for the stored `h_max` and `M.chainStateOf C B` for the stored chain
state of a block. The landed hypothesis that the stored chain states are the blocks' own is
dropped: over the record it always holds. The other theorems of the landed page are on
`FGStateReaders.lean`, `FGStateReadersOnChain.lean` and `FGStateReadersChainState.lean`.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`) at the FG state `n.S` of a node state `n` satisfying the spec's model's node
invariant, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`, reading `hMax` as the stored `n.S.h_max` (`hMax_goldilocks`) and a progress
certificate in the record's form as one in the landed form (`goldilocks_ProgressCertOn`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (hMax IsEntry ProgressCertOn
  goldilocks_ProgressCertOn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Not contested, or `hMax M C n` at least `h(B) + 2`.** At a node state `n` satisfying the
model's node invariant, whose justified block `n.justified` is compatible with `B`, is an entry,
has the chain-state height `n.justifiedHeight`, with `H < n.justifiedHeight`; when, for every block
`D` of the tree, every progress certificate on `D`'s chain at a height `h > H` for a block `T` of
`D`'s chain at height `h` has `T` compatible with `B`: `M.fg_contest n = false`, or
`(M.chainStateOf C B).h + 2 ≤ hMax M C n`.

Why: contested means `hMax M C n = n.justifiedHeight + 1` and a block `D` of the tree at that
height of which the justified block is not an ancestor. When the justification height is at least
`h(B) + 1`, the greatest height is at least `h(B) + 2`. Otherwise `D`'s chain passed the
justification height, so (Lemma 67) it holds a progress certificate at that height for its own
entry `T'`, an ancestor of `D`; the certificate clause makes `T'` compatible with `B`; `T'` and the
justified block are then two entries compatible with `B` at one height at most `h(B)`, so one block
(`entry_eq_of_compatible_le`), and the justified block is an ancestor of `D`: not contested.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block; `H`: the height threshold.

Read aloud: inside and after the period, a contest can only be between two descendants of `B`,
and then the greatest height is at least two past `B`'s. -/
theorem not_contested_or_two_past (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B : Block V) (H : ℕ)
    -- `n`'s justified block is compatible with `B`, an entry, at the height
    -- `n.justifiedHeight > H`
    (hJ : n.justified.AncestorEq B ∨ B.AncestorEq n.justified) (hJE : IsEntry M C n.justified)
    (hJh : (M.chainStateOf C n.justified).h = n.justifiedHeight) (hHj : H < n.justifiedHeight)
    -- the progress certificates at heights greater than `H` on the chains of the tree are for
    -- blocks compatible with `B`
    (hCert : ∀ D ∈ n.tree, ∀ (h : Height) (T : Block V), T.AncestorEq D →
      ProgressCertOn M D h T → H < h → (M.chainStateOf C T).h = h →
      (T.AncestorEq B ∨ B.AncestorEq T)) :
    M.fg_contest n = false ∨ (M.chainStateOf C B).h + 2 ≤ hMax M C n := by
  by_cases hmax : hMax M C n = n.justifiedHeight + 1
  swap
  · left
    rw [F.ndAdded.fg_contest_eq hI, if_pos hmax]
  by_cases hB : (M.chainStateOf C B).h + 1 ≤ n.justifiedHeight
  · right
    omega_nat
  left
  rw [F.ndAdded.fg_contest_eq hI, if_neg (by rw [hmax]; exact fun h => h rfl)]
  refine decide_eq_false ?_
  rintro ⟨D, hD, _, hDh, hJD⟩
  apply hJD
  show n.justified.AncestorEq D
  rw [hmax] at hDh
  have h1 : 1 ≤ n.justifiedHeight := by omega_nat
  obtain ⟨Y, hYD, -, hYph, -, hTY, hcert⟩ :=
    lem67_first_advance M F C D n.justifiedHeight h1 (by rw [hDh]; omega_nat)
  have hT'D : (M.chainStateOf C Y.parent).T_h.AncestorEq D := ancestorEq_trans hTY hYD
  have hT'h : (M.chainStateOf C (M.chainStateOf C Y.parent).T_h).h = n.justifiedHeight := by
    rw [(isEntry_T_h M F C Y.parent).2.1, hYph]
  -- the certificate on `Y`'s chain is on `D`'s chain
  have hcertD : ProgressCertOn M D n.justifiedHeight (M.chainStateOf C Y.parent).T_h := by
    obtain ⟨Z, hZY, A, hA, hv⟩ := hcert
    exact ⟨Z, ancestorEq_trans hZY hYD, A, hA, hv⟩
  have hT'B := hCert D hD n.justifiedHeight _ hT'D hcertD hHj hT'h
  have hT'E : IsEntry M C (M.chainStateOf C Y.parent).T_h := (isEntry_T_h M F C Y.parent).1
  have hEq : (M.chainStateOf C Y.parent).T_h = n.justified :=
    entry_eq_of_compatible_le M F C hT'E hJE hT'B hJ (by rw [hT'h, hJh])
      (by rw [hT'h]; omega_nat)
  rw [← hEq]
  exact hT'D

/-- Under the hypotheses of `not_contested_or_two_past`, a contested node state has a justification
height at least `h(B) + 1`.

Why: `not_contested_or_two_past` gives "not contested" or `h(B) + 2 ≤ hMax M C n`, and a contested
node state has `hMax M C n = n.justifiedHeight + 1` (`h_max_of_contested`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block; `H`: the height threshold.

Read aloud: inside and after the period, only a node justified past `B` can be contested. -/
theorem justified_past_of_contested (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B : Block V) (H : ℕ)
    (hJ : n.justified.AncestorEq B ∨ B.AncestorEq n.justified) (hJE : IsEntry M C n.justified)
    (hJh : (M.chainStateOf C n.justified).h = n.justifiedHeight) (hHj : H < n.justifiedHeight)
    (hCert : ∀ D ∈ n.tree, ∀ (h : Height) (T : Block V), T.AncestorEq D →
      ProgressCertOn M D h T → H < h → (M.chainStateOf C T).h = h →
      (T.AncestorEq B ∨ B.AncestorEq T))
    (hc : M.fg_contest n = true) : (M.chainStateOf C B).h + 1 ≤ n.justifiedHeight := by
  have hm := h_max_of_contested M F C P X n hI hc
  rcases not_contested_or_two_past M F C P X n hI B H hJ hJE hJh hHj hCert with h | h
  · rw [hc] at h
    exact absurd h (by decide)
  · omega_nat

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.not_contested_or_two_past`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `not_contested_or_two_past` holds at the FG state of every node state
satisfying the invariant. -/
theorem not_contested_or_two_past_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.not_contested_or_two_past V _ _ C n.S) := by
  intro C P X n hI B H _ hJ hJE hJh hHj hCert
  have h := not_contested_or_two_past Model.goldilocks goldilocksFacts C P X n hI B H hJ hJE hJh
    hHj (fun D hD h T hTD hc hH hT =>
      hCert D hD h T hTD (by rw [goldilocks_ProgressCertOn]; exact hc) hH hT)
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.justified_past_of_contested`, recovered from
its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `justified_past_of_contested` holds at the FG state of every node state
satisfying the invariant. -/
theorem justified_past_of_contested_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.justified_past_of_contested V _ _ C
        n.S) := by
  intro C P X n hI B H _ hJ hJE hJh hHj hCert hc
  exact justified_past_of_contested Model.goldilocks goldilocksFacts C P X n hI B H hJ hJE hJh hHj
    (fun D hD h T hTD hc hH hT =>
      hCert D hD h T hTD (by rw [goldilocks_ProgressCertOn]; exact hc) hH hT) hc

end GoldilocksCorrectness.Record.Proofs.Routines
