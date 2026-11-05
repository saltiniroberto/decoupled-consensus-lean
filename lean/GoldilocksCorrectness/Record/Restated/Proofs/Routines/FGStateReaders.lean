module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FrameDefs
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# FGStateReaders, over a model: the readers of the stored chain states and the stored greatest height

The theorems of `GoldilocksCorrectness/Proofs/Routines/FGStateReaders.lean` that read
`fg_contest`, `head_height_floor`, `get_fc_root` or `is_viable`, over a model `M` whose facts `F`
hold: the contest test, the least chain-state height of a viable block, the fork-choice root and
the viable heads of `M.fg_to_ac n`. Each is stated for a node state `n` satisfying the model's node
invariant `M.nodeInv C P X n` (the readers' facts `F.ndAdded` hold under it), with the greatest
chain-state height of the tree `hMax M C n` for the stored `h_max` and `M.chainStateOf C B` for the
stored chain state of a block. A hypothesis that the stored chain states are the blocks' own is
dropped: over the record it always holds. The free theorems of the landed page are on
`FGStateReadersOnChain.lean` and `FGStateReadersChainState.lean`.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`) at the FG state `n.S` of a node state `n` satisfying the spec's model's node
invariant, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`, reading `hMax` as the stored `n.S.h_max` (`hMax_goldilocks`) and the chain state
of a block of the tree as the stored one (the invariant's clause `ChainStatesComputed`). The landed
`is_viable_iff` reads the stored chain state of any block, of the tree or not: its record form takes
the block in the tree, and it has no recovery here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (hMax FinalizedAncestorJustified BoxOne
  BoxThree)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_compatible ancestorEq_refl ancestorEq_trans
  compatible_iff)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- The fork-choice root is the justified block or the finalized block.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the fork-choice root is the justified block or the finalized block. -/
theorem get_fc_root_cases (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) :
    M.get_fc_root n = n.justified ∨ M.get_fc_root n = n.finalized := by
  rw [F.ndAdded.get_fc_root_eq hI]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- When the finalized block is the justified block or an ancestor of it, the finalized block is
the fork-choice root or an ancestor of it.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the finalized block is the fork-choice root or an ancestor of it, when it is the
justified block or an ancestor of it. -/
theorem F_ancestorEq_get_fc_root (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n)
    -- the finalized block of `n` is the justified block of `n` or an ancestor of it
    (h : FinalizedAncestorJustified M n) :
    n.finalized.AncestorEq (M.get_fc_root n) := by
  rw [F.ndAdded.get_fc_root_eq hI]
  split
  · exact h
  · exact ancestorEq_refl _

/-- On a node state satisfying the clock-free part of the node invariant, the finalized block is the
fgroot `M.get_fc_root n` or an ancestor of it, when it is the justified block or an ancestor of it:
`F_ancestorEq_get_fc_root` read through `get_fc_root_eq_of_core`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state; `hI`: `n`
  satisfies the clock-free part of the node invariant; `h`: the finalized block is the justified
  block or an ancestor of it.

Read aloud: under the clock-free part, the finalized block is on the fgroot's chain. -/
theorem F_ancestorEq_get_fc_root_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n)
    -- the finalized block of `n` is the justified block of `n` or an ancestor of it
    (h : FinalizedAncestorJustified M n) :
    n.finalized.AncestorEq (M.get_fc_root n) := by
  rw [F.ndAdded.get_fc_root_eq_of_core hI]
  split
  · exact h
  · exact ancestorEq_refl _

/-- The root of the frame's fork choice is the fork-choice root `M.get_fc_root n`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: the root of the frame's fork choice is `M.get_fc_root n`. -/
theorem fc_root_eq (n : M.N) :
    (M.fg_to_ac n).fc_root = M.get_fc_root n := by
  rw [F.rd.fg_to_ac_eq]

/-- **`h_max_of_contested` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `h_max_of_contested` is this theorem at
`F.nd.nodeInv_core hI`.

 A contested node state has `hMax M C n = n.justifiedHeight + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`; `hc`: `n` is contested.

Read aloud: a node is contested only when its greatest height is one past its justification
height. -/
theorem h_max_of_contested_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (hc : M.fg_contest n = true) :
    hMax M C n = n.justifiedHeight + 1 := by
  by_contra hne
  rw [F.ndAdded.fg_contest_eq_of_core hI, if_pos hne] at hc
  exact absurd hc (by decide)

/-- A contested node state has `hMax M C n = n.justifiedHeight + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `hc`: `n` is contested.

Read aloud: a node is contested only when its greatest height is one past its justification
height. -/
theorem h_max_of_contested (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (hc : M.fg_contest n = true) :
    hMax M C n = n.justifiedHeight + 1 :=
  h_max_of_contested_of_core M F C P X n (F.nd.nodeInv_core hI) hc

/-- **`fg_contest_spec` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `fg_contest_spec` is this theorem at
`F.nd.nodeInv_core hI`.

 A contested node state has `hMax M C n = n.justifiedHeight + 1` and a block of its tree, the
finalized block or a descendant of it, of chain-state height `hMax M C n`, of which the justified
block is not an ancestor.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`; `h`: `n` is contested.

Read aloud: a contested node has its greatest height one past its justification height and a block
of that height on the finalized block's chain and off the justified block's chain. -/
theorem fg_contest_spec_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (h : M.fg_contest n = true) :
    hMax M C n = n.justifiedHeight + 1 ∧ ∃ B ∈ n.tree, n.finalized.AncestorEq B ∧
      (M.chainStateOf C B).h = hMax M C n ∧ ¬ n.justified.AncestorEq B := by
  rw [F.ndAdded.fg_contest_eq_of_core hI] at h
  split at h
  · cases h
  · rename_i hne
    exact ⟨Decidable.of_not_not hne, of_decide_eq_true h⟩

/-- A contested node state has `hMax M C n = n.justifiedHeight + 1` and a block of its tree, the
finalized block or a descendant of it, of chain-state height `hMax M C n`, of which the justified
block is not an ancestor.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `h`: `n` is contested.

Read aloud: a contested node has its greatest height one past its justification height and a block
of that height on the finalized block's chain and off the justified block's chain. -/
theorem fg_contest_spec (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (h : M.fg_contest n = true) :
    hMax M C n = n.justifiedHeight + 1 ∧ ∃ B ∈ n.tree, n.finalized.AncestorEq B ∧
      (M.chainStateOf C B).h = hMax M C n ∧ ¬ n.justified.AncestorEq B :=
  fg_contest_spec_of_core M F C P X n (F.nd.nodeInv_core hI) h

/-- A node state with `hMax M C n = n.justifiedHeight + 1` and a block of its tree, the finalized
block or a descendant of it, of chain-state height `hMax M C n`, that is not the justified block nor
a descendant of it, is contested.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block.

Read aloud: a block of the greatest height on the finalized block's chain and off the justified
block's chain makes the node contested, when the greatest height is one past the justification
height. -/
theorem fg_contest_true_of (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B : Block V) (hm : hMax M C n = n.justifiedHeight + 1)
    (hB : B ∈ n.tree) (hFB : n.finalized.AncestorEq B) (hh : (M.chainStateOf C B).h = hMax M C n)
    (hJB : ¬ n.justified.AncestorEq B) :
    M.fg_contest n = true := by
  rw [F.ndAdded.fg_contest_eq hI, if_neg (by rw [hm]; exact fun h => h rfl)]
  exact decide_eq_true ⟨B, hB, hFB, hh, hJB⟩

/-- **`floor_cases` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `floor_cases` is this theorem at
`F.nd.nodeInv_core hI`.

 A contested node state has `hMax M C n = n.justifiedHeight + 1` and `head_height_floor` equal
to `hMax M C n`; one not contested has `head_height_floor` equal to `hMax M C n - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: the least height of a viable block is the greatest height when the node is contested,
and one less otherwise. -/
theorem floor_cases_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) :
    (M.fg_contest n = true ∧ hMax M C n = n.justifiedHeight + 1 ∧
        M.head_height_floor n = hMax M C n) ∨
      (M.fg_contest n = false ∧ M.head_height_floor n = hMax M C n - 1) := by
  by_cases hc : M.fg_contest n = true
  · left
    exact ⟨hc, h_max_of_contested_of_core M F C P X n hI hc,
      by rw [F.ndAdded.head_height_floor_eq_of_core hI, if_pos hc]⟩
  · have hcf : M.fg_contest n = false := by simpa using hc
    right
    refine ⟨hcf, ?_⟩
    rw [F.ndAdded.head_height_floor_eq_of_core hI, hcf]
    rfl

/-- A contested node state has `hMax M C n = n.justifiedHeight + 1` and `head_height_floor` equal
to `hMax M C n`; one not contested has `head_height_floor` equal to `hMax M C n - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the least height of a viable block is the greatest height when the node is contested,
and one less otherwise. -/
theorem floor_cases (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) :
    (M.fg_contest n = true ∧ hMax M C n = n.justifiedHeight + 1 ∧
        M.head_height_floor n = hMax M C n) ∨
      (M.fg_contest n = false ∧ M.head_height_floor n = hMax M C n - 1) :=
  floor_cases_of_core M F C P X n (F.nd.nodeInv_core hI)

/-- **`head_height_floor_le_h_max` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `head_height_floor_le_h_max` is this theorem at
`F.nd.nodeInv_core hI`.

 `head_height_floor` is at most `hMax M C n`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: the least height of a viable block is at most the greatest height. -/
theorem head_height_floor_le_h_max_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) :
    M.head_height_floor n ≤ hMax M C n := by
  rw [F.ndAdded.head_height_floor_eq_of_core hI]
  split
  · exact le_refl _
  · exact Nat.sub_le _ 1

/-- `head_height_floor` is at most `hMax M C n`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the least height of a viable block is at most the greatest height. -/
theorem head_height_floor_le_h_max (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) :
    M.head_height_floor n ≤ hMax M C n :=
  head_height_floor_le_h_max_of_core M F C P X n (F.nd.nodeInv_core hI)

/-- **`floor_le_h_max` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `floor_le_h_max` is this theorem at
`F.nd.nodeInv_core hI`.

 `head_height_floor` is at most `hMax M C n`, as natural numbers.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: the least height of a viable block is at most the greatest height. -/
theorem floor_le_h_max_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) :
    (M.head_height_floor n : ℕ) ≤ (hMax M C n : ℕ) :=
  head_height_floor_le_h_max_of_core M F C P X n hI

/-- `head_height_floor` is at most `hMax M C n`, as natural numbers.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the least height of a viable block is at most the greatest height. -/
theorem floor_le_h_max (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) :
    (M.head_height_floor n : ℕ) ≤ (hMax M C n : ℕ) :=
  floor_le_h_max_of_core M F C P X n (F.nd.nodeInv_core hI)

/-- **`h_max_sub_one_le_floor` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `h_max_sub_one_le_floor` is this theorem at
`F.nd.nodeInv_core hI`.

 `head_height_floor` is at least `hMax M C n - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: the least height of a viable block is at least one less than the greatest height. -/
theorem h_max_sub_one_le_floor_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) :
    hMax M C n - 1 ≤ M.head_height_floor n := by
  rcases floor_cases_of_core M F C P X n hI with ⟨-, -, h⟩ | ⟨-, h⟩ <;> rw [h]
  exact Nat.sub_le _ _

/-- `head_height_floor` is at least `hMax M C n - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the least height of a viable block is at least one less than the greatest height. -/
theorem h_max_sub_one_le_floor (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) :
    hMax M C n - 1 ≤ M.head_height_floor n :=
  h_max_sub_one_le_floor_of_core M F C P X n (F.nd.nodeInv_core hI)

/-- **`h_max_le_floor_add_one` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `h_max_le_floor_add_one` is this theorem at
`F.nd.nodeInv_core hI`.

 `hMax M C n` is at most `head_height_floor` plus one.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: the greatest height is at most one more than the least height of a viable block. -/
theorem h_max_le_floor_add_one_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) :
    hMax M C n ≤ M.head_height_floor n + 1 := by
  have := h_max_sub_one_le_floor_of_core M F C P X n hI
  omega_nat

/-- `hMax M C n` is at most `head_height_floor` plus one.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the greatest height is at most one more than the least height of a viable block. -/
theorem h_max_le_floor_add_one (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) :
    hMax M C n ≤ M.head_height_floor n + 1 :=
  h_max_le_floor_add_one_of_core M F C P X n (F.nd.nodeInv_core hI)

/-- **`head_height_floor_of_not_contested` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `head_height_floor_of_not_contested` is this theorem at
`F.nd.nodeInv_core hI`.

 When the node state is not contested, `head_height_floor` is `hMax M C n - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`; `hc`: `n` is not contested.

Read aloud: when the node is not contested, the least height of a viable block is one less than
the greatest height. -/
theorem head_height_floor_of_not_contested_of_core (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (hI : M.nodeInvCore C P X n) (hc : M.fg_contest n = false) :
    M.head_height_floor n = hMax M C n - 1 := by
  rcases floor_cases_of_core M F C P X n hI with ⟨h, -, -⟩ | ⟨-, h⟩
  · rw [hc] at h
    cases h
  · exact h

/-- When the node state is not contested, `head_height_floor` is `hMax M C n - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `hc`: `n` is not contested.

Read aloud: when the node is not contested, the least height of a viable block is one less than
the greatest height. -/
theorem head_height_floor_of_not_contested (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (hI : M.nodeInv C P X n) (hc : M.fg_contest n = false) :
    M.head_height_floor n = hMax M C n - 1 :=
  head_height_floor_of_not_contested_of_core M F C P X n (F.nd.nodeInv_core hI) hc

/-- The fork-choice root is the justified block, with `hMax M C n = n.justifiedHeight + 1` and the
node not contested; or it is the finalized block, with the node contested or
`hMax M C n ≠ n.justifiedHeight + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: the fork-choice root is the justified block when the greatest height is one past the
justification height and the node is not contested, and the finalized block otherwise. -/
theorem root_cases (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) :
    (M.get_fc_root n = n.justified ∧ hMax M C n = n.justifiedHeight + 1 ∧
        M.fg_contest n = false) ∨
      (M.get_fc_root n = n.finalized ∧
        (M.fg_contest n = true ∨ hMax M C n ≠ n.justifiedHeight + 1)) := by
  by_cases hc : M.fg_contest n = true
  · right
    refine ⟨?_, Or.inl hc⟩
    rw [F.ndAdded.get_fc_root_eq hI, hc]
    simp
  · have hcf : M.fg_contest n = false := by simpa using hc
    by_cases hm : hMax M C n = n.justifiedHeight + 1
    · left
      refine ⟨?_, hm, hcf⟩
      rw [F.ndAdded.get_fc_root_eq hI, hcf, hm]
      simp
    · right
      refine ⟨?_, Or.inr hm⟩
      rw [F.ndAdded.get_fc_root_eq hI]
      simp [hm]

/-- When the fork-choice root is the finalized block (the node contested, or
`hMax M C n ≠ n.justifiedHeight + 1`) and `n.justifiedHeight < hMax M C n`, `head_height_floor` is
greater than `n.justifiedHeight`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: when the fork-choice root is the finalized block, the least height of a viable block
is greater than the justification height. -/
theorem h_j_lt_floor_of_root_F (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (hm : n.justifiedHeight < hMax M C n)
    (hor : M.fg_contest n = true ∨ hMax M C n ≠ n.justifiedHeight + 1) :
    n.justifiedHeight < M.head_height_floor n := by
  rcases floor_cases M F C P X n hI with ⟨-, hme, hfl1⟩ | ⟨hcf, hfl1⟩
  · rw [hfl1, hme]
    exact Nat.lt_succ_self _
  · rcases hor with hc | hne
    · rw [hcf] at hc
      cases hc
    · rw [hfl1]
      omega_nat

/-- With `n.justifiedHeight + 1 ≤ hMax M C n`, when the fork-choice root is not the justified
block, `head_height_floor` is at least `n.justifiedHeight + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: a node whose root is not its justified block finds no block viable at a height at most
its justification height. -/
theorem floor_of_root_ne_J (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (hm : n.justifiedHeight + 1 ≤ hMax M C n)
    (hroot : M.get_fc_root n ≠ n.justified) :
    n.justifiedHeight + 1 ≤ M.head_height_floor n := by
  rcases root_cases M F C P X n hI with ⟨h, -, -⟩ | ⟨-, hor⟩
  · exact absurd h hroot
  · exact h_j_lt_floor_of_root_F M F C P X n hI (by omega_nat) hor

/-- The fork-choice root is `L` or an ancestor of `L` when the tree holds `L` at the chain-state
height `hMax M C n`, on the finalized block's chain.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `L`: the block.

Read aloud: the fork-choice root is an ancestor of every block of the greatest height on the
finalized block's chain, or that block. -/
theorem fc_root_ancestorEq_of_tall (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (L : Block V) (hLT : L ∈ n.tree)
    (hFL : n.finalized.AncestorEq L) (hLh : (M.chainStateOf C L).h = hMax M C n) :
    (M.get_fc_root n).AncestorEq L := by
  rw [F.ndAdded.get_fc_root_eq hI]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨hbox, hcon⟩ := hc
    by_contra hJL
    have := fg_contest_true_of M F C P X n hI L hbox hLT hFL hLh hJL
    rw [hcon] at this
    exact Bool.false_ne_true this
  · exact hFL

/-- The fork-choice root is compatible with `B` when the justified block is, and the finalized
block is the justified block or an ancestor of it.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block.

Read aloud: the fork choice starts from a block compatible with `B` when the caches are. -/
theorem fc_root_compatible (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B : Block V)
    (hJ : n.justified.AncestorEq B ∨ B.AncestorEq n.justified)
    (hFJ : n.finalized.AncestorEq n.justified) :
    (M.get_fc_root n).compatible B = true := by
  have hF : n.finalized.compatible B = true := by
    rcases hJ with h | h
    · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ h))
    · exact (compatible_iff _ _).2 (ancestorEq_compatible hFJ h)
  rcases get_fc_root_cases M F C P X n hI with hr | hr <;> rw [hr]
  · exact (compatible_iff _ _).2 hJ
  · exact hF

/-- When the node state is in the first case of Lemma 56 (`BoxOne`) with
`lo ≤ hMax M C n - 1` and `hMax M C n ≤ hi + 1`, or in the third (`BoxThree`, contested) with
`lo ≤ hMax M C n ≤ hi`: its fork-choice root is its finalized block, its `head_height_floor` is
between `lo` and `hi`, and its justification height is less than `hi`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `lo`, `hi`: the bounds.

Read aloud: in the first or the third case of Lemma 56, the root is the finalized block and the
least height of a viable block lies within the bounds on the greatest height. -/
theorem floor_of_boxOne_or_boxThree (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (lo hi : ℕ)
    (h : (BoxOne M C n ∧ lo ≤ hMax M C n - 1 ∧ hMax M C n ≤ hi + 1) ∨
      (BoxThree M n ∧ lo ≤ hMax M C n ∧ hMax M C n ≤ hi)) :
    M.get_fc_root n = n.finalized ∧ lo ≤ M.head_height_floor n ∧ M.head_height_floor n ≤ hi ∧
      n.justifiedHeight < hi := by
  rcases h with ⟨hb, hlo, hhi⟩ | ⟨hb, hlo, hhi⟩
  · have hb' : n.justifiedHeight + 1 < hMax M C n := hb
    have hne : hMax M C n ≠ n.justifiedHeight + 1 := by omega_nat
    have hcf : M.fg_contest n = false := by
      rcases Bool.eq_false_or_eq_true (M.fg_contest n) with hc | hc
      · exact absurd (h_max_of_contested M F C P X n hI hc) hne
      · exact hc
    have hfl := head_height_floor_of_not_contested M F C P X n hI hcf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases root_cases M F C P X n hI with ⟨-, hm, -⟩ | ⟨hr, -⟩
      · exact absurd hm hne
      · exact hr
    · rw [hfl]; exact hlo
    · rw [hfl]; omega_nat
    · omega_nat
  · have hc : M.fg_contest n = true := hb
    have hm := h_max_of_contested M F C P X n hI hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases root_cases M F C P X n hI with ⟨-, -, hcf⟩ | ⟨hr, -⟩
      · rw [hc] at hcf; cases hcf
      · exact hr
    · rw [F.ndAdded.head_height_floor_eq hI, if_pos hc]; exact hlo
    · rw [F.ndAdded.head_height_floor_eq hI, if_pos hc]; exact hhi
    · omega_nat

/-- A block `B` of the tree is viable exactly when `head_height_floor` is at most its chain-state
height.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block, of the tree.

Read aloud: a block of the tree is viable when its chain-state height is at least the least height
of a viable block. -/
theorem is_viable_iff (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B : Block V) (hB : B ∈ n.tree) :
    M.is_viable n B = true ↔ M.head_height_floor n ≤ (M.chainStateOf C B).h := by
  rw [F.ndAdded.is_viable_eq hI hB, decide_eq_true_eq]

/-- A block of the tree at a chain-state height at least `hMax M C n` is a viable descendant of
each of its ancestors.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block; `Y`: the block of the tree.

Read aloud: a block of the tree at the greatest height is a viable descendant of each of its
ancestors. -/
theorem has_viable_descendant_of (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B Y : Block V) (hY : Y ∈ n.tree) (hBY : B.AncestorEq Y)
    (hh : hMax M C n ≤ (M.chainStateOf C Y).h) :
    M.has_viable_descendant n B = true := by
  rw [F.rd.has_viable_descendant_eq, decide_eq_true_eq]
  refine ⟨Y, hY, hBY, ?_⟩
  rw [F.ndAdded.is_viable_eq hI hY, decide_eq_true_eq]
  exact le_trans (head_height_floor_le_h_max M F C P X n hI) hh

/-- **`mem_viable_heads_iff` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `mem_viable_heads_iff` is this theorem at
`F.nd.nodeInv_core hI`.

 A block is a viable head of the frame `M.fg_to_ac n` exactly when it is in the tree, it is the
finalized block or a descendant of it, it is the frame's fork-choice root or a descendant of it,
and its chain-state height is at least `head_height_floor`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`; `B`: the block.

Read aloud: the viable heads are the blocks of the tree on the finalized block's and the root's
chains whose chain-state height is at least the least height of a viable block. -/
theorem mem_viable_heads_iff_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (B : Block V) :
    B ∈ (M.fg_to_ac n).viable_heads ↔
      B ∈ n.tree ∧ n.finalized.AncestorEq B ∧ (M.fg_to_ac n).fc_root.AncestorEq B ∧
        M.head_height_floor n ≤ (M.chainStateOf C B).h := by
  rw [F.rd.fg_to_ac_eq]
  simp only [Finset.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hB, hF⟩, hr, hv⟩
    rw [F.ndAdded.is_viable_eq_of_core hI hB, decide_eq_true_eq] at hv
    exact ⟨hB, hF, hr, hv⟩
  · rintro ⟨hB, hF, hr, hv⟩
    refine ⟨⟨hB, hF⟩, hr, ?_⟩
    rw [F.ndAdded.is_viable_eq_of_core hI hB, decide_eq_true_eq]
    exact hv

/-- A block is a viable head of the frame `M.fg_to_ac n` exactly when it is in the tree, it is the
finalized block or a descendant of it, it is the frame's fork-choice root or a descendant of it,
and its chain-state height is at least `head_height_floor`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block.

Read aloud: the viable heads are the blocks of the tree on the finalized block's and the root's
chains whose chain-state height is at least the least height of a viable block. -/
theorem mem_viable_heads_iff (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B : Block V) :
    B ∈ (M.fg_to_ac n).viable_heads ↔
      B ∈ n.tree ∧ n.finalized.AncestorEq B ∧ (M.fg_to_ac n).fc_root.AncestorEq B ∧
        M.head_height_floor n ≤ (M.chainStateOf C B).h :=
  mem_viable_heads_iff_of_core M F C P X n (F.nd.nodeInv_core hI) B

/-- A block of the tree that is the finalized block or a descendant of it, and the fork-choice root
or a descendant of it, at a chain-state height at least `head_height_floor`, is a viable head of
the frame `M.fg_to_ac n`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `W`: the block.

Read aloud: a block of the tree on the finalized block's and the root's chains, at height at least
the least height of a viable block, is a viable head. -/
theorem mem_viable_heads_of (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (W : Block V) (hWT : W ∈ n.tree) (hFW : n.finalized.AncestorEq W)
    (hrW : (M.get_fc_root n).AncestorEq W)
    (hfl : M.head_height_floor n ≤ (M.chainStateOf C W).h) :
    W ∈ (M.fg_to_ac n).viable_heads :=
  (mem_viable_heads_iff M F C P X n hI W).2
    ⟨hWT, hFW, by rw [fc_root_eq M F]; exact hrW, hfl⟩

/-- At a node state whose justified block is compatible with `B` and has the chain-state height
`n.justifiedHeight`, whose blocks two heights past `B` descend from `B`, with
`n.justifiedHeight < hMax M C n` and `h(B) + 1 ≤ n.justifiedHeight`: every viable head of the frame
`M.fg_to_ac n` is `B` or a descendant of `B`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block.

Read aloud: at a node justified past `B` whose caches are compatible with `B`, every viable head is
`B` or a descendant of `B`. -/
theorem viable_head_descends_of_justified_past (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (hI : M.nodeInv C P X n) (B : Block V)
    (hJ : n.justified.AncestorEq B ∨ B.AncestorEq n.justified)
    (hJh : (M.chainStateOf C n.justified).h = n.justifiedHeight)
    (hTwo : ∀ D ∈ n.tree, (M.chainStateOf C B).h + 2 ≤ (M.chainStateOf C D).h → B.AncestorEq D)
    (hjmax : n.justifiedHeight < hMax M C n)
    (hSafe : (M.chainStateOf C B).h + 1 ≤ n.justifiedHeight) :
    ∀ W ∈ (M.fg_to_ac n).viable_heads, B.AncestorEq W := by
  intro W hW
  obtain ⟨hWT, -, hroot, hv⟩ := (mem_viable_heads_iff M F C P X n hI W).1 hW
  rw [fc_root_eq M F] at hroot
  rcases floor_cases M F C P X n hI with ⟨-, hm, hfl⟩ | ⟨hc', hfl⟩
  · rw [hfl] at hv
    exact hTwo W hWT (by omega_nat)
  · rw [hfl] at hv
    by_cases hm : hMax M C n = n.justifiedHeight + 1
    · have hr : M.get_fc_root n = n.justified := by
        rcases root_cases M F C P X n hI with ⟨hr, -, -⟩ | ⟨-, hor⟩
        · exact hr
        · rcases hor with hc | hne
          · rw [hc'] at hc; cases hc
          · exact absurd hm hne
      rw [hr] at hroot
      have hBJ := descends_of_compatible_higher M F C hJ (by rw [hJh]; omega_nat)
      exact ancestorEq_trans hBJ hroot
    · exact hTwo W hWT (by omega_nat)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_fc_root_cases`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `get_fc_root_cases` holds at the FG state of every node state satisfying
the invariant. -/
theorem get_fc_root_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_fc_root_cases V _ n.S) := by
  intro C P X n hI
  exact get_fc_root_cases Model.goldilocks goldilocksFacts C P X n hI

/-- The landed `GoldilocksCorrectness.Proofs.Routines.F_ancestorEq_get_fc_root`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `F_ancestorEq_get_fc_root` holds at the FG state of every node state
satisfying the invariant. -/
theorem F_ancestorEq_get_fc_root_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.F_ancestorEq_get_fc_root V _ n.S) := by
  intro C P X n hI
  exact F_ancestorEq_get_fc_root Model.goldilocks goldilocksFacts C P X n hI

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fc_root_eq`, recovered from its record form at
the spec's model, at the FG state `n.S` of every node state `n`.

Read aloud: the landed `fc_root_eq` holds at the FG state of every node state. -/
theorem fc_root_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.fc_root_eq V _ n.S) := by
  intro n
  exact fc_root_eq Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.h_max_of_contested`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `h_max_of_contested` holds at the FG state of every node state satisfying
the invariant. -/
theorem h_max_of_contested_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.h_max_of_contested V _ _ n.S) := by
  intro C P X n hI hc
  rw [← hMax_goldilocks hI]
  exact h_max_of_contested Model.goldilocks goldilocksFacts C P X n hI hc

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fg_contest_spec`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `fg_contest_spec` holds at the FG state of every node state satisfying the
invariant. -/
theorem fg_contest_spec_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.fg_contest_spec V _ n.S) := by
  intro C P X n hI h
  obtain ⟨h1, B, hB, h2, h3, h4⟩ := fg_contest_spec Model.goldilocks goldilocksFacts C P X n hI h
  rw [hMax_goldilocks hI] at h1 h3
  refine ⟨h1, B, hB, h2, ?_, h4⟩
  rw [hI.1.2.2.2.2.2.1 B hB]
  exact h3

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fg_contest_true_of`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `fg_contest_true_of` holds at the FG state of every node state satisfying
the invariant. -/
theorem fg_contest_true_of_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.fg_contest_true_of V _ n.S) := by
  intro C P X n hI B hm hB hFB hh hJB
  refine fg_contest_true_of Model.goldilocks goldilocksFacts C P X n hI B
    (by rw [hMax_goldilocks hI]; exact hm) hB hFB ?_ hJB
  rw [hMax_goldilocks hI, ← hh, hI.1.2.2.2.2.2.1 B hB]
  rfl

/-- The landed `GoldilocksCorrectness.Proofs.Routines.floor_cases`, recovered from its record form at
the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's model's node
invariant.

Read aloud: the landed `floor_cases` holds at the FG state of every node state satisfying the
invariant. -/
theorem floor_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.floor_cases V _ n.S) := by
  intro C P X n hI
  have h := floor_cases Model.goldilocks goldilocksFacts C P X n hI
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.head_height_floor_le_h_max`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `head_height_floor_le_h_max` holds at the FG state of every node state
satisfying the invariant. -/
theorem head_height_floor_le_h_max_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.head_height_floor_le_h_max V _ n.S) := by
  intro C P X n hI
  have h := head_height_floor_le_h_max Model.goldilocks goldilocksFacts C P X n hI
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.floor_le_h_max`, recovered from its record form
at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's model's
node invariant.

Read aloud: the landed `floor_le_h_max` holds at the FG state of every node state satisfying the
invariant. -/
theorem floor_le_h_max_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.floor_le_h_max V _ n.S) := by
  intro C P X n hI
  have h := floor_le_h_max Model.goldilocks goldilocksFacts C P X n hI
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.h_max_sub_one_le_floor`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `h_max_sub_one_le_floor` holds at the FG state of every node state
satisfying the invariant. -/
theorem h_max_sub_one_le_floor_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.h_max_sub_one_le_floor V _ n.S) := by
  intro C P X n hI
  have h := h_max_sub_one_le_floor Model.goldilocks goldilocksFacts C P X n hI
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.h_max_le_floor_add_one`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `h_max_le_floor_add_one` holds at the FG state of every node state
satisfying the invariant. -/
theorem h_max_le_floor_add_one_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.h_max_le_floor_add_one V _ n.S) := by
  intro C P X n hI
  have h := h_max_le_floor_add_one Model.goldilocks goldilocksFacts C P X n hI
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.head_height_floor_of_not_contested`, recovered
from its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying
the spec's model's node invariant.

Read aloud: the landed `head_height_floor_of_not_contested` holds at the FG state of every node
state satisfying the invariant. -/
theorem head_height_floor_of_not_contested_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.head_height_floor_of_not_contested V _
        n.S) := by
  intro C P X n hI hc
  rw [← hMax_goldilocks hI]
  exact head_height_floor_of_not_contested Model.goldilocks goldilocksFacts C P X n hI hc

/-- The landed `GoldilocksCorrectness.Proofs.Routines.root_cases`, recovered from its record form at
the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's model's node
invariant.

Read aloud: the landed `root_cases` holds at the FG state of every node state satisfying the
invariant. -/
theorem root_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.root_cases V _ n.S) := by
  intro C P X n hI
  have h := root_cases Model.goldilocks goldilocksFacts C P X n hI
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.h_j_lt_floor_of_root_F`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `h_j_lt_floor_of_root_F` holds at the FG state of every node state
satisfying the invariant. -/
theorem h_j_lt_floor_of_root_F_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.h_j_lt_floor_of_root_F V _ n.S) := by
  intro C P X n hI
  rw [← hMax_goldilocks hI]
  exact h_j_lt_floor_of_root_F Model.goldilocks goldilocksFacts C P X n hI

/-- The landed `GoldilocksCorrectness.Proofs.Routines.floor_of_root_ne_J`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `floor_of_root_ne_J` holds at the FG state of every node state satisfying
the invariant. -/
theorem floor_of_root_ne_J_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.floor_of_root_ne_J V _ n.S) := by
  intro C P X n hI
  rw [← hMax_goldilocks hI]
  exact floor_of_root_ne_J Model.goldilocks goldilocksFacts C P X n hI

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fc_root_ancestorEq_of_tall`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `fc_root_ancestorEq_of_tall` holds at the FG state of every node state
satisfying the invariant. -/
theorem fc_root_ancestorEq_of_tall_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.fc_root_ancestorEq_of_tall V _ n.S) := by
  intro C P X n hI L hL hFL hLh
  refine fc_root_ancestorEq_of_tall Model.goldilocks goldilocksFacts C P X n hI L hL hFL ?_
  rw [hMax_goldilocks hI, ← hLh, hI.1.2.2.2.2.2.1 L hL]
  rfl

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fc_root_compatible`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `fc_root_compatible` holds at the FG state of every node state satisfying
the invariant. -/
theorem fc_root_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.fc_root_compatible V _ _ n.S) := by
  intro C P X n hI
  exact fc_root_compatible Model.goldilocks goldilocksFacts C P X n hI

/-- The landed `GoldilocksCorrectness.Proofs.Routines.floor_of_boxOne_or_boxThree`, recovered from
its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `floor_of_boxOne_or_boxThree` holds at the FG state of every node state
satisfying the invariant. -/
theorem floor_of_boxOne_or_boxThree_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.floor_of_boxOne_or_boxThree V _ n.S) := by
  intro C P X n hI lo hi h
  have hH := (hMax_goldilocks hI).symm
  refine floor_of_boxOne_or_boxThree Model.goldilocks goldilocksFacts C P X n hI lo hi ?_
  rcases h with ⟨hb, hlo, hhi⟩ | ⟨hb, hlo, hhi⟩
  · rw [hH] at hlo hhi
    exact Or.inl ⟨(GoldilocksCorrectness.Record.Statements.Routines.goldilocks_BoxOne C n hH).1 hb,
      hlo, hhi⟩
  · rw [hH] at hlo hhi
    exact Or.inr ⟨hb, hlo, hhi⟩

/-- The landed `GoldilocksCorrectness.Proofs.Routines.has_viable_descendant_of`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `has_viable_descendant_of` holds at the FG state of every node state
satisfying the invariant. -/
theorem has_viable_descendant_of_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.has_viable_descendant_of V _ n.S) := by
  intro C P X n hI B Y hY hBY hh
  refine has_viable_descendant_of Model.goldilocks goldilocksFacts C P X n hI B Y hY hBY ?_
  rw [hMax_goldilocks hI]
  show n.S.h_max ≤ (GoldilocksCorrectness.Statements.Routines.chainStateOf C Y).h
  rw [← hI.1.2.2.2.2.2.1 Y hY]
  exact hh

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_viable_heads_iff`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `mem_viable_heads_iff` holds at the FG state of every node state satisfying
the invariant. -/
theorem mem_viable_heads_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_viable_heads_iff V _ n.S) := by
  intro C P X n hI B
  have hσ := hI.1.2.2.2.2.2.1
  refine (mem_viable_heads_iff Model.goldilocks goldilocksFacts C P X n hI B).trans
    ⟨fun ⟨hB, hF, hr, hv⟩ => ⟨hB, hF, hr, ?_⟩, fun ⟨hB, hF, hr, hv⟩ => ⟨hB, hF, hr, ?_⟩⟩
  · show Goldilocks.head_height_floor n.S ≤ (n.S.σ B).h
    rw [hσ B hB]
    exact hv
  · show Goldilocks.head_height_floor n.S ≤
      (GoldilocksCorrectness.Statements.Routines.chainStateOf C B).h
    rw [← hσ B hB]
    exact hv

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_viable_heads_of`, recovered from its record
form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `mem_viable_heads_of` holds at the FG state of every node state satisfying
the invariant. -/
theorem mem_viable_heads_of_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_viable_heads_of V _ _ C n.S) := by
  intro C P X n hI W _ hWT hFW hrW hfl
  exact mem_viable_heads_of Model.goldilocks goldilocksFacts C P X n hI W hWT hFW hrW hfl

/-- The landed `GoldilocksCorrectness.Proofs.Routines.viable_head_descends_of_justified_past`,
recovered from its record form at the spec's model, at the FG state `n.S` of every node state `n`
satisfying the spec's model's node invariant.

Read aloud: the landed `viable_head_descends_of_justified_past` holds at the FG state of every node
state satisfying the invariant. -/
theorem viable_head_descends_of_justified_past_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.viable_head_descends_of_justified_past V _ _
        C n.S) := by
  intro C P X n hI B _ hJ hJh hTwo hjmax hSafe
  exact viable_head_descends_of_justified_past Model.goldilocks goldilocksFacts C P X n hI B hJ hJh
    hTwo (by rw [hMax_goldilocks hI]; exact hjmax) hSafe

end GoldilocksCorrectness.Record.Proofs.Routines
