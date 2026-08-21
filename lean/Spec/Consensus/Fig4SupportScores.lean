import Spec.Consensus.Fig2FinalityStore
import Spec.Consensus.Fig3Schedule

/-!
# Figure 4 — Support scores in round `r`

Definition 11's support sets and scores, Figure 4's two evaluators, and Definition 12's
grades. Round `r` grades the heads of the round-`(r−1)` attestations through the timed
store's head bookkeeping: the scores compare stored processing times against the round's
grade instants, so a grade evaluated at any time after its instants gives one fixed answer.

The `-- line n` comments use Figure 4's own line numbering, in the draft as of 2026-08-19.

## The round-`(r−1)` entries, and round 0

Definition 11 reads `Σ.head[r−1]` and `Σ.equiv[r−1]`, and says that for round 0 the
round-`(−1)` entries are empty, so every score is 0. Round indices are `Nat` here, where
`0 − 1` would silently read round 0's own entries, so the two reads go through
`Store.prevHead` and `Store.prevEquiv`, which are empty at `r = 0` by definition — the
draft's clause, made a case rather than left to arithmetic.

## The scores are the components Figure 4 returns

`S_j(B)` and `S̄_j(B)` are the two components of `supportScores`, and `S_{−1,1}(B)` is
`twoViewSupport` — Definition 12's grades read them as such rather than through separately
named score functions, so there is exactly one rendering of each expression.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator : Type}

/-- The round-`(r−1)` head entries Definition 11 reads — empty for `r = 0`, the draft's
    "for round 0 the round-`(−1)` entries are empty". -/
def Store.prevHead (S : Store Validator) :
    StoreTable Validator (Block Validator × Int)
  | 0 => fun _ => none
  | r + 1 => S.head[r]

/-- The round-`(r−1)` equivocation entries Definition 11 reads — empty for `r = 0`,
    likewise. -/
def Store.prevEquiv (S : Store Validator) : StoreTable Validator Int
  | 0 => fun _ => none
  | r + 1 => S.equiv[r]

section Scores
variable [DecidableEq Validator] [Electorate Validator] [Params]

/-- `H_j(B)` (Definition 11): the validators whose stored round-`(r−1)` head was processed
    before round `r`'s instant `Γ^j` and supports `B` — the stored entry is `(H, t_H)` with
    `t_H < Γ^j` and `B ⪯ H`. Intersected with the electorate, since only `V`'s weights are
    ever summed. -/
def supporters (S : Store Validator) (r : Nat) (j : Int) (B : Block Validator) :
    Finset Validator :=
  {i ∈ Electorate.V | (S.prevHead[r] i).any fun (H, tH) => tH < gradeInstant r j ∧ B ⪯ H}

/-- `E_j` (Definition 11): the validators whose stored round-`(r−1)` equivocation time is
    before round `r`'s instant `Γ^j`. Likewise intersected with the electorate. -/
def equivocators (S : Store Validator) (r : Nat) (j : Int) : Finset Validator :=
  {i ∈ Electorate.V | (S.prevEquiv[r] i).any fun tE => tE < gradeInstant r j}

/-- `support_scores(Σ, r, j, B)` (Figure 4, lines 1–4): the pair
    `(S_j(B), S̄_j(B)) = (w(H_j(B) \ E_j), w(H_j(B) ∪ E_j))` — the pessimistic score drops
    the equivocators, the optimistic one adds them all. -/
def supportScores (S : Store Validator) (r : Nat) (j : Int) (B : Block Validator) :
    Nat × Nat := Id.run do
  let Hj := supporters S r j B                                -- line 2
  let Ej := equivocators S r j                                -- line 3
  return (w(Hj \ Ej), w(Hj ∪ Ej))                             -- line 4: `S_j(B), S̄_j(B)`

/-- `two_view_support(Σ, r, B)` (Figure 4, lines 5–8):
    `S_{−1,1}(B) = w(H_{−1}(B) \ E_1)` — the head cutoff from `Γ^{−1}`, the equivocation
    cutoff from `Γ^1`, which is why Figure 6 writes grade 3 at `Γ^1`. -/
def twoViewSupport (S : Store Validator) (r : Nat) (B : Block Validator) : Nat := Id.run do
  let Hneg := supporters S r (-1) B                           -- line 6
  let E1 := equivocators S r 1                                -- line 7
  return w(Hneg \ E1)                                         -- line 8: `S_{−1,1}(B)`

/-! ## Definition 12 — the grades

A grade is computed when a rule tests it; evaluated at any time after its instants it gives
one fixed answer. Support counts descendants, so every grade is inherited by ancestors; two
conflicting blocks cannot both hold direct support `m`, so the blocks with grade 2, and
those with grade 3, lie on one chain. Those are the draft's observations, to be proved
where needed, not extra clauses here. -/

/-- `G3(B) ⇔ S_{−1,1}(B) ≥ m` (Definition 12). -/
def G3 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  twoViewSupport S r B ≥ m Validator

/-- `G2(B) ⇔ S_0(B) ≥ m` (Definition 12). -/
def G2 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  (supportScores S r 0 B).1 ≥ m Validator

/-- `G1(B) ⇔ S̄_1(B) ≥ m` (Definition 12). -/
def G1 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  (supportScores S r 1 B).2 ≥ m Validator

/-- `G0(B) ⇔ S̄_2(B) ≥ m` (Definition 12). -/
def G0 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  (supportScores S r 2 B).2 ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (G3 S r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (G2 S r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (G1 S r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (G0 S r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

end Scores

end Consensus
