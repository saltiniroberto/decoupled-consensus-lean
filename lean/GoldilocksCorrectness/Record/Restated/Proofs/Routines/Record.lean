module
public import GoldilocksCorrectness.Record.Facts

@[expose] public section

/-!
# Record, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Record.lean` on the readers of the
node's anti-slashing record, over a model `M` whose facts `F` hold, each the field of
`ReaderFacts` it restates: `finality_pair`, `own_lock` and `height_pair` by their cases.
The page's theorems on `record_attestation`, `create_attestation` and Lemma 72 read routines
the record has no member for; they are restated with the tick's family.

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

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- When `finality_pair` returns a pair, it is `(h_j, J)`, `h_F < h_j`, and the node's
anti-slashing record holds at
`h_j` no target other than `J`, no timeout and no lock other than `J`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `h_j`, `J`, `h_F`: the justification height, the justified root and the
  finalization height; `p`: the pair returned.

Read aloud: when `finality_pair` returns a pair, it is the justification `(h_j, J)`, the justification is not finalized, and the record holds at `h_j` no target and no lock for another block and no timeout. -/
theorem finality_pair_some {n : M.N} {h_j : Height} {J : BlockId} {h_F : Height}
    {p : FinalityPair} (hfp : M.finality_pair n h_j J h_F = some p) :
    p = ⟨h_j, J⟩ ∧ h_F < h_j ∧ (∀ T : BlockId, n.sentTarget h_j = some T → T = J) ∧
      n.sentTimeout h_j = false ∧ (∀ T : BlockId, n.sentLock h_j = some T → T = J) :=
  F.rd.finality_pair_some hfp

/-- The lock `own_lock` reads at `h` is the record's lock at `h`, or the target of the finality
pair `fp` when `fp` is at `h`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `h`: the height; `fp`: the finality pair.

Read aloud: the lock `own_lock` reads at `h` is the record's lock at `h`, or the block of the finality pair `fp` when `fp` is at `h`. -/
theorem own_lock_cases (n : M.N) (h : Height) (fp : Option FinalityPair) :
    M.own_lock n h fp = n.sentLock h ∨
      ∃ q : FinalityPair, fp = some q ∧ q.hf = h ∧ M.own_lock n h fp = some q.Tf :=
  F.rd.own_lock_cases n h fp

/-- A height pair `height_pair` computes from the source `(h_c, T_c)` that is a vote is at `h_c`
and names `T_c`; a target vote is cast only when the record holds no timeout at `h_c` and the lock
read at `h_c` is unset or `T_c`; a timeout only when the record holds a timeout at `h_c` or the lock
read at `h_c` is unset.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `h_c`, `T_c`: the source's height and root; `fp`: the finality pair;
- `h`, `T`, `τ`: the vote.

Read aloud: a vote `height_pair` computes from the source `(h_c, T_c)` is at `h_c` for `T_c`; it is a target only where the record holds no timeout and the lock read is unset or `T_c`, and a timeout only where the record holds a timeout or the lock read is unset. -/
theorem height_pair_vote_cases {n : M.N} {h_c : Height} {T_c : BlockId}
    {fp : Option FinalityPair} {h : Height} {T : BlockId} {τ : Bool}
    (hp : M.height_pair n (some (h_c, T_c)) fp = .vote h T τ) :
    h = h_c ∧ T = T_c ∧
      (τ = false → n.sentTimeout h_c = false ∧
        ∀ L : BlockId, M.own_lock n h_c fp = some L → L = T_c) ∧
      (τ = true → n.sentTimeout h_c = true ∨ M.own_lock n h_c fp = none) :=
  F.rd.height_pair_vote_cases hp

/-- A timeout `height_pair` computes from the source `(h_c, T_c)` is cast only when the record
holds a timeout at `h_c`, or a target at `h_c` for a block other than `T_c`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `h_c`, `T_c`: the source's height and root; `fp`: the finality pair;
- `h`, `T`: the vote's height and root.

Read aloud: a timeout `height_pair` computes from the source `(h_c, T_c)` is cast only where the record holds a timeout at `h_c`, or a target at `h_c` for a block other than `T_c`. -/
theorem height_pair_timeout {n : M.N} {h_c : Height} {T_c : BlockId}
    {fp : Option FinalityPair} {h : Height} {T : BlockId}
    -- `M.height_pair` computes a timeout
    (hp : M.height_pair n (some (h_c, T_c)) fp = .vote h T true) :
    n.sentTimeout h_c = true ∨ ∃ T' : BlockId, n.sentTarget h_c = some T' ∧ T' ≠ T_c :=
  F.rd.height_pair_timeout hp

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.finality_pair_some`,
recovered from its record form at the spec's model, at
the anti-slashing record `n.Λ` of every node state `n`.

Read aloud: the landed `finality_pair_some` holds at the anti-slashing record `n.Λ` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem finality_pair_some_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.finality_pair_some n.Λ) := by
  intro n
  exact finality_pair_some (n := n) Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.own_lock_cases`,
recovered from its record form at the spec's model, at
the anti-slashing record `n.Λ` of every node state `n`.

Read aloud: the landed `own_lock_cases` holds at the anti-slashing record `n.Λ` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem own_lock_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.own_lock_cases n.Λ) := by
  intro n
  exact own_lock_cases Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.height_pair_vote_cases`,
recovered from its record form at the spec's model, at
the anti-slashing record `n.Λ` of every node state `n`.

Read aloud: the landed `height_pair_vote_cases` holds at the anti-slashing record `n.Λ` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem height_pair_vote_cases_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.height_pair_vote_cases n.Λ) := by
  intro n
  exact height_pair_vote_cases (n := n) Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.height_pair_timeout`,
recovered from its record form at the spec's model, at
the anti-slashing record `n.Λ` of every node state `n`.

Read aloud: the landed `height_pair_timeout` holds at the anti-slashing record `n.Λ` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem height_pair_timeout_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.height_pair_timeout n.Λ) := by
  intro n
  exact height_pair_timeout (n := n) Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
