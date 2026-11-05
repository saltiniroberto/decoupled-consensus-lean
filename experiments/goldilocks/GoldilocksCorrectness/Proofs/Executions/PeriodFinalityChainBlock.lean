module
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Executions.HeightInvariant

@[expose] public section

/-!
# Lemmas 103 and 106 at a step, over the copied certificate clause

The proofs of the step lemmas of Lemma 103 (the caches stay compatible with `B`) and Lemma 106 (a
held block two heights past `B` descends from `B`), stated in
`GoldilocksCorrectness/Statements/Executions/PeriodFinalityChainBlockStatements.lean`, over the
copied certificate clause `CertificatesCompatibleWithAtOfChainBlock`:

- `caches_step_ofChainBlock`: Lemma 84's step (`lem84_caches_stay_on_chain`) with the family
  "compatible with `B`";
- `blocksTwoPastDescend_at_ofChainBlock`: Lemma 67's route at height `h(B) + 1`.

The probe's statements (`scratch/goldilocks_async/probe_lanes_1.lean:705`, `:721`), over the
original clause, are false.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (JustifiedOnChainWith chainStateOf_height_mono)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (CachesFrom cachesFrom_of_frame cachesFrom_refl
  cachesFrom_trans)

open GoldilocksCorrectness.Proofs.Routines (reaction_tick_cachesFrom receive_cachesFrom)
open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn lem66_chain_state_certified)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans on_chain_mono)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Lemma 103, the step -/

/-- **Lemma 103, the step: the caches stay compatible with `B`.** The proof; the audited
statement is in `Statements/Executions/PeriodFinalityChainBlockStatements.lean`. Lemma 84's step
with the family `fun E => E.AncestorEq B ∨ B.AncestorEq E`: the step relates `u`'s state at `j`
to its state at `j + 1` (`CachesFrom`, by `step_cases`), and every block `D` of `u`'s tree at
`j + 1` with a justification height greater than `H` has its justified block compatible with `B`
(the copied certificate clause at `j + 1`, for the justification certificate on `D`'s chain,
Lemma 66, read as a progress certificate), an entry (Lemma 47f) at that height (Lemma 66).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step; `u`: the validator. -/
theorem caches_step_ofChainBlock (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {H : ℕ} {B : Block V} (j : ℕ) (u : V)
    (hu : u ∉ Sched.adv (x[j + 1].time : Int))
    (hC : CachesCompatibleWith S B H (x[j][u].st))
    (hCert : CertificatesCompatibleWithAtOfChainBlock S Sched x H B (j + 1)) :
    CachesCompatibleWith S B H (x[j + 1][u].st) := by
  have hCS := (lem11_node_invariant S Sched x j u).1.2.2.2.2.2.1
  -- every block of `u`'s tree after the step has its justified block compatible with `B`
  have hJ : ∀ D ∈ (x[j + 1][u].st).S.T,
      JustifiedOnChainWith S.C H (fun E => E.AncestorEq B ∨ B.AncestorEq E) D := by
    intro D hD hH
    have h1 : 1 ≤ (chainStateOf S.C D).h_j := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le H) hH)
    obtain ⟨hcert, hJD, hJh⟩ := (lem66_chain_state_certified S.C D).1 h1
    refine ⟨hCert u D _ _ hu hD hJD (progressCertOn_of_justificationCertOn hcert) hH, ?_, hJh⟩
    -- the justified block is an entry
    obtain ⟨Y, -, -, hYT⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem47f_justified_is_entry S.C D _ rfl h1
    unfold IsEntry
    rw [← hYT]
    exact chainStateOf_T_h_T_h S.C Y
  have hrel : CachesFrom S.C H (fun E => E.AncestorEq B ∨ B.AncestorEq E) (x[j][u].st)
      (x[j + 1][u].st) := by
    rcases step_cases x j u with h | ⟨t, n', sent, -, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
    · rw [h]
      exact cachesFrom_refl _ _ _ _
    · rw [h]
      obtain ⟨hS, -, -⟩ := tickInputState_frame x j t u
      have h1 := reaction_tick_cachesFrom S H (fun E => E.AncestorEq B ∨ B.AncestorEq E)
        (tickInputState x j t u) n' (t : Int) sent hok (by rw [hS]; exact hCS)
      exact cachesFrom_trans _ _ _ (cachesFrom_of_frame _ _ _ (congrArg FGState.T hS)
        (congrArg FGState.J hS) (congrArg FGState.h_j hS) (congrArg FGState.F hS)) h1
    · rw [h]
      exact receive_cachesFrom S.C S.P S.X H _ _ _ hCS
  exact hrel.2 hJ hC

/-! ## Lemma 106, the step -/

/-- **Lemma 106 at a step: a held block two heights past `B` descends from `B`.** The proof; the
audited statement is in `Statements/Executions/PeriodFinalityChainBlockStatements.lean`. Lemma 67
at the height `h(B) + 1` gives a block `Y` of `D`'s chain whose chain holds a progress certificate
at `h(B) + 1` for its own entry `T'` at `h(B) + 1`, `T'` an ancestor of `Y`; the copied
certificate clause makes `T'` compatible with `B`; its height `h(B) + 1` rules out `T'` being an
ancestor of `B` (heights grow along a chain), so `B` is an ancestor of `T'`, hence of `D`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step. -/
theorem blocksTwoPastDescend_at_ofChainBlock (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {H : ℕ} {B : Block V} (j : ℕ)
    (hHB : H < (chainStateOf S.C B).h)
    (hCert : CertificatesCompatibleWithAtOfChainBlock S Sched x H B j) :
    ∀ (w : V) (D : Block V), w ∉ Sched.adv (x[j].time : Int) → D ∈ (x[j][w].st).S.T →
      (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D := by
  intro w D hw hD hDh
  obtain ⟨Y, hYD, -, hYph, -, hTY, hcert⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem67_first_advance S.C D
      ((chainStateOf S.C B).h + 1) (by omega_nat) (by omega_nat)
  have hT'D : (chainStateOf S.C Y.parent).T_h.AncestorEq D := ancestorEq_trans hTY hYD
  have hT'h : (chainStateOf S.C (chainStateOf S.C Y.parent).T_h).h =
      (chainStateOf S.C B).h + 1 := by
    rw [(GoldilocksCorrectness.Proofs.Routines.isEntry_T_h S.C Y.parent).2.1, hYph]
  -- the certificate on `Y`'s chain is on `D`'s chain
  have hcertD : ProgressCertOn D ((chainStateOf S.C B).h + 1)
      (chainStateOf S.C Y.parent).T_h := by
    obtain ⟨A, hA, hv⟩ := hcert
    refine ⟨A, hA, fun v hvA => ?_⟩
    obtain ⟨a, h1, h2, h3, h4⟩ := hv v hvA
    exact ⟨a, h1, h2, h3, on_chain_mono a hYD h4⟩
  rcases hCert w D _ _ hw hD hT'D hcertD (by omega_nat) with h | h
  · -- an ancestor of `B` has a height at most `h(B)`
    have := chainStateOf_height_mono S.C h
    omega_nat
  · exact ancestorEq_trans h hT'D

end GoldilocksCorrectness.Proofs.Executions
