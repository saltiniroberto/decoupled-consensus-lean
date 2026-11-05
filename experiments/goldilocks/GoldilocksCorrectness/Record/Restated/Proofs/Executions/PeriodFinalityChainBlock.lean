module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Executions.HeightInvariant

@[expose] public section

/-!
# PeriodFinalityChainBlock, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodFinalityChainBlock.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the step lemmas of Lemmas
103 and 106 over the copied certificate clause, the caches staying compatible with `B` and a held
block two heights past `B` descending from `B`. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (CachesFrom cachesFrom_of_frame cachesFrom_refl
  cachesFrom_trans)

open GoldilocksCorrectness.Proofs.Routines (reaction_tick_cachesFrom receive_cachesFrom)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith)
open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedOnChainWith CachesOnChainWith)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

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
to its state at `j + 1` (`CachesFrom`, by `step_cases_per_step`), and every block `D` of `u`'s tree at
`j + 1` with a justification height greater than `H` has its justified block compatible with `B`
(the copied certificate clause at `j + 1`, for the justification certificate on `D`'s chain,
Lemma 66, read as a progress certificate), an entry (Lemma 47f) at that height (Lemma 66).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step; `u`: the validator.

Read aloud: the step of Lemma 103 over the certificate clause that speaks of the chain's own block.
-/
theorem caches_step_ofChainBlock (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {H : ℕ} {B : Block V} (j : ℕ) (u : V)
    (hu : u ∉ A.corrupted (j + 1))
    (hC : CachesCompatibleWith M S B H (x.st j u))
    (hCert : CertificatesCompatibleWithAtOfChainBlock M A x H B (j + 1)) :
    CachesCompatibleWith M S B H (x.st (j + 1) u) := by
  -- every block of `u`'s tree after the step has its justified block compatible with `B`
  have hJ : ∀ D ∈ (x.st (j + 1) u).tree,
      JustifiedOnChainWith M S.C H (fun E => E.AncestorEq B ∨ B.AncestorEq E) D := by
    intro D hD hH
    have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le H) hH)
    obtain ⟨hcert, hJD, hJh⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
    -- the record's progress certificate on `D`'s chain (some block `X ⪯ D` with a set reaching the
    -- quorum at `X`) is the copied clause's (the spec's): with fixed validators the quorum at `X` is
    -- `quorum V`, and a vote on `X`'s chain is on `D`'s chain
    have hcertL : GoldilocksCorrectness.Statements.Routines.ProgressCertOn D (M.chainStateOf S.C D).h_j
        (M.chainStateOf S.C D).J := by
      obtain ⟨X, hXD, A, hA, hvA⟩ := (progressCertOn_of_justificationCertOn M F) hcert
      refine ⟨A, ?_, fun v hv => ?_⟩
      · rw [← GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X]
        exact hA
      · obtain ⟨a, h2, h3, h4, h5⟩ := hvA v hv
        exact ⟨a, h2, h3, h4, GoldilocksCorrectness.Proofs.Routines.on_chain_mono a hXD
          ((GoldilocksCorrectness.Proofs.Routines.on_chain_iff a X).2
            ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F a X).1 h5))⟩
    refine ⟨hCert u D _ _ hu hD hJD hcertL hH, ?_, hJh⟩
    -- the justified block is an entry
    obtain ⟨Y, -, -, hYT⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem47f_justified_is_entry M F) S.C D _ rfl h1
    unfold IsEntry
    rw [← hYT]
    exact (chainStateOf_T_h_T_h M F) S.C Y
  -- the step keeps the state, or runs the tick or a delivery (the fields `tick_cachesFrom` and
  -- `receive_cachesFrom`, from a node state satisfying the node invariant); `CachesCompatibleWith`
  -- is `CachesOnChainWith` for the family "compatible with `B`"
  have hI := (lem11_node_invariant M F S A x R E j u (E.not_mem_corrupted_of_le (Nat.le_succ j) hu)).1
  show CachesOnChainWith M S.C H (fun E => E.AncestorEq B ∨ B.AncestorEq E) (x.st (j + 1) u)
  have hC' : CachesOnChainWith M S.C H (fun E => E.AncestorEq B ∨ B.AncestorEq E) (x.st j u) := hC
  rcases (step_cases_per_step M F) x R E j u with h | ⟨t, n', sent, hl, -, hok, h, -⟩ | ⟨sm, -, -, h⟩ |
      ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h]
    exact hC'
  · rw [h] at hJ ⊢
    -- the tick's input state is `u`'s state at step `j`, the step of the tick
    have hTIj : x.tickInput u t = x.st j u := by
      show x.st (x.tickStep u t) u = x.st j u
      rw [(tickStep_eq_of_lbl M) x E hl]
    have hInvT : M.nodeInv S.C S.P S.X (x.tickInput u t) := by
      rw [hTIj]
      exact hI
    have hCT : CachesOnChainWith M S.C H (fun E => E.AncestorEq B ∨ B.AncestorEq E)
        (x.tickInput u t) := by
      rw [hTIj]
      exact hC'
    exact (F.tk.tick_cachesFrom S.C S.P S.X H _ _ (t : Int) n' sent hok hInvT).2 hJ hCT
  · rw [h] at hJ ⊢
    exact (F.rcv.receive_cachesFrom S.C S.P S.X H _ _ _ hI).2 hJ hC'
  · -- a wake keeps the justification, its height and the finalized block
    rw [h tRw keepw hlw]
    obtain ⟨-, -, -, hFin, hJus, hJh, -⟩ := F.wk.wake_readers (x.st j u) (tRw : Int)
    have e1 : (M.wake (x.st j u) (tRw : Int)).finalized = (x.st j u).finalized := hFin
    have e2 : (M.wake (x.st j u) (tRw : Int)).justified = (x.st j u).justified := hJus
    have e3 : (M.wake (x.st j u) (tRw : Int)).justifiedHeight = (x.st j u).justifiedHeight := hJh
    unfold CachesOnChainWith
    rw [e1, e2, e3]
    exact hC'

/-! ## Lemma 106, the step -/

/-- **Lemma 106 at a step: a held block two heights past `B` descends from `B`.** The proof; the
audited statement is in `Statements/Executions/PeriodFinalityChainBlockStatements.lean`. Lemma 67
at the height `h(B) + 1` gives a block `Y` of `D`'s chain whose chain holds a progress certificate
at `h(B) + 1` for its own entry `T'` at `h(B) + 1`, `T'` an ancestor of `Y`; the copied
certificate clause makes `T'` compatible with `B`; its height `h(B) + 1` rules out `T'` being an
ancestor of `B` (heights grow along a chain), so `B` is an ancestor of `T'`, hence of `D`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step.

Read aloud: the step of Lemma 106 over the certificate clause that speaks of the chain's own block.
-/
theorem blocksTwoPastDescend_at_ofChainBlock (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) {H : ℕ} {B : Block V} (j : ℕ)
    (hHB : H < (M.chainStateOf S.C B).h)
    (hCert : CertificatesCompatibleWithAtOfChainBlock M A x H B j) :
    ∀ (w : V) (D : Block V), w ∉ A.corrupted j → D ∈ (x.st j w).tree →
      (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D := by
  intro w D hw hD hDh
  obtain ⟨Y, hYD, -, hYph, -, hTY, hcert⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C D
      ((M.chainStateOf S.C B).h + 1) (by omega_nat) (by omega_nat)
  have hT'D : (M.chainStateOf S.C Y.parent).T_h.AncestorEq D := ancestorEq_trans hTY hYD
  have hT'h : (M.chainStateOf S.C (M.chainStateOf S.C Y.parent).T_h).h =
      (M.chainStateOf S.C B).h + 1 := by
    rw [((GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C Y.parent).2.1, hYph]
  -- the record's certificate on `Y`'s chain (some block `X ⪯ Y` with a set reaching the quorum at
  -- `X`) is the copied clause's on `D`'s chain (the spec's): with fixed validators the quorum at `X`
  -- is `quorum V`, and a vote on `X`'s chain is on `D`'s chain
  have hcertD : GoldilocksCorrectness.Statements.Routines.ProgressCertOn D
      ((M.chainStateOf S.C B).h + 1) (M.chainStateOf S.C Y.parent).T_h := by
    obtain ⟨X, hXY, A, hA, hv⟩ := hcert
    refine ⟨A, ?_, fun v hvA => ?_⟩
    · rw [← GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X]
      exact hA
    · obtain ⟨a, h1, h2, h3, h4⟩ := hv v hvA
      exact ⟨a, h1, h2, h3,
        GoldilocksCorrectness.Proofs.Routines.on_chain_mono a (ancestorEq_trans hXY hYD)
        ((GoldilocksCorrectness.Proofs.Routines.on_chain_iff a X).2
          ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F a X).1 h4))⟩
  rcases hCert w D _ _ hw hD hT'D hcertD (by omega_nat) with h | h
  · -- an ancestor of `B` has a height at most `h(B)`
    have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
    omega_nat
  · exact ancestorEq_trans h hT'D

end GoldilocksCorrectness.Record.Proofs.Executions

