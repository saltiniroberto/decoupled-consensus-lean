module
public import GoldilocksCorrectness.Proofs.Executions.PeriodEntryDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import Mathlib.Tactic.Ring
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-! New kit, no landed statement changes. The audited
statements are in `Statements/Executions/PeriodJustifiedPastStatements.lean`. Write `h(X)` for
`(chainStateOf C X).h`, the chain-state height of a block `X`.


- `vote_head_descends_of_F`: the head of a Goldfish vote is the voter's finalized block or a
  descendant of it;
- `justified_past_spreads` (section 2.3): a justification past `B` held by an honest active voter
  of slot `σ` reaches every honest active voter of the timely slot `σ + 1` whose finalized block
  is `B` or an ancestor of `B`, before its vote.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff one_le_Δ slotStart_eq
  supportCutoff_eq viewFreeze_eq voteTime_eq voteTime_mono)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (F_ancestorEq_get_fc_root fc_root_compatible
  viable_head_descends_of_justified_past)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff compatible_of_ancestorEq_compatible ghost_mem_tree_or_eq deepest?_mem)

variable {V : Type} [DecidableEq V] [Fintype V]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The viable heads of a state justified past `B` -/

/-! ## The viable tree, the root of the fork choice, the anchor, the walk -/

/-! ## The vote of a state justified past `B` -/

/-! ## The vote descends from the voter's finalized block -/

/-! ## The spread of a justification past `B` -/

/-- **A justification past `B` spreads in one delay.** The proof; the audited statement is in
`Statements/Executions/PeriodJustifiedPastStatements.lean`. `w`'s caches are witnessed by a held
block `D` (`cachesWitnessed_of_stateBefore`) with `w`'s justified block and justification height;
`B ⪯ J_w` (compatible and higher) and `J_w ⪯ D` (`chainStateOf_J_spec`), so `B ⪯ D`. `D` reaches
`u` one delay after `voteTime S σ` when the previous votes were due before the period
(`mem_T_before_add_delay_of_held_at_upTo`), and one delay after `supportCutoff S σ` when they were
due after it (`mem_T_before_add_delay_of_held_at`, `GST` moved to `max b₁ GST`); both are before
`voteTime S (σ + 1)`. `u`'s finalized block is an ancestor of `B`, so of `D`, and Lemma 57's cache
bound (`h_j_of_mem_T_of_stateBefore`) gives `(chainStateOf S.C D).h_j ≤ h_j(u)`.

The variables:
- `P`: the hypotheses; `σ`: the slot of `w`'s vote; `w`: the voter justified past `B`; `u`: the
  voter of slot `σ + 1`. -/
theorem justified_past_spreads {S : Setup V} {Sched : Schedule V} [RootOrder]
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (σ : ℕ) (w u : V)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (σ + 1)))
    (hσ : s + 1 ≤ σ) (hgood : ¬ VotesOwedInPeriod S b₀ b₁ (σ + 1))
    (hw : w ∈ honestActiveAt S Sched σ)
    (hCw : CachesCompatibleWith S B H (stateBefore x (voteTime S σ) w))
    (hjw : (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S σ) w).S.h_j)
    (hu : u ∈ honestActiveAt S Sched (σ + 1))
    (hFu : (stateBefore x (voteTime S (σ + 1)) u).S.F.AncestorEq B) :
    (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S (σ + 1)) u).S.h_j := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hgood' : supportCutoff S σ ≤ b₀ ∨ b₁ ≤ supportCutoff S σ := by
    unfold VotesOwedInPeriod at hgood
    simp only [Nat.add_sub_cancel] at hgood
    omega
  -- the times of slots `σ` and `σ + 1`, over the atom `slotStart S σ`
  have hss1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvtσ := voteTime_eq S σ
  have hscσ := supportCutoff_eq S σ
  have hvfσ := viewFreeze_eq S σ
  have hvt1 := voteTime_eq S (σ + 1)
  have hsc1 := supportCutoff_eq S (σ + 1)
  have hss2 : slotStart S (σ + 1 + 1) = slotStart S (σ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvt2 := voteTime_eq S (σ + 1 + 1)
  have hsc2 := supportCutoff_eq S (σ + 1 + 1)
  -- the witness of `w`'s caches: a held block `D` with `B ⪯ D`
  obtain ⟨⟨D, hDT, hJD, hjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (voteTime S σ) w
  obtain ⟨-, hJB, -, hJh, -⟩ := hCw
  have hBJ : B.AncestorEq (stateBefore x (voteTime S σ) w).S.J :=
    GoldilocksCorrectness.Proofs.Routines.descends_of_compatible_higher S.C hJB (by rw [hJh]; omega_nat)
  have hJD' : (stateBefore x (voteTime S σ) w).S.J.AncestorEq D := by
    rw [hJD]
    exact (chainStateOf_J_spec S.C D).1
  have hBD : B.AncestorEq D := ancestorEq_trans hBJ hJD'
  -- `w` is honest at the step before the vote time of `σ`
  have hv1 : 1 ≤ voteTime S σ := by omega
  have hjt := time_stepBefore_add_one x P.hDiv hv1
  have hwH : w ∉ Sched.adv ((x[stepBefore x (voteTime S σ)].time : ℕ) : Int) := fun h' =>
    (Finset.mem_sdiff.1 hw).2 (P.hMono _ _ (by omega) h')
  -- the receiver: `u` is awake and honest from `voteTime S σ` to `viewFreeze S σ`
  have hσ1 : 1 ≤ σ := by omega
  have hdws : dutyWindowStart S (σ + 1) ≤ voteTime S σ := by
    have h1 := dutyWindowStart_le_supportCutoff S (s := σ + 1) (s' := σ - 1) (by omega)
    have h2 := supportCutoff_eq S (σ - 1)
    have h3 := voteTime_eq S (σ - 1)
    have h4 : slotStart S (σ - 1 + 1) = slotStart S (σ - 1) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    have h5 : σ - 1 + 1 = σ := by omega
    rw [h5] at h4
    omega
  have hwin := honestActiveAt_window S Sched (σ + 1) u P.hMono hu
  have hrecv : ∀ t' : ℕ, voteTime S σ ≤ t' → t' ≤ viewFreeze S σ →
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int) :=
    fun t' h1 h2 => hwin t' (le_trans hdws h1) (by omega)
  -- the receiver's finalized block, before any time at most `voteTime S (σ + 1)`, is an ancestor
  -- of `D`
  have hcompatAt : ∀ t' : ℕ, t' ≤ voteTime S (σ + 1) →
      (stateBefore x t' u).S.F.compatible D = true := fun t' ht' =>
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      (stateBefore_grows x P.hDiv u ht').2.1 (ancestorEq_trans hFu hBD)))
  -- `D` is in `u`'s tree before the vote time of `σ + 1`
  have hDu : D ∈ (stateBefore x (voteTime S (σ + 1)) u).S.T := by
    rcases hgood' with hb | hb
    · have hGSTσ : GST ≤ voteTime S σ := le_trans P.hGST (voteTime_mono S (by omega))
      have hmem := mem_T_before_add_delay_of_held_at_upTo P.hDiv P.hMono (t := voteTime S σ)
        ((synchronyFromWakeUpTo_of_outside P.hSync).mono (by omega))
        ((catchUpOnWakeUpTo_of_outside P.hCatch).mono (by omega))
        (hRoots.mono (by omega)) P.hParent le_rfl hGSTσ hwH hDT
        (fun t' h1 h2 => hrecv t' h1 (by omega)) (hcompatAt _ (by omega))
      exact (stateBefore_grows x P.hDiv u (by omega)).1 hmem
    · have hGST' : max b₁ GST ≤ supportCutoff S σ :=
        max_le hb (le_trans P.hGST (by
          have := voteTime_mono S (show s + 1 ≤ σ by omega)
          omega))
      have hmem := mem_T_before_add_delay_of_held_at P.hDiv P.hMono (t := supportCutoff S σ)
        (synchronyFromWake_of_outside_after P.hSync) (catchUpOnWake_of_outside_after P.hCatch)
        (hRoots.mono (by omega)) P.hParent (by omega) hGST' hwH hDT
        (fun t' h1 h2 => hrecv t' (by omega) (by omega)) (hcompatAt _ (by omega))
      exact (stateBefore_grows x P.hDiv u (by omega)).1 hmem
  -- Lemma 57's cache bound at `u`
  have hle := h_j_of_mem_T_of_stateBefore S Sched x (voteTime S (σ + 1)) u D hDu
    (ancestorEq_trans hFu hBD)
  rw [σ_eq_of_stateBefore S Sched x _ u D hDu] at hle
  omega_nat

end GoldilocksCorrectness.Proofs.Executions
