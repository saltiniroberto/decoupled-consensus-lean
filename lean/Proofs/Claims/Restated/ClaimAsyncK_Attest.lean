import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bDirection
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_StableRootFor
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepRoots
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.ClaimAsyncK_Attest
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Attestations after a block graded at a round's three phases

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`. When a validator
grades a block `P` at round `ρ`'s three phases, `P` is an ancestor of the anchor and grade-2 block
of its round-`ρ` action read (`actionGradeRead_preceq_of_graded`), of the block its attestation
names (`attest_covers_of_graded`), and lies on one chain with the block its height vote is bound to
(`attest_heightPair_compatible_of_graded`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open DecoupledConsensusModel.Execution

local macro "pHP% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsPersist)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

private theorem round_cases_att (q c ρ : ℕ) (a : q ≤ c) (b : c ≤ ρ) (h : ρ ≤ q + 1) :
    (ρ = c ∧ (q + 1 = c ∨ q + 1 = c + 1)) ∨ (ρ = c + 1 ∧ q + 1 = c + 1) := by
  omega

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_att {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- The core store of every node state of the round-`r` action read from `before` is an outcome of
    the confirmation update on `before`'s core store with its clock set to `S.a r`. -/
private theorem actionReadFrom_core_att (facts : Record.Facts M) (S : Execution.Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ st : M.NS, n.st = M.store_with_cache st n.cache ∧
      M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1) ⇢ st.core := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨st, by rw [facts.nd.mkNode_st, facts.nd.mkNode_cache], ?_⟩
  rw [facts.nd.mkNode_cache, facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX]
  exact hX

/-- Every node state of the round-`r` action read from `before` has the fork-choice root of
    `before`'s core store. -/
private theorem actionReadFrom_fgRoot_att (facts : Record.Facts M) (S : Execution.Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core_att facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- Every node state of the round-`r` action read from `before` has the filtered tree of `before`'s
    core store. -/
private theorem actionReadFrom_filtered_att (facts : Record.Facts M) (S : Execution.Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
        M.get_filtered_block_tree (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core_att facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_filtered_block_tree,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- The core store of every node state of the round-`r` action read from `before` has the
    chain-state map of `before`'s core store. -/
private theorem actionReadFrom_σ_att (facts : Record.Facts M) (S : Execution.Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.σ = before.st.core.σ := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_σ _ _ _ _ _ X hX, facts.hd.ModelProperties_setClock_core_σ]

/-- The slot of the healing store of every node state of the round-`r₁` action read from `before` is
    in round `r₁`. -/
private theorem actionReadFrom_round_att (facts : Record.Facts M) (S : Execution.Setup V) (before : M.N)
    (r₁ : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        before r₁,
      M.round_of S.hc (M.toHealing n.st.core).s = r₁ := by
  intro n hn
  obtain ⟨c, -, D, hD, rfl⟩ := hn
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)
  rewrite [facts.nd.mkNode_st, Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_core_s,
    facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX, ← facts.sto.toHealing_gs_s,
    facts.dt.update_confirmation_with_toHealing_s _ _ _ _ _ X hX, facts.sto.toHealing_gs_s,
    facts.hd.Sts_setClock_core_s]
  exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r₁

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `t` is at or after round `ρ`'s opening and before round `(ρ + 1)`'s, then the round of `t`'s
    slot is `ρ`. -/
theorem round_of_slotOf_eq_att (facts : Record.Facts M) (S : Setup V) {ρ : Round} {t : Int}
    (h0 : slotStart S.E.Δ ((M.opening_slot S.hc ρ)) ≤ t)
    (h1 : t < slotStart S.E.Δ ((M.opening_slot S.hc (ρ + 1)))) :
    (M.round_of S.hc (S.E.slotOf t)) = ρ := by
  have hnn : (0 : Int) ≤ slotStart S.E.Δ ((M.opening_slot S.hc ρ)) := by
    rw [slotStart_closed]
    exact mul_nonneg (mul_nonneg (by decide) (le_of_lt S.E.Δ_pos)) (Int.natCast_nonneg _)
  apply le_antisymm
  · exact Restated.round_of_le_of_lt_opening_slot_sr facts S
      (slotOf_lt_of_lt_slotStart S (le_trans hnn h0) h1)
  · apply Restated.le_round_of_of_opening_slot_le_sr facts S
    rw [← slotOf_slotStart S ((M.opening_slot S.hc ρ))]
    exact slotOf_mono_sts S h0

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Round `(q + 1)`'s domain instant of the phase `p` is positive, a multiple of `Δ`, in round `q`
    or `q + 1`, at or after one delay before the round's grade-2 early cutoff, and strictly before
    the round's action instant. -/
theorem domain_facts_att (facts : Record.Facts M) (S : Setup V) (q : Round) (p : Protocol.Phase) :
    0 < M.domain S.E S.hc (q + 1) p ∧
      M.domain S.E S.hc (q + 1) p % S.E.Δ = 0 ∧
      ((M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc (q + 1) p))) = q ∨
        (M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc (q + 1) p))) = q + 1) ∧
      M.early S.E S.hc (q + 1) .g2 - S.E.Δ ≤ M.domain S.E S.hc (q + 1) p ∧
      M.domain S.E S.hc (q + 1) p < (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hsucc : ((M.opening_slot S.hc (q + 1)) : ℕ) = ((M.opening_slot S.hc q) : ℕ) + S.hc.R :=
    facts.gr.opening_slot_succ S.hc q
  have hsucc2 : ((M.opening_slot S.hc (q + 1 + 1)) : ℕ) = ((M.opening_slot S.hc (q + 1)) : ℕ) + S.hc.R :=
    facts.gr.opening_slot_succ S.hc (q + 1)
  have hR3 : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  set O : Int := (((M.opening_slot S.hc (q + 1)) : ℕ) : Int) with hO
  set Oq : Int := (((M.opening_slot S.hc q) : ℕ) : Int) with hOq
  set O2 : Int := (((M.opening_slot S.hc (q + 1 + 1)) : ℕ) : Int) with hO2
  have hOs : O = Oq + (S.hc.R : Int) := by rw [hO, hOq, hsucc]; push_cast; ring
  have hO2s : O2 = O + (S.hc.R : Int) := by rw [hO, hO2, hsucc2]; push_cast; ring
  have hOq0 : (0 : Int) ≤ Oq := Int.natCast_nonneg _
  have hopen : M.opening S.E S.hc (q + 1) = 4 * S.E.Δ * O := by
    rw [(pHP% opening_eq_slotStart_hp) facts, slotStart_closed]
  have hact : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) = 4 * S.E.Δ * O + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (q + 1),
      (pCR% confirmation_time_closed_cr) facts]
  have hearly : M.early S.E S.hc (q + 1) .g2 = 4 * S.E.Δ * O - 5 * S.E.Δ := by
    have h := facts.gr.early_g2_eq S (q + 1)
    have h' : M.a S.hc S.E.Δ (q + 1) = 4 * S.E.Δ * O + 6 * S.E.Δ := hact
    rw [h, h']; ring
  have hsq : slotStart S.E.Δ ((M.opening_slot S.hc q)) = 4 * S.E.Δ * Oq := slotStart_closed _ _
  have hsq1 : slotStart S.E.Δ ((M.opening_slot S.hc (q + 1))) = 4 * S.E.Δ * O := slotStart_closed _ _
  have hsq2 : slotStart S.E.Δ ((M.opening_slot S.hc (q + 1 + 1))) = 4 * S.E.Δ * O2 :=
    slotStart_closed _ _
  have hRΔ : 3 * S.E.Δ ≤ (S.hc.R : Int) * S.E.Δ := mul_le_mul_of_nonneg_right hR3 (le_of_lt hΔ)
  have hOqΔ : 0 ≤ Oq * S.E.Δ := mul_nonneg hOq0 (le_of_lt hΔ)
  have e1 : 4 * S.E.Δ * O = 4 * (Oq * S.E.Δ) + 4 * ((S.hc.R : Int) * S.E.Δ) := by
    rw [hOs]; ring
  have e2 : 4 * S.E.Δ * O2 = 4 * S.E.Δ * O + 4 * ((S.hc.R : Int) * S.E.Δ) := by
    rw [hO2s]; ring
  have e3 : 4 * S.E.Δ * Oq = 4 * (Oq * S.E.Δ) := by ring
  cases p with
  | g2 =>
      rw [← facts.gr.gammaNeg1_eq_domain_g2_succ S q, hsq1]
      refine ⟨by linarith, ?_, Or.inl ?_, by rw [hearly]; linarith, by rw [hact]; linarith⟩
      · have : 4 * S.E.Δ * O - S.E.Δ = S.E.Δ * (4 * O - 1) := by ring
        rw [this]; exact Int.mul_emod_right _ _
      · apply Restated.round_of_slotOf_eq_att facts S
        · rw [hsq]; linarith
        · rw [hsq1]; linarith
  | g1 =>
      rw [facts.gr.Sts_domain_g1_eq_opening, hopen]
      refine ⟨by linarith, ?_, Or.inr ?_, by rw [hearly]; linarith, by rw [hact]; linarith⟩
      · have : 4 * S.E.Δ * O = S.E.Δ * (4 * O) := by ring
        rw [this]; exact Int.mul_emod_right _ _
      · apply Restated.round_of_slotOf_eq_att facts S
        · rw [hsq1]
        · rw [hsq2]; linarith
  | g0 =>
      rw [facts.gr.domain_g0_eq_opening, hopen]
      refine ⟨by linarith, ?_, Or.inr ?_, by rw [hearly]; linarith, by rw [hact]; linarith⟩
      · have : 4 * S.E.Δ * O + S.E.Δ = S.E.Δ * (4 * O + 1) := by ring
        rw [this]; exact Int.mul_emod_right _ _
      · apply Restated.round_of_slotOf_eq_att facts S
        · rw [hsq1]; linarith
        · rw [hsq2]; linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At every step, every result `v`'s cache holds is for round `0` or for a phase whose domain
    instant has come. -/
theorem cacheResultsAfterDomain_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) (v : V) :
    Restated.CacheResultsAfterDomain M S Sched x k v := by
  induction k with
  | zero =>
      intro r p o h
      exact Or.inl (facts.grRun.phaseResult_initial_some S Sched x v h)
  | succ k ih =>
      have htm : (x[k].time : Int) ≤ (x[k + 1].time : Int) :=
        Restated.time_mono_int facts S Sched x (Nat.le_succ k)
      have hold : ∀ (r : Round) (p : Protocol.Phase) (o : Option (Block V)),
          M.phaseResult (M.cacheAtRound (x[k][v].st).cache r) p = some o →
          r = 0 ∨ M.domain S.E S.hc r p ≤ (x[k + 1].time : Int) := by
        intro r p o h
        rcases ih r p o h with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (le_trans h1 htm)
      intro r p o h
      rcases Restated.cache_succ_cases_sr facts S Sched x k v with hst | ⟨τ, hl, hc⟩ | hc
      · rw [hst] at h
        exact hold r p o h
      · obtain ⟨c, hc'⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
          (M.toHealing (x[k][v].st).st.core) (τ : Int) (x[k][v].st).cache
        rw [hc c hc'] at h
        have hτ : (x[k + 1].time : Int) = (τ : Int) := (Restated.tickStepAt_time facts x ⟨τ, hl, rfl⟩).1
        obtain ⟨o₁, h₁⟩ := facts.gr.phaseResult_clipCache_isSome h
        rcases facts.gr.phaseResult_onPhaseTick_some_domain_or_kept S.E S.hc _ _ _ c hc' h₁ with h2 | ⟨o', h2⟩
        · right; rw [hτ]; exact le_of_eq h2.symm
        · exact hold r p o' h2
      · rw [hc] at h
        obtain ⟨o₁, h₁⟩ := facts.gr.phaseResult_clipCache_isSome h
        exact hold r p o₁ h₁

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `w`'s cache after `k₀` steps is aligned to round `q` or later, not ahead of the clock, with a
    round-`(q + 1)` phase-`p` root that is a descendant of `P`, the time `x[n].time` is in round
    `q + 1` or earlier, and `P` lies on one chain with `w`'s finalized block at every step up to
    `n`, then the same holds after `n` steps. -/
theorem phaseEntryAbove_kept (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {q : Round} {p : Protocol.Phase} {P : Block V} {w : V}
    {k₀ n : Nat} (hkn : k₀ ≤ n)
    (h₀ : Restated.PhaseEntryAbove M S Sched x q p P k₀ w)
    (hend : (M.round_of S.hc (S.E.slotOf (x[n].time : Int))) ≤ q + 1)
    (hPF : ∀ j : Nat, j ≤ n → Block.compatible P (x[j][w].st).st.core.F = true) :
    Restated.PhaseEntryAbove M S Sched x q p P n w := by
  induction n, hkn using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
      have htm : (x[k].time : Int) ≤ (x[k + 1].time : Int) :=
        Restated.time_mono_int facts S Sched x (Nat.le_succ k)
      have hρ := Restated.roundAt_mono_sr facts S htm
      have hend' : (M.round_of S.hc (S.E.slotOf (x[k].time : Int))) ≤ q + 1 := le_trans hρ hend
      obtain ⟨hq0, hq1, e, he, hPe⟩ :=
        ih hend' (fun j hj => hPF j (Nat.le_succ_of_le hj))
      rcases Restated.cache_succ_cases_sr facts S Sched x k w with hst | ⟨τ, hl, hc⟩ | hc
      · refine ⟨?_, ?_, e, ?_, hPe⟩
        · rw [hst]; exact hq0
        · rw [hst]; exact le_trans hq1 hρ
        · rw [hst]; exact he
      · obtain ⟨c, hc'⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
          (M.toHealing (x[k][w].st).st.core) (τ : Int) (x[k][w].st).cache
        have hc := hc c hc'
        have hτ : (x[k + 1].time : Int) = (τ : Int) := (Restated.tickStepAt_time facts x ⟨τ, hl, rfl⟩).1
        have hρτ : (M.round_of S.hc (S.E.slotOf (τ : Int))) ≤ q + 1 := by rw [← hτ]; exact hend
        have hcτ : (x[k][w].st).cache.round ≤ (M.round_of S.hc (S.E.slotOf (τ : Int))) := by
          rw [← hτ]; exact le_trans hq1 hρ
        have hcases := round_cases_att _ _ _ hq0 hcτ hρτ
        have _hrr_s1 := facts.nd.reachedRead_of_node _ (Record.reachedNode_sts facts S Sched x k w)
        have hk1 := facts.gr.phaseResult_onPhaseTick_kept S.E S.hc (M.toHealing (x[k][w].st).st.core)
          (τ : Int) (x[k][w].st).cache he hcases c hc'
        refine ⟨?_, ?_, M.clipGrade (M.clipGrade e (x[k][w].st).st.core.F)
          (x[k + 1][w].st).st.core.F, ?_, ?_⟩
        · rw [hc, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c hc']
          exact le_trans hq0 hcτ
        · rw [hc, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c hc', hτ]
        · rw [facts.sto.Sts_toHealing_F] at hk1
          rw [hc]; exact facts.gr.phaseResult_clipCache_some hk1
        · exact facts.gr.preceq_clipGrade (hPF (k + 1) le_rfl) _
            (facts.gr.preceq_clipGrade (hPF k (Nat.le_succ k)) e hPe)
      · refine ⟨?_, ?_, M.clipGrade e (x[k + 1][w].st).st.core.F, ?_, ?_⟩
        · rw [hc, facts.gr.clipCache_round]; exact hq0
        · rw [hc, facts.gr.clipCache_round]; exact le_trans hq1 hρ
        · rw [hc]; exact facts.gr.phaseResult_clipCache_some he
        · exact facts.gr.preceq_clipGrade (hPF (k + 1) le_rfl) e hPe

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `d`, round `(q + 1)`'s domain instant of the phase `p`, be positive, a multiple of `Δ` and
    in round `q` or `q + 1`; let `n` be the tick step at `S.a (q + 1)`, `u` be awake and not held at
    `d`, `u`'s grade test for `P` at the last step before `d` be able to return `true`, `u`'s tick
    at the tick steps at `d` have an outcome, and `u`'s finalized block after `n` steps lie on one
    chain with `P`. Then for every node state `nr` of `u`'s round-`(q + 1)` action read after `n`
    steps, the frame read from `nr`'s cache at `nr`'s healing store holds for the phase `p` a block
    `e` with `P ⪯ e`. -/
theorem actionFrame_phase_preceq_of_graded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {q : Round}
    {p : Protocol.Phase}
    (hdpos : 0 < M.domain S.E S.hc (q + 1) p)
    (hdvd : M.domain S.E S.hc (q + 1) p % S.E.Δ = 0)
    (hdρ : (M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc (q + 1) p))) = q ∨
      (M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc (q + 1) p))) = q + 1)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))) {u : V}
    (hu : u ∈ Sched.awake (M.domain S.E S.hc (q + 1) p) \
      Sched.adv (M.domain S.E S.hc (q + 1) p))
    {P : Block V}
    (hgr : ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
        (M.late S.E S.hc (q + 1) p) P ⇢ true)
    (hF : Block.compatible P (x[n][u].st).st.core.F = true)
    (hne : ∀ m : Nat, Restated.tickStepAt M x m (M.domain S.E S.hc (q + 1) p) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (M.domain S.E S.hc (q + 1) p) x[m] u)
          (M.domain S.E S.hc (q + 1) p) ⇢ out) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][u].st) (q + 1),
    ∃ e : Block V,
      M.phaseResult (M.readFrame nr.cache (M.toHealing nr.st.core) (q + 1)) p = some (some e) ∧
        Block.Preceq P e := by
  have _hr_0 : M.reachedNode (x[n][u].st) := Record.reachedNode_sts facts S Sched x n u
  intro nr hnrm
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd hdpos
  have hmB := Restated.stepBeforeInstant_of_tickStepAt facts x hm
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hdlt : M.domain S.E S.hc (q + 1) p < (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
    have h5 := facts.gr.domain_add_five_delta_le_action S (q + 1) p
    have hΔ := S.E.Δ_pos
    have h5' : M.domain S.E S.hc (q + 1) p + 5 * S.E.Δ
        ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := h5
    linarith
  have hmn : m + 1 ≤ n := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (show n + 1 ≤ m + 1 by omega)
    linarith
  have hPF : ∀ j : Nat, j ≤ n → Block.compatible P (x[j][u].st).st.core.F = true := by
    intro j hj
    have hFj := Restated.F_mono facts S Sched x u hj
    rcases compatible_cases hF with h | h
    · exact compatible_of_preceq_common_Preceq h hFj
    · exact compatible_of_cases (Or.inr (preceq_trans_Preceq hFj h))
  have hg := hgr m hmB
  obtain ⟨H, hH, hPH⟩ := facts.gr.Sts_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ _ true hg rfl
  have hPT : P ∈ (M.gradeView (M.toHealing (x[m][u].st).st.core)).T := by
    rw [facts.gr.Sts_gradeView_T] at hH ⊢
    exact Restated.mem_T_of_preceq_sts facts S Sched x m u hH hPH
  classical
  have hgne := fun B : Block V => facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p) B
  let gf : Block V → Bool := fun B => if B = P then true else (hgne B).choose
  have hgf : ∀ B : Block V, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
      (x[m][u].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
      (M.late S.E S.hc (q + 1) p) B ⇢ gf B := by
    intro B
    by_cases hBP : B = P
    · have : gf B = true := if_pos hBP
      rw [this, hBP]; exact hg
    · have : gf B = (hgne B).choose := if_neg hBP
      rw [this]; exact (hgne B).choose_spec
  have hgfP : gf P = true := if_pos rfl
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p)
  obtain ⟨D, hD, hPD⟩ := facts.gr.preceq_freezeRoot S.E _ _ _ _ _ _ gf hgf hPT hgfP
    (fun B _ B' _ hB hB' => facts.gr.compatible_of_gradeBool_phase S.E S.hc _ _ _ p
      (gf B) (hgf B) hB (gf B') (hgf B') hB') fr hfr
  have hnone : M.phaseResult (M.cacheAtRound (x[m][u].st).cache (q + 1)) p
      = none := by
    cases hpr : M.phaseResult (M.cacheAtRound (x[m][u].st).cache (q + 1)) p with
    | none => rfl
    | some o =>
        exfalso
        rcases Restated.cacheResultsAfterDomain_sts facts S Sched x m u (q + 1) p o hpr with h | h
        · exact Nat.succ_ne_zero q h
        · linarith
  obtain ⟨τ, hl, hτ⟩ := hm
  obtain ⟨out₁, hout, hst⟩ : ∃ out₁ : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[m] u) (τ : Int) ⇢ out₁ ∧
        x[m + 1][u].st = out₁.1 := by
    rcases Restated.st_succ_of_tick_awake facts S Sched x u hl (by rw [hτ]; exact hu)
      (by rw [hτ]; exact hdvd) with h | ⟨hno, -⟩
    · exact h
    · obtain ⟨out, hout⟩ : ∃ out : M.N × List (NamedObject V),
          M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[m] u) (τ : Int) ⇢ out := by
        rw [hτ]; exact hne m ⟨τ, hl, hτ⟩
      exact absurd hout (hno out)
  obtain ⟨c₁, hc₁⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (M.toHealing (x[m][u].st).st.core) (M.domain S.E S.hc (q + 1) p) (x[m][u].st).cache
  have hc1 : (x[m + 1][u].st).cache = M.clipCache (x[m + 1][u].st).st.core.F c₁ := by
    rw [hst]
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (m) u (↑τ)
    exact facts.nd.namedNode_tick_cache _ u _ _ out₁ hout c₁
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, hτ]; exact hc₁)
  have hfr' : M.freezeRoot S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
      (M.toHealing (x[m][u].st).st.core).toFG.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
      (M.late S.E S.hc (q + 1) p) ⇢ fr := by
    rw [facts.sto.Sts_toHealing_F]
    exact hfr
  have hwrite : M.phaseResult (M.cacheAtRound c₁ (q + 1)) p
      = some (fr.map (fun B => M.clipGrade B (M.toHealing (x[m][u].st).st.core).toFG.F)) := by
    rcases hdρ with h | h
    · exact facts.gr.phaseResult_onPhaseTick_domain S.E S.hc _ _ _ (by rw [h]) rfl hnone
        c₁ hc₁ fr hfr'
    · exact facts.gr.phaseResult_onPhaseTick_domain_current S.E S.hc _ _ (le_of_lt hdpos) _ h rfl hnone
        c₁ hc₁ fr hfr'
  rw [hD, Option.map_some, facts.sto.Sts_toHealing_F] at hwrite
  have hbase : Restated.PhaseEntryAbove M S Sched x q p P (m + 1) u := by
    refine ⟨?_, ?_, M.clipGrade (M.clipGrade D (x[m][u].st).st.core.F)
      (x[m + 1][u].st).st.core.F, ?_, ?_⟩
    · rw [hc1, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c₁ hc₁]
      rcases hdρ with h | h
      · rw [h]
      · rw [h]; exact Nat.le_succ q
    · rw [hc1, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c₁ hc₁, hm1]
    · rw [hc1]; exact facts.gr.phaseResult_clipCache_some hwrite
    · exact facts.gr.preceq_clipGrade (hPF (m + 1) hmn) _ (facts.gr.preceq_clipGrade (hPF m (by omega)) D hPD)
  have hρa : (M.round_of S.hc (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))))) = q + 1 := Restated.round_of_slotOf_action facts S (q + 1)
  have hendn : (M.round_of S.hc (S.E.slotOf (x[n].time : Int))) ≤ q + 1 := by
    rw [← hρa]; exact Restated.roundAt_mono_sr facts S (by linarith)
  obtain ⟨hq0, hq1, e, he, hPe⟩ := Restated.phaseEntryAbove_kept facts S Sched x hmn hbase hendn hPF
  have hcases := round_cases_att _ _ ((M.round_of S.hc (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S (q + 1)))))) hq0
    (by rw [hρa]; exact le_trans hq1 hendn) (le_of_eq hρa)
  have hFnr : (M.toHealing nr.st.core).toFG.F = (x[n][u].st).st.core.F := by
    have h := Restated.actionHealingStore_F facts S (x[n][u].st) (q + 1) (M.toHealing nr.st.core)
      ⟨nr, hnrm, rfl⟩
    rw [Record.Model.HS.F] at h
    exact h
  obtain ⟨c, hc, st, hst', rfl⟩ := hnrm
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  rewrite [facts.nd.mkNode_st] at hFnr; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hFnr
  have _hrr_s2 := facts.nd.reachedRead_of_node _ (Record.reachedNode_sts facts S Sched x n u)
  have hkept := facts.gr.phaseResult_onPhaseTick_kept S.E S.hc (M.toHealing (x[n][u].st).st.core)
    ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) (x[n][u].st).cache he hcases c hc
  refine ⟨M.clipGrade (M.clipGrade e (M.toHealing (x[n][u].st).st.core).toFG.F)
    (M.toHealing st.core).toFG.F, facts.gr.readFrame_phase_of_cache hkept, ?_⟩
  have hFa : Block.compatible P (M.toHealing st.core).toFG.F = true := by
    have h := hFnr
    rw [facts.sto.Sts_toHealing_F, facts.nd.store_with_cache_core_F] at h
    rw [facts.sto.Sts_toHealing_F, h]; exact hF
  exact facts.gr.preceq_clipGrade hFa _
    (by rw [facts.sto.Sts_toHealing_F]; exact facts.gr.preceq_clipGrade (hPF n le_rfl) e hPe)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `n` be the tick step at `S.a ρ` of a round `ρ ≥ 1`, `u` be awake throughout
    `[early ρ .g2 − Δ, S.a ρ]` and honest through the step after the tick, `u`'s grade test for `P`
    be able to return `true` at the last step before each of round `ρ`'s three domain instants,
    `u`'s finalized block after `n` steps lie on one chain with `P`, and `P` be in `u`'s filtered
    tree there or an ancestor of `u`'s fork-choice root there; let every tick at a public instant,
    for a validator awake there and honest up to it, have an outcome. Then for every node state `nr`
    of `u`'s round-`ρ` action read after `n` steps and every grade read `g` of `nr`'s frame, `P` is
    an ancestor of `g`'s anchor, of `g`'s grade-2 block when it has one, and of the fork-choice root
    of `nr`'s healing store when it has none. -/
theorem actionGradeRead_preceq_of_graded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {ρ : Round} (hρ : 0 < ρ)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) {u : V}
    (hawake : u ∈ Sched.awakeThroughout (M.early S.E S.hc ρ .g2 - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hvh : Restated.HonestThrough M Sched x (n + 1) u) {P : Block V}
    (hgr : ∀ (p : Protocol.Phase) (m : Nat),
      Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p)
        (M.late S.E S.hc ρ p) P ⇢ true)
    (hF : Block.Compatible P (x[n][u].st).st.core.F)
    (hroot : P ∈ M.get_filtered_block_tree (M.toHealing (x[n][u].st).st.core).toFG ∨
      Block.Preceq P (M.get_fg_root (M.toHealing (x[n][u].st).st.core).toFG))
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][u].st) ρ,
    ∀ g : Protocol.GradeRead V,
      M.frameGradeRead nr.cache S.E S.hc (M.toHealing nr.st.core) ρ ⇢ g →
    Block.Preceq P g.anchor ∧
      (∀ q : Block V, g.Q2 = some q → Block.Preceq P q) ∧
      (g.Q2 = none → Block.Preceq P (M.get_fg_root (M.toHealing nr.st.core).toFG)) := by
  intro nr hnrm g hg
  obtain ⟨q, rfl⟩ : ∃ q : Round, ρ = q + 1 :=
    ⟨ρ - 1, (Nat.sub_add_cancel (show (1 : Nat) ≤ ρ from hρ)).symm⟩
  obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn
  have hentry : ∀ p : Protocol.Phase, ∃ e : Block V,
      M.phaseResult (M.readFrame nr.cache (M.toHealing nr.st.core) (q + 1)) p = some (some e) ∧
        Block.Preceq P e := by
    intro p
    obtain ⟨hdpos, hdvd, hdρ, hdlo, hdhi⟩ := Restated.domain_facts_att facts S q p
    have hu : u ∈ Sched.awake (M.domain S.E S.hc (q + 1) p) \
        Sched.adv (M.domain S.E S.hc (q + 1) p) :=
      Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hawake hdlo (le_of_lt hdhi),
        hvh _ (by rw [hn1]; exact le_of_lt hdhi)⟩
    exact Restated.actionFrame_phase_preceq_of_graded facts S Sched x htd hdpos hdvd hdρ hn hu (hgr p)
      (compatible_iff_Compatible.mp hF)
      (fun m hm => by
        obtain ⟨τ, hl, hτ⟩ := hm
        rw [← hτ]
        exact hnr m τ u hl (by rw [hτ]; exact hdvd) (by rw [hτ]; exact hu)
          (fun t ht => hvh t (by rw [hn1]; exact le_trans (le_trans ht hτ.le) (le_of_lt hdhi))))
      nr hnrm
  obtain ⟨e0, he0, -⟩ := hentry .g0
  obtain ⟨e1, he1, hPe1⟩ := hentry .g1
  obtain ⟨e2, he2, hPe2⟩ := hentry .g2
  rw [facts.gr.phaseResult_g0] at he0
  rw [facts.gr.phaseResult_g1] at he1
  rw [facts.gr.Sts_phaseResult_g2] at he2
  rw [← actionReadFrom_filtered_att facts (Setup.alwaysAwake S) (x[n][u].st) (q + 1) nr hnrm,
    ← actionReadFrom_fgRoot_att facts (Setup.alwaysAwake S) (x[n][u].st) (q + 1) nr hnrm] at hroot
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing nr.st.core) (q + 1)
    (M.readFrame nr.cache (M.toHealing nr.st.core) (q + 1)).g1
  have hga : g.anchor = a := facts.gr.frameGradeRead_anchor _ _ _ _ _ g hg a ha
  obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing nr.st.core)
    (M.readFrame nr.cache (M.toHealing nr.st.core) (q + 1))
  have hgQ : g.Q2 = o := facts.nd.Sts_gradeContract_read_Q2 nr.cache S.E S.hc _ (q + 1) g
    ((facts.nd.gradeContract_read nr.cache S.E S.hc _ (q + 1) g).2 hg) o ho
  rcases hroot with hPt | hPr
  · obtain ⟨Q, hQ, hPQ⟩ := facts.gr.preceq_grade2Block_of_g2 he0 he1 he2 hPt hPe2 o ho
    refine ⟨?_, ?_, ?_⟩
    · rw [hga]
      rw [he1] at ha
      exact facts.gr.preceq_anchor_of_g1 S.E S.hc _ (q + 1) hPt hPe1 a ha
    · intro Q' hQ'
      rw [hgQ, hQ] at hQ'
      rw [← Option.some_inj.mp hQ']
      exact hPQ
    · intro hnone
      rw [hgQ, hQ] at hnone
      exact absurd hnone (by simp)
  · refine ⟨?_, ?_, fun _ => hPr⟩
    · rw [hga]
      exact facts.gr.preceq_anchor_of_fgRoot S.E S.hc _ (q + 1) _ hPr a ha
    · intro Q' hQ'
      rw [hgQ] at hQ'
      exact preceq_trans_Preceq hPr (facts.gr.fgRoot_preceq_grade2Block o ho hQ')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `n` is the tick step at `S.a ρ` and `u` is honest through `n`, then for every node state `nr`
    of `u`'s round-`ρ` action read after `n` steps and every outcome `D` of the attestation duty at
    `nr` whose height pair is the vote for `h₀` bound to `entry`, every outcome of the
    finality-gadget source at `nr` is a block `Cfg` such that every block on the wire whose root is
    `entry` is `Cfg` or an ancestor of `Cfg`. -/
theorem entry_preceq_source_of_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {ρ : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) {u : V}
    (hu : Restated.HonestThrough M Sched x n u)
    {h₀ : Height} {entry : BlockId} {tmo : Bool} :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][u].st) ρ,
    ∀ D, M.duties_attest_with (M.gradeContract nr.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nr.st nr.record ⇢ D →
    D.2.2.height_pair = NamedHeightPair.vote h₀ entry tmo →
    ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nr ⇢ o →
    ∃ Cfg : Block V, o = some Cfg ∧
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
        Block.Preceq C.erase Cfg := by
  classical
  intro nr hnr D hD hvote o ho
  obtain ⟨w₀, hw₀, hw₀u⟩ := Restated.stateBeforeTime_runOf_action facts S Sched x hn u
  have hw₀' : w₀ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x u (n + 1))
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) ρ) := hw₀
  have hnw : nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M
      (Setup.alwaysAwake S) (w₀ u) ρ := by
    rw [hw₀u]; exact hnr
  have hn₀ : nr ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M (Setup.alwaysAwake S)
        (Record.runOfM M S Sched x u (n + 1)) u ρ :=
    ⟨w₀, hw₀', hnw⟩
  obtain ⟨Cfg, rfl, -, hCfgroot⟩ :=
    Restated.source_of_actionAttestation_heightPair facts (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x u (n + 1)) u ρ nr hn₀ D hD hvote o ho
  have hCfgT := Restated.fgSource_mem_stateBeforeTime' facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x u (n + 1)) u ρ w₀ hw₀' nr hnw ho
  have hco := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x u (n + 1)) ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) ρ)) u
    w₀ hw₀').1.1.1
  have hCfgroot' : ((x[n][u].st).st.core.σ Cfg).T_h.root = entry := by
    rw [← actionReadFrom_σ_att facts (Setup.alwaysAwake S) (x[n][u].st) ρ nr hnr]
    exact hCfgroot
  rw [hw₀u] at hCfgT hco
  rw [hco.1] at hCfgT
  obtain ⟨Cfgn, hCfgnMem, hCfgnErase⟩ := Finset.mem_image.mp hCfgT
  have hσ : (x[n][u].st).st.core.σ Cfg = M.derive_named S.E S.cfg Cfgn := by
    have hd := hco.2.2.2.2 Cfgn hCfgnMem
    rw [hCfgnErase] at hd
    exact hd
  obtain ⟨E0, hE0le, hE0er, -⟩ :=
    facts.cs.entry_ancestor_same_height S.E S.cfg Cfgn
  have hE0mem : E0 ∈ (x[n][u].st).st.bodies :=
    Restated.mem_bodies_of_preceq hco.2.2.1 hCfgnMem hE0le
  have hE0log : Restated.blockInLog M S Sched x E0 := Restated.blockInLog_of_mem_bodies facts S Sched hu hE0mem
  have hE0root : E0.root = entry := by
    rw [← Proofs.NamedWire.erase_root E0, hE0er, ← hσ, hCfgroot']
  refine ⟨Cfg, rfl, ?_⟩
  intro C hC hCroot
  have hCE : C.erase = E0.erase :=
    Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec hC hE0log (by rw [hCroot, hE0root])
  rw [hCE, ← hCfgnErase]
  exact Proofs.NamedWire.erase_preceq hE0le

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `actionGradeRead_preceq_of_graded`, for every node state `nr` of `u`'s
    round-`ρ` action read after `n` steps and every outcome `D` of the attestation duty at `nr`,
    every block `C` of `u`'s tree after the tick whose root is the `confirmed` field of `D`'s
    attestation is `P` or has `P` as an ancestor. -/
theorem attest_covers_of_graded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) {ρ : Round} (hρ : 0 < ρ)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) {u : V}
    (hawake : u ∈ Sched.awakeThroughout (M.early S.E S.hc ρ .g2 - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hvh : Restated.HonestThrough M Sched x (n + 1) u) {P : Block V}
    (hgr : ∀ (p : Protocol.Phase) (m : Nat),
      Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p)
        (M.late S.E S.hc ρ p) P ⇢ true)
    (hF : Block.Compatible P (x[n][u].st).st.core.F)
    (hroot : P ∈ M.get_filtered_block_tree (M.toHealing (x[n][u].st).st.core).toFG ∨
      Block.Preceq P (M.get_fg_root (M.toHealing (x[n][u].st).st.core).toFG)) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][u].st) ρ,
    ∀ D, M.duties_attest_with (M.gradeContract nr.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nr.st nr.record ⇢ D →
    ∀ C : NamedBlock V, C ∈ (x[n + 1][u].st).st.bodies →
      D.2.2.confirmed = some C.root →
      Block.Preceq P C.erase := by
  intro nr hnr D hD C hC hconf
  obtain ⟨g, hg'⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ
  have hg := (facts.nd.gradeContract_read nr.cache S.E S.hc _ ρ g).1 hg'
  obtain ⟨hA, hQ, hR⟩ := Restated.actionGradeRead_preceq_of_graded facts S Sched x htd hρ hn hawake hvh hgr
    hF hroot (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew) nr hnr g hg
  have hsgP : Block.Preceq P (M.currentSGVote (M.toHealing nr.st.core) g) :=
    facts.gr.preceq_currentSGVote_of_cases hA hQ hR
  have hvhn : Restated.HonestThrough M Sched x n u := fun t ht =>
    hvh t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n)))
  rw [Restated.attest_confirmed_eq_sgVote facts S (x[n][u].st) u ρ nr hnr D hD g hg] at hconf
  obtain ⟨E, hElog, hEe⟩ := Restated.exists_inLog_erase_actionSGVote facts S Sched x hvhn ρ nr hnr g hg
  have hCE : C.erase = E.erase := by
    refine Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hvh hC)
      hElog ?_
    rw [← Proofs.NamedWire.erase_root E, hEe]
    exact (Option.some_inj.mp hconf).symm
  rw [hCE, hEe]
  exact hsgP

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `attest_covers_of_graded`, for every node state `nr` of `u`'s round-`ρ`
    action read after `n` steps and every outcome `D` of the attestation duty at `nr` whose
    attestation carries a height vote for height `h` bound to the root `root`, every block on the
    wire whose root is `root` is an ancestor or a descendant of `P`. -/
theorem attest_heightPair_compatible_of_graded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) {ρ : Round} (hρ : 0 < ρ)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) {u : V}
    (hawake : u ∈ Sched.awakeThroughout (M.early S.E S.hc ρ .g2 - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hvh : Restated.HonestThrough M Sched x (n + 1) u) {P : Block V}
    (hgr : ∀ (p : Protocol.Phase) (m : Nat),
      Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p)
        (M.late S.E S.hc ρ p) P ⇢ true)
    (hF : Block.Compatible P (x[n][u].st).st.core.F)
    (hroot : P ∈ M.get_filtered_block_tree (M.toHealing (x[n][u].st).st.core).toFG ∨
      Block.Preceq P (M.get_fg_root (M.toHealing (x[n][u].st).st.core).toFG)) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][u].st) ρ,
    ∀ D, M.duties_attest_with (M.gradeContract nr.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nr.st nr.record ⇢ D →
    ∀ (h : Height) (root : BlockId) (tmo : Bool),
      D.2.2.height_pair = NamedHeightPair.vote h root tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root →
        Block.Compatible P C.erase := by
  intro nr hnr D hD h root tmo hvote C hC hCroot
  obtain ⟨g, hg'⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ
  have hg := (facts.nd.gradeContract_read nr.cache S.E S.hc _ ρ g).1 hg'
  obtain ⟨-, hQ, -⟩ := Restated.actionGradeRead_preceq_of_graded facts S Sched x htd hρ hn hawake hvh hgr
    hF hroot (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew) nr hnr g hg
  have hvhn : Restated.HonestThrough M Sched x n u := fun t ht =>
    hvh t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n)))
  have hRd := actionReadFrom_round_att facts S (x[n][u].st) ρ nr hnr
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ
  obtain ⟨o, ho'⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ A2
  have ho : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nr ⇢ o := by
    refine (returns_bind_iff_att _ _ _).2 ⟨A2, ?_, ?_⟩
    · show M.grade2_block_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
        (M.round_of S.hc (M.toHealing nr.st.core).s) ⇢ A2
      rw [hRd]; exact hA2
    · show M.fg_source_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
        (M.round_of S.hc (M.toHealing nr.st.core).s) A2 ⇢ o
      rw [hRd]; exact ho'
  obtain ⟨Cfg, rfl, hCfg⟩ := Restated.entry_preceq_source_of_honest facts S Sched x hexec hn hvhn
    nr hnr D hD hvote o ho
  obtain ⟨Q, hQ', hQCfg⟩ := facts.dt.fg_source_with_some _ _ _ _ _ (some Cfg) ho' rfl
  have hA2g : A2 = g.Q2 :=
    facts.nd.gradeContract_grade2_block_with nr.cache S.E S.hc _ ρ g hg A2 hA2
  exact compatible_iff_Compatible.mpr
    (compatible_of_preceq_common_Preceq
      (preceq_trans_Preceq (hQ Q (by rw [← hA2g]; exact hQ')) hQCfg)
      (hCfg C hC hCroot))

end

end DecoupledConsensusModel.Sts.Restated
