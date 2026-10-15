import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConfirmedAgree
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReaders
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_InclusionAnchorTree
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKit
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_StableRootFor
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReadersRecv

/-!
# The stable root descends from graded blocks

Cache and round facts along the execution, and the theorem that the stable root an honest reader
writes from at a confirmation tick of round `q + 1` is a descendant of every block it graded at that
round's grade-2 domain instant; stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open DecoupledConsensusModel.Statements.Instantiation

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pSB% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

private theorem round_cases_sr (q c ρ : ℕ) (a : q ≤ c) (b : c ≤ ρ) (h : ρ ≤ q + 1) :
    (ρ = c ∧ (q + 1 = c ∨ q + 1 = c + 1)) ∨ (ρ = c + 1 ∧ q + 1 = c + 1) := by
  omega

private theorem slot_add_three_sr (a b R : ℕ) (h : b = a + R) (hR : 3 ≤ R) : a + 3 ≤ b := by
  omega

private theorem slot_gap_sr (a b c s R : ℕ) (h : b = a + R) (hR : 3 ≤ R) (h2 : b ≤ c)
    (h3 : c ≤ s) : a + 2 ≤ s ∧ 0 < s := by
  omega

/-- The same arithmetic with `c ≤ s + 1`: `a + 3 ≤ b ≤ c ≤ s + 1`. -/
private theorem slot_gap_sr' (a b c s R : ℕ) (h : b = a + R) (hR : 3 ≤ R) (h2 : b ≤ c)
    (h3 : c ≤ s + 1) : a + 2 ≤ s ∧ 0 < s := by
  omega

/-- Every block the confirmation walk at `st` can start from, under the grade contract of `c`, is
    `st`'s fork-choice root or a member of `st`'s filtered tree. -/
private theorem confAnchorWith_gradeContract_root_or_mem_sr (facts : Record.Facts M) (S : Execution.Setup V)
    (c : M.Cache) (st : M.S) (A : Block V)
    (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc st ⇢ A) :
    A = M.get_fg_root (M.toHealing st).toFG ∨
      A ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
  unfold Restated.Vocabulary.Protocol.confAnchorWith at hA
  have hA' := (facts.nd.gradeContract_sgRoot_eq_frameAnchor c S.E S.hc (M.toHealing st)
    (M.round_of S.hc st.s) A).1 hA
  rcases facts.gr.anchor_cases S.E S.hc _ _ _ A hA' with h | ⟨root, A', -, hp, rfl⟩
  · exact Or.inl h
  · exact Or.inr (facts.gr.activePrefix_mem _ _ _ hp)

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `o_r ≤ s`, then `r` is at most the round of `s`. -/
theorem le_round_of_of_opening_slot_le_sr (facts : Record.Facts M) (S : Setup V) {r : Round} {s : Slot}
    (h : (M.opening_slot S.hc r) ≤ s) : r ≤ (M.round_of S.hc s) := by
  by_contra hcon
  have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
  have h2 : (M.opening_slot S.hc ((M.round_of S.hc s) + 1)) ≤ (M.opening_slot S.hc r) :=
    facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon))
  exact Nat.lt_irrefl s (lt_of_lt_of_le h1 (le_trans h2 h))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `s < o_{r+1}`, then the round of `s` is at most `r`. -/
theorem round_of_le_of_lt_opening_slot_sr (facts : Record.Facts M) (S : Setup V) {r : Round} {s : Slot}
    (h : s < (M.opening_slot S.hc (r + 1))) : (M.round_of S.hc s) ≤ r := by
  by_contra hcon
  have h1 := facts.gr.opening_slot_round_of_le_slot S.hc s
  have h2 : (M.opening_slot S.hc (r + 1)) ≤ (M.opening_slot S.hc ((M.round_of S.hc s))) :=
    facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon))
  exact Nat.lt_irrefl s (lt_of_lt_of_le h (le_trans h2 h1))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `t_0 ≤ t_1`, the round of `t_0`'s slot is at most the round of `t_1`'s. -/
theorem roundAt_mono_sr (facts : Record.Facts M) (S : Setup V) {t_0 t_1 : Int} (h : t_0 ≤ t_1) :
    (M.round_of S.hc (S.E.slotOf t_0)) ≤ (M.round_of S.hc (S.E.slotOf t_1)) :=
  Restated.le_round_of_of_opening_slot_le_sr facts S
    (le_trans (facts.gr.opening_slot_round_of_le_slot S.hc _) (slotOf_mono_sts S h))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Two steps that are both the last one strictly before the instant `c` are the same step. -/
theorem stepBeforeInstant_unique_sr (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m_1 m_2 : Nat} {c : Int}
    (h_1 : Restated.stepBeforeInstant M x m_1 c) (h_2 : Restated.stepBeforeInstant M x m_2 c) : m_1 = m_2 := by
  rcases lt_trichotomy m_1 m_2 with h | h | h
  · have a := h_2.1 m_1 h
    have b := h_1.2 m_1 le_rfl
    omega
  · exact h
  · have a := h_1.1 m_2 h
    have b := h_2.2 m_2 le_rfl
    omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- After step `k`, `v`'s node state is the one before; or step `k` is the tick at some instant `τ`
    and, for every outcome `c` of the phase tick at `τ` of `v`'s cache and store before, `v`'s cache
    is `c` clipped to its finalized block after; or `v`'s cache is its cache before, clipped to its
    finalized block after. -/
theorem cache_succ_cases_sr (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) (v : V) :
    x[k + 1][v].st = x[k][v].st ∨
    (∃ τ : Nat, x.lbl k = AtomicAction.tickAllAwake τ ∧
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[k][v].st).st.core) (τ : Int)
          (x[k][v].st).cache ⇢ c →
        (x[k + 1][v].st).cache = M.clipCache (x[k + 1][v].st).st.core.F c) ∨
    (x[k + 1][v].st).cache = M.clipCache (x[k + 1][v].st).st.core.F (x[k][v].st).cache := by
  cases hl : x.lbl k with
  | tickAllAwake τ =>
      rcases Restated.st_succ_of_tick facts S Sched x v hl with ⟨-, out₁, hout, hst⟩ | hst
      · right; left
        refine ⟨τ, rfl, fun c hc => ?_⟩
        rw [hst]
        have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) v (↑τ)
        exact facts.nd.namedNode_tick_cache _ v _ _ out₁ hout c
          (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc)
      · -- the tick has no outcome: `v` holds the node state its tick reads
        right; right
        rw [hst, Record.wakeStage_cache facts, Record.wakeStage_st facts]
        exact ((Restated.nodeInvariant_sts facts S Sched x k v).2.2).symm
  | deliver p m =>
      by_cases hp : p = v
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
        · right; right
          have _hr_s2 := Record.reachedNode_sts facts S Sched x (k) p
          exact facts.nd.namedNode_process_cache _ _ _ _ hproc
        · left; exact hst
      · left
        rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]
  | custom _ ev => exact ev.elim
  | adversarial p m =>
      left
      rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]
  | forward p m =>
      left
      rw [Restated.getElem_succ_of_forward facts S Sched x hl]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At every step, every result `v`'s cache holds is for a round at most the current instant's
    round, or for a phase whose domain instant has come. -/
theorem cacheNoFutureResult_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) (v : V) : Restated.CacheNoFutureResult M S Sched x k v := by
  induction k with
  | zero =>
      intro r p o h
      left
      rw [facts.grRun.phaseResult_initial_some S Sched x v h]
      exact Nat.zero_le _
  | succ k ih =>
      have htm : (x[k].time : Int) ≤ (x[k + 1].time : Int) :=
        Restated.time_mono_int facts S Sched x (Nat.le_succ k)
      have hρ := Restated.roundAt_mono_sr facts S htm
      have hold : ∀ (r : Round) (p : Protocol.Phase) (o : Option (Block V)),
          M.phaseResult (M.cacheAtRound (x[k][v].st).cache r) p = some o →
          r ≤ (M.round_of S.hc (S.E.slotOf (x[k + 1].time : Int))) ∨
            M.domain S.E S.hc r p ≤ (x[k + 1].time : Int) := by
        intro r p o h
        rcases ih r p o h with h1 | h1
        · exact Or.inl (le_trans h1 hρ)
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
        rcases facts.gr.phaseResult_onPhaseTick_some_cases S.E S.hc _ _ _ c hc' h₁ with h2 | h2 | ⟨o', h2⟩
        · left; rw [hτ]; exact le_of_eq h2
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

/-- If `G2EntryAbove` holds for `w`, `q` and `X` after `k₀` steps, the instant `x[n].time` is in
    round `q + 1` or earlier, and `X` lies on one chain with `w`'s finalized block at every step up
    to `n`, then `G2EntryAbove` holds after `n` steps. -/
theorem g2EntryAbove_kept (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {q : Round} {X : Block V} {w : V} {k₀ n : Nat} (hkn : k₀ ≤ n)
    (h₀ : Restated.G2EntryAbove M S Sched x q X k₀ w)
    (hend : (M.round_of S.hc (S.E.slotOf (x[n].time : Int))) ≤ q + 1)
    (hXF : ∀ j : Nat, j ≤ n → Block.compatible X (x[j][w].st).st.core.F = true) :
    Restated.G2EntryAbove M S Sched x q X n w := by
  induction n, hkn using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
      have htm : (x[k].time : Int) ≤ (x[k + 1].time : Int) :=
        Restated.time_mono_int facts S Sched x (Nat.le_succ k)
      have hρ := Restated.roundAt_mono_sr facts S htm
      have hend' : (M.round_of S.hc (S.E.slotOf (x[k].time : Int))) ≤ q + 1 := le_trans hρ hend
      obtain ⟨hq0, hq1, e, he, hXe⟩ :=
        ih hend' (fun j hj => hXF j (Nat.le_succ_of_le hj))
      rcases Restated.cache_succ_cases_sr facts S Sched x k w with hst | ⟨τ, hl, hc⟩ | hc
      · refine ⟨?_, ?_, e, ?_, hXe⟩
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
        have hcases : ((M.round_of S.hc (S.E.slotOf (τ : Int))) = (x[k][w].st).cache.round ∧
            (q + 1 = (x[k][w].st).cache.round ∨ q + 1 = (x[k][w].st).cache.round + 1)) ∨
            ((M.round_of S.hc (S.E.slotOf (τ : Int))) = (x[k][w].st).cache.round + 1 ∧
              q + 1 = (x[k][w].st).cache.round + 1) := by
          exact round_cases_sr _ _ _ hq0 hcτ hρτ
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
        · exact facts.gr.preceq_clipGrade (hXF (k + 1) le_rfl) _
            (facts.gr.preceq_clipGrade (hXF k (Nat.le_succ k)) e hXe)
      · refine ⟨?_, ?_, M.clipGrade e (x[k + 1][w].st).st.core.F, ?_, ?_⟩
        · rw [hc, facts.gr.clipCache_round]; exact hq0
        · rw [hc, facts.gr.clipCache_round]; exact le_trans hq1 hρ
        · rw [hc]; exact facts.gr.phaseResult_clipCache_some he
        · exact facts.gr.preceq_clipGrade (hXF (k + 1) le_rfl) e hXe

end

-- Folded in from the former module `Claim13bK_StableRootForRecv.lean` (wake switch, lane S).
/-!
# The stable root is a descendant of a graded block, at a reader awake from t₀, from a receipt

`stableRoot_descendant_of_graded` of `Claim13bK_StableRootFor.lean` with the reader `w` of the
round-`(q + 1)` grade awake from some `t₀` at or before its grade-2 late cutoff less `2 * Δ + 1` in
place of `S.a q`, and its receipt of round `q`'s honest attestations before the grade-2 first
cutoff.
-/

open DecoupledConsensusModel.Statements.Instantiation






section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises and the joint invariant at the switch round: if `q` is at least two
    rounds after the switch round, `w` is awake from `t₀` to round `(q + 1)`'s grade-2 domain
    instant, with `t₀` at or before its grade-2 late cutoff less `2 * Δ + 1`, receives round `q`'s
    honest attestations before its grade-2 first cutoff, `w`'s store at the last step before that instant can grade `X` for round `q + 1`, `s`
    is a slot such that `s + 1` is in round `q + 1` and at or after `o_{q+1}`, `X` is an ancestor of every
    honest head of slot `s` when `s` is `o_{q+1} − 1`, and `w` is awake from one
    delay before slot `s`'s start to its confirmation instant and held by the adversary at no
    instant up to it, then for every outcome of `w`'s phase tick at that confirmation instant, every
    stable root its grade contract can return is a descendant of `X` or `X` itself. -/
theorem stableRoot_descendant_of_graded_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {q : Round} (hq : Restated.switchRound M S tE + 2 ≤ q) {X : Block V} {w : V}
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc (q + 1) .g2 - 1 - 2 * S.E.Δ)
    (hawT : w ∈ Sched.awakeThroughout t₀ (M.domain S.E S.hc (q + 1) .g2))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x q w (M.early S.E S.hc (q + 1) .g2))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) .g2))
    (hgr : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
      (M.late S.E S.hc (q + 1) .g2) X ⇢ true)
    {s : Slot} (hs1 : (M.opening_slot S.hc (q + 1)) ≤ s + 1) (hsr : (M.round_of S.hc (s + 1)) = q + 1)
    (hXs0 : (M.opening_slot S.hc (q + 1)) ≤ s ∨ Restated.HeadsBelow M S Sched x X s)
    {n : Nat} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hvaw2 : w ∈ Sched.awakeThroughout
      (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ) (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) w)
    {G : Block V} {c : M.Cache}
    (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
        (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G) :
    Block.Preceq X G := by
  have hvaw := Restated.slotWindow_of_grade2Window facts S Sched hvaw2
  have _hr_0 : M.reachedNode (x[m][w].st) := Record.reachedNode_sts facts S Sched x m w
  have _hr_1 : M.reachedNode (x[m + 1][w].st) := Record.reachedNode_sts facts S Sched x (m + 1) w
  have _hr_2 : M.reachedNode (x[n][w].st) := Record.reachedNode_sts facts S Sched x n w
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hq' : Restated.switchRound M S tE ≤ q := le_trans (Nat.le_add_right _ 2) hq
  -- the instants, in closed form
  have hdomE : M.domain S.E S.hc (q + 1) .g2
      = 4 * S.E.Δ * (((M.opening_slot S.hc (q + 1)) : Nat) : Int) - S.E.Δ := by
    rw [← facts.gr.gammaNeg1_eq_domain_g2_succ S q, slotStart_closed]
  have hSaq : (Restated.Vocabulary.Execution.Setup.a M S q) = 4 * S.E.Δ * (((M.opening_slot S.hc q) : Nat) : Int) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S q, (pCR% confirmation_time_closed_cr) facts]
  have hctc := (pCR% confirmation_time_closed_cr) facts S.E s
  have hss := slotStart_closed S.E.Δ s
  have hsucc : ((M.opening_slot S.hc (q + 1)) : ℕ) = ((M.opening_slot S.hc q) : ℕ) + S.hc.R :=
    facts.gr.opening_slot_succ S.hc q
  have hR3 := S.hc.R_ge_three
  have hO1 : (((M.opening_slot S.hc q) : Nat) : Int) + 3 ≤ (((M.opening_slot S.hc (q + 1)) : Nat) : Int) := by
    have := slot_add_three_sr _ _ _ hsucc hR3
    exact_mod_cast this
  have hO1s : (((M.opening_slot S.hc (q + 1)) : Nat) : Int) ≤ ((s : Nat) : Int) + 1 := by exact_mod_cast hs1
  have hO0 : (0 : Int) ≤ (((M.opening_slot S.hc q) : Nat) : Int) := Int.natCast_nonneg _
  have hm1 := mul_le_mul_of_nonneg_left hO1 (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
  have hm2 := mul_le_mul_of_nonneg_left hO1s (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
  have hm0 := mul_le_mul_of_nonneg_left hO0 (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
  set dom := M.domain S.E S.hc (q + 1) .g2 with hdom
  have hSa_dom : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ dom := by rw [hdomE, hSaq]; linarith
  have hdom_ct : dom < M.confirmation_time S.E s := by rw [hdomE, hctc]; linarith
  have hdom_pos : 0 < dom := by rw [hdomE]; linarith
  have hdom_lt : dom < slotStart S.E.Δ ((M.opening_slot S.hc (q + 1))) := by
    rw [hdomE, slotStart_closed]; linarith
  have hdom_ge : slotStart S.E.Δ ((M.opening_slot S.hc q)) ≤ dom - 1 := by
    rw [hdomE, slotStart_closed]; linarith
  have hdvd : dom % S.E.Δ = 0 := by
    have : dom = S.E.Δ * (4 * (((M.opening_slot S.hc (q + 1)) : Nat) : Int) - 1) := by
      rw [hdomE]; ring
    rw [this]; exact Int.mul_emod_right _ _
  -- the rounds of the instants
  have hρdom : (M.round_of S.hc (S.E.slotOf dom)) = q := by
    apply le_antisymm
    · exact Restated.round_of_le_of_lt_opening_slot_sr facts S
        (slotOf_lt_of_lt_slotStart S (by linarith) hdom_lt)
    · apply Restated.le_round_of_of_opening_slot_le_sr facts S
      rw [← slotOf_slotStart S ((M.opening_slot S.hc q))]
      exact slotOf_mono_sts S (by linarith)
  have hρdom1 : (M.round_of S.hc (S.E.slotOf (dom - 1))) ≤ q :=
    Restated.round_of_le_of_lt_opening_slot_sr facts S (slotOf_lt_of_lt_slotStart S (by linarith) (by linarith))
  have hρct : (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) = q + 1 := by
    rw [facts.sch.Optimistic_slotOf_confirmation_time S.E s, hsr]
  -- the reader's facts
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hvn : Restated.HonestThrough M Sched x n w := fun t ht => hvh t (by linarith)
  have hwdom : w ∈ Sched.awake dom \ Sched.adv dom :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hawT
      (by rw [hdom]; linarith [facts.gr.late_le_domain S (q + 1) .g2, S.E.Δ_pos]) le_rfl,
      hvh dom (le_of_lt hdom_ct)⟩
  -- the tick step at the domain instant is `m`
  obtain ⟨d, hdt⟩ := Restated.exists_tickStepAt facts x htd hdom_pos
  have hmd : m = d := Restated.stepBeforeInstant_unique_sr facts S Sched x hm (Restated.stepBeforeInstant_of_tickStepAt facts x hdt)
  subst hmd
  obtain ⟨hd1t, hd0t⟩ := Restated.tickStepAt_time facts x hdt
  have hdn : m + 1 ≤ n := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (show n + 1 ≤ m + 1 by omega)
    linarith
  -- the joint invariants at rounds `q` and `q + 1`, and the heads of every graded block
  obtain ⟨n1, T1, hJ1, -, hTW1⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch le_rfl hTW₀ hJ₀ hq'
  obtain ⟨n2, T2, hJ2, -, -⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch le_rfl hTW₀ hJ₀ (Nat.le_succ_of_le hq')
  have hgH : ∀ B : Block V, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
      (M.late S.E S.hc (q + 1) .g2) B ⇢ true →
      Restated.AncestorOfHonestHeadsFrom M S Sched x B ((M.opening_slot S.hc (q + 1))) :=
    fun B hB => Restated.graded_ancestorOfHonestHeadsFrom_at_awakeReader_recv facts S Sched x tE hexec hmono htd
      hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev
      hclear hB' hnW hAW hJswitch hq' hTW1 hJ1 hJ2 t₀ ht₀ hawT hrecv (Finset.mem_sdiff.1 hwdom).2 hm hB
  have hXH := hgH X hgr
  -- the frozen root is a descendant of `X`
  obtain ⟨H, hH, hXH'⟩ := facts.gr.Sts_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ _ true hgr rfl
  have hXT : X ∈ (M.gradeView (M.toHealing (x[m][w].st).st.core)).T := by
    rw [facts.gr.Sts_gradeView_T] at hH ⊢
    exact Restated.mem_T_of_preceq_sts facts S Sched x m w hH hXH'
  -- one outcome of the grade test for every block, `true` at `X`
  classical
  have hgne := fun B : Block V => facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) .g2) (M.late S.E S.hc (q + 1) .g2) B
  let g : Block V → Bool := fun B => if B = X then true else (hgne B).choose
  have hg : ∀ B : Block V, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
      (M.late S.E S.hc (q + 1) .g2) B ⇢ g B := by
    intro B
    by_cases hBX : B = X
    · have : g B = true := if_pos hBX
      rw [this, hBX]; exact hgr
    · have : g B = (hgne B).choose := if_neg hBX
      rw [this]; exact (hgne B).choose_spec
  have hgX : g X = true := if_pos rfl
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) .g2) (M.late S.E S.hc (q + 1) .g2)
  obtain ⟨D, hD, hXD⟩ := facts.gr.preceq_freezeRoot S.E _ _ _ _ _ _ g hg hXT hgX
    (fun D _ D' _ hD hD' => Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs
      (hgH D (hD ▸ hg D)) (hgH D' (hD' ▸ hg D'))) fr hfr
  -- `X` on one chain with every finalized block up to `n`
  have hFn := Restated.finalized_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
    hJswitch le_rfl hTW₀ hJ₀ (k := n)
    (by have := Restated.action_mono facts S hq'; linarith) hvn
  have hXFn := Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hXH hFn
  have hXF : ∀ j : Nat, j ≤ n → Block.compatible X (x[j][w].st).st.core.F = true := by
    intro j hj
    have hFj := Restated.F_mono facts S Sched x w hj
    rcases compatible_cases hXFn with h | h
    · exact Block.compatible_of_preceq_common (preceq_eq_true_iff_Preceq.mpr h)
        (preceq_eq_true_iff_Preceq.mpr hFj)
    · exact compatible_of_cases (Or.inr (preceq_trans_Preceq hFj h))
  -- the cache held no round-`(q + 1)` grade-2 result before the domain tick
  have hnone : M.phaseResult (M.cacheAtRound (x[m][w].st).cache (q + 1)) .g2
      = none := by
    cases hpr : M.phaseResult (M.cacheAtRound (x[m][w].st).cache (q + 1)) .g2 with
    | none => rfl
    | some o =>
        exfalso
        have ht : (x[m].time : Int) = dom - 1 := by linarith
        rcases Restated.cacheNoFutureResult_sts facts S Sched x m w (q + 1) .g2 o hpr with h | h
        · rw [ht] at h; exact Nat.not_succ_le_self q (le_trans h hρdom1)
        · rw [ht] at h; linarith
  -- the domain tick writes the clipped frozen root
  obtain ⟨τ, hl, hτ⟩ := hdt
  obtain ⟨out₁, hout, hst⟩ : ∃ out₁ : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (τ : Int) x[m] w) (τ : Int) ⇢ out₁ ∧
        x[m + 1][w].st = out₁.1 := by
    rcases Restated.st_succ_of_tick_awake facts S Sched x w hl (by rw [hτ]; exact hwdom)
      with h | ⟨hno, -⟩
    · exact h
    · obtain ⟨out, hout⟩ := facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
        m τ w hl (by rw [hτ]; exact hwdom)
        (fun t' ht' => hvh t' (by rw [hτ] at ht'; linarith))
      exact absurd hout (hno out)
  obtain ⟨c₁, hc₁⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (M.toHealing (x[m][w].st).st.core) dom (x[m][w].st).cache
  have hc1 : (x[m + 1][w].st).cache = M.clipCache (x[m + 1][w].st).st.core.F c₁ := by
    rw [hst]
    have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (m) w (↑τ)
    exact facts.nd.namedNode_tick_cache _ w _ _ out₁ hout c₁
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, hτ]; exact hc₁)
  have hfr' : M.freezeRoot S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (M.toHealing (x[m][w].st).st.core).toFG.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
      (M.late S.E S.hc (q + 1) .g2) ⇢ fr := by
    rw [facts.sto.Sts_toHealing_F]
    exact hfr
  have hdomtick := facts.gr.phaseResult_onPhaseTick_domain S.E S.hc (M.toHealing (x[m][w].st).st.core) dom
    (x[m][w].st).cache (by rw [hρdom]) rfl hnone c₁ hc₁ fr hfr'
  rw [hD, Option.map_some, facts.sto.Sts_toHealing_F] at hdomtick
  have hbase : Restated.G2EntryAbove M S Sched x q X (m + 1) w := by
    refine ⟨?_, ?_, M.clipGrade (M.clipGrade D (x[m][w].st).st.core.F)
      (x[m + 1][w].st).st.core.F, ?_, ?_⟩
    · rw [hc1, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c₁ hc₁, hρdom]
    · rw [hc1, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c₁ hc₁, hd1t]
    · rw [hc1]; exact facts.gr.phaseResult_clipCache_some hdomtick
    · exact facts.gr.preceq_clipGrade (hXF (m + 1) hdn) _ (facts.gr.preceq_clipGrade (hXF m (by omega)) D hXD)
  -- kept up to the read step
  have hendn : (M.round_of S.hc (S.E.slotOf (x[n].time : Int))) ≤ q + 1 := by
    rw [← hρct]; exact Restated.roundAt_mono_sr facts S (by linarith)
  obtain ⟨hq0, hq1, e, he, hXe⟩ := Restated.g2EntryAbove_kept facts S Sched x hdn hbase hendn hXF
  -- the read tick keeps the entry, and the frame read clips it once more
  have hcases : ((M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s)))
        = (x[n][w].st).cache.round ∧
      (q + 1 = (x[n][w].st).cache.round ∨ q + 1 = (x[n][w].st).cache.round + 1)) ∨
      ((M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s)))
        = (x[n][w].st).cache.round + 1 ∧ q + 1 = (x[n][w].st).cache.round + 1) := by
    rw [hρct]
    exact round_cases_sr _ _ _ hq0 (le_trans hq1 hendn) le_rfl
  have _hrr_s2 := facts.nd.reachedRead_of_node _ (Record.reachedNode_sts facts S Sched x n w)
  have hkept := facts.gr.phaseResult_onPhaseTick_kept S.E S.hc (M.toHealing (x[n][w].st).st.core)
    (M.confirmation_time S.E s) (x[n][w].st).cache he hcases c hc
  have hrf := facts.gr.readFrame_g2_of_cache (st := (M.toHealing (M.ns_setClock S.E (x[n][w].st).st
    (M.confirmation_time S.E s)).core)) (r := q + 1) hkept
  have hXst' : Block.compatible X (M.toHealing (M.ns_setClock S.E (x[n][w].st).st
      (M.confirmation_time S.E s)).core).toFG.F = true := by
    rw [facts.hd.setClock_toHealing_F]; exact hXF n le_rfl
  have hXe'' : Block.Preceq X (M.clipGrade (M.clipGrade e
      (M.toHealing (x[n][w].st).st.core).toFG.F) (M.toHealing (M.ns_setClock S.E (x[n][w].st).st
      (M.confirmation_time S.E s)).core).toFG.F) :=
    facts.gr.preceq_clipGrade hXst' _ (facts.gr.preceq_clipGrade (by rw [facts.sto.Sts_toHealing_F]; exact hXF n le_rfl) e hXe)
  -- the round the stable root is read at
  have hslot : (M.ns_setClock S.E (x[n][w].st).st
      (M.confirmation_time S.E s)).core.s = s + 1 := by
    rw [facts.hd.Sts_setClock_core_s]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  rw [hslot, hsr] at hG
  -- `X` is in the filtered tree, or an ancestor of the fork-choice root
  have hsl : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ s := by
    have h1 : ((M.opening_slot S.hc (Restated.switchRound M S tE + 1 + 1)) : ℕ)
        = ((M.opening_slot S.hc (Restated.switchRound M S tE + 1)) : ℕ) + S.hc.R :=
      facts.gr.opening_slot_succ S.hc (Restated.switchRound M S tE + 1)
    have h2 : ((M.opening_slot S.hc (Restated.switchRound M S tE + 1 + 1)) : ℕ)
        ≤ ((M.opening_slot S.hc (q + 1)) : ℕ) :=
      facts.gr.opening_slot_mono S (Nat.le_succ_of_le hq)
    exact (slot_gap_sr' _ _ _ _ _ h1 S.hc.R_ge_three h2 hs1).1
  have hspos : 0 < s := by
    have h1 := facts.gr.opening_slot_succ S.hc (Restated.switchRound M S tE + 1)
    have h2 : (M.opening_slot S.hc (Restated.switchRound M S tE + 1 + 1)) ≤ (M.opening_slot S.hc (q + 1)) :=
      facts.gr.opening_slot_mono S (Nat.le_succ_of_le hq)
    exact (slot_gap_sr' _ _ _ _ _ h1 S.hc.R_ge_three h2 hs1).2
  have hXs : Restated.HeadsBelow M S Sched x X s := by
    rcases hXs0 with h | h
    · exact hXH s h
    · exact h
  -- one outcome of the SG root the confirmation walk starts from, under `c`'s grade contract
  obtain ⟨A, hA₀⟩ : ∃ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][w].st) s) ⇢ A :=
    facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.toHealing (Restated.confStoreAt M S (x[n][w].st) s))
      (M.round_of S.hc (Restated.confStoreAt M S (x[n][w].st) s).s)
  have hA : Restated.HeadsBelow M S Sched x A s :=
    Restated.confAnchor_headsBelow_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
      hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀
      hsl hn hvaw2 hvh c hc A hA₀
  obtain ⟨t', -, ht's, -, hcs'⟩ := Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap
    hgst hlen hphase hcs (r := Restated.switchRound M S tE + 1) (Nat.le_succ _)
  have hanchor : t' ≤ slotStart S.E.Δ (s + 1) :=
    le_trans ht's (slotStart_mono S (Nat.le_succ_of_le hsl))
  have hAX := Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hspos hanchor hA hXs
  have hrootA := Restated.confAnchor_fgRoot_preceq facts S (x[n][w].st) s c hc A hA₀
  have hpc0 : Restated.Vocabulary.Internal.ParentClosed M (x[n][w].st).st.core :=
    (pSB% parentClosed_of_inv') facts (Restated.nodeInvariant_sts facts S Sched x n w)
  have hpc : Restated.Vocabulary.Internal.ParentClosed M (Restated.confStoreAt M S (x[n][w].st) s) := by
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc0 ⊢
    rw [facts.sto.toHealing_gs_T] at hpc0 ⊢
    rw [Restated.confStoreAt, facts.hd.Sts_setClock_core_T]
    exact hpc0
  have hFJ : Block.Preceq (Restated.confStoreAt M S (x[n][w].st) s).F (Restated.confStoreAt M S (x[n][w].st) s).J := by
    rw [Restated.confStoreAt, facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Restated.F_preceq_J_sts facts S Sched x n w
  have hXA_case : Block.Preceq X A →
      X ∈ M.get_filtered_block_tree (M.toHealing (Restated.confStoreAt M S (x[n][w].st) s)).toFG ∨
      Block.Preceq X (M.get_fg_root (M.toHealing (Restated.confStoreAt M S (x[n][w].st) s)).toFG) := by
    intro hXA
    rcases confAnchorWith_gradeContract_root_or_mem_sr facts S c
      (Restated.confStoreAt M S (x[n][w].st) s) A hA₀ with hAr | hAm
    · right; rw [← hAr]; exact hXA
    · rcases compatible_cases (Block.compatible_of_preceq_common (preceq_eq_true_iff_Preceq.mpr hXA)
        (preceq_eq_true_iff_Preceq.mpr hrootA)) with h | h
      · right; exact h
      · left; exact Restated.mem_filtered_of_preceq_mem_filtered_l85b facts hpc hFJ hAm hXA h
  have hTR : X ∈ M.get_filtered_block_tree (M.toHealing (Restated.confStoreAt M S (x[n][w].st) s)).toFG ∨
      Block.Preceq X (M.get_fg_root (M.toHealing (Restated.confStoreAt M S (x[n][w].st) s)).toFG) := by
    rcases compatible_cases hAX with hAX' | hXA
    · by_cases hne : X = A
      · exact hXA_case (by rw [hne]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self A))
      · left
        have hmem := Restated.confAnchorChainInTree_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
          hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
          hTW₀ hJ₀ hsl hn hvaw hvh hXs c hc A hA₀ X hAX' hne
          (preceq_eq_true_iff_Preceq.mp (Block.preceq_self X))
        exact hmem
    · exact hXA_case hXA
  exact facts.gr.preceq_frameStableRoot _ S.E S.hc _ (q + 1) hrf hXe'' hTR _ hG rfl

end


section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises and the joint invariant at the switch round: if `q` is at least two
    rounds after the switch round, `w` is an honest active attester of round `q + 1`, and `w`'s
    store at the last step before round `(q + 1)`'s grade-2 domain instant can grade `X` for round
    `q + 1`, then for every outcome of `w`'s phase tick at `S.a (q + 1)`, every stable root its
    grade contract can return is a descendant of `X` or `X` itself. -/
theorem stableRoot_descendant_of_graded_at_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {q : Round} (hq : Restated.switchRound M S tE + 2 ≤ q) {X : Block V} {w : V}
    (hw1 : w ∈ Restated.HonRound M S Sched (q + 1))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) .g2))
    (hgr : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
      (M.late S.E S.hc (q + 1) .g2) X ⇢ true)
    {n : Nat} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))))
    {G : Block V} {c : M.Cache}
    (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
        (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) (x[n][w].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot
          S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))))).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))))).core.s) ⇢ some G) :
    Block.Preceq X G := by
  have hawT := Restated.awakeThroughout_late_domain_of_honRound_succ facts S Sched hw1
    (facts.gr.domain_le_action S (q + 1) .g2)
  have hrecv := (Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
    (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
      (le_trans (Nat.le_add_right _ 2) hq))).1 w hw1
  have hvhT : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) w :=
    mem_honestThroughSet.1 (Restated.honRound_subset_honestThroughSet facts S Sched (q + 1) hmono hw1)
  have hsr : (M.round_of S.hc ((M.opening_slot S.hc (q + 1)) + 1)) = q + 1 := by
    rw [← Restated.slotOf_action facts S (q + 1)]; exact Restated.round_of_slotOf_action facts S (q + 1)
  exact Restated.stableRoot_descendant_of_graded_recv facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch hTW₀
    hJ₀ hq _ le_rfl hawT hrecv hm hgr (Nat.le_succ _) hsr (Or.inl le_rfl) hn (Restated.honRound_grade2Window_confirmation facts S Sched (q + 1) hw1)
    (by rw [Restated.confirmation_time_opening_slot facts S (q + 1)]; exact hvhT) hc hG

end

end DecoupledConsensusModel.Sts.Restated
