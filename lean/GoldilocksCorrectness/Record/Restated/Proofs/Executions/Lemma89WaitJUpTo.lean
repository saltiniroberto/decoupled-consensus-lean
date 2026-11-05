module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89WaitJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89WaitJUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89WaitJUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: part B of Lemma 89, no honest
validator reaching the height of a later honest proposal's justification one delay before it, and no
honest justification height reaching the waited height before the later opening's support cutoff,
restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm ancestorEq_genesis_iff)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **No honest validator reaches the height of a later honest proposal's justification one delay
before it.** When `p` proposes `B` at the start of slot `s + 1`, active from `max (Δ S) Δs` before
`t + Δ` to that start, a validator `u` active from that time through `t` and honest at its last step
before `t`, with `GST + max (Δ S) Δs ≤ t + Δ` and `t + Δ` at most that start, has `h_j` less than
`B`'s chain-state height. At `t = 0` `u`'s state is the initial one; otherwise `held_spread_h_j`
reads `u` at `t + Δ − max (Δ S) Δs` and `p` from then.

Roots name blocks until `M.slotStart S.C (s + 1)`: the proposer's `h_j` is read before the start of
slot `s + 1` (`h_j_mono`), after `u`'s justification spreads to it by `t + Δ`.

Restated with the delivery premises up to `M.slotStart S.C (s + 1)`: the bound of its roots
`hRoots`; the one delivery its proof reads is `held_spread_h_j_upTo` at `t`, due by `t + Δ S`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: one delay before an honest proposal, every honest justification is lower than it, with
the delivery premises up to the start of slot `s + 1`. -/
theorem h_j_lt_of_later_proposal_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd t s : ℕ) (u p : V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.slotStart S.C (s + 1)))
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hGST : GST + max (Δ S) Δs ≤ t + Δ S) (hle : t + Δ S ≤ M.slotStart S.C (s + 1))
      (hEnd : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- `u` is active from `max (Δ S) Δs` before `t + Δ S` through `t + Δ S`, and honest at its last step before `t`
    (hu₀ : u ∈ A.activeThroughout x ((t + Δ S) - (max (Δ S) Δs)) (t + Δ S))
    (hu : u ∉ A.corrupted (x.stepBefore t))
    -- `p` is active at every step from the real time `max (Δ S) Δs` before `t + Δ S` up to its tick to the start of
    -- slot `s + 1`
    (hp : ∀ i : ℕ, (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ x.tickStep p (M.slotStart S.C (s + 1)) →
      p ∈ A.active i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    (x.stateBefore t u).justifiedHeight < (M.chainStateOf S.C B).h := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
  obtain ⟨kv, hkv⟩ := hpv
  have h3 := (honest_proposal_above_h_j M F U Fx) S A x R E s B p hPropose
  obtain ⟨iP, hiP, -⟩ := hPropose
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hIn : x.tickInput p (M.slotStart S.C (s + 1)) = x.st iP p := by
    unfold Trace.tickInput
    rw [hkP]
  rw [hIn] at h3
  rw [hkP] at hRoots hEnd hp
  obtain ⟨⟨D, hD, hJD, hj⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t u
  rw [hj]
  have hlt47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  by_cases hg : D = Block.genesis
  · have hh := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) (C := S.C)
    rw [hg] at hlt47 ⊢
    unfold Height at *
    omega
  have hD' : D ∈ (x.st (x.stepBefore t) u).tree := hD
  obtain ⟨ie, hie, -⟩ := (tree_block_relayed_entry M F) x R E hD' hg
  have ht1 : 1 ≤ t := by
    -- the relayed entry `ie` comes before `x.stepBefore t`, so the step after it is at a real time less
    -- than `t`, and every real time of the trace is at least `0`
    have h1 := ((lt_stepBefore_iff M) x R E).1 hie
    have h2 := (time_nonneg M) x R (ie + 1)
    exact Nat.cast_pos.1 (lt_of_le_of_lt h2 h1)
  have hFu : (x.stateBefore t u).finalized.AncestorEq D := by
    have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_stateBefore M F) S A x R E t u
    rw [hJD] at hFJ
    exact ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1
  -- the block's slot is at most `s`: `u`'s clock before `t` is less than `t + ΔClockAhead`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hHs := (slot_le_clockValue_of_mem_tree M F) R E hu hD'
  rw [← hsl] at hHs
  have hcv := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore t) u
  have hkt := ((stepBefore_time M) x R E ht1).1
  have hleR : (t : ℝ) + Δ S ≤ M.slotStart S.C (s + 1) := by exact_mod_cast hle
  have hDs : D.slot ≤ s := by
    by_contra hc
    have h1 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S (s + 1)
      (x.clockValue (x.stepBefore t) u)).2 (le_trans (Nat.succ_le_of_lt (not_le.1 hc)) hHs)
    have h2 : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ x.clockValue (x.stepBefore t) u := by exact_mod_cast h1
    have h4 : max 0 (x.time (x.stepBefore t) + ΔClockAhead) < (t : ℝ) + Δ S :=
      max_lt (by positivity) (by linarith)
    linarith
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hDc₂ : M.slotStart S.C D.slot ≤ M.viewFreeze S.C s := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hDs
    omega
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_add_Δ_le_slotStart_of_lt M.toSlotLayout
    F.sched) S (Nat.lt_succ_self s)
  have hmx1 := le_max_left (Δ S) Δs
  have hu₀' : u ∈ A.activeThroughout x (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    refine Activity.mem_activeThroughout.2 (fun i h1 h2 => Activity.mem_activeThroughout.1 hu₀ i ?_ ?_)
    · have : (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs ≤ (t : ℝ) + Δ S := by
        have : (t + Δ S) - max (Δ S) Δs + Δs ≤ t + Δ S := by
          have := le_max_right (Δ S) Δs
          omega
        exact_mod_cast this
      push_cast at this ⊢
      linarith
    · have : ((t : ℝ) + Δ S) - (max (Δ S) Δs : ℕ) ≤ (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) := by
        have := Nat.sub_add_cancel (show max (Δ S) Δs ≤ t + Δ S by omega)
        have h' : ((((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ)) + (max (Δ S) Δs : ℕ) = (t : ℝ) + Δ S := by
          exact_mod_cast this
        linarith
      push_cast at this ⊢
      linarith
  rcases (held_spread_tick M F U Fx) S A x R GST (M.slotStart S.C (s + 1)) tEnd t ((t + Δ S) - max (Δ S) Δs)
      (M.slotStart S.C (s + 1)) (M.viewFreeze S.C s) iP kv u p D E hNet hRedeliver Sy hRoots
      hParent hThird hEnd (by omega) (by omega) (by omega) hle le_rfl hu₀' hu hD hFu hg hiP hp hkv hc₂ hDc₂
    with ⟨hDw, hFw⟩ | hle'
  · have := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E iP p D hDw hFw
    unfold Height at *
    omega
  · unfold Height at *
    omega

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the
waited height `h`, other than the genesis block.** With `t₀ + Δ` the start of the later opening's
slot `s + 1`, whose honest proposer `p` proposes `B₂` at the height `h`; every honest
`head_height_floor` at most `h` from `t₀` to `tc`; `p` ticking to the view freeze of slot `s`; and no honest fork-choice change from `t₀` to before `tc`:
every honest validator at a time from `tL` to `tc` has `h_j < h`, or the genesis block as its
justified block.

Roots name blocks until `M.slotStart S.C (s + 1)`: `h_j_lt_of_later_proposal` at the later opening's
slot `s + 1`, the only reading of the premise.

Restated with the delivery premises up to `M.slotStart S.C (s + 1)`: the bound of its roots
`hRoots`, as `h_j_lt_of_later_proposal_upTo`, which it calls.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: until the later opening's support cutoff, no honest validator has justified anything at
the waited height, with the delivery premises up to the start of slot `s + 1`. -/
theorem h_j_lt_or_genesis_before_cutoff_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd tL t₀ tc s h : ℕ) (p : V) (B₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.slotStart S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hL0 : tL ≤ t₀) (ht₀ : t₀ + Δ S = M.slotStart S.C (s + 1))
    (hs : M.slotStart S.C (s + 1) ≤ tEnd)
    -- the proposer's tick to the start of slot `s + 1` is at a real time at most `tEnd`
    (hsT : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- from a time `a` after `GST`, at least one delay or one sync delay before `tL + Δ S` and before `tL`,
    -- every validator outside the adversary set is awake through `tEnd`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ tL + Δ S) (ha₁ : a + 1 ≤ tL)
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₂ : (M.chainStateOf S.C B₂).h = h)
    (hF : ∀ (u : V) (t : ℕ), t₀ ≤ t → t ≤ tc → u ∉ A.corruptedAtTime x t →
      M.head_height_floor (x.stateBefore t u) ≤ h)
    (hNo : ∀ (w : V) (j : ℕ), (t₀ : ℝ) ≤ x.time j → x.time j < (tc : ℝ) → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (u : V) (t : ℕ) (hGt : tL ≤ t) (htc' : t ≤ tc) (hu : u ∉ A.corruptedAtTime x (t + Δ S)) :
    (x.stateBefore t u).justifiedHeight < h ∨
      (x.stateBefore t u).justified = Block.genesis := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨iP, hiP, hsentP⟩ := hPropose
  have huN : u ∉ A.corruptedAtTime x ((t + Δ S : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    exact hu
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hpP : p ∉ A.corrupted iP := E.not_mem_corrupted_of_tick hiP
  have hsTP : x.time iP ≤ tEnd := by rw [← hkP]; exact hsT
  have hsR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ tEnd := by exact_mod_cast hs
  -- up to `t₀`: `h_j_lt_of_later_proposal`, with the windows read from `hAw` and `u`'s, `p`'s honesty
  have hW3 : ∀ t', tL ≤ t' → t' ≤ t₀ → t' ≤ t →
      (x.stateBefore t' u).justifiedHeight < h := by
    intro t' h1 h2 h3
    have hmx1 := le_max_left (Δ S) Δs
    have hat' : a ≤ (t' + Δ S) - max (Δ S) Δs := by omega
    have hatR : (a : ℝ) ≤ (((t' + Δ S) - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hat'
    have hsub : (((t' + Δ S) - max (Δ S) Δs : ℕ) : ℝ) = (t' : ℝ) + Δ S - (max (Δ S) Δs : ℕ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have ht'R : (t' : ℝ) + Δ S ≤ M.slotStart S.C (s + 1) := by
      have : t' + Δ S ≤ M.slotStart S.C (s + 1) := by omega
      exact_mod_cast this
    have htt'R : (t' : ℝ) + Δ S ≤ ((t + Δ S : ℕ) : ℝ) := by
      have : t' + Δ S ≤ t + Δ S := by omega
      exact_mod_cast this
    have hu₀ : u ∈ A.activeThroughout x ((t' + Δ S) - (max (Δ S) Δs)) (t' + Δ S) := by
      refine Activity.mem_activeThroughout.2 (fun i hi1 hi2 => ?_)
      have hui : u ∉ A.corrupted i := (not_mem_corrupted_of_le_time M) x R E huN (by linarith)
      refine Activity.mem_active.2 ⟨hAw i u (by linarith) ?_ hui, hui⟩
      push_cast at hi2 hsub
      linarith
    have hu' : u ∉ A.corrupted (x.stepBefore t') := by
      refine (not_mem_corrupted_of_le_time M) x R E huN ?_
      have := (time_stepBefore_le M) x R E t'
      have : (t' : ℝ) ≤ t := by exact_mod_cast h3
      push_cast
      have : (0 : ℝ) ≤ Δ S := by positivity
      linarith
    have hp' : ∀ i : ℕ, (((t' + Δ S) - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i →
        i ≤ x.tickStep p (M.slotStart S.C (s + 1)) → p ∈ A.active i := by
      intro i hi1 hi2
      rw [hkP] at hi2
      have hpi : p ∉ A.corrupted i := fun hc => hpP (E.corrupted_mono _ _ hi2 hc)
      exact Activity.mem_active.2 ⟨hAw i p (le_trans (htime hi2) hsTP)
        (le_trans hatR (le_trans hi1 (htime (Nat.le_succ i)))) hpi, hpi⟩
    have := (h_j_lt_of_later_proposal_upTo M F U Fx) S A x R GST tEnd t' s u p B₂ E hNet hSkew hRedeliver Sy
      hRoots hParent hThird (by omega) (by omega) hsT hu₀ hu' hp' hpv ⟨iP, hiP, hsentP⟩
    rw [hB₂] at this
    exact this
  by_cases hlt : (x.stateBefore t u).justifiedHeight < h
  · exact Or.inl hlt
  right
  by_contra hJg
  have htt₀ : t₀ < t := by
    by_contra hle
    exact hlt (hW3 t hGt (by omega) le_rfl)
  -- `h ≥ 2`: a justified block other than the genesis block has a justification height at least 2
  obtain ⟨⟨D, -, hJD, hjD⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t u
  have hj2 : 2 ≤ (x.stateBefore t u).justifiedHeight := by
    by_contra hlt2
    apply hJg
    rw [hJD]
    exact (J_genesis_of_h_j_le_one M F) S.C D (by rw [← hjD]; unfold Height at *; omega)
  have hut : u ∉ A.corruptedAtTime x t := (not_mem_corruptedAtTime_of_le M) x R E (by omega) huN
  have hflt := hF u t (by omega) htc' hut
  have hjl := (h_j_lt_h_max M F) S A x R E t u
  have hmx := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X
    (x.stateBefore t u) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hut)
  have hh2 : 2 ≤ h := by
    unfold Height at *
    omega
  -- the step `x.stepBefore t₀` moves the time, so it leaves `u`'s state as it was
  have ht01 : 1 ≤ t₀ := by omega
  obtain ⟨hk0a, hk0b⟩ := (stepBefore_time M) x R E ht01
  have hother : x.lbl (x.stepBefore t₀) = Event.other := by
    by_contra hne
    have := R.time_keep _ hne
    linarith
  have hst0 : x.st (x.stepBefore t₀ + 1) u = x.st (x.stepBefore t₀) u :=
    R.untouched _ u (fun _ hc => by rw [hother] at hc; cases hc)
      (fun _ _ hc => by rw [hother] at hc; cases hc) (fun _ hc => by rw [hother] at hc; cases hc)
  -- the first step from `x.stepBefore t₀ + 1` after which `u`'s `h_j` reaches `h` or its
  -- `head_height_floor` exceeds `h`
  have hP0 : ¬ (h ≤ (x.st (x.stepBefore t₀ + 1) u).justifiedHeight ∨
      h < M.head_height_floor (x.st (x.stepBefore t₀ + 1) u)) := by
    rw [hst0]
    have h1 : (x.st (x.stepBefore t₀) u).justifiedHeight < h := hW3 t₀ hL0 le_rfl htt₀.le
    have h2 : M.head_height_floor (x.st (x.stepBefore t₀) u) ≤ h :=
      hF u t₀ le_rfl (by omega) ((not_mem_corruptedAtTime_of_le M) x R E htt₀.le hut)
    (try unfold Height at *)
    omega
  have hPt : h ≤ (x.st (x.stepBefore t) u).justifiedHeight ∨
      h < M.head_height_floor (x.st (x.stepBefore t) u) := Or.inl (Nat.le_of_not_lt hlt)
  have hk0t : x.stepBefore t₀ + 1 ≤ x.stepBefore t := by
    by_contra hc
    have heq : x.stepBefore t = x.stepBefore t₀ :=
      le_antisymm (by omega) ((stepBefore_mono M) x R E htt₀.le)
    exact hP0 (by rw [hst0, ← heq]; exact hPt)
  classical
  have hex : ∃ n : ℕ, h ≤ (x.st (x.stepBefore t₀ + 1 + n) u).justifiedHeight ∨
      h < M.head_height_floor (x.st (x.stepBefore t₀ + 1 + n) u) :=
    ⟨x.stepBefore t - (x.stepBefore t₀ + 1), by
      rw [show x.stepBefore t₀ + 1 + (x.stepBefore t - (x.stepBefore t₀ + 1)) = x.stepBefore t by omega]
      exact hPt⟩
  have hn := Nat.find_spec hex
  have hnle : Nat.find hex ≤ x.stepBefore t - (x.stepBefore t₀ + 1) :=
    Nat.find_min' hex (by
      rw [show x.stepBefore t₀ + 1 + (x.stepBefore t - (x.stepBefore t₀ + 1)) = x.stepBefore t by omega]
      exact hPt)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at hn
    exact hP0 hn
  have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  obtain ⟨j, hjdef⟩ : ∃ j, j = x.stepBefore t₀ + 1 + (Nat.find hex - 1) := ⟨_, rfl⟩
  rw [← hjdef] at hprev
  rw [show x.stepBefore t₀ + 1 + Nat.find hex = j + 1 by omega] at hn
  have hlo : (x.st j u).justifiedHeight < h := by
    (try unfold Height at *)
    omega
  have hflo : M.head_height_floor (x.st j u) ≤ h := by
    (try unfold Height at *)
    omega
  -- the step `j` is at a time from `t₀` to before `tc`, at which `u` is honest
  have ht1 : 1 ≤ t := by omega
  have hkt := ((stepBefore_time M) x R E ht1).1
  have hj0 : (t₀ : ℝ) ≤ x.time j := le_trans hk0b (htime (show x.stepBefore t₀ + 1 ≤ j by omega))
  have hjt : x.time j < x.time (x.stepBefore t) + 1 := by
    have := htime (show j ≤ x.stepBefore t by omega)
    linarith
  have hjtc : x.time j < (tc : ℝ) := by
    have h1 := htime (show j ≤ x.stepBefore t by omega)
    have h2 : (t : ℝ) ≤ tc := by exact_mod_cast htc'
    linarith
  have huj : u ∉ A.corrupted j := by
    refine (not_mem_corrupted_of_le_time M) x R E huN ?_
    have h1 := htime (show j ≤ x.stepBefore t by omega)
    push_cast
    have : (0 : ℝ) ≤ Δ S := by positivity
    linarith
  apply hNo u j hj0 hjtc huj
  rcases hn with hhi | hfl
  · by_cases hfl1 : M.head_height_floor (x.st (j + 1) u) ≤ h
    · have hJg₁ : (x.st (j + 1) u).justified ≠ Block.genesis := by
        intro hg
        obtain ⟨⟨D₁, -, hJD₁, hjD₁⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (j + 1) u
        have hh1 : 1 ≤ (M.chainStateOf S.C D₁).h_j := by
          rw [← hjD₁]
          unfold Height at *
          omega
        have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D₁).2.2 hh1
        rw [← hJD₁, hg] at hJh
        have : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
          (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
        rw [this, ← hjD₁] at hJh
        unfold Height at *
        omega
      exact (change_of_h_j_reaches M F) S A x R E u j h hlo hhi hfl1 hJg₁
    · exact Or.inr (by (try unfold Height at *); omega)
  · exact Or.inr (by (try unfold Height at *); omega)


/-- **One delay before an honest proposal, every honest justification is lower than it, read at a step**
, with the delivery premises up to the start of slot `s + 1`. When `p` proposes `B` at its tick to the start
of slot `s + 1`, active at every step from the real time `a` up to that tick and ticking to the view freeze of slot `s`,
a validator `u` outside the adversary set at the step `k`, active from `a` through the sync delay after it, with
`GST ≤ a ≤ x.time k`, `a + max (Δ S) Δs` at most the start of slot `s + 1` and `x.time k + Δ S` at most that start, has
`h_j` at `k` less than `B`'s chain-state height.

Why: as `h_j_lt_of_later_proposal`, with the holder read at its step `k` in place of its last step before a natural
time. The block `D` witnessing `u`'s `h_j` at `k` has its slot at most `s` (`u`'s clock at `k` is at most
`x.time k + ΔClockAhead`, less than the start of slot `s + 1`); when `D` is higher than `p`'s `h_j` at its tick,
`p`'s finalized block there is an ancestor of `D` (`F_ancestorEq_of_high_st`) and `block_at_tick_of_held_step` puts `D`
in `p`'s tree (its earlier tick to the view freeze of slot `s` supplies the re-delivery premise), so `D`'s `h_j` is at
most `p`'s; otherwise `D`'s `h_j` is less than its height, at most `p`'s `h_j`; and `p`'s `h_j` is less than `B`'s
height (`honest_proposal_above_h_j`).

Roots name blocks until the time of the proposer's tick to the start of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound; `a`: the start of the windows; `s + 1`: the proposal's slot;
  `k`: the reader's step; `u`: the reader; `p`: the proposer; `B`: the proposal.

Read aloud: one delay before an honest proposal, every honest validator's justification at a step is lower than it. -/
theorem h_j_lt_of_later_proposal_st_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd a s k : ℕ) (u p : V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.slotStart S.C (s + 1)))
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hEnd : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- the windows start at `a`, from `GST` on and at most the real time of `k`; one delay or one sync delay after `a`
    -- is at most the start of slot `s + 1`, and so is one delay after the real time of `k`
    (hGSTa : GST ≤ a) (hak : (a : ℝ) ≤ x.time k) (ha : a + max (Δ S) Δs ≤ M.slotStart S.C (s + 1))
    (hle : x.time k + Δ S ≤ M.slotStart S.C (s + 1))
    -- `u` is active from `a` through the sync delay after it, and outside the adversary set at `k`
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hu : u ∉ A.corrupted k)
    -- `p` is active at every step from the real time `a` up to its tick to the start of slot `s + 1`
    (hp : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep p (M.slotStart S.C (s + 1)) → p ∈ A.active i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    (x.st k u).justifiedHeight < (M.chainStateOf S.C B).h := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨kv, hkv⟩ := hpv
  have h3 := (honest_proposal_above_h_j M F U Fx) S A x R E s B p hPropose
  obtain ⟨iP, hiP, -⟩ := hPropose
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hIn : x.tickInput p (M.slotStart S.C (s + 1)) = x.st iP p := by
    unfold Trace.tickInput
    rw [hkP]
  rw [hIn] at h3
  rw [hkP] at hRoots hEnd hp
  obtain ⟨⟨D, hD, hJD, hj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k u
  rw [hj]
  have hlt47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  by_cases hg : D = Block.genesis
  · have hh := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) (C := S.C)
    rw [hg] at hlt47 ⊢
    unfold Height at *
    omega
  have hFu : (x.st k u).finalized.AncestorEq D := by
    have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E k u
    rw [hJD] at hFJ
    exact ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1
  -- the block's slot is at most `s`: `u`'s clock at `k` is at most `x.time k + ΔClockAhead`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hHs := (slot_le_clockValue_of_mem_tree M F) R E hu hD
  rw [← hsl] at hHs
  have hcv := (clockValue_le_time_add_ahead M F) x R E k u
  have hk0 := (time_nonneg M) x R k
  have hDs : D.slot ≤ s := by
    by_contra hc
    have h1 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S (s + 1)
      (x.clockValue k u)).2 (le_trans (Nat.succ_le_of_lt (not_le.1 hc)) hHs)
    have h2 : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ x.clockValue k u := by exact_mod_cast h1
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
    have h4 : max 0 (x.time k + ΔClockAhead) < x.time k + Δ S :=
      max_lt (by linarith) (by linarith)
    linarith
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hDc₂ : M.slotStart S.C D.slot ≤ M.viewFreeze S.C s := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hDs
    omega
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_add_Δ_le_slotStart_of_lt M.toSlotLayout
    F.sched) S (Nat.lt_succ_self s)
  -- the reader's step comes before the proposer's tick
  have hiPt := (E.tick_active iP p _ hiP).2.1
  have hkiP : x.time k ≤ x.time iP := by linarith
  have hpi : p ∉ A.corrupted iP := E.not_mem_corrupted_of_tick hiP
  by_cases hlt : (x.st iP p).justifiedHeight < (M.chainStateOf S.C D).h
  · have hFD := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd iP k p u D hThird
      hEnd (le_trans hkiP hEnd) hpi hu hD hlt (max_le le_rfl hkiP)
    -- `stepBefore a ≤ k`, so `u`'s finalized block at its last step before `a` is an ancestor of the one at `k`
    have hak' : x.stepBefore a ≤ k := by
      by_contra hc
      have h1 := ((lt_stepBefore_iff M) x R E).1 (show k < x.stepBefore a by omega)
      have h2 := htime (Nat.le_succ k)
      linarith
    have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E u hak') ((compatible_iff _ _).2 (Or.inl hFu))
    have hstΔ : Δ S ≤ M.slotStart S.C (s + 1) := by
      have : ((Δ S : ℕ) : ℝ) ≤ M.slotStart S.C (s + 1) := by linarith
      exact_mod_cast this
    have htu : x.time k ≤ ((M.slotStart S.C (s + 1) - Δ S : ℕ) : ℝ) := by
      rw [Nat.cast_sub hstΔ]
      linarith
    have hΔN : ΔNet ≤ Δ S := by
      have : (ΔNet : ℝ) ≤ Δ S := by linarith
      exact_mod_cast this
    have hDw := block_at_tick_of_held_step M F U S A x R GST (M.slotStart S.C (s + 1))
      (M.slotStart S.C (s + 1) - Δ S) k a (M.slotStart S.C (s + 1)) (M.viewFreeze S.C s) iP kv u p D
      E hNet hSkew hRedeliver Sy hRoots hParent hGSTa ha (by omega) le_rfl hu₀ htu hu hD hFa hg
      hiP hp hkv hc₂ hDc₂ ((compatible_iff _ _).2 (Or.inl hFD))
    have := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E iP p D hDw hFD
    unfold Height at *
    omega
  · unfold Height at *
    omega

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the waited height `h`,
other than the genesis block, read at a step**, with the delivery premises up to the start of slot `s + 1`. With `p` proposing `B₂` at the height `h` at its tick to the start of slot `s + 1`, as in
`h_j_lt_of_later_proposal_st_upTo`: a validator `u` outside the adversary set at a step `k` and active from `a` through
the sync delay after it, with an earlier step `k₁ ≤ k` at a real time at least `tL` and at least one delay before the start of slot `s + 1`,
whose `head_height_floor` at `k₁` and at `k` is at most `h` and none of whose steps from `k₁` to before `k` is a
fork-choice change, has `h_j` at `k` less than `h`, or the genesis block as its justified block there.

Why: at `k₁`, `u`'s `h_j` is less than `h` (`h_j_lt_of_later_proposal_st_upTo`, the windows from `hAw`, from `a`). When
`u`'s `h_j` at `k` is at least `h` with a justified block other than the genesis block, `h ≥ 2` (`u`'s `h_j` is less
than its greatest chain-state height, at most its `head_height_floor` plus one, at most `h + 1`); take the first step
`j` from `k₁` after which `u`'s `h_j` reaches `h` or its `head_height_floor` exceeds `h`. The step `j` is a
`ForkChoiceChangeStep`: its `head_height_floor` rises, or `h_j` reaches `h` with `head_height_floor` at most `h`
(`change_of_h_j_reaches`, `h ≥ 2` keeping the justified block off the genesis block); `hNo` excludes it.

Restated in place of the earlier step form (twenty-third launch): the floor and the no-change premise are read on the
reader's own steps from its step `k₁`, the steps its proof reads; a premise read at every honest validator's step up
to a time needs, for the callers' no-change facts, a later tick of each such validator, which only the reader is known
to have.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound and of the awake window; `tL`: the earliest real time of
  `k₁`; `s + 1`: the later proposal's slot; `h`: its chain-state height; `p`: its proposer; `B₂`: the proposal; `a`:
  the start of the windows; `u`: the reader; `k₁ ≤ k`: its two steps.

Read aloud: until the later opening's support cutoff, no honest validator has justified anything at the waited height,
read at any of its steps after an earlier step one delay before the opening at which its floor is at most that
height, with no fork-choice change of its own in between. -/
theorem h_j_lt_or_genesis_before_cutoff_st_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd tL s h : ℕ) (p : V) (B₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.slotStart S.C (s + 1)))
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hs : M.slotStart S.C (s + 1) ≤ tEnd)
    -- the proposer's tick to the start of slot `s + 1` is at a real time at most `tEnd`
    (hsT : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- from a time `a` after `GST`, at least one delay or one sync delay before `tL + Δ S` and before `tL`,
    -- every validator outside the adversary set is awake through `tEnd`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ tL + Δ S) (ha₁ : a + 1 ≤ tL)
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₂ : (M.chainStateOf S.C B₂).h = h)
    -- the reader `u`, outside the adversary set at its step `k` and active from `a` through `a + Δs`; its earlier step
    -- `k₁`, at a real time at least `tL` and at least one delay before the start of slot `s + 1`
    (u : V) (k₁ k : ℕ) (hk₁k : k₁ ≤ k) (hGt : (tL : ℝ) ≤ x.time k₁)
    (hk₁s : x.time k₁ + Δ S ≤ M.slotStart S.C (s + 1))
    (hu : u ∉ A.corrupted k) (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    -- `u`'s `head_height_floor` at `k₁` and at `k` is at most `h`
    (hF₁ : M.head_height_floor (x.st k₁ u) ≤ h) (hF : M.head_height_floor (x.st k u) ≤ h)
    -- no step of `u` from `k₁` to before `k` is a fork-choice change
    (hNo : ∀ j : ℕ, k₁ ≤ j → j < k → ¬ ForkChoiceChangeStep M S A x u j) :
    (x.st k u).justifiedHeight < h ∨ (x.st k u).justified = Block.genesis := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨iP, hiP, hsentP⟩ := hPropose
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hpP : p ∉ A.corrupted iP := E.not_mem_corrupted_of_tick hiP
  have hsTP : x.time iP ≤ tEnd := by rw [← hkP]; exact hsT
  have hsR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ tEnd := by exact_mod_cast hs
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  -- `u` is outside the adversary set at `k` and at `k₁`
  have hk₁t := htime hk₁k
  have huk : u ∉ A.corrupted k := hu
  have huk₁ : u ∉ A.corrupted k₁ := E.not_mem_corrupted_of_le hk₁k hu
  -- `p` is active at every step from `a` up to its tick
  have hp' : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep p (M.slotStart S.C (s + 1)) → p ∈ A.active i := by
    intro i hi1 hi2
    rw [hkP] at hi2
    have hpi : p ∉ A.corrupted i := fun hc => hpP (E.corrupted_mono _ _ hi2 hc)
    exact Activity.mem_active.2 ⟨hAw i p (le_trans (htime hi2) hsTP)
      (le_trans hi1 (htime (Nat.le_succ i))) hpi, hpi⟩
  have hatL : ((a + max (Δ S) Δs : ℕ) : ℝ) ≤ (tL : ℝ) + Δ S := by exact_mod_cast ha
  push_cast at hatL
  -- at `k₁`: the step form of `h_j_lt_of_later_proposal`
  have hW₁ : (x.st k₁ u).justifiedHeight < h := by
    have hak : (a : ℝ) ≤ x.time k₁ := by
      have : ((a + 1 : ℕ) : ℝ) ≤ tL := by exact_mod_cast ha₁
      push_cast at this
      linarith
    have ha' : a + max (Δ S) Δs ≤ M.slotStart S.C (s + 1) := by
      have : ((a + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.slotStart S.C (s + 1) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have := (h_j_lt_of_later_proposal_st_upTo M F U Fx) S A x R GST tEnd a s k₁ u p B₂ E hNet hSkew hRedeliver Sy
      hRoots hParent hThird hsT hGSTa hak ha' hk₁s hu₀ huk₁ hp' hpv ⟨iP, hiP, hsentP⟩
    rw [hB₂] at this
    exact this
  by_cases hlt : (x.st k u).justifiedHeight < h
  · exact Or.inl hlt
  right
  by_contra hJg
  -- `h ≥ 2`: a justified block other than the genesis block has a justification height at least 2
  obtain ⟨⟨D, -, hJD, hjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k u
  have hj2 : 2 ≤ (x.st k u).justifiedHeight := by
    by_contra hlt2
    apply hJg
    rw [hJD]
    exact (J_genesis_of_h_j_le_one M F) S.C D (by rw [← hjD]; unfold Height at *; omega)
  have hjl := (h_j_lt_h_max_st M F) S A x R E k u
  have hmx := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X
    (x.st k u) ((lem11_node_invariant M F S A x R E k u huk).1)
  have hh2 : 2 ≤ h := by
    unfold Height at *
    omega
  -- the first step from `k₁` after which `u`'s `h_j` reaches `h` or its `head_height_floor` exceeds `h`
  have hP0 : ¬ (h ≤ (x.st k₁ u).justifiedHeight ∨ h < M.head_height_floor (x.st k₁ u)) := by
    (try unfold Height at *)
    omega
  have hPt : h ≤ (x.st k u).justifiedHeight ∨ h < M.head_height_floor (x.st k u) :=
    Or.inl (Nat.le_of_not_lt hlt)
  classical
  have hex : ∃ n : ℕ, h ≤ (x.st (k₁ + n) u).justifiedHeight ∨ h < M.head_height_floor (x.st (k₁ + n) u) :=
    ⟨k - k₁, by
      rw [show k₁ + (k - k₁) = k by omega]
      exact hPt⟩
  have hn := Nat.find_spec hex
  have hnle : Nat.find hex ≤ k - k₁ :=
    Nat.find_min' hex (by
      rw [show k₁ + (k - k₁) = k by omega]
      exact hPt)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at hn
    exact hP0 hn
  have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  obtain ⟨j, hjdef⟩ : ∃ j, j = k₁ + (Nat.find hex - 1) := ⟨_, rfl⟩
  rw [← hjdef] at hprev
  rw [show k₁ + Nat.find hex = j + 1 by omega] at hn
  have hlo : (x.st j u).justifiedHeight < h := by
    (try unfold Height at *)
    omega
  have hflo : M.head_height_floor (x.st j u) ≤ h := by
    (try unfold Height at *)
    omega
  apply hNo j (by omega) (by omega)
  rcases hn with hhi | hfl
  · by_cases hfl1 : M.head_height_floor (x.st (j + 1) u) ≤ h
    · have hJg₁ : (x.st (j + 1) u).justified ≠ Block.genesis := by
        intro hg
        obtain ⟨⟨D₁, -, hJD₁, hjD₁⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (j + 1) u
        have hh1 : 1 ≤ (M.chainStateOf S.C D₁).h_j := by
          rw [← hjD₁]
          unfold Height at *
          omega
        have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D₁).2.2 hh1
        rw [← hJD₁, hg] at hJh
        have : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
          (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
        rw [this, ← hjD₁] at hJh
        unfold Height at *
        omega
      exact (change_of_h_j_reaches M F) S A x R E u j h hlo hhi hfl1 hJg₁
    · exact Or.inr (by (try unfold Height at *); omega)
  · exact Or.inr (by (try unfold Height at *); omega)


end GoldilocksCorrectness.Record.Proofs.Executions

