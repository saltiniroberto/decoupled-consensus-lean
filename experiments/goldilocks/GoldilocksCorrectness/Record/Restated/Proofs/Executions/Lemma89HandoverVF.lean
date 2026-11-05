module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Handover
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Handover
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89HandoverVF, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89HandoverVF.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 89 of record (`lem89_phase`)
with the voter frame at the first slot of the last honest round opening slot's round, the
hand-over's copy that adds that clause, and the line facts with the phase's end at that slot. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_mono supportCutoff_eq
  supportCutoff_mono times_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn TreeClosed)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows OutsideSpans
  Vocab.goldilocks acObject fgObject healFrontSlots)
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible ancestorEq_of_parent?
  ancestorEq_node_iff state_transition_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The line facts with the phase's end at the last opening -/

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **The finalized block is compatible with every line source (copy with the end at slot
`σ + 1`).** `F_compat` with its end premise `M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd` replaced by
the two bounds its proof reads, `M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd` and `t ≤ tAwakeEnd`: at a
time `t ≥ 1` up to the vote time of slot `σ + 2` and up to `tAwakeEnd`, when the invariant
holds at every slot up to `σ`, an honest validator's finalized block is compatible with every line
source of a slot at most `σ`. The body is `F_compat`'s, with each comparison of two line sources split
on their slots (`sources_compatible_lt`, `sources_compatible_eq` with `hEndA` at a round's first slot).
The time `t` is at most the vote time of slot `σ + 2`: a tick to the support cutoff of slot `σ + 2` is at a
real time at least that cutoff minus `ΔClockAhead`, later than that vote time, so every certificate the
validator holds before `t` names a line source of a slot at most `σ`.

The variables:
- `M`: the model; `F`: its facts.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: at a time `t ≥ 1` up to the vote time of slot `σ + 2` and up to the phase's end,
with the phase running at least to the support cutoff of slot `σ + 1` and the line invariant at
every slot up to `σ`, and every tick to the action time of a round whose first slot is at most `σ` in
the phase, an honest validator's finalized block is compatible with every line source of
a slot at most `σ`. -/
theorem F_compat_vf (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (ht1 : 1 ≤ t)
    (ht : t ≤ M.voteTime S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (x.stateBefore t w).finalized.compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  obtain ⟨D, hD, hFD⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E
      (x.stepBefore t) w
  show (x.st (x.stepBefore t) w).finalized.compatible X = true
  rw [hFD]
  -- the step before `t` is at a time less than `t` (`stepBefore_time`'s strict bound)
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have htE' : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast htE
  have hjE : x.time (x.stepBefore t) ≤ tAwakeEnd := by linarith
  have hw' : w ∉ A.corrupted (x.stepBefore t) :=
    (not_mem_corrupted_of_le_time M) x R P.E hw htj.le
  by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
  · -- `v` held `L` at its tick to the action time of round `r` (`L_held_v`), honest there, in the phase
    have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
    have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
        (max (x.time (x.stepBefore t)) (x.time (x.tickStep v (aR M S r)))) :=
      P.hThird.mono (max_le hjE P.hEndStep)
    have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
    have hFL := (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots (x.stepBefore t)
      (x.tickStep v (aR M S r)) w v D L hT hw' hv' hD hLv
      (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep)
    -- `L` is a line source of slot `r * R`: two slots compared by `sources_compatible_lt`, one slot (a round's
    -- first slot, `hEndA` at `r`) by `sources_compatible_eq`
    have hLX : L.compatible X = true := by
      rcases Nat.lt_or_eq_of_le (hX.slot_ge M F) with h | h
      · exact PartAHyps.sources_compatible_lt M F hG (P.source_L M F R U hEndR) hX h hμ
      · subst h
        exact P.sources_compatible_eq M F R U (hEndA r hσ) (P.source_L M F R U hEndR) hX
    exact compatible_of_ancestorEq_compatible hFL hLX
  · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (M.chainStateOf S.C D).F ∈ (x.st (x.stepBefore t) w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hFanc
    obtain ⟨r', Eb, u, kc, hkc, hkcj, -, hE, -, -, hEr, -⟩ :=
      P.cert_source_fast_round M F R E U Fx hjE hD
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hFE : (M.chainStateOf S.C D).F = Eb :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := w) hw' hjE hFT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hFE]
    -- the update of slot `r' * R` ran at a tick before the reading, at most the vote time of slot `σ + 2`,
    -- so `r' * R ≤ σ`: a tick to the support cutoff of slot `σ + 2` or later is at a real time at least that
    -- cutoff minus `ΔClockAhead`, more than one delay `Δ S` before it (`hSkew`)
    have hμ'σ : r' * S.C.R ≤ σ := by
      by_contra h
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 2 ≤ r' * S.C.R + 1 by omega)
      obtain ⟨hv2, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
      have hcv : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) = ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) + Δ S := by
        rw [hc2, hv2]; push_cast; ring
      have hle2 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      have hkt := (E.tick_active _ _ _ hkc).2.1
      have hkk := (time_mono M) x R hkcj.le
      have htR : ((t : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) := by exact_mod_cast ht
      have hsk := hSkew
      have hB0 := E.behind_nonneg
      linarith
    rcases lt_trichotomy (r' * S.C.R) μ with h | h | h
    · exact PartAHyps.sources_compatible_lt M F hG hE hX h hμ
    · subst h
      exact P.sources_compatible_eq M F R U (hEndA r' hμ) hE hX
    · exact GoldilocksCorrectness.Proofs.Routines.compatible_symm' (PartAHyps.sources_compatible_lt M F hG hX hE h hμ'σ)

/-- **The root is compatible with every line source, given `L` at the reading (copy with the end at
slot `σ + 1`).** `root_compat_vf`'s argument, as `root_compat_of_L` for `root_compat`, with the one fact it reads from `L_tall` taken as hypotheses: `w` holds `L` before `t`
(`hLT`), and its greatest chain-state height before `t` is at least `H₂ + 1` (`hM`). The root is
the finalized block (`F_compat_vf`), or the justified block: a line source of a round's first slot at
most `σ` when its height is greater than `H₂` (`cert_source_fast_round`; at most `σ` since `t` is at most
the vote time of slot `σ + 2`), compared with `X` on their slots (`sources_compatible_lt`, or
`sources_compatible_eq` at the round's first slot with `hEndA`), and `L` or an ancestor of `L` otherwise (the contest rule, with
the finalized block an ancestor of `L` by Lemma 89a, or a line source taller than the justified
block, which cannot be).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.
- `hLT`, `hM`: `w` holds `L` before `t`, at a greatest chain-state height at least `H₂ + 1`.

Read aloud: when an honest validator holds `L` before `t`, at a greatest chain-state height at least
`H₂ + 1`, its fork-choice root before `t` is compatible with every line source of a slot at most `σ`,
up to the phase's end. -/
theorem root_compat_vf_of_L (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (ht0 : M.viewFreeze S.C (r * S.C.R) ≤ t)
    (ht : t ≤ M.voteTime S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hLT : L ∈ (x.stateBefore t w).tree) (hM : H₂ + 1 ≤ hMax M S.C (x.stateBefore t w)) :
    (M.get_fc_root (x.stateBefore t w)).compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have ht1 : 1 ≤ t := by
    obtain ⟨-, -, hf0, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
    omega
  have hwj : w ∉ A.corrupted (x.stepBefore t) :=
    Activity.not_mem_corruptedAtTime.1 hw _ ((time_stepBefore_le M) x R E t)
  have hInv : M.nodeInv S.C S.P S.X (x.stateBefore t w) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
      (x.stepBefore t) w) hwj).1
  by_cases hR : M.get_fc_root (x.stateBefore t w) = (x.stateBefore t w).finalized
  · rw [hR]
    exact P.F_compat_vf M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 htE hEndA ht1 ht hw hX hμ
  have key : hMax M S.C (x.stateBefore t w) = (x.stateBefore t w).justifiedHeight + 1 ∧
      M.get_fc_root (x.stateBefore t w) = (x.stateBefore t w).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.stateBefore t w) hInv
      with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_stateBefore M F) S A x R E t w
  -- the step before `t` is at a time less than `t` (`stepBefore_time`'s strict bound)
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have htE' : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast htE
  have hjE : x.time (x.stepBefore t) ≤ tAwakeEnd := by linarith
  rw [key.2]
  by_cases hlt : H₂ < (x.stateBefore t w).justifiedHeight
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hD' : D ∈ (x.st (x.stepBefore t) w).tree := hD
    have hJT : (M.chainStateOf S.C D).J ∈ (x.st (x.stepBefore t) w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
    obtain ⟨r', Eb, u, kc, hkc, hkcj, -, hE, -, -, hEr, -⟩ :=
      P.cert_source_fast_round M F R E U Fx hjE hD'
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hJE : (M.chainStateOf S.C D).J = Eb :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := w) hwj hjE hJT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hJD, hJE]
    -- the update of slot `r' * R` ran at a tick before the reading, at most the vote time of slot `σ + 2`,
    -- so `r' * R ≤ σ` (`hSkew`), as in `F_compat_vf`
    have hμ'σ : r' * S.C.R ≤ σ := by
      by_contra h
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 2 ≤ r' * S.C.R + 1 by omega)
      obtain ⟨hv2, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
      have hcv : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) = ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) + Δ S := by
        rw [hc2, hv2]; push_cast; ring
      have hle2 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      have hkt := (E.tick_active _ _ _ hkc).2.1
      have hkk := (time_mono M) x R hkcj.le
      have htR : ((t : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) := by exact_mod_cast ht
      have hsk := hSkew
      have hB0 := E.behind_nonneg
      linarith
    rcases lt_trichotomy (r' * S.C.R) μ with h | h | h
    · exact PartAHyps.sources_compatible_lt M F hG hE hX h hμ
    · subst h
      exact P.sources_compatible_eq M F R U (hEndA r' hμ) hE hX
    · exact GoldilocksCorrectness.Proofs.Routines.compatible_symm' (PartAHyps.sources_compatible_lt M F hG hX hE h hμ'σ)
  · have hhj : (x.stateBefore t w).justifiedHeight = H₂ := by
      have := key.1
      have h1 : (x.stateBefore t w).justifiedHeight ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    -- `L` is a line source of slot `r * R`, compared with `X` as in `F_compat_vf`
    have hLX : L.compatible X = true := by
      rcases Nat.lt_or_eq_of_le (hX.slot_ge M F) with h | h
      · exact PartAHyps.sources_compatible_lt M F hG (P.source_L M F R U hEndR) hX h hμ
      · subst h
        exact P.sources_compatible_eq M F R U (hEndA r hσ) (P.source_L M F R U hEndR) hX
    by_cases h0 : (M.chainStateOf S.C D).h_j = 0
    · have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 h0
      rw [hJD, hg]
      exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))
    · have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (x.stateBefore t w).finalized.AncestorEq (x.stateBefore t w).justified := by
        have := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E t w
        rw [key.2] at this
        exact this
      -- the finalized block is an ancestor of `L`: at a finalization height at most `H₂` by Lemma 89a; at a
      -- greater one it is a line source taller than the justified block, its descendant, which cannot be
      have hFL : (x.stateBefore t w).finalized.AncestorEq L := by
        obtain ⟨DF, hDF, hFDF⟩ :=
          (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E
            (x.stepBefore t) w
        have hFDF' : (x.stateBefore t w).finalized = (M.chainStateOf S.C DF).F := hFDF
        rw [hFDF']
        by_cases hle : (M.chainStateOf S.C DF).h_F ≤ H₂
        · have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
          have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
              (max (x.time (x.stepBefore t)) (x.time (x.tickStep v (aR M S r)))) :=
            P.hThird.mono (max_le hjE P.hEndStep)
          have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
          exact (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots
            (x.stepBefore t) (x.tickStep v (aR M S r)) w v DF L hT hwj hv' hDF hLv
            (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep)
        · exfalso
          have hlt2 : H₂ < (M.chainStateOf S.C DF).h_F := Nat.lt_of_not_le hle
          obtain ⟨hFC, -, hFanc, -⟩ :=
            ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C DF).2.2
              (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt2))
          have hFT : (M.chainStateOf S.C DF).F ∈ (x.st (x.stepBefore t) w).tree :=
            (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w DF _ hDF hFanc
          obtain ⟨μ₂, Eb₂, u₂, kc₂, hkc₂, hkcj₂, -, hE₂, -, hEh₂, hEr₂⟩ :=
            P.cert_source M F R E U Fx hjE hDF
              ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hFC) hlt2
          have hFE : (M.chainStateOf S.C DF).F = Eb₂ :=
            P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := w) hwj hjE hFT)
              ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
                (le_trans ((time_mono M) x R hkcj₂.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE₂ hkc₂)) hEr₂
          rw [hFDF', hFE, hJD] at hFJ
          have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hFJ
          rw [hEh₂, hJh, ← hhjD, hhj] at h1
          unfold Height at *
          omega
      have hRL := (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_of_tall M F) S.C S.P S.X
        (x.stateBefore t w) hInv L hLT hFL (by rw [P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact compatible_of_ancestorEq_compatible hRL hLX

/-- **The root is compatible with every line source (copy with the end at slot `σ + 1`).**
`root_compat` with its end premise `M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd` replaced by
`M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd` and `t ≤ tAwakeEnd`: from the start of slot `r * R + 1`
to the vote time of slot `σ + 2` and up to `tAwakeEnd`, when the invariant holds at every slot
up to `σ`, an honest validator's fork-choice root is compatible with every line source of a slot at
most `σ`. The body is `root_compat`'s, calling `F_compat_vf`.

The variables:
- `M`: the model; `F`: its facts.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: from the start of slot `r * R + 1` to the vote time of slot `σ + 2` and up to the
phase's end, with the phase running at least to the support cutoff of slot `σ + 1` and the line
invariant at every slot up to `σ`, an honest validator's fork-choice root is compatible with every
line source of a slot at most `σ`. -/
theorem root_compat_vf (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (ht0 : M.slotStart S.C (r * S.C.R + 1) ≤ t)
    (ht : t ≤ M.voteTime S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (M.get_fc_root (x.stateBefore t w)).compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hfR : M.viewFreeze S.C (r * S.C.R) ≤ t := by
    obtain ⟨-, -, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
    omega
  obtain ⟨hLT, -, hM⟩ := P.L_tall M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR ht0 hw
  exact P.root_compat_vf_of_L M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 htE hEndA hfR ht hw hX hμ hLT hM

/-- **A viable block on a line source's chain, given the held sources (copy with the end at slot
`σ + 1`).** `viable_candidate_vf`'s argument, as `viable_candidate_of_held` for `viable_candidate`, with the facts it reads from `source_held` and `L_held` taken as hypotheses, in a node state
`nH`: every line source of a slot at most `σ` that is `X` or a descendant of `X` is in `nH`'s tree
(`hheld`), and so is `L` (`hLH`). From the vote time of slot `σ + 1` to the vote time of
slot `σ + 2`: some block `W`, `X` or a descendant of
`X`, in `nH`'s tree, has a chain-state height at least `w`'s `head_height_floor`. `W` is `L` or `X`
when the greatest chain-state height is at most `H₂ + 1`; otherwise the state is not contested (the
entries one height lower are one block, a line source, `tall_entry` and `cert_source`) and `W` is that
entry or `X`. The line sources compared are of a round's first slot (`L`, `tall_entry_round`,
`cert_source_round`), against each other or `X` by `sources_compatible_lt` on two slots and by
`sources_compatible_eq` with `hEndA` at one. Every line source read here comes from a tick before the reading, so of a slot at most
`σ`: a tick to the support cutoff of slot `σ + 2` is at a real time later than the vote time of slot
`σ + 2` (`hSkew`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.
- `nH`: the node state in which the sources are held; `hheld`, `hLH`: the held sources and `L`.

Read aloud: when the line sources on a line source's chain and `L` are in a node state's tree, some block of that tree, that source or a descendant of it, is
viable for the validator. -/
theorem viable_candidate_vf_of_held (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {Δs : ℕ} (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (ht0 : M.voteTime S.C (σ + 1) ≤ t)
    (ht : t ≤ M.voteTime S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    {nH : M.N}
    (hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ nH.tree)
    (hLH : L ∈ nH.tree) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ nH.tree ∧
      M.head_height_floor (x.stateBefore t w) ≤ (M.chainStateOf S.C W).h := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  obtain ⟨hv2, hc2, -, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨hv1, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  have ht1 : 1 ≤ t := by omega
  have hEndE : t ≤ tAwakeEnd := htE
  -- the step before `t` is at a time less than `t` (`stepBefore_time`'s strict bound)
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have hwj : w ∉ A.corrupted (x.stepBefore t) :=
    Activity.not_mem_corruptedAtTime.1 hw _ ((time_stepBefore_le M) x R E t)
  have hInv : M.nodeInv S.C S.P S.X (x.stateBefore t w) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
      (x.stepBefore t) w) hwj).1
  -- a slot whose update ran at a tick before the reading is at most `σ`: a tick to the support cutoff
  -- of slot `σ + 2` or later is at a real time later than the vote time of slot `σ + 2`
  have hslot : ∀ (μ' : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) →
      k < x.stepBefore t → μ' ≤ σ := by
    intro μ' u k hk hkj
    by_contra h
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ + 2 ≤ μ' + 1 by omega)
    have hkt := (E.tick_active _ _ _ hk).2.1
    have hkk := (time_mono M) x R hkj.le
    have h4 : ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (σ + 2) + Δ S ≤ M.supportCutoff S.C (μ' + 1) by omega)
    have htR : ((t : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) := by exact_mod_cast ht
    have hsk := hSkew
    have hB0 := E.behind_nonneg
    linarith
  -- two line sources, one at a round's first slot `r₁ * R ≤ σ`, compared on their slots
  have hcmp : ∀ {r₁ μ₂ : ℕ} {X₁ X₂ : Block V}, LineSource M S A x r H₂ (r₁ * S.C.R) X₁ →
      LineSource M S A x r H₂ μ₂ X₂ → r₁ * S.C.R ≤ σ → μ₂ ≤ σ → X₁.compatible X₂ = true := by
    intro r₁ μ₂ X₁ X₂ h₁ h₂ hr₁ hμ₂
    rcases lt_trichotomy (r₁ * S.C.R) μ₂ with h | h | h
    · exact PartAHyps.sources_compatible_lt M F hG h₁ h₂ h hμ₂
    · rw [← h] at h₂
      exact P.sources_compatible_eq M F R U (hEndA r₁ hr₁) h₁ h₂
    · exact GoldilocksCorrectness.Proofs.Routines.compatible_symm' (PartAHyps.sources_compatible_lt M F hG h₂ h₁ h hr₁)
  have hXh := hheld hX hμ (ancestorEq_refl X)
  by_cases hMle : hMax M S.C (x.stateBefore t w) ≤ H₂ + 1
  · have hfl := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.stateBefore t w) hInv
    rcases (compatible_iff _ _).1 (hcmp (r₁ := r) (P.source_L M F R U hEndR) hX hσ hμ)
      with h | h
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [P.hL] at this
      unfold Height at *
      omega
    · refine ⟨L, h, hLH, ?_⟩
      rw [P.hL]
      unfold Height at *
      omega
  · have hM2 : H₂ + 2 ≤ hMax M S.C (x.stateBefore t w) := by unfold Height at *; omega
    obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_stateBefore M F) S A x R E t w
    obtain ⟨r', Eb, -, ⟨u', k', hk', hkj', -⟩, hE, hEe, hEh, hEY⟩ :=
      P.tall_entry_round M F R E U Fx ht1 hEndE hw hY (by rw [hYh]; exact hM2)
    have hμ' : r' * S.C.R ≤ σ := hslot (r' * S.C.R) u' k' hk' hkj'
    rw [hYh] at hEh
    -- the state is not contested
    have hnc : M.fg_contest (x.stateBefore t w) = false := by
      cases hcs : M.fg_contest (x.stateBefore t w)
      · rfl
      exfalso
      obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X (x.stateBefore t w) hInv hcs
      obtain ⟨rB, EB, -, ⟨uB, kB, hkB, hkjB, -⟩, hEB, hEBe, hEBh, hEBB⟩ :=
        P.tall_entry_round M F R E U Fx ht1 hEndE hw hBT (by rw [hBh]; exact hM2)
      have hμB : rB * S.C.R ≤ σ := hslot (rB * S.C.R) uB kB hkB hkjB
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_stateBefore M F) S A x R E t w
      have hjE : x.time (x.stepBefore t) ≤ tAwakeEnd := by
        have : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEndE
        linarith
      have hlt : H₂ < (M.chainStateOf S.C D).h_j := by
        rw [← hhjD]
        unfold Height at *
        omega
      obtain ⟨hJC, hJanc, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
        S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hD' : D ∈ (x.st (x.stepBefore t) w).tree := hD
      have hJT : (M.chainStateOf S.C D).J ∈ (x.st (x.stepBefore t) w).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
      obtain ⟨rJ, EJ, uJ, kJ, -, hkJ, hkjJ, -, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source_round M F R E U Fx hjE hD'
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
      have hμJ : rJ * S.C.R ≤ σ := hslot (rJ * S.C.R) uJ kJ hkJ hkjJ
      have hJE : (M.chainStateOf S.C D).J = EJ :=
        P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := w) hwj hjE hJT)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
            (le_trans ((time_mono M) x R hkjJ.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hEJ hkJ)) hEJr
      have hEE : EJ = EB := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hEJe hEBe (by
          rw [hEJh, hEBh, ← hhjD, hBh, hbox]
          unfold Height at *
          omega)
        (hcmp hEJ hEB hμJ hμB)
      apply hJB
      rw [hJD, hJE, hEE]
      exact hEBB
    have hfloor : M.head_height_floor (x.stateBefore t w) = hMax M S.C (x.stateBefore t w) - 1 :=
      (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X
        (x.stateBefore t w) hInv hnc
    rcases (compatible_iff _ _).1 (GoldilocksCorrectness.Proofs.Routines.compatible_symm' (hcmp hE hX hμ' hμ)) with h | h
    · exact ⟨Eb, h, hheld hE hμ' h, by rw [hfloor, hEh]⟩
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [hfloor, ← hEh]
      exact this

/-- **A viable block on a line source's chain (copy with the end at slot `σ + 1`).**
`viable_candidate` with its end premise `M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd` replaced by
`M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd` and `t ≤ tAwakeEnd`: from the vote time of slot `σ + 1` to
the vote time of slot `σ + 2` and up to `tAwakeEnd`, when the invariant holds at every slot up
to `σ` and an honest validator's root is a line source `X` of a slot at most `σ` or an ancestor of
it, some block `W`, `X` or a descendant of `X`, held by the validator at its tick to the view freeze of
slot `σ`, has a chain-state height at least its `head_height_floor`. The body is
`viable_candidate`'s.

The variables:
- `M`: the model; `F`: its facts.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: from the vote time of slot `σ + 1` to the vote time of slot `σ + 2` and up to the
phase's end, with the phase running at least to the support cutoff of slot `σ + 1` and the line
invariant at every slot up to `σ`, when an honest validator's root is a line source `X` or an
ancestor of it, some block `W`, `X` or a descendant of `X`, held at its tick to the view freeze of slot `σ`,
has a chain-state height at least the validator's `head_height_floor`. -/
theorem viable_candidate_vf (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (htE : t ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (ht0 : M.voteTime S.C (σ + 1) ≤ t)
    (ht : t ≤ M.voteTime S.C (σ + 2)) (hw : w ∉ A.corruptedAtTime x t) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (M.get_fc_root (x.stateBefore t w)).AncestorEq X) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree ∧
      M.head_height_floor (x.stateBefore t w) ≤ (M.chainStateOf S.C W).h := by
  obtain ⟨hvσ, hcσ, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hEndE : t ≤ tAwakeEnd := htE
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  -- `w` ticks to the view freeze of every slot `μ₁` from `r * R` to `σ` before `t`
  have htick : ∀ μ₁ : ℕ, r * S.C.R ≤ μ₁ → μ₁ ≤ σ →
      ∃ k : ℕ, x.lbl k = Event.tick w (M.viewFreeze S.C μ₁) ∧ k ≤ x.stepBefore t := by
    intro μ₁ h1 h2
    obtain ⟨hv₁, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
    obtain ⟨hG1, -, -⟩ := P.gstSync M F U h1
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2
    exact P.tick_before M F (by omega) (by omega) hEndE hw
  obtain ⟨kσ, hkσ, hkσt⟩ := htick σ hσ le_rfl
  have hkσR : x.tickStep w (M.viewFreeze S.C σ) = kσ := (tickStep_eq_of_lbl M) x P.E hkσ
  have hTIσ : x.tickInput w (M.viewFreeze S.C σ) = x.st kσ w := by
    show x.st (x.tickStep w (M.viewFreeze S.C σ)) w = x.st kσ w; rw [hkσR]
  -- a tree read at `w`'s tick to the view freeze of a slot `μ₁ ≤ σ` grows to its tick to the one of `σ`
  have hgrow : ∀ μ₁ : ℕ, μ₁ ≤ σ → ∀ k₁ : ℕ, x.lbl k₁ = Event.tick w (M.viewFreeze S.C μ₁) →
      ∀ B : Block V, B ∈ (x.st k₁ w).tree → B ∈ (x.st kσ w).tree := by
    intro μ₁ h2 k₁ hk₁ B hB
    refine (mem_T_mono M F) x R P.E w ?_ hB
    rcases Nat.lt_or_eq_of_le h2 with hlt | heq
    · obtain ⟨-, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show μ₁ + 1 ≤ σ by omega)
      have h1 := (P.E.tick_active _ w _ hk₁).2.2
      have h2' := (P.E.tick_active _ w _ hkσ).2.1
      have h4 : ((M.viewFreeze S.C μ₁ : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
        exact_mod_cast (show M.viewFreeze S.C μ₁ + Δ S ≤ M.viewFreeze S.C σ by omega)
      exact ((lt_of_time_lt M) x R (by linarith)).le
    · subst heq
      exact (P.E.tick_unique _ _ w _ hk₁ hkσ).le
  -- `w`'s finalized block at a tick before `t` is an ancestor of `X`
  have hFX : ∀ k₁ : ℕ, k₁ ≤ x.stepBefore t → (x.st k₁ w).finalized.AncestorEq X := fun k₁ hk₁ =>
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R P.E w hk₁)
      (ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R P.E t w) hRX)
  -- a line source of a slot at most `σ` on `X`'s chain is held at `w`'s tick to the view freeze of `σ`
  have hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    intro μ₁ X₁ hX₁ hμ₁ hXX₁
    obtain ⟨k₁, hk₁, hk₁t⟩ := htick μ₁ (hX₁.slot_ge M F) hμ₁
    have hk₁R : x.tickStep w (M.viewFreeze S.C μ₁) = k₁ := (tickStep_eq_of_lbl M) x P.E hk₁
    have hTI₁ : x.tickInput w (M.viewFreeze S.C μ₁) = x.st k₁ w := by
      show x.st (x.tickStep w (M.viewFreeze S.C μ₁)) w = x.st k₁ w; rw [hk₁R]
    have hE₁ : M.supportCutoff S.C (μ₁ + 1) ≤ tAwakeEnd :=
      le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
    have h := P.source_held M F R E hNet hSkew hRedeliver Sy hΔs U hX₁ hE₁ hk₁ (by
      rw [hTI₁]
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans (hFX k₁ hk₁t) hXX₁)))
    rw [hTI₁] at h
    rw [hTIσ]
    exact hgrow μ₁ hμ₁ k₁ hk₁ X₁ h
  have hLH : L ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    obtain ⟨kL, hkL, -⟩ := htick (r * S.C.R) le_rfl hσ
    have hkLR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = kL := (tickStep_eq_of_lbl M) x P.E hkL
    have h := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hkL
    rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st kL w by
      show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st kL w; rw [hkLR]] at h
    rw [hTIσ]
    exact hgrow (r * S.C.R) hσ kL hkL L h
  exact P.viable_candidate_vf_of_held M F R E hSkew U Fx hG hσ hEnd1 htE hEndA ht0 ht hw hX hμ hheld hLH


/-- **The voter half of the step's frame conditions, with the end at slot `σ + 1`.** The first two
conjuncts of `StepFrameAt` (those `stepFrame_source` proves for the vote of slot `σ + 1`), under
`M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd` in place of `stepFrame_source`'s
`M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd`, and for every validator `w` outside the adversary set at
the vote time of slot `σ + 1` (in place of the support cutoff of slot `σ + 2`): when the invariant
holds at every slot up to `σ`, for every line source `X` of a slot at most `σ`, `w`'s root before
that vote time is compatible with `X`, and, when the root is `X` or an ancestor of `X`, some block
of `w`'s voter tree of slot `σ + 1` that is `X` or a descendant of `X` is a viable head.

Why: the vote time of slot `σ + 1` is at most the support cutoff of slot `σ + 1`, so at most
`tAwakeEnd`; `root_compat_vf` gives the root clause, `viable_candidate_vf` a viable candidate held
at its tick to the view freeze of slot `σ`, and `proposal_viable_head_at_tick` puts it in the voter tree.

The variables:
- `M`: the model; `F`: its facts.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: with the phase running at least to the support cutoff of slot `σ + 1` and the line
invariant at every slot up to `σ`, every validator outside the adversary set at the vote time of
slot `σ + 1` has, before that time, its fork-choice root compatible with every line source `X` of a
slot at most `σ`, and, when the root is `X` or an ancestor of `X`, a viable head in its voter tree
of slot `σ + 1` that is `X` or a descendant of `X`. -/
theorem voterFrame_source_vf (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x (M.voteTime S.C (σ + 1))) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (M.fg_to_ac (x.stateBefore (M.voteTime S.C (σ + 1)) w)).fc_root.compatible X = true ∧
    ((M.fg_to_ac (x.stateBefore (M.voteTime S.C (σ + 1)) w)).fc_root.AncestorEq X →
      ∃ W, VoterTreeAt M (x.stateBefore (M.voteTime S.C (σ + 1)) w)
        (S.C.t_ ((σ + 1) - 1) + 3 * S.C.Δ) (σ + 1) W ∧ W ∈
          (M.fg_to_ac (x.stateBefore (M.voteTime S.C (σ + 1)) w)).viable_heads ∧
          X.AncestorEq W) := by
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨-, hcσ2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv1c : M.voteTime S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢
    omega
  have hvE : M.voteTime S.C (σ + 1) ≤ tAwakeEnd := by omega
  have hv12 : M.voteTime S.C (σ + 1) ≤ M.voteTime S.C (σ + 2) := by
    obtain ⟨hv2, -, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
    rw [show σ + 2 = σ + 1 + 1 by omega] at hv2 ⊢
    omega
  have hfR : M.slotStart S.C (r * S.C.R + 1) ≤ M.voteTime S.C (σ + 1) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show r * S.C.R + 1 ≤ σ + 1 by omega)
    omega
  refine ⟨by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact P.root_compat_vf M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 hvE hEndA hfR hv12 hw hX hμ,
    fun hR => ?_⟩
  have hR' : (M.get_fc_root (x.stateBefore (M.voteTime S.C (σ + 1)) w)).AncestorEq X := by
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hR
  obtain ⟨W, hXW, hWT, hφ⟩ := P.viable_candidate_vf M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 hvE hEndA le_rfl hv12 hw hX hμ hR'
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U hσ
  obtain ⟨kσ, hkσ, hkσv⟩ := P.tick_before M F (c := M.viewFreeze S.C σ) (by omega) (by omega) hvE hw
  -- `w` is honest at its last step before the vote time, and its clock is less than the view freeze of slot `σ`
  -- before its tick to it (it is active from `ΔClockAhead` before that view freeze, `clockValue_lt_of_tick_of_active`)
  have hcG : tGAT + Δ S ≤ M.viewFreeze S.C σ := by omega
  have hv1 : 1 ≤ M.voteTime S.C (σ + 1) := by omega
  have htv := ((stepBefore_time M) x R P.E hv1).1
  have hwv : w ∉ A.corrupted (x.stepBefore (M.voteTime S.C (σ + 1))) :=
    (not_mem_corrupted_of_le_time M) x R P.E hw htv.le
  have hwk : w ∉ A.corrupted kσ := P.E.not_mem_corrupted_of_tick hkσ
  have hlt := (clockValue_lt_of_tick_of_active M F) P.E hkσ (by omega) (fun j hj hjk => by
    have hA0 := P.E.ahead_nonneg
    have hsk := P.hSkew
    have hB0 := P.E.behind_nonneg
    have hjt : x.time j ≤ x.time (x.stepBefore (M.voteTime S.C (σ + 1))) :=
      (time_mono M) x R (le_trans hjk hkσv)
    have hj1 : x.time j ≤ x.time (j + 1) := (time_mono M) x R (Nat.le_succ j)
    have hcGR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by exact_mod_cast hcG
    have hvER : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hvE
    have hjc : w ∉ A.corrupted j := fun h => hwk (P.E.corrupted_mono j kσ hjk h)
    exact Activity.mem_active.2 ⟨P.hAwake j w (by linarith) (by linarith) hjc, hjc⟩)
  obtain ⟨hWt, hWv⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_viable_head_at_tick M F U) S A x R (M.viewFreeze S.C σ) (σ + 1) w W _ _
    P.E kσ hkσ hlt hkσv hwv hWT (by rw [Nat.add_sub_cancel]) ⟨rfl, rfl⟩
    (ancestorEq_trans hR' hXW) hφ
  exact ⟨W, (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (σ + 1) W).1
    hWt, hWv, hXW⟩

/-- **The voter frame at a slot whose support cutoff is in the phase.** For a slot `s` with
`M.supportCutoff S.C s ≤ tAwakeEnd` and a first slot `s₀ ≥ r * R + k`, every validator `w` outside
the adversary set at the vote time of slot `s` has `VoterFrameOnChainAt M S Sched x s₀ s w`.

Why, as `frames_at_phase_slots` for its voter clause: a block on the honest chain before `s` from
`s₀` is on an updater's confirmation of a slot `s'` with `s₀ ≤ s' < s`, so it is a line source of
slot `s'` (`source_conf`, `s' ≥ r * R + k`); the line invariant holds at every slot before `s − 1`
(`lineInv_all`) and at `s − 1`; `voterFrame_source_vf` at `σ := s − 1` gives the two conjuncts.

The variables:
- `M`: the model; `F`: its facts.
- `hEndA`: every tick to the action time of a round whose first slot is less than `s` is in the phase.
- `TR`: the phase up to a later end `tEnd`, and roots up to every tick to a clock value at most the support cutoff of
  slot `s`, each at a real time at most `tEnd`.

Read aloud: for a slot `s` whose support cutoff is in the phase and a slot `s₀ ≥ r * R + k`, every
validator outside the adversary set at the vote time of slot `s` has
`VoterFrameOnChainAt M S Sched x s₀ s`. -/
theorem voterFrame_at_last_opening (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {s₀ s : ℕ} (hs₀ : r * S.C.R + S.C.k ≤ s₀) (hEnd : M.supportCutoff S.C s ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R < s → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    -- the phase to a later end `tEnd`, and roots up to the real time of every tick to a clock value at most the support
    -- cutoff of slot `s`, each at a real time at most `tEnd` ('s rows, T-C-83-2)
    {tEnd : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd (M.supportCutoff S.C s)) {w : V}
    (hw : w ∉ A.corruptedAtTime x (M.voteTime S.C s)) : VoterFrameOnChainAt M S A x s₀ s w := by
  intro B hB k hk
  obtain ⟨s', hs', hs₀', u, hu, C, hC, hBC⟩ := hB
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 1 := ⟨s - 1, by omega⟩
  -- the line invariant at every slot up to `σ = s - 1`: `lineInv_all` at the slots before `σ`, whose updates run at ticks
  -- to the support cutoff of a slot at most `s - 1`, inside the phase; `lineInv_last` at `σ`
  have hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ' := fun σ' h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx σ'
        (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (by omega)) hEnd)
    · -- slot `s - 1`: its updates run at ticks to the support cutoff of slot `s`, read through `TR` (`lineInv_last`)
      subst h
      exact P.lineInv_last M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hEnd le_rfl
  -- `B` is on an updater's confirmation of slot `s'`, so a line source of slot `s'`
  have hsrc := PartAHyps.source_conf_of_updater M F (H₂ := H₂) R E U (show r * S.C.R + S.C.k ≤ s' by omega) hu hC hBC
  exact P.voterFrame_source_vf_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG (by omega) hEnd
    (fun r'' h => hEndA r'' (by omega)) hk hsrc (by omega)

end PartAHyps

/-! ## The hand-over and Lemma 89 with the voter frame at slot `s_m` -/

/-- **The rounds' action ticks before a round's first slot are in the phase.** When the support cutoff of
the first slot `rm * R` of a round is at most `tAwakeEnd`, every tick to the action time `aR M S r''` of a
round whose first slot is less than `rm * R` is at a real time at most `tAwakeEnd`: such a round ends
before round `rm` starts, and `R ≥ 2` puts its action time, the support cutoff of its second slot, at
least `4Δ` before the support cutoff of slot `rm * R`; the tick is at most `ΔClockBehind` after its
clock value (`tick_active`), less than one delay (`hSkew`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: every action tick of a round before round `rm` is in the phase when the support cutoff of
round `rm`'s first slot is. -/
theorem action_ticks_before_round_in_phase (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {rm tAwakeEnd : ℕ}
    (hEnd : M.supportCutoff S.C (rm * S.C.R) ≤ tAwakeEnd) :
    ∀ r'' : ℕ, r'' * S.C.R < rm * S.C.R → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd := by
  intro r'' hr u k hk
  have hR2 := S.C.R_ge_two
  have hrr : r'' + 1 ≤ rm := by
    by_contra h
    exact absurd hr (not_lt.2 (Nat.mul_le_mul_right _ (by omega)))
  have h2 : r'' * S.C.R + 2 ≤ rm * S.C.R := by
    have := Nat.mul_le_mul_right S.C.R hrr
    rw [Nat.add_mul, one_mul] at this
    omega
  have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h2
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S
    (r'' * S.C.R + 1)
  have hc : ((aR M S r'' : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℕ) := by
    exact_mod_cast (show aR M S r'' + Δ S ≤ tAwakeEnd by
      show M.supportCutoff S.C (r'' * S.C.R + 1) + Δ S ≤ tAwakeEnd
      rw [show r'' * S.C.R + 1 + 1 = r'' * S.C.R + 2 from rfl] at h1
      omega)
  have hkt := (E.tick_active _ _ _ hk).2.2
  have hA0 := E.ahead_nonneg
  linarith

/-- **The hand-over after the fast block, with the voter frame at slot `s_m` (copy).** The proof;
the audited statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the
action time is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'`
(template A2), without A2's hypothesis that `v` has been awake since the duty window's start of slot
`r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. The statement
and body of `handover_after_fast_block` with one clause added to the conclusion: every validator
outside the adversary set at the vote time of slot `s_m := rs m * R` has
`VoterFrameOnChainAt M S Sched x s₀ s_m`. Why the clause: `PartAHyps.voterFrame_at_last_opening` at
`s := s_m`, with `s₀ = rs j * R ≥ r * R + k + 2 ≥ r * R + k` and
`M.supportCutoff S.C s_m ≤ tAwakeEnd` (`HonestOpeningSeq.last`).

Roots name blocks until `M.supportCutoff S.C (rs m * S.C.R)`: the bundle `PartAHyps` is built with
its end time `M.supportCutoff S.C (rs m * S.C.R)`; C4 at the honest round opening slots `j` and
`j + 1`, C1, C3, C6, C7 and the voter frame at slot `s_m` read up to that time.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the first honest round opening slot a `k + 2`-slot wait after the fast block is the
healed round, and the two honest round opening slots after it bring the justification above `h(B₀)`
to every honest validator by the vote time of the last honest round opening slot, and every
validator outside the adversary set at the vote time of slot `rs m * R` has its voter frame there on
the honest chain from the healed round's slot. -/
theorem handover_after_fast_block_vf (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m r H₂ : ℕ) (rs : ℕ → ℕ) (v : V)
    (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot before the last, the members of its round are active through the
    -- attestations' sync delay after the later of its duty window's start and `GST`, C4's row at that slot
    --
    (hHoldF : ∀ i, i < m → ∀ w ∈ Hon M S A x (rs i * S.C.R),
      w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (rs m * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot `rs m * R`
    -- (, T-C-83-2)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `rs m * R` is at a real time at most `tAwakeEnd`
    -- (, T-C-83-2)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      x.time k ≤ tAwakeEnd)
    -- the climb's output
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n') (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (j : ℕ) (hj2 : j + 2 ≤ m) (hsj : r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R) :
    RootCollisionAtOpening M S A x rs m ∨
    (∃ (j' s₀ : ℕ) (B₀ : Block V),
      j' < m ∧ s₀ = rs j' * S.C.R ∧
      HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt M S A x s₀,
        (x.tickOutput u (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)) ∧
      (∀ u : V, x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
        u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.tickInput u (M.voteTime S.C (rs m * S.C.R)))) ∧
      (∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C (rs m * S.C.R)) →
        VoterFrameOnChainAt M S A x s₀ (rs m * S.C.R) w)) := by
  classical
  by_cases hNoCol : RootCollisionAtOpening M S A x rs m
  · exact Or.inl hNoCol
  right
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcm := fun {a b : ℕ} (h : a ≤ b) =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hle : ∀ a b : ℕ, a ≤ b → b ≤ m → rs a * S.C.R ≤ rs b * S.C.R := by
    intro a b hab hbm
    rcases Nat.lt_or_ge a b with h | h
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono a b h hbm))
    · rw [show a = b by omega]
  have hss : ∀ i, i < m → rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := by
    intro i hi
    have h' : (rs i + 1) * S.C.R ≤ rs (i + 1) * S.C.R :=
      Nat.mul_le_mul_right _ (hmono i (i + 1) (by omega) hi)
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have hEndO : ∀ i, i ≤ m → M.supportCutoff S.C (rs i * S.C.R) ≤ tAwakeEnd := fun i hi =>
    le_trans (hcm (hle i m hi le_rfl)) hSeq.last
  have hEndP : ∀ i, i ≤ m → M.supportCutoff S.C (rs i * S.C.R) ≤ M.supportCutoff S.C (rs m * S.C.R) :=
    fun i hi => hcm (hle i m hi le_rfl)
  have hRootsP : ∀ {t : ℕ}, t ≤ M.supportCutoff S.C (rs m * S.C.R) → RootsNameBlocksUntil M A x t := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast h) hRoots
  have hjm := hle j m (by omega) le_rfl
  -- the bundle with its end time `M.supportCutoff S.C (rs m * S.C.R)`
  have P := (PartAHyps.of_tick M F U) (tAwakeEnd := M.supportCutoff S.C (rs m * S.C.R)) R E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hGST (hThird.mono (by exact_mod_cast hSeq.last))
    (fun i u hi => hAwake i u (le_trans hi (by exact_mod_cast hSeq.last)))
    (fun s h1 h2 => hActive s h1 (le_trans h2 hSeq.last)) (hCommittees.mono M hSeq.last) hAnchor hOld hv hUpdate hFast hL
    (hcm (show r * S.C.R + 2 ≤ rs m * S.C.R by omega))
  -- the proposals
  have hP : ∀ i, i ≤ m → ∃ B : Block V, ProposalAt M S x (rs i * S.C.R) B :=
    fun i hi => (opening_proposal_exists M F U) S A x R tGAT tAwakeEnd m i rs E hAwake hSkew hSeq hi
  let Bf : ℕ → Block V := fun i =>
    if hi : i ≤ m then Classical.choose (hP i hi) else Block.genesis
  have hBf : ∀ i (hi : i ≤ m), ProposalAt M S x (rs i * S.C.R) (Bf i) := by
    intro i hi
    simp only [Bf, dif_pos hi]
    exact Classical.choose_spec (hP i hi)
  have hnc : ∀ i, i ≤ m → ¬ RootCollisionAtProposal M S A x (rs i * S.C.R) (Bf i) :=
    fun i hi h => hNoCol (((GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M) x rs m).2
      ⟨i, hi, Bf i, hBf i hi, h⟩)
  have hheld : ∀ i (hi : i ≤ m), (Bf i).slot = rs i * S.C.R ∧
      Bf i ∈ (x.tickOutput (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R))).tree :=
    fun i hi => (opening_proposal_held M F U) S A x R tGAT tAwakeEnd m i rs (Bf i) E hSeq hi hNoCol (hBf i hi)
  have hTC : ∀ i, TreeClosed M S.P S.X
      (x.tickOutput (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R))) := fun i =>
    F.nd.nodeInvCore_treeClosed
      ((lem11_node_invariantCore_of_run M F) S x R
        (x.tickStep (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R)) + 1)
        (S.P.proposer (rs i * S.C.R))).1
  -- C4 at the openings `j`, `j + 1`
  have hC4 : ∀ i, j ≤ i → i + 1 ≤ m →
      (Bf i).AncestorEq (Bf (i + 1)) ∧
      (M.chainStateOf S.C (Bf i)).h + 1 ≤ (M.chainStateOf S.C (Bf (i + 1))).h ∧
      ((M.chainStateOf S.C (Bf (i + 1)).parent).h = (M.chainStateOf S.C (Bf i)).h →
        (M.chainStateOf S.C (Bf (i + 1))).J = (M.chainStateOf S.C (Bf i)).T_h) ∧
      ∀ u ∈ Hon M S A x (rs i * S.C.R),
        (x.tickOutput u (M.supportCutoff S.C (rs i * S.C.R + 1))).savedConfirmation
          (rs i * S.C.R) = some (Bf i) := by
    intro i hji him
    rcases (opening_rises_after_fast_block_opening M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ (rs i * S.C.R)
        (rs (i + 1) * S.C.R) v L (Bf i) (Bf (i + 1)) E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F (hHoldF i (by omega))
        (hRootsP (hEndP (i + 1) him))
        (fun k u c hk hc => hRootsTick k u c hk (le_trans hc (hEndP (i + 1) him))) hParent hGST hThird hAwake hActive hCommittees
        hAnchor hOld hv hL n' sent hUpdate
        hFast (le_trans hsj (hle j i hji (by omega))) (Dvd.intro_left _ rfl) (hss i (by omega))
        (hEndO (i + 1) him) (fun k u c hk hc => hEndTick k u c hk (le_trans hc (hEndP (i + 1) him)))
        (hSeq.honest i (by omega)) (hSeq.honest (i + 1) him)
        (hBf i (by omega)) (hBf (i + 1) him) with h | h
    · exact absurd h (hnc i (by omega))
    · exact h
  obtain ⟨h01, h01h, -, -⟩ := hC4 j le_rfl (by omega)
  obtain ⟨h12, h12h, h12J, -⟩ := hC4 (j + 1) (by omega) (by omega)
  rw [show j + 1 + 1 = j + 2 from rfl] at h12 h12h h12J
  have h0 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C (Bf j) (Bf j)).1.1
  -- C5 at the openings `j + 1` and `j + 2`
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_spec M F) S.C (Bf (j + 1))
  have hB0T : (Bf j).AncestorEq (M.chainStateOf S.C (Bf (j + 1))).T_h := by
    rcases ancestorEq_compatible hT1.1 h01 with h | h
    · exfalso
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [hT1.2] at this
      unfold Height at *
      omega
    · exact h
  have hB0ne : Bf j ≠ (M.chainStateOf S.C (Bf (j + 1))).T_h := by
    intro h
    have h' := hT1.2
    rw [← h] at h'
    unfold Height at *
    omega
  have hTmem : (M.chainStateOf S.C (Bf (j + 1))).T_h ∈
      (x.tickOutput (S.P.proposer (rs (j + 1) * S.C.R)) (M.slotStart S.C (rs (j + 1) * S.C.R))).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E
      (x.tickStep (S.P.proposer (rs (j + 1) * S.C.R)) (M.slotStart S.C (rs (j + 1) * S.C.R)) + 1)
      (S.P.proposer (rs (j + 1) * S.C.R)) _ _ (hheld (j + 1) (by omega)).2 hT1.1
  have hslotT := (slot_lt_of_ancestorEq_of_treeClosed_node M F) (hTC (j + 1)) hTmem hB0T hB0ne
  rw [(hheld j (by omega)).1] at hslotT
  have hsp := hSeq.spacing j hj2
  have hJ2 : (M.chainStateOf S.C (Bf (j + 1))).h ≤ (M.chainStateOf S.C (Bf (j + 2))).h_j := by
    refine (GoldilocksCorrectness.Record.Proofs.Routines.round_justified_of_spacing3 M F) S.C (Bf (j + 1)) (Bf (j + 2))
      h12 h12h ?_ ?_ ?_
    · rw [(hheld (j + 2) hj2).1]
      unfold Slot at *
      omega
    · intro Y hY hne
      exact (slot_lt_of_ancestorEq_of_treeClosed_node M F) (hTC (j + 2)) (hheld (j + 2) hj2).2 hY hne
    · intro hpar
      have hJ := h12J hpar
      refine ⟨?_, hJ⟩
      have hspec := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C (Bf (j + 2))
      by_cases hz : (M.chainStateOf S.C (Bf (j + 2))).h_j = 0
      · exfalso
        have hg := hspec.2.1 hz
        rw [hJ] at hg
        have h' := hT1.2
        rw [hg] at h'
        have hg1 : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
          (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
        rw [hg1] at h'
        unfold Height at *
        omega
      · have h' := hspec.2.2 (Nat.one_le_iff_ne_zero.mpr hz)
        rw [hJ, hT1.2] at h'
        exact h'.symm
  -- the base facts at the healed round `s₀ := s_j`
  have hs₀ := hsj
  have hsj1 := hss j (by omega)
  have hEndj1 : M.supportCutoff S.C (rs j * S.C.R + 2) ≤ M.supportCutoff S.C (rs (j + 1) * S.C.R) := hcm (by omega)
  have hEnd₀ : M.supportCutoff S.C (rs j * S.C.R + 2) ≤ tAwakeEnd := le_trans hEndj1 (hEndO (j + 1) (by omega))
  have hEndP₀ : M.supportCutoff S.C (rs j * S.C.R + 2) ≤ M.supportCutoff S.C (rs m * S.C.R) :=
    le_trans hEndj1 (hEndP (j + 1) (by omega))
  have hp₀ := hSeq.honest j (by omega)
  have hBase := (round_base_after_fast_block_opening M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    v L (Bf j) E hNet hSkew hRedeliver Sy hΔs (hRootsP hEndP₀) hParent
    hGST hThird hAwake hActive hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs₀
    (Dvd.intro_left _ rfl) hEnd₀ hp₀ (hBf j (by omega)) (hnc j (by omega))
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega) (hEndP j (by omega)) hp₀
  have hGs1 : LineInv M S A x r H₂ (rs j * S.C.R - 1) :=
    P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx _ (by
      rw [show rs j * S.C.R - 1 + 2 = rs j * S.C.R + 1 by omega]
      exact le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEndP₀)
  obtain ⟨hHCE, hSaved, hslot₀, -⟩ := (healed_round_base_of_prev_votes M F U Fx) S A x R GST tGAT tAwakeEnd
    (rs j * S.C.R) (Bf j) E hNet hSkew hRedeliver Sy hΔs
    (hRootsP (le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEndP₀)) hParent
    hGST hThird hAwake hActive hCommittees (by omega)
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)))
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)))
    hEnd₀ hp₀ (hBf j (by omega)) hBase (hnc j (by omega))
    (fun u hu vote hvote => (hGs1 μA _ hAsrc (by omega)).1.1 u (Finset.mem_inter.1 hu).2 vote hvote)
  -- the old attestations
  have hOA := P.old_attestations_at_opening M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega) (Dvd.intro_left _ rfl)
    (le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEndP₀) hp₀ (hBf j (by omega))
  -- `B₀`'s height is greater than `H₂`
  have hHB₀ : H₂ < (M.chainStateOf S.C (Bf j)).h := by
    obtain ⟨-, hPB⟩ := (proposal_slot_parent M F U) S A x R E (show 1 ≤ rs j * S.C.R by omega)
      (hBf j (by omega))
    have hLP := P.parent_extends_sources M F R E hNet hSkew hRedeliver Sy hΔs U Fx
      (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
      (hEndP j (by omega)) hp₀ (hBf j (by omega)) (r * S.C.R) L
      (P.source_L M F R U (le_trans (hcm (show r * S.C.R + 1 ≤ rs j * S.C.R by omega)) (hEndP j (by omega))))
      (by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans hLP hPB)
    rw [hL] at h1
    unfold Height at *
    omega
  -- the frames
  have hFrames := (frames_at_phase_slots M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    (rs m * S.C.R) v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs₀ hSeq.last hEndTick
  -- the caches at every validator's tick to the vote time of slot `rs m * R`
  have hm2 := hle (j + 2) m hj2 le_rfl
  have h4 : 4 * Δ S * healFrontSlots S = 4 * Δ S * S.C.k * 3 + 4 * Δ S := by
    unfold healFrontSlots; rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 S.C.k, ← Nat.mul_assoc]
  have hss0 : M.slotStart S.C (rs 0 * S.C.R) ≤ M.slotStart S.C (rs (j + 2) * S.C.R) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (hle 0 (j + 2) (by omega) hj2)
  have hFirst := hSeq.first
  have hGAT₃ : tGAT + Δ S ≤ M.slotStart S.C (rs (j + 2) * S.C.R) := by omega
  --: the recovery delay after `tGAT` has elapsed by the vote time of slot `rs (j + 2) * R`
  have hΔsN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by
      push_cast
      linarith
    exact_mod_cast h
  have htGAT : tGAT + max (Δ S) Δs ≤ M.voteTime S.C (rs (j + 2) * S.C.R) := by
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (rs (j + 2) * S.C.R)
    rcases max_choice (Δ S) Δs with hm | hm <;> rw [hm] at hΔsN ⊢ <;> omega
  have hcut₀ : ((M.supportCutoff S.C (rs j * S.C.R + 1) : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by
    exact_mod_cast le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEnd₀
  have hQ := (fewerThanQuorum_of_fewerThanThird M F) A x tAwakeEnd hThird
  have hvtc : M.voteTime S.C (rs m * S.C.R) ≤ M.supportCutoff S.C (rs m * S.C.R) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (rs m * S.C.R)
    omega
  have hkp : x.lbl (x.tickStep (S.P.proposer (rs (j + 2) * S.C.R)) (M.slotStart S.C (rs (j + 2) * S.C.R))) =
      Event.tick (S.P.proposer (rs (j + 2) * S.C.R)) (M.slotStart S.C (rs (j + 2) * S.C.R)) := by
    obtain ⟨i, hl, -⟩ := hBf (j + 2) hj2
    rw [(tickStep_eq_of_lbl M) x E hl]
    exact hl
  have hCaches : ∀ u : V,
      x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
      u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
      CachesOnChain M S A x (rs j * S.C.R) (M.chainStateOf S.C (Bf j)).h
        (x.tickInput u (M.voteTime S.C (rs m * S.C.R))) := by
    intro u hu hhon
    have hti : x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) ≤ (tAwakeEnd : ℝ) :=
      hEndTick _ u _ hu hvtc
    obtain ⟨hAct₃, hTick₃⟩ := (voter_active_from_opening M F U) S A x R E hSkew hAwake hm2 hGAT₃ hSeq.last hkp hu hhon
    refine (caches_at_handover_of_held M F U Fx) S A x R GST tGAT tAwakeEnd (rs j * S.C.R)
      (M.chainStateOf S.C (Bf j)).h (rs (j + 2) * S.C.R) (rs m * S.C.R)
      (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) (Bf (j + 2)) u
      E hNet hSkew hRedeliver Sy hΔs (hRootsTick _ u _ hu hvtc) hParent hGST hThird hAwake hm2 htGAT hSeq.last
      (hSeq.honest (j + 2) hj2) (hheld (j + 2) hj2).2 hAct₃ hTick₃
      (fun w hw _ => P.F_at_vote_tick_ancestor_proposal M F R E hNet hSkew hRedeliver Sy hΔs U Fx
        (show r * S.C.R + S.C.k + 2 ≤ rs (j + 2) * S.C.R by
          have := hle j (j + 2) (by omega) hj2
          omega)
        (hEndP (j + 2) hj2) (hSeq.honest (j + 2) hj2) (hBf (j + 2) hj2) hw)
      (by unfold Height at *; omega) ?_ hu hhon
    intro w D T h hD hJc hh
    have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
        (max (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) (M.supportCutoff S.C (rs j * S.C.R + 1))) :=
      fun X hX => hQ X (fun v hv => let ⟨t'', h1, h2⟩ := hX v hv; ⟨t'', le_trans h1 (max_le hti hcut₀), h2⟩)
    exact (cert_entry_at_slot M F U Fx) S A x R (rs j * S.C.R) (M.chainStateOf S.C (Bf j)).h
      (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) w D T h E hAdvQ hOA hD
      ((progressCertOn_of_justificationCertOn M F) hJc) hh
  -- the voter frame at slot `rs m * R`: the rows past the bundle's end, read through `TickRows`
  have TR : TickRows M S A x tGAT (M.supportCutoff S.C (rs m * S.C.R)) tAwakeEnd (M.supportCutoff S.C (rs m * S.C.R)) :=
    ⟨hSeq.last, hThird, hAwake, hCommittees, hRootsTick, hEndTick⟩
  exact ⟨j, rs j * S.C.R, Bf j, by omega, rfl, hHCE, hSaved, hslot₀, hOA,
    fun s h1 h2 => hFrames s h1 h2, hCaches,
    fun w hw => P.voterFrame_at_last_opening M F R E hNet hSkew hRedeliver Sy hΔs U Fx (by omega) le_rfl
      ((action_ticks_before_round_in_phase M F U) E hSkew le_rfl) TR hw⟩

/-- **Lemma 89 on the fast-confirmation route.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. Why: the climb (`climb_to_fast_block`) gives a root
collision at an honest round opening slot, or the fast block `L` of an honest update at the action
time of a round `r` with the first honest round opening slot `j` at least `k + 2` slots after
`r * R` and `j + 2 ≤ m`; the hand-over's copy with the voter frame
(`handover_after_fast_block_vf`) gives Lemma 89's conclusion from it. The climb's twin names a node
state `n'` that `v`'s confirmation update at the action time of round `r` can leave, and the
hand-over's copy takes an outcome `(n'', sent)` of `v`'s tick there: `v` is awake and honest from
the duty window's start of slot `r * R + 1` to that time, so its tick has an outcome from its state
before the time (`cutoff_tick_outcome_of_active`), whose update has the fast blocks of `n'`
(`fast_of_confirmationUpdated`).

Roots name blocks until `M.supportCutoff S.C (rs m * S.C.R)`: the hand-over's copy
(`handover_after_fast_block_vf`); the climb reads up to `aR M S (rs (m - 1))`, before it.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the conclusion of Lemma 89, and the voter frame at the last opening's slot. -/
theorem lem89_phase (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (rs m * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `rs m * R` (, stops_recheck_85)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `rs m * R` is at a real time at most
    -- `tAwakeEnd` (, stops_recheck_85)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      x.time k ≤ tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening M S A x rs m ∨
    (∃ (j s₀ : ℕ) (B₀ : Block V),
      j < m ∧ s₀ = rs j * S.C.R ∧
      HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt M S A x s₀,
        (x.tickOutput u (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)) ∧
      (∀ u : V, x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
        u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.tickInput u (M.voteTime S.C (rs m * S.C.R)))) ∧
      (∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C (rs m * S.C.R)) →
        VoterFrameOnChainAt M S A x s₀ (rs m * S.C.R) w)) := by
  -- the climb reads up to the action time of the round of the honest round opening slot `m − 1`
  have hcount : ∀ (waits : Fin 2 → ℕ) (w5 : Fin 5 → ℕ),
      9 ≤ ((Finset.range (m + 1)).filter
        (OutsideSpans S rs waits S.C.δt w5 (S.C.k + 2))).card := hm
  have hm1 : 1 ≤ m := by
    have h := hcount (fun _ => 0) (fun _ => 0)
    have := Finset.card_filter_le (Finset.range (m + 1))
      (OutsideSpans S rs (fun _ : Fin 2 => 0) S.C.δt (fun _ : Fin 5 => 0) (S.C.k + 2))
    rw [Finset.card_range] at this
    omega
  have hRm : aR M S (rs (m - 1)) ≤ M.supportCutoff S.C (rs m * S.C.R) := by
    have h' : (rs (m - 1) + 1) * S.C.R ≤ rs m * S.C.R :=
      Nat.mul_le_mul_right _ (GoldilocksCorrectness.Proofs.Executions.r_lt_of_lt_of_mono rs m hSeq.mono (m - 1) m
        (by omega) le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h'
    have hR := S.C.R_ge_two
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  rcases (climb_to_fast_block M F U Fx) S A x R GST tGAT tAwakeEnd m rs E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F
      hΔs_F hHoldF ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M)
        (by exact_mod_cast hRm) hRoots) hParent hGST hThird hAwake hActive hCommittees hSeq hm with
    hcol | ⟨r, H₂, v, L, n', hAnchor, hEnd, hOld, hv, hCU, hFast, hL, -, hk₀, -, j, hj2, hsj, -⟩
  · exact Or.inl hcol
  -- `v` is an updater of slot `r * R` (`hActive`), so its tick to the action time of round `r` has an outcome
  -- `(n'', sent)` from its tick input, whose update has the fast blocks of `n'` (one update from one state)
  have hdwA : tGAT + Δ S ≤ M.dutyWindowStart S.C (r * S.C.R) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT
      (r * S.C.R) hAnchor
  have hupd : v ∈ updaterAt M S A x (r * S.C.R) := (hActive (r * S.C.R) (by omega) hEnd v hv).2
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hupd
    ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
      F.sched U) S (r * S.C.R + 1))
  obtain ⟨n'', sent, hrun, -⟩ := (cutoff_tick_outcome_of_tick M F U) x R E (r * S.C.R) v τ hk₀ hτ hτle
  have hCU'' := (confirmationUpdated_of_phase_tick M F U) x R r v n'' sent E hupd hrun
  have hFast'' := (fast_of_confirmationUpdated M F) (Nat.le_add_left 1 _) hCU hCU'' hFast
  exact (handover_after_fast_block_vf M F U Fx) S A x R GST tGAT tAwakeEnd m r H₂ rs v L E hNet hSkew hRedeliver E_F hNet_F hSkew_F
    Sy hΔs Sy_F hΔs_F
    (fun i hi w hw => hHoldF i hi w ((honest_of_mem_hon M F) S A x hw)) hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hSeq hEndTick
    hAnchor hOld hv n'' sent hrun hFast'' hL j hj2 hsj

end GoldilocksCorrectness.Record.Proofs.Executions

