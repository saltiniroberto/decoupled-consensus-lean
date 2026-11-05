module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma91UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma91UpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 91 (c), with the delivery premises
up to a bound. The page's routine-level theorems are the facts' fields or have their twins in phase
A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slot_after_healed_round slot_le_of_supportCutoff_lt
  voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (hMax)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_antisymm ancestorEq_of_parent?)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- **Lemma 91 (c), the voter is at least as far as the proposer, with the delivery premises up to the
vote time.** The instance of `lem91c_at_until` at `cp := M.slotStart S.C s`, `cw := M.voteTime S.C s`,
`c₂ := M.slotStart S.C s` (the voter's own tick to the slot's start, `kS`), `b := M.voteTime S.C s`: the
slot comes after the healed slot's support cutoff, so `1 ≤ M.slotStart S.C s` (`slot_after_healed_round`);
a tick before `kw` is to a clock value less than the vote time plus one delay, the support cutoff of slot
`s`, so it updates a slot less than `s − 1`. Both validators are read at their ticks.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's
  end; `H`: the threshold; `kp`: `p`'s tick to the slot's start; `kw`, `kS`: `w`'s ticks to the slot's
  vote time and start; `p`: the proposer; `w`: the voter.

Read aloud: after healing, a voter that ticks to the slot's start and to its vote time knows, at its
vote tick, a height at least as great as the proposer knows at its tick to the slot's start, with the
delivery premises up to the vote time. -/
theorem lem91c_proposer_h_max_le_voter_h_max_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s i₁ H kp kw kS : ℕ) (p w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.voteTime S.C s))
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    -- the proposer ticks to the slot's start; the voter ticks to the slot's start and to its vote time
    (hkp : x.lbl kp = Event.tick p (M.slotStart S.C s)) (hkw : x.lbl kw = Event.tick w (M.voteTime S.C s))
    (hkS : x.lbl kS = Event.tick w (M.slotStart S.C s))
    (hs : x.time i₁ < M.slotStart S.C s ∧ ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time kw →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw : w ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) (x.time kw)) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcs : M.supportCutoff S.C (s₀ + 1) < M.slotStart S.C s := by exact_mod_cast lt_of_le_of_lt ht₀ hs.1
  have hc₀ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S
    (show s₀ < s₀ + 1 by omega)
  obtain ⟨-, hcut, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  have hkwt := (E.tick_active kw w _ hkw).2.2
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  rw [hvt] at hkw hp hw E Sy hkwt ⊢
  refine (lem91c_at_until M F U Fx) S A x R GST s₀ (M.slotStart S.C s) i₁ H (M.slotStart S.C s + Δ S) (s - 1) kp
    (M.slotStart S.C s + Δ S) kw (M.slotStart S.C s) kS p w E hNet hSkew hRedeliver Sy hRoots
    hParent hAdvQ hkp hkw le_rfl hkS le_rfl le_rfl (by omega) hs.2 hChain ?_ hOld hCaches hp hw le_rfl
  rintro s_a ⟨k, u, hk, hkl⟩
  have h1 := (E.tick_active k u _ hkl).2.1
  have h2 : x.time k ≤ x.time kw := (time_mono M) x R hk.le
  have h3 : ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) < M.supportCutoff S.C s := by
    rw [hcut]; push_cast at hkwt ⊢; linarith
  have h4 : M.supportCutoff S.C (s_a + 1) < M.supportCutoff S.C s := by exact_mod_cast h3
  by_contra hcon
  have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s ≤ s_a + 1 by omega)
  omega

end GoldilocksCorrectness.Record.Proofs.Executions

