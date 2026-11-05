module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma96, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma96.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 96, three consecutive honest round opening
slots justify the middle proposal's height. The page's routine-level theorems are the facts' fields
or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_mono voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_node parent_ancestorEq_self)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
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
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_node_iff ancestorEq_of_parent? state_transition_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Lemma 96 -/

/-- **Lemma 96, three consecutive honest round opening slots justify the middle proposal's
height.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the middle round; `Bprev`, `B`, `B'`: the proposals of the rounds `r − 1`, `r`, `r + 1`.

Read aloud: with the timeout longer than two rounds less one slot, the next honest round opening
slot justifies the height the previous one's proposal reached. -/
theorem lem96_consecutive_openings_justified (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r : ℕ) (Bprev B B' : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C ((r + 1) * S.C.R)))
    (hRootsK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the support cutoff of slot `(r + 1) * S.C.R + 1`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C ((r + 1) * S.C.R + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C ((r + 1) * S.C.R))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ ((r + 1) * S.C.R - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hCachesK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    (hδt : 2 * S.C.R ≤ S.C.δt + 1)
    (hr : 1 ≤ r) (hAfter : x.time i₂ < M.slotStart S.C ((r - 1) * S.C.R) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer ((r - 1) * S.C.R)) (M.slotStart S.C ((r - 1) * S.C.R)) → x.time i₂ < x.time k)
    (hOpenerPrev : HonestOpenerAt M S A x ((r - 1) * S.C.R))
    (hOpener : HonestOpenerAt M S A x (r * S.C.R))
    (hOpener' : HonestOpenerAt M S A x ((r + 1) * S.C.R))
    (hQuorumPrev : QuorumActiveAt M S A x ((r - 1) * S.C.R))
    -- every attestation a member of round `r − 1`'s honest active validators put on the wire at a tick up to that
    -- round's action time, with the member's justified height at round `r`'s proposal-window start at most its
    -- height, is delivered to round `r`'s opener before its tick to its slot's start, or held by it before its
    -- proposal window starts
    (hDelPrev : ∀ u ∈ honestActiveAt M S A x ((r - 1) * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C ((r - 1) * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C (r * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer (r * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C (r * S.C.R)) (S.P.proposer (r * S.C.R))).attestationsHeld)
    (hQuorum : QuorumActiveAt M S A x (r * S.C.R))
    -- every attestation a member of round `r`'s honest active validators put on the wire at a tick up to the round's
    -- action time, with the member's justified height at the next opener's proposal-window start at most its
    -- height, is delivered to the next opener before its tick to its slot's start, or held by it before its
    -- proposal window starts
    (hDel : ∀ u ∈ honestActiveAt M S A x (r * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C (r * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) (S.P.proposer ((r + 1) * S.C.R))).attestationsHeld)
    (hProposePrev : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r - 1) * S.C.R)) (M.slotStart S.C ((r - 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r - 1) * S.C.R), NamedObject.block Bprev⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoColPrev : ¬ RootCollisionAtProposal M S A x ((r - 1) * S.C.R) Bprev)
    (hNoCol : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal M S A x ((r + 1) * S.C.R) B')
    (hHoldPrev : ∀ σ : ℕ, (r - 1) * S.C.R - 1 ≤ σ → σ ≤ (r - 1) * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ r * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold' : ∀ u ∈ honestActiveAt M S A x ((r + 1) * S.C.R - 1), u ∈ S.P.committee ((r + 1) * S.C.R - 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldPPrev : S.P.proposer ((r - 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r - 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r - 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (r * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP' : S.P.proposer ((r + 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    (M.chainStateOf S.C B).h ≤ (M.chainStateOf S.C B').h_j := by
  obtain ⟨r₀, rfl⟩ : ∃ r₀, r = r₀ + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hAfter hOpenerPrev hQuorumPrev hDelPrev hProposePrev hNoColPrev hHoldPrev hHoldPPrev
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hmul : ∀ a : ℕ, (a + 1) * S.C.R = a * S.C.R + S.C.R := fun a => by
    rw [Nat.add_mul, Nat.one_mul]
  have hm1 := hmul r₀
  have hm2 := hmul (r₀ + 1)
  have hle01 : M.slotStart S.C (r₀ * S.C.R) ≤ M.slotStart S.C ((r₀ + 1) * S.C.R) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)
  have hv12 : M.voteTime S.C ((r₀ + 1) * S.C.R) ≤ M.voteTime S.C ((r₀ + 1 + 1) * S.C.R) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show (r₀ + 1) * S.C.R ≤ (r₀ + 1 + 1) * S.C.R by omega)
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]
    omega
  -- the proposer of `(r₀ + 1) R` ticks to its slot's start at a real time at least `ΔClockAhead` before it, which is
  -- after the start of `r₀ R` and so after the hand-over step (`R ≥ 2`, `ΔClockAhead < Δ S`)
  have hAfterTick : ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer ((r₀ + 1) * S.C.R)) (M.slotStart S.C ((r₀ + 1) * S.C.R)) →
      x.time i₂ < x.time k := by
    intro k hk
    have hA0 := E.ahead_nonneg
    have hB0 := E.behind_nonneg
    have hk1 := (E.tick_active k _ _ hk).2.1
    have hsR : ∀ s' : ℕ, ((M.slotStart S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) := fun s' => by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
    have hRR : (2 : ℝ) ≤ (S.C.R : ℝ) := by exact_mod_cast hR
    have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
    rw [hsR] at hk1
    have h0 := hAfter.1
    rw [hsR] at h0
    push_cast at hk1 h0
    nlinarith
  -- the height step at the rounds `r₀`, `r₀ + 1`
  obtain ⟨hBpslot, hBslot, hPP, hPB, -, hBT, hstep1, -⟩ := (consecutive_openings_step_kit M F U Fx) S A x R
    GST s₀ anchor i₂ H r₀ Bprev B E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M) hv12 hRoots)
    (fun k u c hl hc => hRootsK k u c hl (le_trans hc hv12)) hParent
     (hAdvQ.mono
        -- the support cutoff of slot `(r₀ + 1) R + 1` is at most that of slot `(r₀ + 2) R + 1`
        (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) (hSleepK.mono M ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hAnchor hGST ht₀
    (fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega))
    (fun s' h₁ h₂ => hInv s' h₁ (by omega)) (fun s' h₁ h₂ => hLocks s' h₁ (by omega)) hLocks₀ hOld
    (fun j w h₁ h₂ h₃ => hCaches j w h₁ (le_trans h₂ (by exact_mod_cast hv12)) h₃)
    (fun k u c hl hc => hCachesK k u c hl (le_trans hc hv12)) hParam hAfter hOpenerPrev hOpener
    hQuorumPrev hDelPrev hProposePrev hPropose hNoColPrev hNoCol hHoldPrev
    (hHold _ le_rfl (Nat.sub_le _ _)) hHoldPPrev hHoldP
  -- the height step at the rounds `r₀ + 1`, `r₀ + 2`
  obtain ⟨-, hB'slot, hBP', hPB', hB'ne, hB'T, hstep2, hJ⟩ := (consecutive_openings_step_kit M F U Fx) S A
    x R GST s₀ anchor i₂ H (r₀ + 1) B B' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hRoots hRootsK hParent
    hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hCachesK hParam
    ⟨lt_of_lt_of_le hAfter.1 (by exact_mod_cast hle01), hAfterTick⟩ hOpener hOpener' hQuorum hDel hPropose hPropose' hNoCol hNoCol'
    hHold hHold' hHoldP hHoldP'
  -- an honest opener ticks to its slot's vote time, outside the adversary set
  have hHonT : ∀ s' : ℕ, 2 ≤ s' → HonestOpenerAt M S A x s' →
      S.P.proposer s' ∉ A.corrupted (x.tickStep (S.P.proposer s') (M.voteTime S.C s')) := by
    intro s' hs2 hO
    obtain ⟨q, rfl⟩ : ∃ q, s' = q + 2 := ⟨s' - 2, by omega⟩
    have hp := (opener_mem_honestActiveAt M F U) S A R E q hO
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 ((reader_vote_of_honestActiveAt M F U) R E hSkew hp)
    rw [E.tickStep_eq_of_lbl hk']
    exact E.not_mem_corrupted_of_tick hk'
  -- the trees of the proposers of `(r₀ + 1) R` and `(r₀ + 2) R`
  have hTC := F.nd.nodeInv_treeClosed (lem11_node_invariant M F S A x R E
    (x.tickStep (S.P.proposer ((r₀ + 1) * S.C.R)) (M.voteTime S.C ((r₀ + 1) * S.C.R)))
    (S.P.proposer ((r₀ + 1) * S.C.R)) (hHonT _ (by nlinarith) hOpener)).1
  have hTC' := F.nd.nodeInv_treeClosed (lem11_node_invariant M F S A x R E
    (x.tickStep (S.P.proposer ((r₀ + 1 + 1) * S.C.R)) (M.voteTime S.C ((r₀ + 1 + 1) * S.C.R)))
    (S.P.proposer ((r₀ + 1 + 1) * S.C.R)) (hHonT _ (by nlinarith) hOpener')).1
  -- `T_h(B)` is a strict descendant of `Bprev`, so its slot is after `r₀ R`
  obtain ⟨hThB, hThh⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_spec M F) S.C B
  have hPB0 : Bprev.AncestorEq B := ancestorEq_trans hPP hPB
  have hThSlot : r₀ * S.C.R < (M.chainStateOf S.C B).T_h.slot := by
    rcases ancestorEq_compatible hThB hPB0 with h | h
    · exfalso
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C _ _).2.2.2.1 h
      rw [hThh] at this
      omega_nat
    · have hne : Bprev ≠ (M.chainStateOf S.C B).T_h := by
        intro heq
        rw [← heq] at hThh
        omega_nat
      have hThT : (M.chainStateOf S.C B).T_h ∈
          (x.st (x.tickStep (S.P.proposer ((r₀ + 1) * S.C.R)) (M.voteTime S.C ((r₀ + 1) * S.C.R))) (S.P.proposer ((r₀ + 1) * S.C.R))).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ _ B _ hBT hThB
      have := (slot_lt_of_ancestorEq_of_treeClosed_node M F) hTC hThT h hne
      rw [hBpslot] at this
      exact this
  -- the block that takes `B'`'s chain past `h(B)`
  have hB1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1.1
  obtain ⟨Y, hYB', hYne, hYp, hYh, hbranch⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.first_advance_justified_or_timeout M F) S.C B'
    (M.chainStateOf S.C B).h hB1 (by omega_nat)
  have hYpY : Y.parent.AncestorEq Y := parent_ancestorEq_self Y
  have hBB' : B.AncestorEq B' := ancestorEq_trans hBP' hPB'
  have hTY : (M.chainStateOf S.C Y.parent).T_h = (M.chainStateOf S.C B).T_h := by
    rcases ancestorEq_compatible (ancestorEq_trans hYpY hYB') hBB' with h | h
    · exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Y.parent B).2.2.2.2 h hYp
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B Y.parent).2.2.2.2 h hYp.symm).symm
  rcases hbranch with hjY | hslotY
  · -- `Y` justified `h(B)`, and the justification height only rises along `B'`'s chain
    rw [← hjY]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_h_j_h_F_mono M F) S.C Y B' hYB').1
  · -- the timeout test leaves only `Y = B'`, with its parent at `h(B)`
    rw [hTY] at hslotY
    have hYeq : Y = B' := by
      by_contra hne
      have := (slot_lt_of_ancestorEq_of_treeClosed_node M F) hTC' hB'T hYB' hne
      rw [hB'slot] at this
      have h2 : (r₀ + 1 + 1) * S.C.R = r₀ * S.C.R + 2 * S.C.R := by
        rw [hm2, hm1]
        omega
      omega_nat
    subst hYeq
    have hJB' := hJ hYp
    -- `B'`'s state transition justified its parent's `T_h`
    obtain ⟨P, s'', r'', votes, support, ats, v, hB'def⟩ : ∃ P s'' r'' votes support ats v,
        Y = Block.node P s'' r'' votes support ats v := by
      cases hY : Y with
      | genesis => exact absurd hY hYne
      | node P s'' r'' votes support ats v => exact ⟨P, s'', r'', votes, support, ats, v, rfl⟩
    subst hB'def
    change (M.chainStateOf S.C P).h = (M.chainStateOf S.C B).h at hYp
    change (M.chainStateOf S.C P).T_h = (M.chainStateOf S.C B).T_h at hTY
    have hst := (GoldilocksCorrectness.Record.Proofs.Routines.state_transition_justification M F) S.C
      (.node P s'' r'' votes support ats v) (by intro h; cases h)
    simp only [Block.parent] at hst
    rcases hst with ⟨hj, hJP⟩ | ⟨hj, -⟩
    · exfalso
      rw [hJP, ← hTY] at hJB'
      obtain ⟨-, hJ0, hJ1⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C P
      have hPb := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C P P).1.2.1
      rcases Nat.eq_zero_or_pos (M.chainStateOf S.C P).h_j with h0 | hpos
      · have hg := hJ0 h0
        rw [hJB'] at hg
        rw [← hTY, hg] at hThSlot
        exact Nat.not_lt_zero _ hThSlot
      · have := hJ1 hpos
        rw [hJB', ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_spec M F) S.C P).2] at this
        omega_nat
    · rw [hj, hYp]

end GoldilocksCorrectness.Record.Proofs.Executions

