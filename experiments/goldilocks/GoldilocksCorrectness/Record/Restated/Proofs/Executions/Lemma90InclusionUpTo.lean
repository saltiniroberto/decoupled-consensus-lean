module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalPropagationStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.OrderedFloorStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FastConfirmationStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FrameShapeStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma91UpTo
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.OrderedFloorStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
import Mathlib.Tactic.Rify
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma90InclusionUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma90InclusionUpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the honest proposal extending
the chain and saved by the updaters, and the facts of the update that includes it, with the delivery
premises up to the bound the theorems read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart
  proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  proposalWindowStart_eq slotStart_eq slotStart_mono slot_after_healed_round
  slot_le_of_supportCutoff_lt supportCutoff_eq voteTime_eq)

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
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? awake_since_record_awake deepest?_mem ac_confirmed_cases)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- **Steps 2 and 3 of the inclusion: the proposal's parent extends the chain, and every honest
vote names the proposal.** Under the hypotheses of the inclusion at slot `q + 2`, with the lock
invariant at slot `q` (`hLk`) and `B` the proposal of slot `q + 2` with a root new to its proposer:
every block of the chain before `q + 1` is `B`'s parent or an ancestor of it; `B` is a non-genesis
block of slot `q + 2`; every vote an honest active validator `w` of slot `q + 2` sends at the vote
time of slot `q + 2` names `B`; and every such `w` holds `B` before that vote time.

Why: the proposer's root and anchor are on the chain (Lemma 91 (f), `proposer_anchor_on_chain`);
every honest committee member of slot `q + 1` voted for a block extending the chain, which reaches
the proposer as a viable head; so the proposal's parent extends every block of the chain
(`proposal_parent_extends_majority_block`, `get_anchor_ancestorEq_proposal_parent`). Lemma 59 with
ordered `head_height_floor` values (the least chain-state height a viable block may have) (`lem59le_goldfish_vote_names_honest_proposal_frame`) then names `B` in every
honest vote: the forms with `head_height_floor` at the proposer at most `head_height_floor` at the
voter hold by Lemma 91 (c) and (d), and `head_height_floor` at the voter is at most the
parent's height by Lemma 91 (b). Lemmas 22a and 22 deliver `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks up to the real time of each validator's tick to a clock value at most `M.voteTime S.C (q + 2)`:
the proof reads the proposer's root and anchor at its tick to the start of slot `q + 2`, the voters' roots and
Lemmas 22, 59 (ordered `head_height_floor` values) and 91 (c) at each voter's tick to the vote time of slot `q + 2`.

Caches, and the count of the adversary, up to the real time of each validator's tick to a clock value at most
`M.voteTime S.C (q + 2)`, and the honest voters of slot `q + 1` and the proposer active
through the sync delay after the times the synchronous delivery reads them (`hHold`, `hHoldP`): the text of
`honest_proposal_extends_chain_until`.

Restated with the delivery premises up to `M.voteTime S.C (q + 2)`: the proposal of slot `q + 2`
reaches its voters by then (`lem22_proposal_held_by_voter_upTo`,
`lem59le_goldfish_vote_names_honest_proposal_frame_upTo`,
`lem91c_proposer_h_max_le_voter_h_max_until_upTo`).

Read aloud: the honest proposal of slot `q + 2` has a parent that every block of the chain before
`q + 1` is an ancestor of or equal to, and every honest vote of slot `q + 2` names it, with the
delivery premises up to the bound. -/
theorem honest_proposal_extends_chain_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C (q + 2))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.voteTime S.C (q + 2)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to the real time of each validator's tick to a clock value at most the vote time of slot
    -- `q + 2`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum in the adversary set up to the real time of each validator's tick to a clock value at most
    -- the vote time of slot `q + 2` (, read as `hRoots`)
    (hAdvQ : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q + 2) →
      A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time k))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 1 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- caches on the chain at the steps from the phase's end up to the real time of each validator's tick to a clock
    -- value at most the vote time of slot `q + 2` (, read as `hRoots`)
    (hCaches : ∀ (k : ℕ) (w : V) (c : ℕ), x.lbl k = Event.tick w c → c ≤ M.voteTime S.C (q + 2) →
      ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time k →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2))
    -- the proposer's tick to the start of slot `q + 2` is after the phase's end (, strict by)
    (hip : x.time i₁ < x.time ip)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slot `q + 1` are active through the sync delay after Lemma 12's read time of slot `q + 1`
    -- ( under)
    (hHold : ∀ u ∈ honestActiveAt M S A x (q + 1), u ∈ S.P.committee (q + 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 1) C → C.AncestorEq B.parent) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧ B.parent.AncestorEq B ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (q + 2)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) → vote.head = B.root) ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), B ∈ (x.tickInput w (M.voteTime S.C (q + 2))).tree)
      := by
  -- the times (`extends_chain_until_reals`), the GST lines (`chain_until_windows`)
  set p := S.P.proposer (q + 2) with hpdef
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, htS, htSp, hpwdw, ev2, ec2, ec1, ec3⟩ :=
    (extends_chain_until_reals M F U) S hA0 hB0 hSkew (q := q) hΔs
  obtain ⟨hW1, hW2, hW3, hW4, hW5, hW6, hW7, -, -, -⟩ :=
    (chain_until_windows M F U) S A x R E hSkew hΔs hGST hs₀q hp.1
  have hc0R : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) := by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ q + 1 by omega)
  have hΔ := one_le_Δ S
  have hc1N : 1 ≤ M.supportCutoff S.C (q + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S q).2
  have hs2c1 : M.supportCutoff S.C (q + 1) ≤ M.slotStart S.C (q + 2) := by
    have h : ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C (q + 2) : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ (Δ S : ℝ) := Nat.cast_nonneg _
      linarith only [ec1, this]
    exact_mod_cast h
  have hss2N : M.slotStart S.C (q + 2) ≤ M.voteTime S.C (q + 2) := by
    have h := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2); omega
  have hc1vN : M.supportCutoff S.C (q + 1) ≤ M.voteTime S.C (q + 2) := le_trans hs2c1 hss2N
  have hv2N := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2)
  -- the proposer's tick `ip` to the start of slot `q + 2`, its state, its real time
  obtain ⟨-, hip1, hip2⟩ := E.tick_active ip p _ hl
  have hpi : p ∉ A.corrupted ip := E.not_mem_corrupted_of_tick hl
  have hin : x.tickInput p (M.slotStart S.C (q + 2)) = x.st ip p := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]
  have hipv : x.time ip ≤ ((M.voteTime S.C (q + 2) : ℕ) : ℝ) := by linarith only [hip2, ev2, hSkew, hA0]
  have hc0ip : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time ip := by
    linarith only [hip1, hc0R, ec1, hSkew, hB0]
  have hRootsP : RootsNameBlocksUntil M A x (x.time ip) := hRoots ip p _ hl hss2N
  have hAdvP : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time ip) := hAdvQ ip p _ hl hss2N
  have hAdvPm : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time ip) (M.supportCutoff S.C (s₀ + 1))) := hAdvP.mono (max_le le_rfl hc0ip)
  have hCachesP : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time ip →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u) :=
    hCaches ip p _ hl hss2N
  -- the one caches fact the Lemma 91 kit reads at the proposer's tick
  have hCp : CachesOnChain M S A x s₀ H (x.st ip p) := hCachesP ip p ((lt_of_time_lt M) x R hip) le_rfl hpi
  -- every tick to a support cutoff before a step of real time at most `t` with `t + ΔClockAhead` before the support
  -- cutoff of slot `q + 2` is for a slot before `q + 1`
  have hsBefore : ∀ (j : ℕ), x.time j + ΔClockAhead < ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) →
      ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < q + 1 := by
    rintro j hj s_a ⟨k, u, hk, hkl⟩
    exact (slot_lt_of_tick_time M F) S E hkl (by
      have := (time_mono M) x R hk.le
      linarith only [this, hj])
  have hipc2 : x.time ip ≤ ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) := by
    show _ ≤ ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ)
    linarith only [hip2, ec2, hSkew, hA0]
  have hipc : x.time ip + ΔClockAhead < ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) := by
    show x.time ip + ΔClockAhead < ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ)
    linarith only [hip2, ec2, hSkew]
  -- the proposer is an honest active validator of slot `q + 1`
  have hpAct : p ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
      (M.supportCutoff S.C (q + 1 + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hp.1
      (show 1 ≤ M.supportCutoff S.C (q + 2) from
        ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S (q + 1)).2) r3 r4
  have hpA : p ∈ honestActiveAt M S A x (q + 1) := by
    unfold honestActiveAt activeAt
    refine Finset.mem_sdiff.2 ⟨?_, fun h => ?_⟩
    · rw [← GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q]
      exact Activity.mem_awakeThroughoutToTick_of_mem_activeThroughoutToTick hpAct
    · rcases Finset.mem_union.1 h with h1 | h2
      · exact (not_mem_corruptedAtTime_of_mem_activeThroughoutToTick M F) x R E hp.1
          (show ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) + ΔClockAhead < _ by linarith only [r4, hB0]) h1
      · exact (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E hp.1
          (show ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) + ΔClockBehind + ΔClockAhead < _ by linarith only [r4]) h2
  -- the chain before `q + 1`: the proposer's root and anchor, its entry at `hMax − 1` (Lemma 91 (f), step form)
  have hρp : OnHonestChainBefore M S A x s₀ (q + 1) (M.get_fc_root (x.tickInput p (M.slotStart S.C (q + 2)))) := by
    rw [hin, ← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ ip (q + 1) H p E hRootsP hAdvPm hOld
      hCp hpi (hsBefore ip hipc)
  have hap := (proposer_anchor_on_chain_until M F U Fx) S A x R s₀ q H ip p E hSkew hRootsP hAdvP hOld
    hCp hs₀q hl hpA hLk
  obtain ⟨Hf, hHf⟩ := (chain_votes_of_inv M F) U S A x R s₀ (q + 1) _ E hSkew
    (hInv (q + 1) (by omega) le_rfl) hρp
  obtain ⟨Eb, hE, hEh⟩ := (proposer_entry_on_chain_until M F U Fx) S A x R s₀ q H ip p E hSkew hAdvPm hOld
    hCp hl
  -- committee sleepiness: the honest active members of slot `q + 1` are more than half of its committee
  have hK := hSleepK (q + 1 + 1) (by omega)
    (by have h := lt_of_le_of_lt hAnchor hs
        have h' : anchor < M.slotStart S.C (q + 2) := by exact_mod_cast h
        exact h'.le) le_rfl
  rw [Nat.add_sub_cancel] at hK
  have hsub : S.P.committee (q + 1) \ (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) ⊆
      S.P.committee (q + 1) \ honestActiveAt M S A x (q + 1) := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
    tauto
  have hMaj : |S.P.committee (q + 1) \ (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1))| <
      |honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)| :=
    lt_of_le_of_lt (Finset.card_le_card hsub) hK
  have hcard : 0 < (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)).card := by
    have := Finset.card_le_card_sdiff_add_card (s := S.P.committee (q + 1))
      (t := honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1))
    omega
  obtain ⟨u₀, hu₀⟩ : (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)).Nonempty :=
    Finset.card_pos.1 hcard
  -- the honest members of slot `q + 1` are honest at every step up to the support cutoff of slot `q + 2`
  have hHonU : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1), ∀ j : ℕ,
      x.time j ≤ ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) → u ∉ A.corrupted j := fun u hu j hj =>
    (not_mem_corrupted_of_le_time M) x R E
      (fun h => (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).1).2 (Finset.mem_union_left _ h)) hj
  -- the proposer's tick to the support cutoff of slot `q + 1` and its activity from the sync fact's read time (the
  -- core's form)
  have hpCore : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C (q + 1)) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j := by
    exact (tick_window_of_activeThroughoutToTick_int M) x R E
      ((mem_activeThroughoutToTick_of_inside M F) R E hp.1 hc1N r1 r2) htSp
  obtain ⟨kR, hkR, -⟩ := id hpCore
  have hRootsR : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C (q + 1)))) := by
    rw [(tickStep_eq_of_lbl M) x E hkR]
    exact hRoots kR p _ hkR hc1vN
  have hOwner := (GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R E
  have hFp : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1),
      (x.tickInput p (M.slotStart S.C (q + 2))).finalized.AncestorEq (Hf u) := by
    intro u hu
    refine ancestorEq_trans ?_ ((hHf u hu).2.2 _ hρp)
    rw [hin]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E ip p
  -- every voter's block of slot `q + 1` reaches the proposer by its tick (Lemma 12, step form)
  have hc1v2 : M.supportCutoff S.C (q + 1) ≤ M.voteTime S.C (q + 2) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2)
    omega
  have hHeldP := (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST (q + 1) (M.slotStart S.C (q + 2))
    (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) Hf p (E.mono hc1v2) hNet hSkew hRedeliver (Sy.mono hc1v2) hΔs hRootsR hParent
    hOwner hW3 hs2c1 ip hl
    (fun u hu => ⟨(Finset.mem_inter.1 hu).2, hHonU u hu ip hipc2, (hHf u hu).1,
      (hHf u hu).2.1⟩)
    (fun u hu => hHold u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2)
    hpCore
    hFp
  have hFρp : (x.tickInput p (M.slotStart S.C (q + 2))).finalized.AncestorEq
      (M.get_fc_root (x.tickInput p (M.slotStart S.C (q + 2)))) := by
    rw [hin]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E ip p
  have hInvP : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (q + 2))) := by
    rw [hin]; exact (lem11_node_invariant M F S A x R E ip p hpi).1
  have hφp : M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) =
      hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) - 1 := by
    rw [hin]
    exact ((lem91d_not_contested_until M F U Fx) S A x R s₀ ip (q + 1) H p E hAdvPm hChain hOld hCp hpi
      (hsBefore ip hipc)).2
  have hHp : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1),
      Hf u ∈ (x.tickInput p (M.slotStart S.C (q + 2))).tree := fun u hu =>
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (hHeldP u hu).2.2.1).1
  have hHv : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1),
      Hf u ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 2)))).tree ∧
      Hf u ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 2)))).viable_heads ∧
      M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) ≤ (M.chainStateOf S.C (Hf u)).h := by
    intro u hu
    have hT := hHp u hu
    have hCH := (hHf u hu).2.2
    have hFH := ancestorEq_trans hFρp (hCH _ hρp)
    have hφ : M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) ≤
        (M.chainStateOf S.C (Hf u)).h := by
      rw [hφp, ← hEh]
      exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb (Hf u)).2.2.2.1 (hCH Eb hE)
    refine ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hT, hFH⟩,
      (((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X _ hInvP _ _
        ⟨rfl, rfl⟩).2.2 (Hf u)).2 ⟨hT, hFH, hCH _ hρp, ?_⟩, hφ⟩
    exact hφ
  -- the proposal's parent extends every block of the chain before `q + 1`
  have hPE : ∀ X : Block V, OnHonestChainBefore M S A x s₀ (q + 1) X →
      (M.get_anchor (x.tickInput p (M.slotStart S.C (q + 1 + 1)))
        ((M.slotStart S.C (q + 1 + 1) : ℕ) : Int)).AncestorEq X →
      X.AncestorEq B.parent ∧ B.slot = q + 1 + 1 ∧ B ≠ Block.genesis ∧
      B.parent? = some B.parent ∧
      (B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 1 + 1))))
          (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 1 + 1)))).tree ∨
        B.parent = M.get_anchor (x.tickInput p (M.slotStart S.C (q + 1 + 1)))
          ((M.slotStart S.C (q + 1 + 1) : ℕ) : Int)) := by
    intro X hX haX
    exact (proposal_parent_extends_majority_block_upTo M F U) S A x R GST (q + 1) ip
      (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) Hf X B p (E.mono hc1v2) hNet hSkew hRedeliver (Sy.mono hc1v2) hΔs
      hRootsR hParent hOwner hW3
      (fun u hu => ⟨(Finset.mem_inter.1 hu).2,
        by rw [(tickStep_eq_of_lbl M) x E hl]; exact hHonU u hu ip hipc2,
        (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2 X hX⟩)
      (fun votes_p support_p hPCV => by
        rw [hPCV.1]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
          (by rw [hin]; exact (GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E ip p (q + 1))
          hMaj)
      (fun u hu => hHold u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2)
      hpCore
      hl hsent
      ⟨Hf u₀, (hHv u₀ hu₀).1, (hHv u₀ hu₀).2.1, (hHf u₀ hu₀).2.2 X hX⟩ haX
  obtain ⟨-, hBslot, hBne, hBpar?, hBparT⟩ := hPE _ hap (ancestorEq_refl _)
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 1) C →
      C.AncestorEq B.parent := by
    intro C hC
    rcases (compatible_iff _ _).1 ((onHonestChainBefore_compatible M F) S A x s₀ (q + 1) C _ hChain
      hC hap) with h | h
    · exact ancestorEq_trans h ((get_anchor_ancestorEq_proposal_parent M F) S A x R E (q + 2) ip B p hl
        hsent)
    · exact (hPE C hC h).1
  -- the proposer holds its proposal
  have hJIT : JustifiedInTree M (x.tickInput p (M.slotStart S.C (q + 2))) :=
    F.nd.nodeInv_justifiedInTree hInvP
  have hBparT' : B.parent ∈ (x.tickInput p (M.slotStart S.C (q + 2))).tree := by
    rcases hBparT with h | h
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1).1
    · rw [h]; exact (GoldilocksCorrectness.Record.Proofs.Routines.get_anchor_mem_T M F) S.C S.P S.X _ hInvP _
        (F.nd.nodeInv_finalized_mem_tree hInvP) hJIT
  have hFB : (x.tickInput p (M.slotStart S.C (q + 2))).finalized.AncestorEq B :=
    ancestorEq_trans hFρp (ancestorEq_trans (hParentChain _ hρp) hPB)
  have hBp : B ∈ (x.st (ip + 1) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R
      (q + 1) ip B p E hl hsent hRootNew hBparT' ((compatible_iff _ _).2 (Or.inl hFB))
  have hm1 : hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) - 1 ≤
      (M.chainStateOf S.C B.parent).h := by
    rw [← hEh]; exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb B.parent).2.2.2.1 (hParentChain Eb hE)
  -- at every honest active validator `w` of slot `q + 2`: its tick `iw` to the vote time of slot `q + 2`
  have hwTick : ∀ w ∈ honestActiveAt M S A x (q + 2),
      w ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (q + 2)) (M.voteTime S.C (q + 2)) := by
    intro w hwA
    exact (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (q + 2) w E hwA)
      (show 1 ≤ M.voteTime S.C (q + 2) by omega) r7 r8
  have hwFacts : ∀ w ∈ honestActiveAt M S A x (q + 2), ∀ iw : ℕ,
      x.lbl iw = Event.tick w (M.voteTime S.C (q + 2)) →
      x.tickInput w (M.voteTime S.C (q + 2)) = x.st iw w ∧ w ∉ A.corrupted iw ∧
      x.time i₁ < x.time iw ∧ x.time iw + ΔClockAhead < ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) ∧
      x.time iw ≤ ((M.voteTime S.C (q + 2) : ℕ) : ℝ) + ΔClockBehind ∧
      ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time iw := by
    intro w hwA iw hiw
    obtain ⟨-, hw1, hw2⟩ := E.tick_active iw w _ hiw
    refine ⟨by unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hiw], E.not_mem_corrupted_of_tick hiw,
      by linarith only [hs, hw1, ev2, hSkew, hB0],
      by show _ < ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ); linarith only [hw2, ev2, ec2, hSkew],
      hw2, by linarith only [hw1, ev2, ec1, hc0R, hSkew, hB0]⟩
  have hW : ∀ w ∈ honestActiveAt M S A x (q + 2),
      (M.get_fc_root (x.tickInput w (M.voteTime S.C (q + 2)))).AncestorEq B ∧
      B ∈ (x.tickInput w (M.voteTime S.C (q + 2))).tree := by
    intro w hwA
    obtain ⟨iw, hiw, -⟩ := Activity.mem_activeThroughoutToTick.1 (hwTick w hwA)
    obtain ⟨hinw, hwi, hiwt, hiwc, -, hiw0⟩ := hwFacts w hwA iw hiw
    have hρw : OnHonestChainBefore M S A x s₀ (q + 1) (M.get_fc_root (x.tickInput w (M.voteTime S.C (q + 2)))) := by
      rw [hinw, ← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
      exact (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ iw (q + 1) H w E
        (hRoots iw w _ hiw le_rfl)
        ((hAdvQ iw w _ hiw le_rfl).mono (max_le le_rfl hiw0)) hOld
        (hCaches iw w _ hiw le_rfl iw w ((lt_of_time_lt M) x R hiwt) le_rfl hwi) hwi (hsBefore iw hiwc)
    have hρwB := ancestorEq_trans (hParentChain _ hρw) hPB
    refine ⟨hρwB, ?_⟩
    exact (GoldilocksCorrectness.Record.Statements.Executions.lem22_proposal_held_by_voter_upTo M F U) S A x R GST
      (q + 1) ip B p w E hNet hSkew hRedeliver
      (by rw [(tickStep_eq_of_lbl M) x E hiw]; exact hRoots iw w _ hiw le_rfl) hParent hW4
      (Goldilocks.duty_window_start S.C (q + 2)) r9 (hwTick w hwA) hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans (by
        rw [hinw]
        exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E iw w)
        hρwB)))
  refine ⟨hParentChain, hBslot, hBne, hPB, fun w hwA vote hSend => ?_, fun w hwA => (hW w hwA).2⟩
  -- the vote names `B` (Lemma 59 with ordered `head_height_floor` values, per tick)
  obtain ⟨iw, hiw, hsw⟩ := hSend
  obtain ⟨hinw, hwi, hiwt, hiwc, hiwv, hiw0⟩ := hwFacts w hwA iw hiw
  have hφw : M.head_height_floor (x.tickInput w (M.voteTime S.C (q + 2))) =
      hMax M S.C (x.tickInput w (M.voteTime S.C (q + 2))) - 1 := by
    rw [hinw]
    exact ((lem91d_not_contested_until M F U Fx) S A x R s₀ iw (q + 1) H w E
      ((hAdvQ iw w _ hiw le_rfl).mono (max_le le_rfl hiw0)) hChain hOld
      (hCaches iw w _ hiw le_rfl iw w ((lt_of_time_lt M) x R hiwt) le_rfl hwi) hwi (hsBefore iw hiwc)).2
  -- Lemma 91 (e) at the proposer's tick, and `B` in the voter's tree at its tick (F-77-3's route)
  have hHmax : hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) ≤
      hMax M S.C (x.tickInput w (M.voteTime S.C (q + 2))) := by
    have he := (lem91e_proposal_height_ge_h_max_at_tick M F U Fx) S A x R s₀ (q + 2) i₁ H ip p B E hRootsP hAdvPm
      hs hChain hOld hCp (hsBefore ip hipc) hl hsent (by rw [hφp]; exact hm1) hParentChain
    exact le_trans he (GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) (hW w hwA).2)
  have hb := (lem91b_voter_head_height_floor_le_parent_until M F U Fx) S A x R s₀ (q + 2) H iw w B.parent E
    ((hAdvQ iw w _ hiw le_rfl).mono (max_le le_rfl hiw0)) hiw
    (fun s_a h => by have := hsBefore iw hiwc s_a h; omega) hChain hOld (hCaches iw w _ hiw le_rfl iw w ((lt_of_time_lt M) x R hiwt) le_rfl hwi)
    (fun C hC => hParentChain C hC)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem59le_goldfish_vote_names_honest_proposal_frame_upTo M F U)
    S A x R GST (q + 1) (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) Hf _ B p w vote
    _ _ _ _ E hNet hSkew hRedeliver Sy hΔs
    (by rw [(tickStep_eq_of_lbl M) x E hiw]; exact hRoots iw w _ hiw le_rfl) hParent hOwner hW3
    (fun u hu => ⟨(Finset.mem_inter.1 hu).2,
      by rw [(tickStep_eq_of_lbl M) x E hiw]; exact hHonU u hu iw (by linarith only [hiwc, hA0]),
      (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2 _ hap⟩)
    (fun votes_w support_w hCV => (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      (by rw [hinw] at hCV; exact (countedVotes_committee_st M F) S A x R E iw (q + 1) w votes_w support_w hCV) hMaj)
    (fun u hu => hHold u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2)
    (Goldilocks.duty_window_start S.C (q + 2)) htS
    (Activity.mem_activeThroughoutToTick_of_le hpwdw
      ((mem_activeThroughoutToTick_of_inside M F) R E hp.1 (show 1 ≤ M.slotStart S.C (q + 2) by omega) r5 r6))
    hHoldP (hwTick w hwA) ⟨ip, hl, hsent⟩ ⟨iw, hiw, hsw⟩
    (fun B' hB' hsl => (only_block_of_unforgeability_st M F U) S A x R E (q + 1 + 1) iw B B' p w
      ((not_mem_corrupted_of_le_time M) x R E hp.2 (by linarith only [hiwv, r8, hA0])) rfl ⟨ip, hl, hsent⟩
      (by rw [hinw] at hB'; exact hB') hsl)
    hRootNew ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (show M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) ≤
        M.head_height_floor (x.tickInput w (M.voteTime S.C (q + 2))) by rw [hφp, hφw]; exact Nat.sub_le_sub_right hHmax 1)
    ⟨Hf u₀, hHp u₀ hu₀, (hHf u₀ hu₀).2.2 _ hap, (hHf u₀ hu₀).2.2 _ hρp, (hHv u₀ hu₀).2.2⟩
    (ancestorEq_refl _) (hW w hwA).1
    (fun n' sent hrun hA e he hlive => by
      rcases (mem_honestActiveAt_or_lockFree M F U) S A (q + 1) w R E hSkew hwA with h | hsl
      · obtain ⟨D, hD, heD⟩ := hLocks (q + 1) (by omega) le_rfl w h n' sent hrun hA e he hlive
        exact ancestorEq_trans heD (ancestorEq_trans (hParentChain D hD) hPB)
      · exact ((revoke_locks_empty_of_lockFree M F) S A x (M.voteTime S.C (q + 1 + 1)) (q + 1 + 1) _ n'
          (Nat.le_add_left 1 _) hsl
          ((locksRevoked_of_voteTime_outcome M F U) S A x R E (q + 1 + 1) w n' sent hrun hA) e
          he).elim)
    hb

/-- Lemma 18, an honest validator's confirmation update confirms a block a committee majority
voted for early. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/FastConfirmationStatements.lean`. It is Lemmas 27
and 29 with the committee majority, which gives their voter bound because every vote of `v`'s
pool is from the slot-`s` committee, their half condition, and Lemma 27's lock condition through
Lemma 5.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of Lemma 27,
`lock_entries_compatible_of_half` and Lemma 29, which it calls.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: after the support cutoff of slot `s + 1`, `v` has saved `B` as the confirmation of slot
`s`, `B` is a fast block of `v`, `v` holds a lock entry on `B`, and `v`'s latest confirmed block has
advanced to `B`, when the honest voters of `Hs` for `B` are a majority of the slot-`s` committee.

Restated with the delivery premises up to `M.supportCutoff S.C s` (`lock_entries_compatible_of_half_upTo`,
`lem27_update_confirmation_confirms_voter_majority_block_upTo`, `lem29_update_confirmation_fast_locks_voter_majority_block_upTo`). -/
theorem lem18_update_confirmation_confirms_majority_block_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hMajority : (S.P.committee s \ Hs).card < Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF1 : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed =
        M.advance (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
          (x.tickInput v (M.supportCutoff S.C (s + 1))).latestConfirmed (some B) := by
  -- every vote of `v`'s slot-`s` pool at its tick input is from the slot-`s` committee
  have hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E
        (x.tickStep v (M.supportCutoff S.C (s + 1))) v s) hMajority
  have hHalf : (S.P.committee s).card ≤ 2 * Hs.card := GoldilocksCorrectness.Proofs.Routines.committee_card_le_of_majority hMajority
  have hLk := (lock_entries_compatible_of_half_upTo M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hOwner hGST hHs hHold hHalf hv hF1
  obtain ⟨hsave, hlatest⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem27_update_confirmation_confirms_voter_majority_block_upTo
      M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hBne
      hv hF1 hLk
  obtain ⟨hfast, hlock⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem29_update_confirmation_fast_locks_voter_majority_block_upTo
      M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hHalf
      hBne hv hF1
  exact ⟨hsave, hfast, hlock, hlatest⟩

open Classical in
/-- **Step 4 of the inclusion, at the updaters ticking no later than one updater `v₀`.** The facts of
`honest_proposal_saved_of_locks_until` that do not read the live locks, from its hypotheses with the rows
(roots, the adversary bound, the caches) read up to the real time of `v₀`'s tick to the support cutoff of slot
`q + 3` only: every block of the chain before `q + 2` is `B` or an ancestor of `B`; `B` is a non-genesis block of
slot `q + 2`; some block is on the chain before `q + 2`; every honest vote of slot `q + 2` names `B` and every
honest active validator of slot `q + 2` holds `B` at its vote; and every updater of slot `q + 2` whose tick to the
support cutoff of slot `q + 3` is no later than `v₀`'s has its root on `B`'s chain, saves `B`, makes it fast,
locks it, and has its finalized block on its root's chain.

Why: as `honest_proposal_saved_of_locks_until`. The rows the proposal's step reads are read at ticks to a clock
value at most the support cutoff of slot `q + 2`, before `v₀`'s tick; the strong induction on the updaters' tick
steps reads, at each updater, the rows up to its own tick, no later than `v₀`'s, and calls the induction
hypothesis only at earlier ticks.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment facts;
  `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the time from
  which committee sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the proposal;
  `v₀`: the updater whose tick bounds the rows.

Read aloud: with the rows read up to the tick of one updater `v₀` of slot `q + 2`, every updater of slot `q + 2`
that ticks to the support cutoff of slot `q + 3` no later than `v₀` saves the honest proposal of slot `q + 2`, fast
and locked.

Restated with the delivery premises up to `M.supportCutoff S.C (q + 2)`: the UpTo twins of the kit it calls. -/
theorem honest_proposal_saved_at_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v₀ : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (q + 2))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (q + 2)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- `v₀` is an updater of slot `q + 2`; the rows are read up to the real time of its tick to the support cutoff of slot `q + 3`
    (hv₀ : v₀ ∈ updaterAt M S A x (q + 2))
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time (x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    (∃ C₀ : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C₀) ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (q + 2)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) → vote.head = B.root) ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), B ∈ (x.tickInput w (M.voteTime S.C (q + 2))).tree) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) ≤ x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)) →
      ((M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
        B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
        (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ))) ∧
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq
        (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))))) := by
  have hvc2 : M.voteTime S.C (q + 2) ≤ M.supportCutoff S.C (q + 2) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 2)
    omega
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hsR : ∀ s' : ℕ, ((M.slotStart S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hvR : ∀ s' : ℕ, ((M.voteTime S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + Δ S := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hcR : ∀ s' : ℕ, ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + 2 * Δ S := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hvc : M.voteTime S.C (q + 2) ≤ M.supportCutoff S.C (q + 2) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 2)]; omega
  have hcc : M.supportCutoff S.C (q + 2) ≤ M.supportCutoff S.C (q + 2 + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- the times: every tick to the support cutoff of slot `q + 3` is after the phase's end, and after every tick to a
  -- clock value at most the support cutoff of slot `q + 2` (the cutoffs are `4 Δ S` apart, `hSkew`)
  have hearly : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (q + 2 + 1)) →
      x.time i₁ < x.time k := by
    intro k u hk
    have h1 := (E.tick_active _ _ _ hk).2.1
    have h0 := hs.1
    rw [hcR] at h1
    rw [hsR] at h0
    push_cast at h1 h0
    linarith
  have hlate : ∀ (k j : ℕ) (u w : V) (c : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (q + 2 + 1)) →
      x.lbl j = Event.tick w c → c ≤ M.supportCutoff S.C (q + 2) → x.time j ≤ x.time k := by
    intro k j u w c hk hj hc
    have h1 := (E.tick_active _ _ _ hk).2.1
    have h2 := (E.tick_active _ _ _ hj).2.2
    have hc' : (c : ℝ) ≤ ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) := by exact_mod_cast hc
    rw [hcR] at h1 hc'
    push_cast at h1 hc'
    linarith
  -- an honest active member `w₀` of the slot-`q + 2` committee (Lemma 88)
  have hanc0 : anchor < M.slotStart S.C (q + 2) := by exact_mod_cast lt_of_le_of_lt hAnchor hs.1
  have hanc : anchor ≤ M.slotStart S.C (q + 2 + 1) :=
    le_trans hanc0.le ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have h88 := (lem88_counting_of_committeeSleepiness M F) S A x R E anchor (q + 2) (S.P.proposer (q + 2)) 0
    hSleepK hanc le_rfl
  have h88c := h88.1
  set Hs := honestActiveAt M S A x (q + 2) ∩ S.P.committee (q + 2) with hHsdef
  obtain ⟨w₀, hw₀⟩ : Hs.Nonempty := Finset.card_pos.1 (show 0 < Hs.card by omega)
  have hw₀A := (Finset.mem_inter.1 hw₀).1
  have hw₀C := (Finset.mem_inter.1 hw₀).2
  -- the rows at `v₀`'s tick `k₀` to the support cutoff of slot `q + 3`, after every tick to a clock value at most
  -- the support cutoff of slot `q + 2` (`hlate`)
  obtain ⟨k₀, hk₀, -⟩ := Activity.mem_activeThroughoutToTick.1 hv₀
  have hk₀s : x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)) = k₀ := (tickStep_eq_of_lbl M) x E hk₀
  have hR₀ := hRoots
  have hAdv₀ := hAdvQ
  have hCa₀ := hCaches
  rw [hk₀s] at hR₀ hAdv₀ hCa₀
  have hi₁k₀ := (hearly k₀ v₀ hk₀).le
  -- step 1: the proposal (`honest_proposal_extends_chain_until`), its rows read up to `v₀`'s tick
  obtain ⟨-, hBslot, hBne, -, hVote, hBw⟩ := (honest_proposal_extends_chain_until_upTo M F U Fx) S A x R GST s₀ anchor
    i₁ H q ip B (E.mono hvc2) hNet hSkew hRedeliver (Sy.mono hvc2) hΔs
    (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (hlate k₀ k v₀ u c hk₀ hk (le_trans hc hvc)) hR₀)
    hParent (fun k u c hk hc => hAdv₀.mono (hlate k₀ k v₀ u c hk₀ hk (le_trans hc hvc)))
    ((GoldilocksCorrectness.Record.Statements.Executions.CommitteeSleepinessUntil.mono M) hSleepK hcc) hAnchor hGST
    hChain (fun s h₁ _ => hInv s h₁ (by omega)) (fun s h₁ _ => hLocks s h₁ (by omega)) hOld
    (fun k w c hk hc j u h₁ h₂ h₃ => hCa₀ j u h₁ (le_trans h₂ (hlate k₀ k v₀ w c hk₀ hk (le_trans hc hvc))) h₃)
    ht₀ hs₀q hs.1 (hs.2 ip hl) hLk (fun u hu hc => hHold (q + 1) le_rfl (by omega) u hu hc) hp hHoldP hl hsent
    hRootNew
  -- `w₀`'s vote of slot `q + 2`, at its tick `kV`
  obtain ⟨kV, vote₀, hlV, -, -, hsV⟩ := (honest_active_votes M F U) S A x R (q + 2) w₀ E hSkew hw₀A hw₀C
  have hw₀kV : w₀ ∉ A.corrupted kV := E.not_mem_corrupted_of_tick hlV
  have hVk₀ : x.time kV ≤ x.time k₀ := hlate k₀ kV v₀ w₀ _ hk₀ hlV hvc
  have hi₁kV : x.time i₁ < x.time kV := by
    have h1 := (E.tick_active _ _ _ hlV).2.1
    have h0 := hs.1
    rw [hvR] at h1
    rw [hsR] at h0
    linarith
  -- a block of the chain before `q + 2`: the root at `w₀`'s vote tick (Lemma 91 (f))
  have hC₀ := (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ kV (q + 2) H w₀ E
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hVk₀ hR₀)
    (hAdv₀.mono (max_le hVk₀ (le_trans ht₀ hi₁k₀))) hOld
    (hCa₀ kV w₀ ((lt_of_time_lt M) x R hi₁kV) hVk₀ hw₀kV) hw₀kV (by
      rintro s_a ⟨k, u, hk, hlk⟩
      by_contra hge
      have h1 := (E.tick_active _ _ _ hlk).2.1
      have h2 := (time_mono M) x R hk.le
      have h3 := (E.tick_active _ _ _ hlV).2.2
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show q + 2 + 1 ≤ s_a + 1 by omega)
      have hmR : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s_a + 1) : ℕ) := by
        exact_mod_cast hmono
      rw [hcR] at hmR
      rw [hvR] at h3
      push_cast at hmR h3
      linarith)
  -- the honest votes of slot `q + 2` are for `B`, and every block of the chain before `q + 2` is an ancestor of `B`
  have hRootH : ∀ u ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (q + 2)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∀ H' : Block V, vote = GoldfishVote.mk u (q + 2) H'.root → H'.root = B.root := by
    intro u hu vote hsend H' heq
    have h1 := hVote u hu vote hsend
    rw [heq] at h1
    exact h1
  have hChainLeB : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B := by
    intro C hC
    obtain ⟨H', hH'T, heq, hCH'⟩ := (hInv (q + 2) (by omega) le_rfl C hC).1 w₀ hw₀A vote₀ ⟨kV, hlV, hsV⟩
    have hroot := hRootH w₀ hw₀A vote₀ ⟨kV, hlV, hsV⟩ H' heq
    have hkVs : x.tickInput w₀ (M.voteTime S.C (q + 2)) = x.st kV w₀ := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlV]
    have hT := hH'T
    have hBT := hBw w₀ hw₀A
    rw [hkVs] at hT hBT
    have hHB : H' = B :=
      F.nd.nodeInv_rootsNameBlocksIn (lem11_node_invariant M F S A x R E kV w₀ hw₀kV).1 _ hT _ hBT hroot
    rw [← hHB]
    exact hCH'
  -- the voters' facts Lemma 18 reads, at every updater's tick
  have hHsv : ∀ v ∈ updaterAt M S A x (q + 2), ∀ u ∈ Hs, u ∈ S.P.committee (q + 2) ∧
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (q + 2)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (q + 2) B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C (q + 2))).tree := by
    intro v hv u hu
    have huA := (Finset.mem_inter.1 hu).1
    have huC := (Finset.mem_inter.1 hu).2
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    refine ⟨huC, ?_, ?_, hBw u huA⟩
    · intro h
      rw [(tickStep_eq_of_lbl M) x E hkv] at h
      exact (Finset.mem_sdiff.1 huA).2 (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, kv, v, hkv, E.not_mem_corrupted_of_tick hkv, h⟩))
    · obtain ⟨i, vote, hli, hvi, hvs, hsi⟩ := (honest_active_votes M F U) S A x R (q + 2) u E hSkew huA huC
      have hh := hVote u huA vote ⟨i, hli, hsi⟩
      have hvote : vote = GoldfishVote.mk u (q + 2) B.root := by
        obtain ⟨a, b, c⟩ := vote
        dsimp only at hvi hvs hh
        rw [hvi, hvs, hh]
      rw [hvote] at hsi
      exact ⟨i, hli, hsi⟩
  have hHoldHs : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C (q + 2) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (q + 2) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := fun u hu =>
    hHold (q + 2) (by omega) le_rfl u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2
  have hMaj : (S.P.committee (q + 2) \ Hs).card < Hs.card := by
    have hcd := Finset.card_sdiff_add_card_eq_card (show Hs ⊆ S.P.committee (q + 2) from Finset.inter_subset_right)
    omega
  have hGST2 : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (q + 2) :=
    le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ ≤ q + 2 by omega))
  -- the finalized block at an updater's tick is the root or an ancestor of it (the caches)
  have hFin : ∀ v ∈ updaterAt M S A x (q + 2), x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) ≤ k₀ →
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq
        (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))) := by
    intro v hv hle
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    have hkvs : x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = kv := (tickStep_eq_of_lbl M) x E hkv
    have hvk : v ∉ A.corrupted kv := E.not_mem_corrupted_of_tick hkv
    obtain ⟨-, -, -, -, hFJ⟩ := hCa₀ kv v ((lt_of_time_lt M) x R (hearly kv v hkv)) ((time_mono M) x R (hkvs ▸ hle)) hvk
    have hin : x.tickInput v (M.supportCutoff S.C (q + 2 + 1)) = x.st kv v := by
      unfold Trace.tickInput; rw [hkvs]
    rw [hin]
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_fc_root_cases M F) S.C S.P S.X _
        (lem11_node_invariant M F S A x R E kv v hvk).1 with h | h
    · rw [h]; exact hFJ
    · rw [h]; exact ancestorEq_refl _
  -- step 2, by strong induction on the updaters' tick steps to the support cutoff of slot `q + 3`: each updater's
  -- root is on `B`'s chain (`updater_root_on_chain_or_earlier`: on the chain before `q + 2`, or on an earlier
  -- updater's confirmation, which is `B`), so its finalized block is too, and its update saves `B`, makes it fast
  -- and locks it (Lemma 18, the honest committee members of slot `q + 2` a majority of it, Lemma 88)
  have hMain : ∀ n : ℕ, ∀ v ∈ updaterAt M S A x (q + 2), x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = n → n ≤ k₀ →
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro v hv hn hnk
    have htm : x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) ≤ x.time k₀ :=
      (time_mono M) x R (hn ▸ hnk)
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    have hkvs : x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = kv := (tickStep_eq_of_lbl M) x E hkv
    have hvkv : v ∉ A.corrupted kv := E.not_mem_corrupted_of_tick hkv
    have hRootB : (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B := by
      rcases (updater_root_on_chain_or_earlier M F U Fx) S A x R s₀ H (q + 2) v E hSkew
          ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htm hR₀)
          (hAdv₀.mono (max_le htm (le_trans ht₀ hi₁k₀))) hOld
          (by unfold Trace.tickInput; rw [hkvs]
              exact hCa₀ kv v ((lt_of_time_lt M) x R (hearly kv v hkv)) (hkvs ▸ htm) hvkv) hv with
        h | ⟨u, hu, hlt, C, hC, hrC⟩
      · exact hChainLeB _ h
      · rw [hn] at hlt
        rw [(ih _ hlt u hu rfl (by omega)).2.1] at hC
        cases hC
        exact hrC
    have hR18 : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2)))) := by
      refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htm hR₀)
      have h1 := (time_tickStep_le_add_behind M F) x R E v (M.supportCutoff S.C (q + 2))
      have h2 := (E.time_tickStep ⟨kv, hkv⟩).1
      rw [hcR] at h1 h2
      push_cast at h1 h2
      linarith
    have h18 := (lem18_update_confirmation_confirms_majority_block_upTo
      M F U) S A x R GST (q + 2) Hs B v E hNet hSkew hRedeliver Sy hΔs hR18 hParent
      ((votesCastByOwner_of_unforgeability M F) S A x R E) hGST2 (hHsv v hv) hHoldHs hMaj hBne hv
      (ancestorEq_trans (hFin v hv (hn ▸ hnk)) hRootB)
    exact ⟨hRootB, h18.1, h18.2.1, h18.2.2.1⟩
  refine ⟨hChainLeB, hBslot, hBne, ⟨_, hC₀⟩, hVote, hBw, fun v hv hle => ?_⟩
  rw [hk₀s] at hle
  exact ⟨hMain _ v hv rfl hle, hFin v hv hle⟩

open Classical in
/-- **Step 4 of the inclusion, with the live locks of every updater.** The conclusion of
`honest_proposal_saved_until`, from its hypotheses without `hLatest` (not read) and with `hLocksU`: every
updater of slot `q + 2` outside `honestActiveAt M S A x (q + 2)` keeps its live locks, after its revocation
of slot `q + 3`, on the chain before `q + 2` (`hLocks` gives it at the honest active validators).

Why: `honest_proposal_extends_chain_until` names `B` in every honest vote of slot `q + 2`, its rows read up to
the tick of an honest active committee member `w₀` (Lemma 88) to the support cutoff of slot `q + 3`, which is
after every tick to a clock value at most the support cutoff of slot `q + 2`. The chain before `q + 2` is on
`B`'s chain (`hInv` at `w₀`'s vote, whose block is `B`, roots naming blocks in `w₀`'s tree). By strong
induction on the updaters' tick steps to the support cutoff of slot `q + 3`: an updater's fork-choice root is on
the chain before `q + 2` or on the confirmation of slot `q + 2` an earlier updater saved
(`updater_root_on_chain_or_earlier`), which is `B` by induction; its finalized block is an ancestor of the root
(the caches); so Lemma 18, the honest active committee members of slot `q + 2` a majority of the committee,
saves `B`, makes it fast and locks it. The live locks are on the chain before `q + 2`, so on `B`'s chain.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment facts;
  `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the time from
  which committee sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the proposal.

Read aloud: when the updaters of slot `q + 2` that are not honest active validators keep their live locks on
the chain before `q + 2`, every updater of slot `q + 2` saves the honest proposal of slot `q + 2`, fast and
locked.

Restated with the delivery premises up to `M.supportCutoff S.C (q + 2)`: the UpTo twins of the kit it calls. -/
theorem honest_proposal_saved_of_locks_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (q + 2))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (q + 2)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ v ∈ updaterAt M S A x (q + 2), RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : ∀ v ∈ updaterAt M S A x (q + 2), A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ v ∈ updaterAt M S A x (q + 2), ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- every updater of slot `q + 2` outside `honestActiveAt` keeps its live locks, after its revocation of slot `q + 3`,
    -- on the chain before `q + 2` (`hLocks` gives it at the honest active validators)
    (hLocksU : ∀ v ∈ updaterAt M S A x (q + 2), v ∉ honestActiveAt M S A x (q + 2) →
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 2)) (q + 2) v)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    HonestChainExtends M S A x (honestActiveAt M S A x (q + 2)) B (q + 2) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
          ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq B ∧
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
      ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
        ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (q + 2 + 1))) (q + 2 + 1) →
        ∀ e ∈ M.lockEntries n',
          M.is_live (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
            ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ))) := by
  -- an honest active member `w₀` of the slot-`q + 2` committee (Lemma 88), an updater of slot `q + 2`
  have hanc0 : anchor < M.slotStart S.C (q + 2) := by exact_mod_cast lt_of_le_of_lt hAnchor hs.1
  have hanc : anchor ≤ M.slotStart S.C (q + 2 + 1) :=
    le_trans hanc0.le ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have h88 := (lem88_counting_of_committeeSleepiness M F) S A x R E anchor (q + 2) (S.P.proposer (q + 2)) 0
    hSleepK hanc le_rfl
  have h88c := h88.1
  set Hs := honestActiveAt M S A x (q + 2) ∩ S.P.committee (q + 2) with hHsdef
  obtain ⟨w₀, hw₀⟩ : Hs.Nonempty := Finset.card_pos.1 (show 0 < Hs.card by omega)
  have hw₀U := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) (Finset.mem_inter.1 hw₀).1
  -- the step's facts at each updater, with the rows read up to its own tick (`honest_proposal_saved_at_until`)
  have hAt := fun (v₀ : V) (hv₀ : v₀ ∈ updaterAt M S A x (q + 2)) =>
    (honest_proposal_saved_at_until_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v₀ E hNet hSkew hRedeliver Sy hΔs
      hv₀ (hRoots v₀ hv₀) hParent (hAdvQ v₀ hv₀) hSleepK hAnchor hGST hChain hInv hLocks hOld
      (fun j u h₁ h₂ h₃ => hCaches v₀ hv₀ j u ((time_mono M) x R h₁.le) h₂ h₃) ht₀
      hs₀q hs hLk hHold hp hHoldP hl hsent hRootNew
  obtain ⟨hChainLeB, hBslot, hBne, ⟨C₀, hC₀⟩, hVote, hBw, -⟩ := hAt w₀ hw₀U
  have hAll := fun v (hv : v ∈ updaterAt M S A x (q + 2)) => ((hAt v hv).2.2.2.2.2.2 v hv le_rfl).1
  have hFin := fun v (hv : v ∈ updaterAt M S A x (q + 2)) => ((hAt v hv).2.2.2.2.2.2 v hv le_rfl).2
  have hRootH : ∀ u ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (q + 2)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∀ H' : Block V, vote = GoldfishVote.mk u (q + 2) H'.root → H'.root = B.root := by
    intro u hu vote hsend H' heq
    have h1 := hVote u hu vote hsend
    rw [heq] at h1
    exact h1
  -- the live locks after the revocation of slot `q + 3`: `hLocks` at the honest active validators, `hLocksU` at the others
  have hLF : ∀ v ∈ updaterAt M S A x (q + 2),
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 2)) (q + 2) v := fun v hv =>
    if h : v ∈ honestActiveAt M S A x (q + 2) then hLocks (q + 2) (by omega) le_rfl v h else hLocksU v hv h
  have hsub := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2)
  refine ⟨hChainLeB, hBslot, hBne, ⟨fun u hu vote hsend => ?_, fun w hw n' sent hrun hA e he hlive => ?_,
    fun v hv C' hC' => ?_⟩, fun v hv => (hAll v hv).2.1,
    fun v hv => ⟨ancestorEq_trans (hFin v hv) (hAll v hv).1, (hAll v hv).1, fun n' sent hrun hA e he hlive => ?_⟩,
    fun v hv => ⟨(hAll v hv).2.2.1, (hAll v hv).2.2.2⟩⟩
  · obtain ⟨H', -, heq, -⟩ := (hInv (q + 2) (by omega) le_rfl _ hC₀).1 u hu vote hsend
    have hroot := hRootH u hu vote hsend H' heq
    refine ⟨B, hBw u hu, ?_, ancestorEq_refl B⟩
    rw [heq, hroot]
  · obtain ⟨D, hD, heD⟩ := hLF w (hsub hw) n' sent hrun hA e he hlive
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hChainLeB D hD)))
  · rw [(hAll v (hsub hv)).2.1] at hC'
    cases hC'
    exact ancestorEq_refl B
  · obtain ⟨D, hD, heD⟩ := hLF v hv n' sent hrun hA e he hlive
    exact ancestorEq_trans heD (hChainLeB D hD)

/-- **Step 4 of the inclusion: every updater saves the proposal, fast and locked.** Under the
hypotheses of `honest_proposal_extends_chain`: every block of the chain before `q + 2` is `B` or an
ancestor of `B`; `B` is a non-genesis block of slot `q + 2`; `HonestChainExtends` holds for `B` at
slot `q + 2` at its honest active validators; every updater of slot `q + 2` saves `B` (Lemma 27),
has its finalized block and its fork-choice root on `B`'s chain, keeps no live lock off `B`'s
chain after its revocation of slot `q + 3`, and has `B` fast and locked (Lemma 60).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks, the count of the adversary and the caches up to the real time of each updater's tick to
`M.supportCutoff S.C (q + 2 + 1)`; the proposer's tick to the start of slot `q + 2` at or after `x[i₁].time`; the
honest voters of slots `q + 1` and `q + 2` and the proposer active through the sync delay after the times the
synchronous delivery reads them (`hHold`, `hHoldP`): the text of `honest_proposal_saved_until` without `hLatest`,
which its proof does not read.

Restated with the delivery premises up to `M.supportCutoff S.C (q + 2)`: the slot-`(q + 2)` votes
reach every updater by then (`lem27_update_confirmation_confirms_voter_majority_block_upTo`,
`lem60_update_confirmation_fast_locks_frame_upTo`).

Read aloud: every updater of slot `q + 2` saves the honest proposal of slot `q + 2`, fast and
locked, with the delivery premises up to the bound. -/
theorem honest_proposal_saved_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (q + 2))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (q + 2)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ v ∈ updaterAt M S A x (q + 2), RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : ∀ v ∈ updaterAt M S A x (q + 2), A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ v ∈ updaterAt M S A x (q + 2), ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    HonestChainExtends M S A x (honestActiveAt M S A x (q + 2)) B (q + 2) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
          ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq B ∧
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
      ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
        ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (q + 2 + 1))) (q + 2 + 1) →
        ∀ e ∈ M.lockEntries n',
          M.is_live (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
            ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ))) := by
  refine (honest_proposal_saved_of_locks_until_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q ip B E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hCaches ht₀ hs₀q hs hLk ?_ hHold hp hHoldP hl
    hsent hRootNew
  -- the updaters outside `honestActiveAt`: the lock step from slot `q + 1` at each
  exact fun v hv _ => (updater_locks_on_chain_of_updaterAt M F U) S A x R E hSkew s₀ q hs₀q
    (hLocks (q + 1) (by omega) (by omega)) v hv

/-- `lem90_included_update_facts` at the slot `q + 2`, with the lock invariant at slot `q` (`hLk`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal; `v`: the updater.

Roots name blocks until `M.supportCutoff S.C (q + 2 + 1)`: `honest_proposal_saved`.

Caches up to `M.supportCutoff S.C (q + 2 + 1)`: `honest_proposal_saved_until`.

Read aloud: the per-validator facts of the inclusion at the slot `q + 2`, with the lock invariant at
slot `q` and the honest voters of slots `q + 1` and `q + 2` and the proposer active for the sync delay after
the times the synchrony condition reads them.

Restated with the delivery premises up to `M.supportCutoff S.C (q + 2)`: the bound of
`honest_proposal_saved_at_until_upTo`. -/
theorem included_update_facts_q_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (q + 2))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (q + 2)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root)
    (hv : v ∈ updaterAt M S A x (q + 2)) :
    (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, ∀ n₀ : M.N,
        M.is_live n₀ ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).latestConfirmed = B := by
  -- step 4 at `v`, with the rows at `v`'s own tick (`honest_proposal_saved_at_until`)
  obtain ⟨hChainLeB, hBslot, -, -, -, -, hUp⟩ := (honest_proposal_saved_at_until_upTo M F U Fx) S A x R GST s₀ anchor i₁
    H q ip B v E hNet hSkew hRedeliver Sy hΔs hv hRoots hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld
    hCaches ht₀ hs₀q hs hLk hHold hp hHoldP hl hsent hRootNew
  obtain ⟨⟨-, hSavedv, hFastv, hLockv⟩, -⟩ := hUp v hv le_rfl
  -- the live locks after `v`'s revocation of slot `q + 3` are on `B`'s chain
  have hLF := (updater_locks_on_chain_of_updaterAt M F U) S A x R E hSkew s₀ q hs₀q
    (hLocks (q + 1) (by omega) (by omega)) v hv
  have hRevC : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
        ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (q + 2 + 1))) (q + 2 + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
          ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
    intro n' sent hrun hA e he hlive
    obtain ⟨D, hD, heD⟩ := hLF n' sent hrun hA e he hlive
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hChainLeB D hD)))
  -- the outcome of `v`'s tick to the support cutoff of slot `q + 3`, from a state awake since the duty window's start
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
    (by
      have hdwz : (Goldilocks.duty_window_start S.C (q + 2 + 1) : ℤ) ≤
          ((M.dutyWindowStart S.C (q + 2 + 1) : ℕ) : ℤ) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
        exact Int.self_le_toNat _
      have h := (dutyWindowStart_succ_lt_supportCutoff M F U) S (q + 2)
      have h' : ((M.dutyWindowStart S.C (q + 2 + 1) : ℕ) : ℤ) < ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      exact lt_of_le_of_lt hdwz h')
  obtain ⟨n'', sent, hrun, hAwF, hSv, -, hLe, -⟩ :=
    (update_state_of_tick M F U) S A x R (q + 2) v E hlK ⟨τ, hτ, hτle⟩
  have hSaved'' : M.savedConfirmation n'' (q + 2) = some B := by rw [← hSv]; exact hSavedv
  refine ⟨hSavedv, hFastv, hLockv, fun e he n₀ hlive => ?_, ?_⟩
  · -- the entries after the update: on `B`'s chain, the liveness read only for its deadline
    have he' : e ∈ M.lockEntries n'' := by rw [← hLe]; exact he
    exact (update_lock_entries_ancestorEq_at M F U) S A x R (q + 2) B v E hSkew hv n'' sent hrun hAwF hSaved''
      hBslot hRevC e he' _ hlive
  · -- the record of the confirmed tip: no live lock of the update's input conflicts with `B`
    exact (latest_confirmed_after_update_of_compatible M F U) S A x R (q + 2) B v E hSkew (by rw [hBslot]) hv
      hSavedv ((live_locks_compatible_of_revocation_of_active M F U) S A x R (q + 2) B v E hSkew hv
        (fun _ => hRevC))

/-- **The per-validator export of the inclusion.** The proof; the audited
statement is in `Statements/Executions/ConfirmedTipStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: `included_update_facts_q` at `q := s − 2`.

Caches up to `M.supportCutoff S.C (s + 1)`: `included_update_facts_q_until` at `q := s − 2`.

Read aloud: with the lock invariant also at the healed slot, and the honest voters of slots `s - 1` and `s`
and the proposer active for the sync delay after the times the synchrony condition reads them, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain, reading nothing
after the slot's update.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of
`included_update_facts_q_until_upTo` at `s = q + 2`. -/
theorem lem90_included_update_facts_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    --, the amended row `hHoldP`, under)
    (hHold : ∀ s' : ℕ, s ≤ s' + 1 → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hv : v ∈ updaterAt M S A x s) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed = B := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hs.1)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  obtain ⟨h1, h2, h3, h4, h5⟩ := (included_update_facts_q_until_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hSleepK hAnchor hGST (by rwa [show q + 2 - 1 = q + 1 by omega] at hChain) hInv hLocks hOld
    (fun j u h₁ h₂ h₃ => hCaches j u ((time_mono M) x R h₁.le) h₂ h₃) ht₀ (by omega) hs
    ((locks_before_of_locks_le M F) S A x s₀ q (fun s' h₁ h₂ => hLocks s' h₁ (by omega)) hLocks₀ (by omega))
    (fun s' h1 h2 => hHold s' (by omega) h2) hp hHoldP hl hsent (fun B' hB' hr => hNoCollision ⟨B', hB', hr⟩) hv
  exact ⟨h1, h2, h3, fun e he => h4 e he _, h5⟩

end GoldilocksCorrectness.Record.Proofs.Executions

