module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42UpTo
public import GoldilocksCorrectness.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma31UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma42UpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PhaseChainUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PhaseChainUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the phase step, the locks clause of
the re-base and Lemma 45b, with the delivery premises up to a bound. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart dutyWindowStart_succ_le_supportCutoff lockDeadline_injective
  one_le_Δ slotStart_eq slotStart_mono supportCutoff_eq supportCutoff_lt_of_lt
  supportCutoff_succ_le viewFreeze_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (votesOnceInPoolFor_of_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  LocksRevoked VoterTreeAt)



open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible awake_since_record_awake)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The phase step.** The proof; the audited statement is in
`Statements/Executions/PhaseChainStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `𝓒`: the family.

Roots name blocks until `M.supportCutoff S.C (s' + 1)`: the proof reads `lem89s_chain_step` at slot
`s'`, whose bound is that time.

Restated with the delivery premises up to `M.supportCutoff S.C (s' + 1)`: the chain step at slot
`s'` reads deliveries due by then (`lem89s_chain_step_upTo`).

Read aloud: inside the phase, the honest chain grows by the confirmations of slot `s'`, each slot's
members awake and honest only through their own slot's update, with the delivery premises up to the
bound. -/
theorem lem89s_phase_step_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' : Finset V) (𝓒 : Block V → Prop)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s' + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `s' + 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hHon : Hon ⊆ honestActiveAt M S A x s')
    (hHon' : Hon' ⊆ honestActiveAt M S A x (s' + 1))
    (hSub : Hon' ⊆ Hon)
    (hCommittee : (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon).card)
    (hCommittee' : (S.P.committee (s' + 1)).card < 2 * (S.P.committee (s' + 1) ∩ Hon').card)
    (hInv : ChainInvFor M S A x Hon 𝓒 s')
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt M S A x 𝓒 s' u)
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Hon',
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt M S A x C s' w) :
    ChainInvFor M S A x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) ∧
    ∀ u ∈ Hon', LiveLocksOnFamilyAt M S A x (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) u := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the updaters of slot `s'`: every honest active validator of slot `s' + 1` is one
  have hUpd : Hon' ⊆ updaterAt M S A x s' :=
    fun u hu => (honestActiveAt_succ_subset_updaterAt M F U) S A s' R E hSkew (hHon' hu)
  refine ⟨(lem89s_chain_step_upTo M F U) S A x R GST s' Hon Hon' Hon' 𝓒 E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick
    hParent hOwner hGST hHon hHon' hUpd subset_rfl hCommittee hCommittee' hInv
    (fun u hu => Or.inl (hSub hu)) hLocks
    (fun C hC v hv C' hC' => (hInv C hC).2.2 v (hSub hv) C' hC') hStep, ?_⟩
  -- the lock invariant at every member of `Hon'`: its window from the duty window's start of slot `s' + 2`
  -- up to its tick to the vote time of slot `s' + 2`, inside its window as an honest active validator of slot `s' + 1`
  intro u hu
  have hwin := (honestActiveAt_window M F) S A (s' + 1) u E (hHon' hu)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1 + 1)
  have hvt1 : 1 ≤ M.voteTime S.C (s' + 2) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 2)
    omega
  have hds : duty_window_start S.C (s' + 1) ≤ ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (s' + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
      (show s' + 1 ≤ s' + 2 by omega)
    have h3 : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℤ) ≤ ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) := by
      exact_mod_cast h2
    exact le_trans h1 h3
  have hdsR := duty_window_start_real S (s' + 1)
  have hdle := (duty_window_start_le_real M F U) S (s' + 1)
  have hwin' : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.voteTime S.C (s' + 2)) := by
    refine (mem_activeThroughoutToTick_of_le_end_int M) x R E hvt1 ?_ ?_ hwin
    · have h1 : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) + 3 * Δ S ≤ ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) := by
        have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
        have h22 : M.voteTime S.C (s' + 2) = M.voteTime S.C (s' + 1) + 4 * Δ S :=
          (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s' + 1)
        exact_mod_cast (show M.supportCutoff S.C (s' + 1) + 3 * Δ S ≤ M.voteTime S.C (s' + 2) by omega)
      have h2 : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by
        exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_supportCutoff M.toSlotLayout F.sched U) S
          (by omega)
      have h3 := (duty_window_start_le_real M F U) S (s' + 1)
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      linarith
    · have h4 : ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) = ((M.voteTime S.C (s' + 2) : ℕ) : ℝ) + Δ S := by
        rw [hc2]; push_cast; ring
      linarith
  have hwin'' : u ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 2)) := by
    exact Activity.mem_activeThroughoutToTick_of_le hds hwin'
  exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <|
    (liveLocksOnFamilyAt_step M F U) S A x R 𝓒 _ s' u E hSkew hwin'' (fun C hC => Or.inl hC)
    (fun C hC => Or.inr ⟨u, hu, C, hC, ancestorEq_refl C⟩) (hLocks u (hSub hu))

/-- **The lock clause from the votes.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block reaches a validator
only once it holds the parent, and nobody votes in an honest validator's name: if `GST` is at most
the vote time of slot `s`; the members are awake and honest at every time from the duty window's
start of slot `s` to the support cutoff of slot `s + 1`; the committee of slot `s` has fewer than twice
its members in `Hon`; every committee member `u` of `Hon` put on the wire at its tick at the vote
time of slot `s` its slot-`s` vote for `(H u).root`, `H u` a block it holds then that is `B` or a
descendant of `B`; and every member's finalized block before the support cutoff of slot `s + 1` is
compatible with `B` — then every lock entry a member's revocation of slot `s + 1` leaves, run from the state
its tick to the vote time of slot `s + 1` starts from (rule R3), is on a block compatible with `B`.

Why: `w`'s finalized block `F` at its tick input to the vote time of slot `s + 1` is an ancestor of its
finalized block before the support cutoff of slot `s + 1`, or it, so it is compatible with `B`. When `B` is
`F` or an ancestor of `F`, every entry left is on a block of `w`'s frame tree, which descends from
`F`. When `F` is an ancestor of `B`, every vote of a committee member of `Hon` reached `w`, held
early, by the support cutoff of slot `s` (Lemma 12 in the step form, `lem12_honest_vote_delivered_until_of_steps_upTo`,
`w` active at every step from the sync fact's read time), so it is the member's only slot-`s` vote in
`w`'s pool at its tick input to the vote time of slot `s + 1`, resolving to a block of `w`'s frame tree on `B`'s chain; Lemma 5 concludes.

Read aloud: a majority of honest votes for `B`'s chain at slot `s` leaves no honest lock
conflicting with `B` after the revocation of slot `s + 1`, whatever the locks were before.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the members; `B`: the block; `H`: the block of
  each committee member's vote.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: the proof
reads Lemma 12 at slot `s` at the receiver's own tick to that cutoff.

Restated with the delivery premises up to `M.supportCutoff S.C s`: Lemma 12 at slot `s` reads the
votes due by then (`lem12_honest_vote_delivered_until_of_steps_upTo`). -/
theorem locks_clause_of_votes_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (B : Block V)
    (H : V → Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member is an updater of slot `s`: active from a tick at or before the duty window's start of slot `s + 1`
    -- up to its own tick to the support cutoff of slot `s + 1`
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x s)
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    (hVotes : ∀ u ∈ S.P.committee s ∩ Hon,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ B.AncestorEq (H u))
    (hF : ∀ v ∈ Hon,
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    ∀ w ∈ Hon, ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) (s + 1) n' →
      ∀ e ∈ M.lockEntries n', e.B.compatible B = true := by
  intro w hw n' hRevoke e he
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  -- the times
  obtain ⟨hv0, hc0, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hv1, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw1 := duty_window_start_real S (s + 1)
  push_cast at hdw1
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hkm : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h' : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast at hΔs ⊢; linarith
    exact_mod_cast h'
  have hm1 := le_max_left (Δ S) Δs
  have hΔ1R : ((Δ S : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm1
  have hkmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by exact_mod_cast hkm
  have hvR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by
    rw [hv1, hs1, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hc1, hs1, hss]; push_cast; ring
  -- `w`'s ticks to the vote time and to the support cutoff of slot `s + 1`, inside its reader of slot `s`
  have hw' : w ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.voteTime S.C (s + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E (hHonUpd w hw) (by omega)
      (by rw [hdw1, hvR]; linarith) (by rw [hvR, hc1R]; linarith)
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hw'
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd w hw)
  have hkc2 := (E.tick_active kc w _ hkc).2.2
  have hk'1 := (E.tick_active k' w _ hk').2.1
  have hkck' : kc ≤ k' := ((lt_of_time_lt M) x R (by rw [hvR] at hkc2; rw [hc1R] at hk'1; linarith)).le
  have hkcs : x.tickStep w (M.voteTime S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  have hk's : x.tickStep w (M.supportCutoff S.C (s + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  -- `w`'s tick to the support cutoff of slot `s`, and its window from Lemma 12's read time to it
  obtain ⟨kR, hkR, hkRw⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew (hHonUpd w hw)
  have hkRs : x.tickStep w (M.supportCutoff S.C s) = kR := (tickStep_eq_of_lbl M) x E hkR
  -- `w`'s finalized block at its tick input to the vote time of slot `s + 1` is compatible with `B`: an ancestor of
  -- its finalized block at its tick input to the support cutoff of slot `s + 1`, or it
  have hFF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (x.tickInput w (M.supportCutoff S.C (s + 1))).finalized := by
    unfold Trace.tickInput; rw [hkcs, hk's]; exact (F_ancestorEq_of_le M F) x R E w hkck'
  have hFc := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hFF (hF w hw)
  rcases (compatible_iff _ _).1 hFc with hFB | hBF
  swap
  · -- `B` is the finalized block or an ancestor of it: every entry left descends from it
    have heT := GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree hb1 hRevoke e he
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hBF
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 heT).2))
  -- the finalized block is an ancestor of `B`, or `B`: Lemma 5 against the members' votes, held at `w`'s tick input
  -- to the vote time of slot `s + 1` (Lemma 12 in the step form)
  have hHeld : ∀ u ∈ S.P.committee s ∩ Hon, HeldEarlyVoteFor M S.C
      (x.tickInput w (M.voteTime S.C (s + 1))) s (H u) u := by
    refine (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST s (M.voteTime S.C (s + 1))
      (S.P.committee s ∩ Hon) H w E hNet hSkew hRedeliver Sy hΔs ?_ hParent hOwner hGST (by omega) kc hkc ?_ ?_
      ⟨kR, hkR, hkRw⟩ ?_
    · rw [hkRs]; exact hRoots kR w _ hkR le_rfl
    · intro u hu
      -- the voter is outside the adversary set at `w`'s tick to the vote time of slot `s + 1`: its reader of slot `s`
      -- reaches past every honest tick to that vote time
      have hX := (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E
        (hHonUpd u (Finset.mem_inter.1 hu).2) (c := M.voteTime S.C (s + 1)) (by rw [hvR, hc1R]; linarith)
      have hnc := (not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl M F) x E hkc hX
      rw [hkcs] at hnc
      exact ⟨(Finset.mem_inter.1 hu).1, hnc, (hVotes u hu).1, (hVotes u hu).2.1⟩
    · intro u hu
      exact (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hHonUpd u (Finset.mem_inter.1 hu).2)
    · intro u hu
      exact ancestorEq_trans hFB (hVotes u hu).2.2
  have hHalf := ((counting_of_committee_majority_st M F) S A x R E s kc Hon w hCommittee).1
  refine ((GoldilocksCorrectness.Record.Statements.Routines.lem5_revoke_locks_entries_compatible F) B
    (S.P.committee s ∩ Hon) hb1 (fun u hu => ?_) (by rw [Nat.add_sub_cancel]; exact hHalf) hRevoke e he).2
  obtain ⟨hp, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u hu
  exact ⟨_, hp, rfl, ⟨y, hy⟩, ⟨H u, hHΦ, rfl, (hVotes u hu).2.2⟩, huniq⟩

/-- **Lemma 45b, a lock whose window is after `GST` is extended by the next slot's honest votes,
the held form.** The proof; the audited statement is in
`Statements/Executions/PhaseChainStatements.lean`. It is the proof of Lemma 45
(`GoldilocksCorrectness/Proofs/Executions/Lemma45.lean`), steps 1 to 3 verbatim, with step 4
calling Lemma 21b (`lem21b_goldfish_vote_extends_eligible_block_held`) in place of Lemma 21, so
that the block the vote names is kept, held by `w`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `n'`, `sent`: an outcome
of `v`'s tick at the support cutoff of slot `s + 1`, which runs that update; `w`: the voter of slot
`s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: the proof reads Lemma 42 and Lemma 21b at
slot `s`, and Lemma 31 at a slot `s' < s`, whose bounds are at most that time.

Restated with the delivery premises up to `M.supportCutoff S.C (s + 1)`: Lemma 42 and Lemma 21b at
slot `s` read deliveries due by then, and Lemma 31 at a slot `s' < s` reads earlier.

Read aloud: under Lemma 45's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is the lock's block or a descendant of it, with the delivery
premises up to the bound. -/
theorem lem45b_honest_vote_extends_lock_held_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (v w : V) (e : M.LE) (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s + 1 - S.C.k))
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `w` ticks to the vote time of slot `s + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most `tStartW`, more than both clock bounds before the window start Lemma 42 reads; `v` and
    -- `w` are active through the sync delay after the two read times of Lemma 42's sync facts
    (tStartW : ℤ) (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.voteTime S.C (s + 1)))
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (he : e ∈ M.lockEntries n')
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible e.B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq e.B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
        (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          e.B.AncestorEq W)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ e.B.AncestorEq H_w := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  -- the slot times
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfrk := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (s + 1 - S.C.k)
  have hk2 := S.C.k_ge_two
  have hsk := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s + 1 - S.C.k ≤ s by omega)
  have hGSTv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s := by omega
  -- the reads of Lemmas 21b and 42 at `v` (`lem21b_reads_of_dutyWindow`)
  obtain ⟨htStart, -⟩ := (lem21b_reads_of_dutyWindow M F U) S R E hSkew hΔs (le_of_add_le_right hGSTv) htStartW hv
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from that cutoff less `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have hdle := (duty_window_start_le_real M F U) S (s + 1)
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead) (by linarith)
  have hti_v : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hRootsΦv : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti_v]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  -- the confirmation update `v`'s tick ran
  have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n' sent hUpdate hAwake
  -- step 1: Lemma 35 on `v`'s update; `e` is an entry it adds
  obtain ⟨-, h35⟩ := GoldilocksCorrectness.Record.Statements.Routines.lem35_update_confirmation_lock_entries hCU
  rcases h35 e he with hin | ⟨-, -, -, ⟨C', hSaved, hLC'⟩, hFS⟩
  · -- an entry of the input was added by the update of its own slot `s`, before `v`'s tick
    exfalso
    rw [hti_v] at hin
    obtain ⟨s', hd', hlt, -⟩ := (lem39_lock_entry_provenance M F U) S A x R k_v v e E hin
    have hbb : s' = s :=
      GoldilocksCorrectness.Proofs.Routines.lockDeadline_injective S (hd'.symm.trans hd)
    rw [hbb, (tickStep_eq_of_lbl M) x E hk_v] at hlt
    exact lt_irrefl _ hlt
  -- step 2: Lemma 36 gives the early supporters of `e`'s block at `v`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' e.B hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti_v]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v hwinv)
      hCU hSaved hLC'
  simp only [Nat.add_sub_cancel] at hSup hElig hFS
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hcf : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
    have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by
      rw [hsc, hvt, hfr, hss1, hss0]; ring
    rw [h]; push_cast; ring
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [hcf]
    linarith
  -- `w`, active up to its tick to the view freeze of slot `s`
  have hvfv : (M.viewFreeze S.C s : ℝ) + ΔClockBehind < (M.voteTime S.C (s + 1) : ℝ) - ΔClockAhead := by
    have h : M.voteTime S.C (s + 1) = M.viewFreeze S.C s + 2 * Δ S := by
      rw [hvt, hfr, hss1, hss0]; ring
    rw [h]; push_cast; linarith
  have hfr1 : 1 ≤ M.viewFreeze S.C s := by rw [hfr]; omega
  have hwF : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s) :=
    (mem_activeThroughoutToTick_of_le_end_int M) x R E hfr1
      (by
        have h3 : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        linarith)
      hvfv hw
  -- `w`'s tick `kV` to the vote time of slot `s + 1`, and its finalized block there
  obtain ⟨kV, hkV, hsV⟩ := hSend
  have hti_w : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kV w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkV]
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti_w]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E kV w
  have hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible e.B = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hFroot hF2
  -- step 3: the lock condition at `w`, on the revocation every outcome of `w`'s tick ran
  have hLocks : ∀ (n'' : M.N) (sent'' : List (NamedObject V)),
      .ok (n'', sent'') ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e' ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e' = true → e'.B.compatible e.B = true := by
    intro n'' sent'' hrun hAwakeW e' he' _
    have hRevoke := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s + 1) w n'' sent'' hrun hAwakeW
    rcases hFS with hFast | hSlow
    · -- fast: Lemma 42
      exact (lem42_fast_lock_clears_conflicting_locks_upTo M F U) S A x R GST s e.B v w n' E hNet hSkew hRedeliver
        Sy hΔs hRoots' hParent hGSTv (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hwF hv₀ hw₀
        hCU hFast kV hkV hFw n'' hRevoke e' he'
    · -- slow: through the slot of each entry `w`'s revocation reads
      obtain ⟨e_w, he_w, hlive_w, -, he'w, -⟩ :=
        GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved hs1 hRevoke e' he'
      have hlt_w : ((M.voteTime S.C (s + 1) : ℕ) : Int) < e_w.d :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hlive_w |>.1
      rw [hti_w] at he_w
      obtain ⟨s', hd_w, hc_w, hlw', ⟨τw, hτw, hτwle⟩, h39w⟩ :=
        (lem39_lock_entry_provenance M F U) S A x R kV w e_w E he_w
      rw [(tickStep_eq_of_lbl M) x E hlw'] at hc_w
      -- `s' < s`: `w`'s tick to the support cutoff of slot `s' + 1` is before its tick to the vote time of slot
      -- `s + 1`, so to a smaller clock value (`clock_mono`, `tick_unique`)
      have hcv : M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s + 1) := by
        generalize x.tickStep w (M.supportCutoff S.C (s' + 1)) = kc at hc_w hlw'
        have hbc := E.clock_mono _ kV w _ _ hc_w (E.not_mem_corrupted_of_tick hkV) (Or.inl hlw') (Or.inl hkV)
        rcases Nat.lt_or_ge (M.supportCutoff S.C (s' + 1)) (M.voteTime S.C (s + 1)) with h | h
        · exact h
        · have hbb : M.supportCutoff S.C (s' + 1) = M.voteTime S.C (s + 1) := le_antisymm hbc h
          rw [hbb] at hlw'
          exact absurd (E.tick_unique _ kV w _ hlw' hkV) (by omega)
      have hlt : s' < s := by
        by_contra h
        have h' : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s' + 1) := by
          rcases Nat.lt_or_eq_of_le (show s + 1 ≤ s' + 1 by omega) with h'' | h''
          · exact le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S h'')
          · rw [h'']
        omega
      -- `s + 1 − k ≤ s'`: `e_w` is live at the vote time of slot `s + 1`
      have hlow : s + 1 - S.C.k ≤ s' := by
        by_cases hkb : S.C.k ≤ s + 1
        · refine (lem41_slot_of_live_entry M F U) S (s + 1 - S.C.k) s' (M.voteTime S.C (s + 1)) e_w hd_w hlt_w ?_
          rw [Nat.sub_add_cancel hkb]
        · omega
      -- `e`'s block is `v`'s saved confirmation of slot `s'` or an ancestor of it
      obtain ⟨-, hj⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.lem37_slow_test_saved_confirmations F) S.C _ s e.B hSlow
      obtain ⟨Cj, hCj, -, hBj⟩ := hj s' hlow hlt
      rw [hti_v] at hCj
      obtain ⟨hlt40, hl40, ⟨τ₁, hτ₁, hτ₁le⟩, hS40, -⟩ :=
        (lem40_saved_confirmation_provenance M F U) S A x R k_v v s' Cj E hCj
      obtain ⟨n₁, sent₁, hrun₁, hAw₁, -⟩ :=
        (update_state_of_tick M F U) S A x R s' v E hl40 ⟨τ₁, hτ₁, hτ₁le⟩
      have hU₁ := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n₁ sent₁ hrun₁ hAw₁
      -- `w`'s update of slot `s' + 1` and the confirmation `e_w` traces to
      obtain ⟨nw, sentw, hrunw, hAww, -⟩ :=
        (update_state_of_tick M F U) S A x R s' w E hlw' ⟨τw, hτw, hτwle⟩
      have hU_w := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' w nw sentw hrunw hAww
      obtain ⟨e₀w, -, -, -, -, ⟨C₀w, hC₀w, hB₀w⟩, -, hBw₀, -⟩ := h39w nw sentw hrunw hAww
      -- Lemma 31 at slot `s'`, its windows read off the two duty tests
      have hfrw := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s'
      have hsw := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hlow
      have hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s' := by omega
      have hcb : Δs ≤ M.viewFreeze S.C s' := by
        have := le_max_right (Δ S) Δs
        omega
      obtain ⟨kF₁, hkF₁, -, hwin₁, hv₁₀⟩ :=
        (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hl40 hτ₁ hτ₁le
      obtain ⟨kF₂, hkF₂, -, hwin₂, hv₂₀⟩ :=
        (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hlw' hτw hτwle
      -- the two ticks to the support cutoff of slot `s' + 1` are before the support cutoff of slot `s + 1`
      have hcc : M.supportCutoff S.C (s' + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s + 1) := by
        have hsc' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
        have hvt' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1)
        have hss' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
          (show s' + 1 ≤ s by omega)
        have hsS : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
            (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add,
            Nat.mul_one]
        omega
      have hccR : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcc
      have hR31 : RootsNameBlocksUntil M A x
          (max (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))))
            (x.time (x.tickStep w (M.supportCutoff S.C (s' + 1))))) := by
        refine (RootsNameBlocksUntil.mono M) ?_ hRoots
        have h1 := (E.tick_active _ v _ hl40).2.2
        have h2 := (E.tick_active _ w _ hlw').2.2
        exact max_le (by linarith) (by linarith)
      -- Lemma 31's delivery premises are due by the support cutoff of slot `s'` plus one delay, at most
      -- the support cutoff of slot `s + 1`
      have hb31 : M.supportCutoff S.C s' + Δ S ≤ M.supportCutoff S.C (s + 1) := by
        have h0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
        have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
        have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
        have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1)
        have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
        have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 1)
        rw [Nat.mul_add, Nat.mul_one] at h5
        omega
      have hcomp := (lem31_saved_confirmations_compatible_upTo M F U) S A x R GST s' v w n₁ nw Cj C₀w (E.mono hb31)
        hNet hSkew hRedeliver (Sy.mono hb31) hGSTw kF₁ hkF₁ hwin₁ hv₁₀ kF₂ hkF₂ hwin₂ hv₂₀ _ hl40 _ hlw' hR31
        hU₁ (hS40 n₁ sent₁ hrun₁ hAw₁) hU_w hC₀w
      exact GoldilocksCorrectness.Proofs.Routines.compatible_symm'
        (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both hBj
        (ancestorEq_trans he'w (ancestorEq_trans hBw₀ hB₀w)) hcomp)
  -- step 4: Lemma 21b, which keeps the block the vote names
  exact (lem21b_goldfish_vote_extends_eligible_block_held_upTo M F U) S A x R GST s Sup e.B v w vote E hNet hSkew hRedeliver
    Sy hΔs hRoots' hParent hGSTv (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hwF hv₀ hw₀ hSup hElig
    hF2 hF3 hLocks ⟨kV, hkV, hsV⟩

end GoldilocksCorrectness.Record.Proofs.Executions

