module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma27
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma27
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma27UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma27UpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the lock entries compatible with a block
half the voters support, the confirmation of a voter majority's block, and Lemma 27, an honest
confirmation update confirms a voter majority's block, each with the delivery premises up to a
bound. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_cast supportCutoff_eq voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes
  votesOnceInPoolFor_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (earlyVoteOnceFor_of_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor EarlyVoteOnceFor)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Under the half condition, every lock entry live at `t₃` that `v`'s revocation of slot `s + 1`
leaves is on a block compatible with `B`, when every `u ∈ Hs` is an honest member of the slot-`s`
committee that sent at the vote time of slot `s` a vote for `B`, a block it holds, and `v` is awake
and honest from the duty window's start of slot `s + 1` to `t₂`, with its finalized block before
`t₂` an ancestor of `B` or `B`.

Why: by Lemma 12 at `t₃` every `u ∈ Hs` has its vote for `B` in `v`'s pool as its only slot-`s`
vote, and Lemma 5 with the half condition makes every entry of the revocation's answer compatible
with `B`.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `v` by
then (`lem12_honest_vote_delivered_until_upTo`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: every live lock entry that an outcome of `v`'s tick at the vote time of slot `s + 1`
leaves, from a state awake for the slot, is compatible with `B`, when the honest voters of `Hs` for
`B` are at least half of the slot-`s` committee. -/
theorem lock_entries_compatible_of_half_upTo (U : UniformSchedule M.toSlotLayout)
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
    -- the slot-`s` committee is at most twice `Hs`
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF1 : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) :
    ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro n' sent hrun hAwake e he _
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  obtain ⟨hv0, hc0, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hv1, hc1, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hm1 := le_max_left (Δ S) Δs
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hkmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by exact_mod_cast hkm
  have hΔ1R : ((Δ S : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm1
  have hvR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by
    rw [hv1, hs1, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hc1, hs1, hss]; push_cast; ring
  -- the revocation the outcome ran, from the tick input (the field `tick_voteTime_locks` of `F.tk2`)
  have hsl : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.tickStep v (M.voteTime S.C (s + 1))) v).1
  have hRevoke := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n' sent hrun hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout
      F.sched U) S (s + 1))
    (by rw [hsl]; exact hAwake)
  rw [hsl] at hRevoke
  -- `v`'s ticks to the vote time and to the support cutoff of slot `s + 1`
  have hv' : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.voteTime S.C (s + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hv (by omega)
      (by rw [hdw, hvR]; linarith) (by rw [hvR, hc1R]; linarith)
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hv'
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkc2 := (E.tick_active kc v _ hkc).2.2
  have hk'1 := (E.tick_active k' v _ hk').2.1
  have hkck' : kc ≤ k' := ((lt_of_time_lt M) x R (by rw [hvR] at hkc2; rw [hc1R] at hk'1; linarith)).le
  have hkcs : x.tickStep v (M.voteTime S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  have hk's : x.tickStep v (M.supportCutoff S.C (s + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  -- the finalized block at the tick input to the vote time is an ancestor of `B`
  have hF : (x.tickInput v (M.voteTime S.C (s + 1))).finalized.AncestorEq B := by
    have h := (F_ancestorEq_of_le M F) x R E v hkck'
    unfold Trace.tickInput at hF1 ⊢
    rw [hkcs]; rw [hk's] at hF1
    exact ancestorEq_trans h hF1
  -- the votes of `Hs`, held at that tick input (Lemma 12 in the step form)
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) s B u :=
    (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST s (M.voteTime S.C (s + 1)) Hs (fun _ => B) v
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) kc hkc
      (fun u hu => ⟨(hHs u hu).1, fun hc => (hHs u hu).2.1 (by rw [hk's]; exact E.corrupted_mono kc k' hkck' hc),
        (hHs u hu).2.2.1, (hHs u hu).2.2.2⟩)
      hHold ((updater_reader_gives_core_window M F U) x R E hΔs hSkew hv) (fun _ _ => hF)
  refine ((GoldilocksCorrectness.Record.Statements.Routines.lem5_revoke_locks_entries_compatible F) B Hs
    (Nat.le_add_left 1 s) (fun u hu => ?_) hHalf hRevoke e he).2
  obtain ⟨hp, -, hBΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u hu
  exact ⟨_, hp, rfl, ⟨y, hy⟩, ⟨B, hBΦ, rfl, ancestorEq_refl B⟩, huniq⟩

/-- `v`'s confirmation update at `t₂` saves `B`, advances the confirmed tip with `B`, and, under
the half condition, makes `B` fast and adds the lock entry on `B`, under Lemma 27's hypotheses:
the voter bound on `v`'s slot-`s` pool before `t₂` and the lock condition on `v`'s revocation of
slot `s + 1`.

Why: the proof of Lemma 18 with the voter bound for the committee majority, `hLocks` for Lemma 5,
and Lemmas 25 and 28 for Lemma 8b.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `v` by
then (`lem12_honest_vote_delivered_until_upTo`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: after the support cutoff of slot `s + 1`, `v` has saved `B` as the confirmation of slot
`s` and advanced its confirmed tip with `B`, and, when `Hs` is at least half of the slot-`s`
committee, `B` is a fast block of `v` and `v` holds a lock entry on `B`. -/
theorem confirmation_of_voter_majority_upTo (U : UniformSchedule M.toSlotLayout)
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
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF1 : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    -- the block of every lock entry live at `t₃` that `v`'s revocation leaves is compatible
    -- with `B`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed =
        M.advance (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
          (x.tickInput v (M.supportCutoff S.C (s + 1))).latestConfirmed (some B) ∧
      ((S.P.committee s).card ≤ 2 * Hs.card →
        B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
        (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- step 0: the times
  obtain ⟨hv0, hc0, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hv1, hc1, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hm1 := le_max_left (Δ S) Δs
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hkmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by exact_mod_cast hkm
  have hΔ1R : ((Δ S : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm1
  have hvR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by
    rw [hv1, hs1, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hc1, hs1, hss]; push_cast; ring
  have hslot : ∀ t : ℕ, M.voteTime S.C (s + 1) ≤ t → t ≤ M.supportCutoff S.C (s + 1) →
      M.slot S.C t = s + 1 :=
    fun t h1 h2 => (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  -- step 1: `v`'s ticks to the vote time and to the support cutoff of slot `s + 1`
  have hv' : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.voteTime S.C (s + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hv (by omega)
      (by rw [hdw, hvR]; linarith) (by rw [hvR, hc1R]; linarith)
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hv'
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨hkck', hbetw⟩ := (ticks_between M F) x E v (show M.voteTime S.C (s + 1) < M.supportCutoff S.C (s + 1) by omega)
    hkc hk'
  have hkcs : x.tickStep v (M.voteTime S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  have hk's : x.tickStep v (M.supportCutoff S.C (s + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  have hti₃ : x.tickInput v (M.voteTime S.C (s + 1)) = x.st kc v := by unfold Trace.tickInput; rw [hkcs]
  have hti₂ : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k' v := by unfold Trace.tickInput; rw [hk's]
  -- step 2: the votes of `Hs`, held early at the tick input to the support cutoff (Lemma 12 in the step form)
  have hHeld₂ : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s B u :=
    (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST s (M.supportCutoff S.C (s + 1)) Hs (fun _ => B) v
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) k' hk'
      (fun u hu => ⟨(hHs u hu).1, hk's ▸ (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2⟩)
      hHold ((updater_reader_gives_core_window M F U) x R E hΔs hSkew hv) (fun _ _ => hF1)
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  -- step 3: the tick to the vote time of slot `s + 1`: the outcome the step took, awake for the slot, and the
  -- revocation it ran from the tick input (the field `tick_voteTime_locks_of_core` of `F.tk2`)
  obtain ⟨n₃, sent₃, hok₃, hst₃, -⟩ := R.tick kc v _ hkc
  have hrun₃ : .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
      ((M.voteTime S.C (s + 1) : ℕ) : Int) := by
    rw [hti₃]; exact hok₃
  obtain ⟨τ₃, hτ₃, hτ₃le⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv'
    (by
      have h : ((duty_window_start S.C (s + 1) : ℤ) : ℝ) < ((M.voteTime S.C (s + 1) : ℕ) : ℝ) := by
        rw [hdw, hvR]
        have hk8 : (4 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by linarith
        linarith
      exact_mod_cast h)
  have hAwake₃ : AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) := ⟨τ₃, hτ₃, hτ₃le⟩
  have hsl₃ : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact hslot _ le_rfl (by omega)
  have hInv₃ := (lem11_node_invariantCore_of_run M F S x R (x.tickStep v (M.voteTime S.C (s + 1))) v).1
  have hRevoke := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n₃ sent₃ hrun₃ hInv₃
    (by
      rw [hsl₃]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s + 1))
    (by rw [hsl₃]; exact hAwake₃)
  rw [hsl₃] at hRevoke
  -- step 4: the locks, by the lock condition on that outcome
  have hLocksA' := hLocks n₃ sent₃ hrun₃ hAwake₃
  -- step 5: from the tick to the vote time to the tick to the support cutoff, the lock entries only shrink: every
  -- tick between is to a value strictly between the two, neither a vote time nor a support cutoff of its slot
  have hsub : (x.tickInput v (M.supportCutoff S.C (s + 1))).lockEntries ⊆ n₃.lockEntries := by
    rw [hti₂, ← hst₃]
    refine (lockEntries_subset_of_ticks_off_duty_between M F) x R v (Nat.succ_le_of_lt hkck')
      (fun i h1 h2 t'' hl => ?_)
    obtain ⟨hlo, hhi⟩ := hbetw i (by omega) h2 t'' hl
    have hsl'' : S.C.slot (t'' : Int) = s + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact hslot t'' hlo.le hhi.le
    rw [hsl'', ← (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U),
      ← (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
    constructor <;> intro h <;> omega
  -- step 6: the tick to the support cutoff: the outcome the step took, and the update it ran
  obtain ⟨n₂, sent₂, hrun₂, hAwake₂, hsave, hfast, hlocks, hlatest⟩ :=
    (update_state_of_tick M F U) S A x R s v E hk'
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
        ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
          F.sched U) S (s + 1)))
  have hUpdate := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n₂ sent₂ hrun₂ hAwake₂
  -- step 7: Lemmas 25 and 28 on the update, which reads the tick input; "no live lock vetoes `B`" moves the
  -- liveness of an entry from the support cutoff to the vote time
  have hRoots₂ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti₂]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E k' v
  have hB₂ : B ∈ (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := (hHeld₂ u₀ hu₀).2.2.1
  have hNoVeto : ∀ e ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).lockEntries,
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
    intro e he hlive
    have heA' : e ∈ n₃.lockEntries := hsub he
    refine hLocksA' e heA' ?_
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive ⊢
    have h32 : ((M.voteTime S.C (s + 1) : ℕ) : Int) < ((M.supportCutoff S.C (s + 1) : ℕ) : Int) :=
      Int.ofNat_lt.2 (by omega)
    exact ⟨lt_trans h32 hlive.1,
      GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s) hRevoke e heA'⟩
  have hPathF : ∀ P' : Block V,
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).F.AncestorEq P' →
      P'.AncestorEq B → P' ∈ (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti₂] at hB₂ ⊢
    exact fun P' h1 h2 => (GoldilocksCorrectness.Record.Statements.Executions.frame_path_of_exec M F) S A x R E k' v
      B P' hB₂ h1 h2
  have hHsE : ∀ u ∈ Hs, EarlyVoteOnceFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1)))
      (s + 1 - 1) B u := by
    intro u hu
    obtain ⟨hmem, -, -, hres, huniq⟩ := hHeld₂ u hu
    exact ⟨_, hmem, rfl, rfl, hres, huniq⟩
  have hSlot : ∀ vote ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1),
      vote.slot = s + 1 - 1 := by
    rw [hti₂]
    exact (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k' v s
  have h25 :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem25_update_confirmation_confirms_voter_majority_block F)
      B Hs (Nat.le_add_left 1 s) hRoots₂ hBne
      (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact hF1) hPathF hHsE hSlot hVoters
      hNoVeto hUpdate
  rw [Nat.add_sub_cancel] at h25
  -- step 8: the state after the tick to the support cutoff is the outcome's
  refine ⟨?_, ?_, fun hHalf => ?_⟩
  · rw [hsave]
    exact h25.1
  · rw [hlatest]
    exact h25.2
  · have h28 :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem28_update_confirmation_fast_locks_voter_majority_block F)
        B Hs (Nat.le_add_left 1 s) hRoots₂ hBne
        (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact hF1) hPathF hHsE hSlot
        hVoters hHalf hNoVeto hUpdate
    rw [Nat.add_sub_cancel] at h28
    refine ⟨?_, ?_⟩
    · rw [hfast]
      exact h28.1
    · rw [hlocks]
      exact h28.2

/-- Lemma 27, an honest validator's confirmation update confirms a block a voter majority voted
for. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/FastConfirmationStatements.lean`.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of `confirmation_of_voter_majority`,
which it calls.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the slot-`s` votes reach `v` by
then (`lem12_honest_vote_delivered_until_upTo`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: after the support cutoff of slot `s + 1`, `v` has saved `B` as the confirmation of slot
`s` and advanced its confirmed tip with `B`, when the honest voters of `Hs` for `B` are more than
half of the voters in `v`'s pool. -/
theorem lem27_update_confirmation_confirms_voter_majority_block_upTo
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
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
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hF1 : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    -- the block of every lock entry live at `t₃` that `v`'s revocation leaves is compatible
    -- with `B`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed =
        M.advance (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
          (x.tickInput v (M.supportCutoff S.C (s + 1))).latestConfirmed (some B) := by
  -- the confirmation update of `v` at its tick to the support cutoff of slot `s + 1` (`confirmation_of_voter_majority`)
  obtain ⟨h1, h2, -⟩ := (confirmation_of_voter_majority_upTo M F U) S A x R GST s Hs B v E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hOwner hGST hHs hHold hVoters hBne hv hF1 hLocks
  exact ⟨h1, h2⟩

end GoldilocksCorrectness.Record.Proofs.Executions

