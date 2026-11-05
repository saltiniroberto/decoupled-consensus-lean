module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89FastLineUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89FastLineUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 36b read at an ancestor of the
saved confirmation, with the delivery premises up to a bound. The page's routine-level theorems are
the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt hMax)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl tick_attest_awake
  awakeSince_of_record_awake create_attestation_cases)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A4, a confirmed block's ancestor is extended by the next slot's honest votes, the held
form.** The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: Lemma 36b's proof (`lem36b_confirmed_block_extended_held`), with Lemma 36 at the
ancestor `L` of the saved confirmation `C'` in place of `C'` itself, then Lemma 21 in the held form
at `L`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `L`: `C'` or an ancestor of it; `v`: the validator whose update
  saves `C'`; `w`: the voter of slot `s + 1`; `n'`: a node state the update can leave (the landed
  update's answer, as Lemma 36b's twin reads it); `vote`: `w`'s Goldfish vote.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: the proof reads Lemma 21 in the held form at
slot `s`, whose bound, the latest real time of `w`'s tick to the view freeze of slot `s`, is at most that
time.

Read at the validators' own ticks (T-RC8-2): `v` from `tStart` up to its tick to the support cutoff of
slot `s + 1`, `w` from `tStartW` up to its tick to the view freeze of slot `s`, the holders `v` (`hv₀`)
and `w` (`hw₀`) for the sync delay after the sync fact's read times.

Restated with the delivery premises up to `M.supportCutoff S.C (s + 1)`: Lemma 21b at slot `s` reads
deliveries due by then (`lem21b_goldfish_vote_extends_eligible_block_held_upTo`).

Read aloud: the next slot's honest votes extend every ancestor of a confirmation whose frame and
lock conditions hold at the voter, with the delivery premises up to the bound. -/
theorem lem36c_fast_ancestor_extended_held_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (C' L : Block V) (v w : V) (n' : M.N)
    (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    -- `v` is active at every step whose real time is in the sync delay after the view freeze of slot `s`
    -- less one delay or one sync delay, whichever is longer (the holder's window,, T-RC8-2)
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v`'s update of slot `s + 1` runs at its tick to the support cutoff of slot `s + 1` (, T-RC8-2)
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hSaved : n'.savedConfirmation s = some C')
    (hLC : L.AncestorEq C')
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible L = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq L →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
        (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          L.AncestorEq W)
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible L = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ L.AncestorEq H_w := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hm6 : max (6 * Δ S) Δs ≥ 6 * Δ S := le_max_left _ _
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from that cutoff less `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead) (by linarith)
  have hti_v : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hRootsΦv : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti_v]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  -- Lemma 36 at `L`, an ancestor of `C'` or `C'` itself, on `v`'s pool at its tick to the support cutoff of
  -- slot `s + 1`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' L hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti_v]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v hwinv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) hLC
  simp only [Nat.add_sub_cancel] at hSup hElig
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    have : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
      have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by omega
      rw [h]; push_cast; ring
    rw [this]
    linarith
  -- Lemma 21, the held form, at `L`
  exact (lem21b_goldfish_vote_extends_eligible_block_held_upTo M F U) S A x R GST s Sup L v w vote E hNet hSkew hRedeliver Sy hΔs
    hRoots' hParent hGST tStart htStart hv tStartW htStartW hw hv₀ hw₀ hSup hElig hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Record.Proofs.Executions

