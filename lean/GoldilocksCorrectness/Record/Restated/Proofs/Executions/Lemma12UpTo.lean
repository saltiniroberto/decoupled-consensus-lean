module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteHeadKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.VoteDeliveryUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma12UpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma12UpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 12 with the delivery premises up to
a bound, an honest early vote held, resolved and unique in the node state of every validator awake
and honest from the vote time to the support cutoff. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (tau_eq_ok_some)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ResolvesAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  blockWithRoot_eq_ok find?_eq_some dre_bind_ok liftM_some occurrenceBefore_eq_true_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 12 at any later time, `w` active at steps from the sync fact's read time, the delivery premises up to the
support cutoff.** `lem12_honest_vote_delivered_until_upTo` with `w`'s activity given as `w`'s tick `kR` to the support cutoff of slot `s` and
`w` active at every step from the real time `supportCutoff s − max (2 · Δ S) Δs` up to `kR`, the form
`lem12_vote_held_at_tick_core` reads, in place of `w`'s tick-window reader from a start `tStartW` more than both clock
bounds before that read time. A caller holding `w` active at every real time from before the read time to after
the tick (a real-time window) supplies it at every slot, also when no natural `tStartW` exists (the read time at most
both clock bounds).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: an honest early vote of slot `s` is held, resolved and unique at every later tick of a validator active
at every step from the sync fact's read time up to its tick to the support cutoff, the delivery premises read up to
the support cutoff. -/
theorem lem12_honest_vote_delivered_until_of_steps_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `w` ticks at `kc` to a clock value `c` at least the support cutoff of slot `s`
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR` (the core's form)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w c) s (H u) u := by
  intro u hu
  obtain ⟨hcomm, hhon, hsend, hHT⟩ := hHs u hu
  obtain ⟨ht₀, ht₀s, hGs, hGv, hcv⟩ := lem12_holder_read_time M F U S s Δs GST hGST
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = (M.voteTime S.C s : ℝ) + Δ S := by
    rw [hcv]; push_cast; ring
  have hGvR : (GST : ℝ) ≤ M.voteTime S.C s := by exact_mod_cast hGv
  refine (lem12_vote_held_at_tick_core M F U) S A x R s c u w (H u) E hSkew hRedeliver ?_ Sy
    (Nat.cast_nonneg _) _ ht₀ ?_ hRoots hParent hOwner hc kc hkc hcomm hhon hsend hHT (hHold u hu) ?_ (hF u hu)
  · intro sm a ha
    have : max a (GST : ℝ) ≤ (M.voteTime S.C s : ℝ) + ΔClockBehind := max_le ha (by linarith)
    have hle : max a (GST : ℝ) + ΔNet ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by rw [hcR]; linarith
    refine ⟨_, if_pos hle, ?_⟩
    rw [hcR]; linarith
  · intro sm
    have hle : max (M.supportCutoff S.C s - max (2 * Δ S) Δs) GST + Δs ≤ M.supportCutoff S.C s := by
      rcases max_cases (M.supportCutoff S.C s - max (2 * Δ S) Δs) GST with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
    exact ⟨_, if_pos hle, hle⟩
  · exact hw

/-- **`lem12_honest_vote_delivered_until_of_steps_upTo` with `w`'s finalized block compatible with every voter's block** (re-check 79 (a),
STOP P2-39). The hypotheses of `lem12_honest_vote_delivered_until_of_steps_upTo`, with `hF` read as compatibility of `w`'s finalized block at
its tick to `c` with each voter's block; the conclusion, for every voter `u` of `Hs`, the clauses of
`lem12_vote_held_at_tick_core_compat`: `w`'s state holds `u`'s vote of slot `s` for the root of `H u`, stamped before the
support cutoff `C.t_ s + 2 · C.Δ`; `H u` is in `w`'s node tree with its slot at most `s` and its block stamp before the
cutoff; and the vote is `u`'s only vote of slot `s` there. The proof is `lem12_honest_vote_delivered_until_of_steps_upTo`'s, over the compat core.

The variables: as `lem12_honest_vote_delivered_until_of_steps_upTo`'s.

Read aloud: every voter's honest early vote of slot `s` is held and stamped before the support cutoff, for a block `w`
holds, as the voter's only vote of the slot, at every later tick of `w` whose finalized block is compatible with that
voter's block. -/
theorem lem12_honest_vote_delivered_until_of_steps_upTo_compat (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `w` ticks at `kc` to a clock value `c` at least the support cutoff of slot `s`
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR` (the core's form)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- `w`'s finalized block at its tick to `c` is compatible with every voter's block
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.compatible (H u) = true) :
    ∀ u ∈ Hs, GoldfishVote.mk u s (H u).root ∈ M.votesHeldSet (x.tickInput w c) s ∧
      (∃ τ : Stamp, (x.tickInput w c).voteStamp (GoldfishVote.mk u s (H u).root) = some τ ∧
        τ < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      H u ∈ (x.tickInput w c).tree ∧ (H u).slot ≤ s ∧
      (∃ τH : Stamp, (x.tickInput w c).blockStamp (H u) = some τH ∧
        τH < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ M.votesHeldSet (x.tickInput w c) s, vote'.val_index = u →
        vote' = GoldfishVote.mk u s (H u).root := by
  intro u hu
  obtain ⟨hcomm, hhon, hsend, hHT⟩ := hHs u hu
  obtain ⟨ht₀, ht₀s, hGs, hGv, hcv⟩ := lem12_holder_read_time M F U S s Δs GST hGST
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = (M.voteTime S.C s : ℝ) + Δ S := by
    rw [hcv]; push_cast; ring
  have hGvR : (GST : ℝ) ≤ M.voteTime S.C s := by exact_mod_cast hGv
  refine (lem12_vote_held_at_tick_core_compat M F U) S A x R s c u w (H u) E hSkew hRedeliver ?_ Sy
    (Nat.cast_nonneg _) _ ht₀ ?_ hRoots hParent hOwner hc kc hkc hcomm hhon hsend hHT (hHold u hu) ?_ (hF u hu)
  · intro sm a ha
    have : max a (GST : ℝ) ≤ (M.voteTime S.C s : ℝ) + ΔClockBehind := max_le ha (by linarith)
    have hle : max a (GST : ℝ) + ΔNet ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by rw [hcR]; linarith
    refine ⟨_, if_pos hle, ?_⟩
    rw [hcR]; linarith
  · intro sm
    have hle : max (M.supportCutoff S.C s - max (2 * Δ S) Δs) GST + Δs ≤ M.supportCutoff S.C s := by
      rcases max_cases (M.supportCutoff S.C s - max (2 * Δ S) Δs) GST with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
    exact ⟨_, if_pos hle, hle⟩
  · exact hw


/-- The delivery lemma at any time `t₃` from the support cutoff of slot `s` on: `lem12`'s proof with
`t₃` in place of the vote time of slot `s + 1`, which it reads only through
`M.supportCutoff S.C s ≤ t₃` and `u`'s honesty up to it. `hw` covers only slot `s`'s vote time to
its support cutoff, the window the proof uses. Its
reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean`. Roots name blocks until
the real time of `w`'s own tick to `M.supportCutoff S.C s`: the proof takes `H u` as held by `w` at a delivery before the support
cutoff (`lem12_vote_held_at_tick_core`).

Restated with the delivery premises up to `M.supportCutoff S.C s`: the votes and blocks of slot `s`
reach `w` by then.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an honest early vote of slot `s` is held, resolved and unique in the node state before
any `t₃` from the support cutoff on, of every validator awake and honest from the vote time to the
support cutoff, the delivery premises read up to the support cutoff.

Every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`,
`t₀ := supportCutoff s − max (2 · Δ S) Δs`, the time the sync fact is read at: a block `H u` the voter held before `t₀` reaches `w` through the sync fact
read at `t₀` (`lem12_vote_held_at_tick_core`). -/
theorem lem12_honest_vote_delivered_until_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `w` ticks at `kc` to a clock value `c` at least the support cutoff of slot `s`, with no restart of `w`
    -- that loses its memory between its tick to the cutoff and `kc`
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hkeep : ∀ (l t' : ℕ), x.tickStep w (M.supportCutoff S.C s) < l → l < kc →
      x.lbl l ≠ Event.restart w t' false)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from `tStartW`, more than both clock bounds before the earlier of the start of slot `s` and
    -- one delay or one sync delay before the support cutoff, up to its own tick to the support cutoff of slot `s`
    -- (T-RC6-1:'s reader,'s bound)
    (tStartW : ℤ)
    (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.supportCutoff S.C s))
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w c) s (H u) u := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  exact (lem12_honest_vote_delivered_until_of_steps_upTo M F U) S A x R GST s c Hs H w E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hOwner hGST hc kc hkc hHs hHold
    ((tick_window_of_activeThroughoutToTick_int M) x R E hw (by push_cast at htStartW ⊢; linarith)) hF

/-- The delivery lemma. `hw` covers only slot `s`'s vote time to its support cutoff, the window
the proof uses. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean`. Roots name blocks until
the real time of `w`'s own tick to `M.supportCutoff S.C s`: `lem12_honest_vote_delivered_until`'s bound.

Restated with the delivery premises up to `M.supportCutoff S.C s`:
`lem12_honest_vote_delivered_until_upTo`'s bound.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an honest early vote of slot `s` is held, resolved and unique in the node state before
the next vote time of every validator awake and honest from the vote time to the support cutoff, the
delivery premises read up to the support cutoff.

Every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`,
`t₀ := supportCutoff s − max (2 · Δ S) Δs`, the time the sync fact is read at: a block `H u` the voter held before `t₀` reaches `w` through the sync fact
read at `t₀` (`lem12_vote_held_at_tick_core`). -/
theorem lem12_honest_vote_delivered_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corruptedAtTime x (M.voteTime S.C (s + 1)) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from `tStartW`, more than both clock bounds before the earlier of the start of slot `s` and
    -- one delay or one sync delay before the support cutoff, up to its own tick to the support cutoff of slot `s`
    -- (T-RC6-1:'s reader,'s bound)
    (tStartW : ℤ)
    (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.supportCutoff S.C s))
    (hF : ∀ u ∈ Hs, (x.tickInput w (M.supportCutoff S.C s)).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w (M.supportCutoff S.C s)) s (H u) u := by
  -- `w`'s tick `kc` to the support cutoff of slot `s`, at a real time at most the vote time of slot `s + 1`
  obtain ⟨kc, hkc, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw
    (behind_lt_of_ahead_behind_lt_int M x E htStartW)
  have hts : x.tickStep w (M.supportCutoff S.C s) = kc := (tickStep_eq_of_lbl M) x E hkc
  have hkct := (E.tick_active kc w _ hkc).2.2
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S s
  have hvsc : M.voteTime S.C (s + 1) = M.supportCutoff S.C s + 3 * Δ S := by omega
  have hkcT : x.time kc ≤ ((M.voteTime S.C (s + 1) : ℕ) : ℝ) := by
    rw [hvsc]; push_cast; linarith [E.ahead_nonneg]
  exact (lem12_honest_vote_delivered_until_upTo M F U) S A x R GST s (M.supportCutoff S.C s) Hs H w E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hOwner hGST le_rfl kc hkc (fun l t' h3 h4 => absurd h4 (by omega))
    (fun u hu => ⟨(hHs u hu).1, (Activity.not_mem_corruptedAtTime.1 (hHs u hu).2.1) kc hkcT, (hHs u hu).2.2⟩)
    hHold tStartW htStartW hw hF

end GoldilocksCorrectness.Record.Proofs.Executions

