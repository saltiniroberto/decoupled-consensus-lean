module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteHeadKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncDeliveryBoundary, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/AsyncDeliveryBoundary.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 12 by a later delay
, the honest votes of a slot held, resolved and unique in the node state of a validator awake
and honest on that window. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem slot_mono
  viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_gfVote_cases)

open GoldilocksCorrectness.Proofs.Routines (on_ac_message_eq tau_eq_ok_some)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ResolvesAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
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

section TickCoreUntil

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)

variable {S : Setup V} {A : Activity V}

/-- **The last step before a real time.** For a positive real time `t`, some step `k` is at a real time less
than `t` and the step after it at a real time at least `t` (the time reaches `⌈t⌉₊`: `time_div`).

A proof-page helper: the sync fact `SyncedWithinBy` reads the last step before a real time,
and Lemma 12's per-voter read time is a real time.

The variables:
- `M`: the model; `F`: its facts;
- `R`: the run's facts; `E`: the environment's facts; `t`: the real time.

Read aloud: every positive real time has a last step before it. -/
theorem exists_step_before_real {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℝ} (ht : 0 < t) : ∃ k : ℕ, x.time k < t ∧ t ≤ x.time (k + 1) := by
  classical
  have hex : ∃ i : ℕ, t ≤ x.time i := by
    obtain ⟨i, hi⟩ := E.time_div ⌈t⌉₊
    exact ⟨i, le_trans (Nat.le_ceil t) hi⟩
  have hspec : t ≤ x.time (Nat.find hex) := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, R.time_zero] at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have h := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at h
    exact h
  · rw [Nat.sub_add_cancel hpos]
    exact hspec

/-- **Kit theorem, Lemma 12's core on the window `[t, t + Δ S]`, read at a real time.** The twin of
`lem12_vote_held_at_tick_core` (`Lemma12.lean`) with the receiver's tick to `t + Δ S`, for a `t` from the vote time of
slot `s` on with `t + Δ S` at most the view freeze of slot `s`, in place of its tick to the support cutoff, and the sync
fact read at a real time `t₀` at or before the real time of the voter's tick to the vote time (F-P2-11-3). The voter
`u`, a member of slot `s`'s committee outside the adversary set at `kc`, puts its vote for the root of `Hu` on the wire
at its tick `i` to the vote time of slot `s`, holding `Hu` there; `w` ticks at `kR` to `t + Δ S`, active at every step
from the real time `t₀` up to `kR`, and later at `kc` to a clock value `c`. Then `w`'s state at `kc` holds `u`'s vote,
stamped and resolved before `t + Δ S`, the only vote of `u` of slot `s` there.

Why: as the core. The vote is delivered before `kR` (`delivered`, its deadline `hdl`), found `w`'s clock at the start
of slot `s` (`releaseOf`, its re-delivery premise from `w`'s tick to `t`, at a real time at most `t + ΔClockBehind`,
and `hRedeliver`) and less than `t + Δ S`, inside slot `s` (`htf`), so `w` admits it. `Hu` entered `u`'s tree at a
step `ie` at which `u` relayed it: from `t₀` on, the relay is delivered before `kR`; before `t₀`, `u` holds and serves
`Hu` at the last step before `t₀` (`exists_step_before_real`) and stays active up to `⌈t₀⌉₊ + ΔHolderOnline`
(`hHold`), so the sync fact `Sy` delivers it before `kR` or `w` holds it already.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its facts and the environment's facts with the
  deadline `deadline`; `Sy`: the sync fact with the sync deadline `sync` and the holder's online time
  `ΔHolderOnline`; `s`: the slot; `t`: the window's start; `c`: the later clock value; `u`: the voter; `w`: the
  receiver; `Hu`: the vote's block; `t₀`: the real time the sync fact is read at; `kR`, `kc`: `w`'s ticks.

Read aloud: an honest early vote of slot `s`, whose block its voter keeps serving from `t₀` to `ΔHolderOnline` after
the clock value `⌈t₀⌉₊`, is held, stamped and resolved before `t + Δ S`, and unique, in the state of every later tick
of a validator active from `t₀` up to its tick to `t + Δ S`. -/
theorem lem12_vote_held_at_tick_core_until (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s t c : ℕ) (u w : V) (Hu : Block V)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (htv : M.voteTime S.C s ≤ t) (htf : t + Δ S ≤ M.viewFreeze S.C s)
    -- a message on the wire at a real time at most `ΔClockBehind` after the vote time of slot `s` is due
    -- `ΔClockAhead` before `t + Δ S` or earlier
    (hdl : ∀ (sm : SignedMsg V (NamedObject V)) (a : ℝ), a ≤ (M.voteTime S.C s : ℝ) + ΔClockBehind →
      ∃ d : ℝ, deadline sm a = some d ∧ d + ΔClockAhead ≤ ((t + Δ S : ℕ) : ℝ))
    {sync : V → SignedMsg V (NamedObject V) → ℕ → Option ℕ} {ΔHolderOnline : ℝ}
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy A x (servesMin M S.C) acObject
      (releaseOf M S.C) ΔRedeliver sync ΔHolderOnline)
    (hHO : 0 ≤ ΔHolderOnline)
    -- the sync fact is read at the real time `t₀`, at least `ΔClockAhead` before `t` and at or before the real time
    -- of `u`'s tick to the vote time of slot `s`, with a deadline for `w` at most `t + Δ S`
    (t₀ : ℝ) (ht₀ : t₀ + ΔClockAhead ≤ t) (ht₀i : t₀ ≤ x.time (x.tickStep u (M.voteTime S.C s)))
    (hsync : ∀ sm, ∃ d : ℕ, sync w sm ⌈t₀⌉₊ = some d ∧ d ≤ t + Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (t + Δ S))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hc : t + Δ S ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hcomm : u ∈ S.P.committee s) (hu : u ∉ A.corrupted kc)
    (hsend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
      (⟨u, NamedObject.gfVote (GoldfishVote.mk u s Hu.root)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hHT : Hu ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- the voter is active in every configuration in force at a real time of `[t₀, ⌈t₀⌉₊ + ΔHolderOnline]`
    (hHold : u ∈ A.activeThroughout x t₀ ((⌈t₀⌉₊ : ℝ) + ΔHolderOnline))
    -- `w` ticks to `t + Δ S` at `kR`, active at every step from the real time `t₀` up to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (t + Δ S) ∧
      ∀ j : ℕ, t₀ ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF : (x.tickInput w c).finalized.AncestorEq Hu) :
    HeldEarlyVoteAt M (x.tickInput w c) (((t + Δ S : ℕ) : Int)) s Hu u := by
  classical
  obtain ⟨i, hl, hsent⟩ := hsend
  obtain ⟨kR, hkR, hwin⟩ := hw
  rw [(tickStep_eq_of_lbl M) x E hkR] at hRoots
  rw [(tickStep_eq_of_lbl M) x E hl] at ht₀i
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the slot layout
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hvf : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hssn : ∀ n : ℕ, M.slotStart S.C n = 4 * Δ S * n := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [hssn, hssn, Nat.mul_add, Nat.mul_one]
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslot₀ : S.C.slot ((M.slotStart S.C s : ℕ) : Int) = s :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S le_rfl
      (by omega)
  have hslotv : S.C.slot ((M.voteTime S.C s : ℕ) : Int) = s :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hslotf : S.C.slot ((M.viewFreeze S.C s : ℕ) : Int) = s :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have htvR : ((M.voteTime S.C s : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast htv
  have htcR : (((t + Δ S : ℕ)) : ℝ) = (t : ℝ) + Δ S := by push_cast; ring
  -- the real times of `u`'s tick `i` and of `w`'s tick `kR`
  obtain ⟨⟨hTi0, hTi⟩, hTi10, hTi1⟩ := (time_of_lbl_tick M) x R E hl
  have hkRt := (E.tick_active kR w _ hkR).2
  rw [htcR] at hkRt
  have hik : i < kR := by
    by_contra hcon
    have := htime (show kR ≤ i by omega)
    linarith [hkRt.1]
  have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  -- `kR` comes no later than `kc`
  have hRc : kR ≤ kc := by
    by_contra hcon
    have hle := E.clock_mono kc kR w c (t + Δ S) (by omega) hwkR (Or.inl hkc) (Or.inl hkR)
    have hcc : c = t + Δ S := le_antisymm hle hc
    rw [hcc] at hkc
    exact absurd (E.tick_unique kc kR w _ hkc hkR) (by omega)
  have huj : ∀ j, j ≤ kc → u ∉ A.corrupted j := fun j hj h => hu (E.corrupted_mono j kc hj h)
  have hti_w : x.tickInput w c = x.st kc w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkc]
  have hti_u : x.tickInput u (M.voteTime S.C s) = x.st i u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]
  rw [hti_w] at hF ⊢
  rw [hti_u] at hHT
  -- `w`'s tick `k₂` to `t`, before `kR`
  obtain ⟨k₂, hk₂, -, hk₂1⟩ := E.tick_of_active t (by omega) w fun j h1 h2 => by
    refine hwin j (by linarith) ?_
    by_contra hcon
    have := htime (show kR ≤ j by omega)
    linarith [hkRt.1]
  -- the re-delivery premise, for every release clock value at most `t`
  have hprem : ∀ (r j₀ k₁ t₁ : ℕ), r ≤ t → ¬ x.ReactedAtLeast j₀ w r → j₀ < k₁ →
      x.lbl k₁ = Event.tick w t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kR := by
    intro r j₀ k₁ t₁ hr hnr hjk₁ hlk₁ hfirst
    have hj₀k₂ : j₀ < k₂ := by
      by_contra hcon
      exact hnr ⟨k₂, by omega, _, hr, Or.inl hk₂⟩
    have hk₁k₂ : k₁ ≤ k₂ := by
      by_contra hcon
      have := hfirst k₂ _ hj₀k₂ (by omega) hk₂
      omega
    have h1 := htime hk₁k₂
    rw [R.time_keep k₁ (by rw [hlk₁]; exact nofun)]
    linarith [hkRt.1]
  -- `w`'s clock value at `kR` is less than `t + Δ S`
  have hcvR : x.clockValue kR w < t + Δ S :=
    clockValue_lt_of_tick_of_active M F E hkR (by omega) fun j hj hjk => hwin j (by push_cast at hj; linarith) hjk
  have hcvle : ∀ j, j ≤ kR → x.clockValue j w < t + Δ S := fun j hj =>
    lt_of_le_of_lt (E.clockValue_mono hj hwkR) hcvR
  -- the vote: delivered before `kR`, admitted
  obtain ⟨dv, hdv, hdvle⟩ := hdl ⟨u, NamedObject.gfVote (GoldfishVote.mk u s Hu.root)⟩ (x.time (i + 1)) hTi1
  rw [htcR] at hdvle
  obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered i kR w
    ⟨u, NamedObject.gfVote (GoldfishVote.mk u s Hu.root)⟩ _ dv ⟨hsent, hui⟩
    (show acObject (NamedObject.gfVote (GoldfishVote.mk u s Hu.root)) from trivial) hkR hik
    (fun j h1 h2 => hwin j (by linarith [htime h1, htime (Nat.le_succ i)]) h2) hdv (by linarith [hkRt.1])
    (fun r j₀ k₁ t₁ hrel _ _ hnr hjk₁ _ hlk₁ _ hfirst => hprem r j₀ k₁ t₁
      (by rw [← Option.some.inj hrel]; show M.slotStart S.C s ≤ _; omega) hnr hjk₁ hlk₁ hfirst)
  have hreact : x.ReactedAtLeast j w (M.slotStart S.C s) := hadm _ rfl (by omega)
  obtain ⟨hwj, hstep⟩ := (deliver_step_state M F) x R E hlj
  have hwjc : w ∉ A.corrupted j := Activity.not_mem_corrupted_of_mem_active hwj
  have hge := (le_clockValue_of_reactedAtLeast M F) E hlj hwjc hreact
  have hlt := hcvle j hjk.le
  have hclock := (clock_eq_clockValue M F) x R j w
  have hs2 : (GoldfishVote.mk u s Hu.root).slot ≤ S.C.slot (x.st j w).t := by
    rw [hclock]
    show s ≤ _
    rw [← hslot₀]
    exact GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hge)
  have hs1 : S.C.slot (x.st j w).t ≤ (GoldfishVote.mk u s Hu.root).slot + 1 := by
    have hjf : x.clockValue j w ≤ M.viewFreeze S.C s := by omega
    have : S.C.slot (x.st j w).t ≤ s := by
      rw [hclock, ← hslotf]
      exact GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hjf)
    exact Nat.le_succ_of_le this
  have hvoteR : GoldfishVote.mk u s Hu.root ∈ M.votesHeldSet (x.st kR w) s := by
    rcases F.rcv.receive_gfVote_cases S.C S.P S.X (x.st j w) (GoldfishVote.mk u s Hu.root) hs1 hs2 hcomm
      with hin | heqv
    · rw [← hstep] at hin
      exact (pool_mono M F) x R E w (show j + 1 ≤ kR by omega) s hin
    · obtain ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.two_votes_of_equivocates M F) heqv
      exact absurd ((unique_vote_of_owner_at M F R) E hOwner (huj j (by omega)) h₁ h₂ hi₁ hi₂) hne
  have hvote₃ : GoldfishVote.mk u s Hu.root ∈ M.votesHeldSet (x.st kc w) s :=
    (pool_mono M F) x R E w hRc s hvoteR
  -- `Hu` is in `w`'s tree at `kR`
  have hcompatR : (x.st kR w).finalized.compatible Hu = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E w hRc) hF))
  have hcvi : x.clockValue i u ≤ M.voteTime S.C s := E.clockValue_le_of_set hui (Or.inl hl)
  have hHslot : Hu.slot ≤ s := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E hui hHT
    rw [← hslotv]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hcvi))
  have hrb : M.slotStart S.C Hu.slot ≤ M.slotStart S.C s := by
    rw [hssn, hssn]; exact Nat.mul_le_mul_left _ hHslot
  have hTR : ∀ j', j' < kR → x.time j' ≤ x.time kR := fun j' hj' => htime hj'.le
  have hTi' : x.time i ≤ x.time kR := hTR i hik
  have hblock : Hu ∈ (x.st kR w).tree := by
    by_cases hg : Hu = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hHT hg
    by_cases hlate : t₀ ≤ x.time (ie + 1)
    · -- `u` relayed `Hu` from `t₀` on: the relay is delivered before `kR`
      obtain ⟨d, hd, hdle⟩ := hdl ⟨u, NamedObject.block Hu⟩ (x.time (ie + 1))
        (le_trans (htime (show ie + 1 ≤ i by omega)) hTi)
      rw [htcR] at hdle
      obtain ⟨j', -, hjk', hlj', hadm', -⟩ := E.delivered ie kR w ⟨u, NamedObject.block Hu⟩ _ d
        ⟨hsende, hhone⟩ (show acObject (NamedObject.block Hu) from trivial) hkR (by omega)
        (fun j h1 h2 => hwin j (le_trans hlate (htime h1)) h2) hd (by linarith [hkRt.1])
        (fun r j₀ k₁ t₁ hrel _ _ hnr hjk₁ _ hlk₁ _ hfirst => hprem r j₀ k₁ t₁
          (by rw [← Option.some.inj hrel]; show M.slotStart S.C Hu.slot ≤ _; omega) hnr hjk₁ hlk₁ hfirst)
      exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hui hTi' hHT hlj' (hTR j' hjk')
        (hadm' _ rfl (by omega)) hjk' hwkR hcompatR
    · -- `u` held `Hu` before `t₀`: the sync fact at `t₀`
      push_neg at hlate
      have h0 : (0 : ℝ) ≤ x.time (ie + 1) := by rw [← R.time_zero]; exact htime (Nat.zero_le _)
      obtain ⟨kb, hk1, hk2⟩ := (exists_step_before_real M F) R E (lt_of_le_of_lt h0 hlate)
      have hiek : ie < kb := by
        have := (lt_of_time_lt M) x R (show x.time (ie + 1) < x.time (kb + 1) by linarith)
        omega
      have hki : kb < i := (lt_of_time_lt M) x R (by linarith)
      have hceil := Nat.le_ceil t₀
      have huk : u ∈ A.active kb :=
        Activity.mem_activeThroughout.1 hHold _ (by linarith) hk2
      have hcomp_i : (x.st i u).finalized.compatible Hu = true := by
        have h := (vote_head_compatible_of_held M F U) x R E s u Hu ⟨i, hl, hsent⟩
          (by rw [hti_u]; exact hHT)
        rw [hti_u] at h
        exact h
      have hserve : servesMin M S.C (x.st kb u) (x.clockValue kb u) (NamedObject.block Hu) :=
        ⟨(mem_T_mono M F) x R E u (show ie + 1 ≤ kb by omega) hie1,
          GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
            ((F_ancestorEq_of_le M F) x R E u hki.le) hcomp_i, hg⟩
      obtain ⟨d, hd, hdle⟩ := hsync ⟨u, NamedObject.block Hu⟩
      rcases Sy t₀ kb u w (NamedObject.block Hu) d (t + Δ S) kR hk1 hk2 huk hserve trivial
          (fun j h1 h2 => Activity.mem_activeThroughout.1 hHold j h2 (le_trans h1 (htime (Nat.le_succ j))))
          hd hkR hdle (fun j h1 h2 => hwin j h1 h2)
          (fun r j₀ k₁ t₁ hrel _ hnr hjk₁ _ hlk₁ _ hfirst => hprem r j₀ k₁ t₁
            (by rw [← Option.some.inj hrel]; show M.slotStart S.C Hu.slot ≤ _; omega) hnr hjk₁ hlk₁ hfirst)
        with hwB | ⟨j', k'', hk''j, hk''t, hk''o, hlj', hjk', hadm', -⟩
      · exact (mem_T_mono M F) x R E w (show kb ≤ kR by omega) hwB.1
      · have hk''T : x.time k'' ≤ x.time kR := htime (show k'' ≤ kR by omega)
        exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent (huj k'' (by omega)) hk''T hk''o.1
          hlj' (hTR j' hjk') (hadm' _ rfl (by omega)) hjk' hwkR hcompatR
  have hblock₃ : Hu ∈ (x.st kc w).tree := (mem_T_mono M F) x R E w hRc hblock
  -- the two stamps, clock values of `w` before `kR`
  obtain ⟨e, he, -, -, hτv⟩ := (voteStamp_entry_clock M F) R E hvoteR
  have hτvlt : ((x.st (e + 1) w).t : Stamp) < ((((t + Δ S : ℕ) : Int)) : Stamp) := by
    rw [(clock_eq_clockValue M F) x R (e + 1) w]
    exact_mod_cast hcvle (e + 1) (by omega)
  have hτv₃ : (x.st kc w).voteStamp (GoldfishVote.mk u s Hu.root) = some ((x.st (e + 1) w).t : Stamp) := by
    rw [(voteStamp_kept M F) x R E w hRc hvoteR, hτv]
  obtain ⟨τH, hτH, hτHlt⟩ : ∃ τH : Stamp, (x.st kc w).blockStamp Hu = some τH ∧
      τH < ((((t + Δ S : ℕ) : Int)) : Stamp) := by
    by_cases hg : Hu = Block.genesis
    · rw [hg]
      exact ⟨⊥, (genesis_stamp M F) x R E kc w, WithBot.bot_lt_coe _⟩
    obtain ⟨e', he', -, -, hτ⟩ := (blockStamp_entry_clock M F) R E hblock hg
    refine ⟨_, by rw [(blockStamp_kept M F) x R E w hRc hblock, hτ], ?_⟩
    rw [(clock_eq_clockValue M F) x R (e' + 1) w]
    exact_mod_cast hcvle (e' + 1) (by omega)
  have hHΦ : Hu ∈ (M.fg_to_ac (x.st kc w)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hblock₃, hF⟩
  have htau : ResolvesAt M (x.st kc w) (GoldfishVote.mk u s Hu.root) (max ((x.st (e + 1) w).t : Stamp) τH) :=
    ⟨_, τH, Hu, hτv₃, hHΦ, rfl, hHslot, hτH, rfl⟩
  refine ⟨hvote₃, ⟨_, hτv₃, hτvlt⟩, hHΦ, ⟨_, htau, ?_⟩, ?_⟩
  · exact (occurrenceBefore_eq_true_iff _ _).2 ⟨_, rfl, max_lt hτvlt hτHlt⟩
  · intro vote' hv' hi'
    exact (unique_vote_of_owner_at M F R) E hOwner (huj kc le_rfl) hv' hvote₃ hi' rfl

end TickCoreUntil

/-- **Active from a real time to a real time, from the tick reader.** `mem_activeThroughout_of_mem_activeThroughoutToTick`
with the two ends of the window real numbers: a validator active from `a` up to its tick to `b` is active in every
configuration in force at a real time of `[a', e]` when `a + ΔClockBehind < a'` and `e + ΔClockAhead < b`.

A proof-page helper.

Read aloud: inside the reader's window, by both clock bounds, the validator is active. -/
theorem mem_activeThroughout_of_mem_activeThroughoutToTick_real {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {b : ℕ} {a' e : ℝ} (hv : v ∈ A.activeThroughoutToTick x a b)
    -- the window starts more than `ΔClockBehind` after `a`
    (ha : (a : ℝ) + ΔClockBehind < a')
    -- the window ends more than `ΔClockAhead` before `b`
    (he : e + ΔClockAhead < b) :
    v ∈ A.activeThroughout x a' e := by
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hk'b := (E.tick_active k' v b hk').2.1
  refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => ?_
  have hik' : i < k' := (lt_of_time_lt M) x R (by linarith)
  rcases hcase with h | ⟨k, -, c, hca, hk, h⟩
  · exact h i hik'.le
  · have hka := (E.tick_active k v c hk).2.2
    have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
    refine h i ?_ hik'.le
    by_contra hc
    have := R.time_mono (show i + 1 ≤ k by omega)
    linarith

/-- **Lemma 12 by a later delay.** The proof; the audited statement is in
`Statements/Executions/AsyncDeliveryBoundaryStatements.lean`.

Roots name blocks up to `w`'s own tick to `t + Δ S`: the proof takes `H u` as held by `w` at its delivery,
before that tick.

The variables:
- `M`: the model; `F`: its facts.

Why the receiver's window starts at the earlier of the vote time and the read time `t + Δ S − max (2 * Δ S) Δs`: the voter serves its vote's head at the vote time, and a head read
at a later time may no longer be compatible with the voter's finalized block. So each head is read at
the window's start when that is at or before the vote time, and at the vote time otherwise, and the
receiver is active from the earlier of the two; the deadline `t + Δ S` is unchanged, and the voter's
activity is asked for the sync delay `Δs` from the earlier of the two.

Read aloud: an honest early vote of slot `s` is held, resolved and unique, with the cutoff
`t + Δ S`, in the state `w`'s tick to any clock value `c ≥ t + Δ S` starts from, for every validator active from
the window's read time up to its tick to `t + Δ S`, for any `t` from the vote time on and after `GST`. -/
theorem lem12_honest_vote_delivered_by_until (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (t + Δ S))))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ t + Δ S) (htv : M.voteTime S.C s ≤ t) (htf : t + Δ S ≤ M.viewFreeze S.C s) (hc : t + Δ S ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, ⌈t₀⌉₊ + Δs]`, `t₀` the earlier
    -- of the real time of its own tick to the vote time and the sync fact's read time `t + Δ S − max (2 * Δ S) Δs`
    -- (; per voter since as amended by; the end at the clock value
    -- `⌈t₀⌉₊` the sync fact's holder window reads,, by)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x
      (min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ))
      (((⌈min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) + Δs))
    -- `w` ticks to `t + Δ S` at `kR` and is active at every step from the earlier of each voter's tick to the vote
    -- time and the sync fact's read time up to `kR` (per voter, as amended by)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (t + Δ S) ∧ ∀ u ∈ Hs,
      ∀ j : ℕ, min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j →
        j ≤ kR → w ∈ A.active j)
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteAt M (x.tickInput w c) (((t + Δ S : ℕ) : Int)) s (H u) u := by
  -- Lemma 12's core on the window `[t, t + Δ S]` (`lem12_vote_held_at_tick_core_until`), read for each voter at the
  -- earlier of the real time of its tick to the vote time and `t + Δ S − max (2 * Δ S) Δs` (F-P2-11-3)
  intro u hu
  obtain ⟨hcomm, hhon, hsend, hHT⟩ := hHs u hu
  obtain ⟨kR, hkR, hwin⟩ := hw
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hm3 := le_max_left (2 * Δ S) Δs
  have hm4 := le_max_right (2 * Δ S) Δs
  -- the read time is at least one delay before `t`, and one sync delay after it is at most `t + Δ S`
  have hr1 : t + Δ S - max (2 * Δ S) Δs + Δ S ≤ t := by omega
  have hr2 : t + Δ S - max (2 * Δ S) Δs + Δs ≤ t + Δ S := by omega
  have hGt : GST + Δs ≤ t + Δ S := by omega
  have hGt' : GST ≤ t := by omega
  have hτr : min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ) ≤
      ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ) := min_le_right _ _
  have hceil : ⌈min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ)⌉₊ ≤
      t + Δ S - max (2 * Δ S) Δs := Nat.ceil_le.2 hτr
  have hr1R : ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ) + Δ S ≤ t := by exact_mod_cast hr1
  have htvR : ((M.voteTime S.C s : ℕ) : ℝ) ≤ t := by exact_mod_cast htv
  have hGtR : (GST : ℝ) ≤ t := by exact_mod_cast hGt'
  refine (lem12_vote_held_at_tick_core_until M F U) S A x R s t c u w (H u) E hSkew hRedeliver htv htf ?_ Sy
    (Nat.cast_nonneg _) _ (by linarith) (min_le_left _ _) ?_ hRoots hParent hOwner hc kc hkc hcomm hhon hsend hHT
    (hHold u hu) ⟨kR, hkR, hwin u hu⟩ (hF u hu)
  · intro sm a ha
    refine ⟨_, rfl, ?_⟩
    have : max a (GST : ℝ) ≤ (t : ℝ) + ΔClockBehind := max_le (by linarith) (by linarith)
    push_cast; linarith
  · intro sm
    refine ⟨_, rfl, ?_⟩
    rcases max_cases ⌈min (x.time (x.tickStep u (M.voteTime S.C s))) ((t + Δ S - max (2 * Δ S) Δs : ℕ) : ℝ)⌉₊ GST
      with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega

end GoldilocksCorrectness.Record.Proofs.Executions

