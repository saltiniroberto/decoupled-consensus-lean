module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.LockStatementsForkChoice
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SupporterDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.SupporterDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameForkChoice
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Statements.Routines.WalkEndStatements
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Proofs.Routines.WalkEndMerge
public import GoldilocksCorrectness.Proofs.Executions.ReadingPoints
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ReadingPoints, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/ReadingPoints.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 62 to 64 over reading points, the
Goldfish vote argument with the times at which each node state is read taken as parameters. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_natCast)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotesAt VoterTreeAt
  VotesOnceInPoolFor ResolvesAt AnchorAt)
open GoldilocksCorrectness.Statements.Routines (WalkEnd)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  tau_eq_some_blockStamp occurrenceBefore_eq_true_iff tau_eq_some_stamp
  compatible_of_ancestorEq_compatible tau_eq_ok_some)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; core's `get_elem_tactic` searches the whole context before it
-- tries `trivial`, which in a context of many hypotheses can exhaust the heartbeats
--. This rule, local to the file, is
-- tried first and proves `True` at once; on any other goal it fails and the search continues.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## A pool vote reaching a validator before its own tick (B3-R1's tenth launch, T-RC8-2)

The vote kit of Lemma 62 read at the receiver's own tick (T-RC6-1's shape): a delivered vote that the
receiver admitted is in its pool at its later ticks, or the receiver holds two votes of the vote's
validator; a re-delivery premise from one of the receiver's ticks; and the two routes of the vote, the
delivery of the holder's re-send and the sync fact read at the start of the holder's window. -/

section PoolVoteAtTick

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy deadlineUpTo_eq_some)

/-- **A vote admitted at a delivery is in the receiver's pool at its later steps.** A Goldfish vote of
slot `s`, of a member of the slot-`s` committee, delivered to `w` at the step `j` before `kR`, at which
`w` has reacted to a clock value at least the start of slot `s` and its clock value is less than the
start of slot `s + 2`, is in `w`'s pool of slot `s` after `kR` steps, or that pool holds two distinct
votes of the vote's validator: the delivery runs Goldilocks's receive reaction on the vote
(`deliver_step_state`), which admits it unless the pool already shows its validator equivocating
(`receive_gfVote_cases`), and the pool only grows (`pool_mono`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `j`: the
  delivery's step; `kR`: the later step; `u`: the sender; `w`: the receiver; `vote`: the vote.

Read aloud: a vote admitted at a delivery is in the receiver's pool later, or the receiver holds two
votes of its validator. -/
theorem pool_vote_at_of_admitted_delivery (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s j kR : ℕ} {u w : V} {vote : GoldfishVote V}
    (hslot : vote.slot = s) (hcomm : vote.val_index ∈ S.P.committee s)
    (hlj : x.lbl j = Event.deliver w ⟨u, NamedObject.gfVote vote⟩) (hjk : j < kR)
    (hreact : x.ReactedAtLeast j w (M.slotStart S.C s))
    (hhi : x.clockValue j w < M.slotStart S.C (s + 2)) :
    vote ∈ M.votesHeldSet (x.st kR w) s ∨
      ∃ u₁ ∈ M.votesHeldSet (x.st kR w) s, ∃ u₂ ∈ M.votesHeldSet (x.st kR w) s,
        u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  obtain ⟨hwj, hstep⟩ := (deliver_step_state M F) x R E hlj
  have hwjc : w ∉ A.corrupted j := Activity.not_mem_corrupted_of_mem_active hwj
  have hge := (le_clockValue_of_reactedAtLeast M F) E hlj hwjc hreact
  have hclock := (clock_eq_clockValue M F) x R j w
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hs2 : vote.slot ≤ S.C.slot (x.st j w).t := by
    rw [hclock, hslot, ← hsl]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S s _).1 hge
  have hs1 : S.C.slot (x.st j w).t ≤ vote.slot + 1 := by
    rw [hclock, hslot, ← hsl]
    by_contra hc
    have := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S (s + 2)
      (x.clockValue j w)).2 (Nat.succ_le_of_lt (not_le.1 hc))
    exact absurd hhi (not_lt.2 this)
  rcases F.rcv.receive_gfVote_cases S.C S.P S.X (x.st j w) vote hs1 hs2 (hslot ▸ hcomm) with hin | heqv
  · left
    rw [← hstep, hslot] at hin
    exact (pool_mono M F) x R E w (show j + 1 ≤ kR by omega) s hin
  · right
    obtain ⟨u₁, h₁, u₂, h₂, hne, hi₁, hi₂⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Routines.two_votes_of_equivocates M F) heqv
    rw [hslot] at h₁ h₂
    exact ⟨u₁, (pool_mono M F) x R E w (show j ≤ kR by omega) s h₁, u₂,
      (pool_mono M F) x R E w (show j ≤ kR by omega) s h₂, hne, hi₁, hi₂⟩

/-- **The re-delivery premise from one of the receiver's ticks.** When `w` ticks to `c` at `k₂` and to
`D` at `kR`, with `c + ΔClockBehind + ΔRedeliver ≤ D − ΔClockAhead`, every delivery `j₀` to `w` that found
`w` not yet reacted to a clock value `r ≤ c` is followed by `w`'s first tick `k₁` at a clock value at
least `r` at a real time at least `ΔRedeliver` before `kR`: `k₁` is no later than `k₂` (the tick to
`c ≥ r`), which is at a real time at most `c + ΔClockBehind`, while `kR` is at a real time at least
`D − ΔClockAhead` (`tick_active`).

The variables:
- `M`: the model; `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `w`: the
  receiver; `c`, `k₂`: the clock value and the step of its earlier tick; `D`, `kR`: those of its later
  tick; `r`: the release clock value.

Read aloud: a re-delivery after the receiver's first tick at the release clock value comes
`ΔRedeliver` before its later tick, when an earlier tick at a clock value at least the release leaves
that room. -/
theorem redeliver_before_of_tick {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {w : V} {c k₂ D kR r : ℕ} (hk₂ : x.lbl k₂ = Event.tick w c) (hkR : x.lbl kR = Event.tick w D)
    (hgap : (c : ℝ) + ΔClockBehind + ΔRedeliver ≤ (D : ℝ) - ΔClockAhead) (hrc : r ≤ c) :
    ∀ (j₀ k₁ t₁ : ℕ), ¬ x.ReactedAtLeast j₀ w r → j₀ < k₁ → x.lbl k₁ = Event.tick w t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kR := by
  intro j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst
  have hj₀k₂ : j₀ < k₂ := by
    by_contra hcon
    exact hnr ⟨k₂, by omega, _, hrc, Or.inl hk₂⟩
  have hk₁k₂ : k₁ ≤ k₂ := by
    by_contra hcon
    have := hfirst k₂ _ hj₀k₂ (by omega) hk₂
    omega
  have h1 := R.time_mono hk₁k₂
  have h2 := (E.tick_active k₂ w c hk₂).2.2
  have h3 := (E.tick_active kR w D hkR).2.1
  rw [R.time_keep k₁ (by rw [hlk₁]; exact nofun)]
  linarith

/-- **The delivery route of a held vote, at the receiver's tick.** A Goldfish vote of slot `s`, of a
member of the slot-`s` committee, that `v₁`, honest, put on the wire at the step `e` at a real time
from `tW` to `t_e + ΔClockBehind`, after `GST`, reaches `v₂`, active after every step whose real time is
at least `tW` up to its tick `kR` to `t_e + Δ S`, before that tick: it is in `v₂`'s pool of slot `s`
after `kR` steps, or that pool holds two distinct votes of its validator. The delivery promise
`delivered` places the delivery before `kR` (its deadline `max τ GST + ΔNet` is at most
`t_e + Δ S − ΔClockAhead` by `hNet`), with the admission clause read from `v₂`'s tick to `t_e`
(`redeliver_before_of_tick`, `hRedeliver`); then `pool_vote_at_of_admitted_delivery`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s`: the slot; `t_e`: the early cutoff; `b`: the bound of the
  delivery premises; `v₁`: the sender; `v₂`: the receiver; `vote`: the vote; `e`: the send's step;
  `tW`: the start of `v₂`'s window; `kR`: `v₂`'s tick to `t_e + Δ S`.

Read aloud: a vote an honest validator re-sent before `ΔClockBehind` after `t_e`, while the receiver
was up, is in the receiver's pool when it ticks to `t_e + Δ S`, or the receiver holds two votes of its
validator. -/
theorem pool_vote_at_tick_of_send (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e b : ℕ) (v₁ v₂ : V)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hGST : GST ≤ t_e) (hb : t_e + Δ S ≤ b) (hhi : t_e + Δ S < M.slotStart S.C (s + 2))
    (hslot : vote.slot = s) (hcomm : vote.val_index ∈ S.P.committee s)
    (hrel : M.slotStart S.C s ≤ t_e) (h1 : 1 ≤ t_e)
    (e : ℕ) (hsent : (⟨v₁, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (e + 1) - x.sent e)
    (hhon : v₁ ∉ A.corrupted e) (heT : x.time (e + 1) ≤ (t_e : ℝ) + ΔClockBehind)
    (tW : ℝ) (htW : tW ≤ x.time (e + 1)) (htWe : tW ≤ (t_e : ℝ) - ΔClockAhead)
    (kR : ℕ) (hkR : x.lbl kR = Event.tick v₂ (t_e + Δ S))
    (hwin : ∀ j : ℕ, tW ≤ x.time j → j ≤ kR → v₂ ∈ A.active j) :
    vote ∈ M.votesHeldSet (x.st kR v₂) s ∨
      ∃ u₁ ∈ M.votesHeldSet (x.st kR v₂) s, ∃ u₂ ∈ M.votesHeldSet (x.st kR v₂) s,
        u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hkRt := (E.tick_active kR v₂ _ hkR).2.1
  push_cast at hkRt
  have hek : e < kR := (lt_of_time_lt M) x R (by linarith [htime (Nat.le_succ e)])
  -- `v₂`'s tick `k₂` to `t_e`, before `kR`
  obtain ⟨k₂, hk₂, -, -⟩ := E.tick_of_active t_e h1 v₂ fun j hj1 hj2 => by
    refine hwin j (by linarith) ?_
    exact ((lt_of_time_lt M) x R (by linarith)).le
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C s) hk₂ hkR
    (by push_cast; linarith) hrel
  -- `v₂`'s clock value at `kR` is less than `t_e + Δ S`
  have hv₂kR : v₂ ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hcvR : x.clockValue kR v₂ < t_e + Δ S :=
    clockValue_lt_of_tick_of_active M F E hkR (by omega) fun j hj hjk => hwin j (by push_cast at hj; linarith) hjk
  -- the delivery of the re-send, before `kR`
  have hGSTR : (GST : ℝ) ≤ t_e := by exact_mod_cast hGST
  have hmax : max (x.time (e + 1)) (GST : ℝ) ≤ (t_e : ℝ) + ΔClockBehind := max_le heT (by linarith)
  have hbR : ((t_e + Δ S : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  push_cast at hbR
  obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered e kR v₂ ⟨v₁, NamedObject.gfVote vote⟩ (t_e + Δ S)
    (max (x.time (e + 1)) GST + ΔNet) ⟨hsent, hhon⟩ trivial hkR hek
    (fun j h1 h2 => hwin j (le_trans htW (htime h1)) h2)
    (deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
    (fun r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst => by
      have hr' : M.slotStart S.C vote.slot = r := Option.some.inj hr
      rw [hslot] at hr'
      subst hr'
      exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
  have hreact : x.ReactedAtLeast j v₂ (M.slotStart S.C s) := by
    have := hadm (M.slotStart S.C vote.slot) rfl (by rw [hslot]; omega)
    rwa [hslot] at this
  exact (pool_vote_at_of_admitted_delivery M F U) R E hslot hcomm hlj hjk hreact
    (lt_of_le_of_lt (E.clockValue_mono hjk.le hv₂kR) (by omega))

/-- **The sync route of a held vote, at the receiver's tick.** A Goldfish vote of slot `s`, of a member
of the slot-`s` committee, that `v₁` holds after its last step `k` before `t₀ ≥ GST`, `v₁` active there
and at every step whose real time is in `[t₀, t₀ + Δs]`, reaches `v₂`, active after every step whose
real time is at least `tW ≤ t₀` up to its tick `kR` to `t_e + Δ S ≥ t₀ + Δs`, before that tick: it is in
`v₂`'s pool of slot `s` after `kR` steps, or that pool holds two distinct votes of its validator. The
sync fact read at `t₀` (`delivered_before_of_held_upTo_tick`) gives the delivery before `kR` with the
admission clause, or `v₂` already holding the vote; then `pool_vote_at_of_admitted_delivery`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s`: the slot; `t_e`: the early cutoff; `b`: the bound of the
  delivery premises; `t₀`: the sync fact's read time; `k`: the holder's last step before it; `v₁`: the
  holder; `v₂`: the receiver; `vote`: the vote; `tW`: the start of `v₂`'s window; `kR`: `v₂`'s tick to
  `t_e + Δ S`.

Read aloud: a vote an honest holder, up for the sync delay after `t₀`, held before `t₀` is in the
receiver's pool when it ticks to `t_e + Δ S`, or the receiver holds two votes of its validator. -/
theorem pool_vote_at_tick_of_held (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e b : ℕ) (v₁ v₂ : V)
    (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hb : t_e + Δ S ≤ b) (hhi : t_e + Δ S < M.slotStart S.C (s + 2))
    (hslot : vote.slot = s) (hcomm : vote.val_index ∈ S.P.committee s)
    (hrel : M.slotStart S.C s ≤ t_e) (h1 : 1 ≤ t_e)
    (t₀ : ℕ) (hGST : GST ≤ t₀) (ht₀ : t₀ + Δs ≤ t_e + Δ S) (ht₀e : (t₀ : ℝ) + ΔClockAhead < t_e + Δ S)
    (k : ℕ) (hkt : x.time k < t₀) (hkt1 : (t₀ : ℝ) ≤ x.time (k + 1)) (hvk : v₁ ∈ A.active k)
    (hvote : vote ∈ M.votesHeldSet (x.st k v₁) s)
    (hhold : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → x.time i ≤ t₀ + Δs → v₁ ∈ A.active i)
    (tW : ℝ) (htW : tW ≤ t₀) (htWe : tW ≤ (t_e : ℝ) - ΔClockAhead)
    (kR : ℕ) (hkR : x.lbl kR = Event.tick v₂ (t_e + Δ S))
    (hwin : ∀ j : ℕ, tW ≤ x.time j → j ≤ kR → v₂ ∈ A.active j) :
    vote ∈ M.votesHeldSet (x.st kR v₂) s ∨
      ∃ u₁ ∈ M.votesHeldSet (x.st kR v₂) s, ∃ u₂ ∈ M.votesHeldSet (x.st kR v₂) s,
        u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hkRt := (E.tick_active kR v₂ _ hkR).2.1
  push_cast at hkRt
  have hkk : k < kR := (lt_of_time_lt M) x R (by linarith)
  -- `v₂`'s tick `k₂` to `t_e`, before `kR`
  obtain ⟨k₂, hk₂, -, -⟩ := E.tick_of_active t_e h1 v₂ fun j hj1 hj2 => by
    refine hwin j (by linarith) ?_
    exact ((lt_of_time_lt M) x R (by linarith)).le
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C s) hk₂ hkR
    (by push_cast; linarith) hrel
  have hv₂kR : v₂ ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hcvR : x.clockValue kR v₂ < t_e + Δ S :=
    clockValue_lt_of_tick_of_active M F E hkR (by omega) fun j hj hjk => hwin j (by
      push_cast at hj
      have : (0 : ℝ) ≤ Δ S := by positivity
      linarith) hjk
  -- `v₁` serves the vote at its clock value after `k`
  have hcvk := (clockValue_le_time_add_ahead M F) x R E k v₁
  have hss : (t_e + Δ S : ℝ) < M.slotStart S.C (s + 2) := by exact_mod_cast hhi
  have hserve : servesMin M S.C (x.st k v₁) (x.clockValue k v₁) (NamedObject.gfVote vote) := by
    refine ⟨by rw [hslot]; exact hvote, ?_⟩
    rw [hslot]
    by_contra hc
    have h2 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S (s + 2)
      (x.clockValue k v₁)).2 (by omega)
    have h3 : ((M.slotStart S.C (s + 2) : ℕ) : ℝ) ≤ (x.clockValue k v₁ : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < M.slotStart S.C (s + 2) := by
      have : (0 : ℝ) ≤ (t_e + Δ S : ℝ) := by positivity
      linarith
    rcases le_max_iff.1 (le_trans h3 hcvk) with h5 | h5
    · linarith
    · linarith
  rcases (delivered_before_of_held_upTo_tick M) x R E Sy (by omega) hvk hkt hkt1 hserve trivial hhold hGST
      ht₀ hkR (fun i hi hik => hwin i (le_trans htW hi) hik)
      (fun r j₀ k₁ t₁ hr _ hnr hjk₁ _ hlk₁ _ hfirst => by
        have hr' : M.slotStart S.C vote.slot = r := Option.some.inj hr
        rw [hslot] at hr'
        subst hr'
        exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
    with hw | ⟨j, -, -, -, -, hlj, hjk, hadm, -⟩
  · left
    have h := hw.1
    rw [hslot] at h
    exact (pool_mono M F) x R E v₂ hkk.le s h
  · have hreact : x.ReactedAtLeast j v₂ (M.slotStart S.C s) := by
      have := hadm (M.slotStart S.C vote.slot) rfl (by rw [hslot]; omega)
      rwa [hslot] at this
    exact (pool_vote_at_of_admitted_delivery M F U) R E hslot hcomm hlj hjk hreact
      (lt_of_le_of_lt (E.clockValue_mono hjk.le hv₂kR) (by omega))

/-- A validator outside the adversary set ticks to a smaller clock value no later: of its ticks to `c`
at `k` and to `c' ≥ c` at `k'`, `k` comes first or is `k'` (`clock_mono`, `tick_unique`).

The variables:
- `M`: the model; `x`: the execution; `E`: the environment's facts; `w`: the validator; `c`, `c'`: the
  two clock values; `k`, `k'`: the steps of the two ticks.

Read aloud: a validator's tick to a smaller clock value is no later than its tick to a larger one. -/
theorem tick_step_le_of_le {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {w : V} {c c' k k' : ℕ} (hk : x.lbl k = Event.tick w c) (hk' : x.lbl k' = Event.tick w c')
    (hcc : c ≤ c') : k ≤ k' := by
  by_contra hcon
  have hle := E.clock_mono k' k w c' c (by omega) (E.not_mem_corrupted_of_tick hk) (Or.inl hk') (Or.inl hk)
  have hc : c' = c := le_antisymm hle hcc
  rw [hc] at hk'
  exact absurd (E.tick_unique k k' w c hk hk') (by omega)

/-- **A vote that entered the holder's pool before its tick to `t_e` reaches the receiver before its
tick.** A Goldfish vote of slot `s` that entered `v₁`'s pool at the step `e`, before `v₁`'s tick to `t_e`,
is in `v₂`'s pool of slot `s` in the state `v₂`'s tick to `c₂ ≥ t_e + Δ S` starts from, or that pool
holds two distinct votes of its validator, when `v₂` is active from a start more than both clock bounds
before `t_e + Δ S − max (Δ S) Δs` up to its tick to `t_e + Δ S`, and `v₁` is active for the sync delay
after that time: `v₁` re-sent the vote at `e` (`step_pool_relayed`), at a real time at most
`t_e + ΔClockBehind`; the delivery route (`pool_vote_at_tick_of_send`) or the sync route
(`pool_vote_at_tick_of_held`), as in Lemma 62's proof.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- as `lem62_early_vote_reaches_at`'s; `vote`: the vote; `e`: the step at which it entered `v₁`'s pool.

Read aloud: a vote the holder took in before its tick to `t_e` is in the receiver's pool from its tick to
`t_e + Δ S` on, or the receiver holds two votes of its validator. -/
theorem pool_vote_reaches_at_tick_core (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e c₂ k₂ b : ℕ) (v₁ v₂ : V)
    (vote : GoldfishVote V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    (hhi : t_e + Δ S < M.slotStart S.C (s + 2)) (hb : t_e + Δ S ≤ b) (h1 : 1 ≤ t_e)
    (tStart₂ : ℤ) (htStart₂ :
      (tStart₂ : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (hv₂ : v₂ ∈ A.activeThroughoutToTick x tStart₂ (t_e + Δ S))
    (h02 : t_e + Δ S ≤ c₂) (hk₂ : x.lbl k₂ = Event.tick v₂ c₂)
    (hv₁ : v₁ ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v₁ t_e)
    (e : ℕ) (hek : e < kₑ) (hne : vote ∉ M.votesHeldSet (x.st e v₁) s)
    (he1 : vote ∈ M.votesHeldSet (x.st (e + 1) v₁) s) :
    vote ∈ M.votesHeldSet (x.st k₂ v₂) s ∨
      ∃ u₁ ∈ M.votesHeldSet (x.st k₂ v₂) s, ∃ u₂ ∈ M.votesHeldSet (x.st k₂ v₂) s,
        u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hsent, hhon, hrel0⟩ := (step_pool_relayed M F U) S A x R E
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 he1)
    (fun h => hne (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))
  have hvₑ : v₁ ∉ A.corrupted kₑ := E.not_mem_corrupted_of_tick hkₑ
  have hrel : M.slotStart S.C s ≤ t_e :=
    le_trans hrel0 (le_trans (E.clockValue_mono (show e + 1 ≤ kₑ by omega) hvₑ)
      (E.clockValue_le_of_set hvₑ (Or.inl hkₑ)))
  have heT : x.time (e + 1) ≤ (t_e : ℝ) + ΔClockBehind :=
    le_trans (htime (show e + 1 ≤ kₑ by omega)) (E.tick_active kₑ v₁ t_e hkₑ).2.2
  have hslot : vote.slot = s := (pool_slot_of_exec M F) S A x R E (e + 1) v₁ s vote he1
  have hcomm : vote.val_index ∈ S.P.committee s := (pool_committee_of_exec M F) S A x R E (e + 1) v₁ s vote he1
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hcb : max (Δ S) Δs ≤ t_e + Δ S := by omega
  have ht₀e : (t_e + Δ S) - max (Δ S) Δs ≤ t_e := by omega
  have ht₀eR : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ t_e := by exact_mod_cast ht₀e
  obtain ⟨kR, hkR, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv₂
    (t₀ := min ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ((t_e : ℝ) - ΔClockAhead))
    (lt_min (by linarith) (by linarith))
  have hres : vote ∈ M.votesHeldSet (x.st kR v₂) s ∨
      ∃ u₁ ∈ M.votesHeldSet (x.st kR v₂) s, ∃ u₂ ∈ M.votesHeldSet (x.st kR v₂) s,
        u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
    by_cases hlate : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ x.time (e + 1)
    · exact (pool_vote_at_tick_of_send M F U) S A x R GST s t_e b v₁ v₂ vote E hNet hSkew hRedeliver
        (by omega) hb hhi hslot hcomm hrel h1 e hsent hhon heT _ (le_trans (min_le_left _ _) hlate)
        (min_le_right _ _) kR hkR hwin
    · push_neg at hlate
      have h0 : (0 : ℝ) ≤ x.time (e + 1) := (time_nonneg M) x R (e + 1)
      have h1t : 1 ≤ (t_e + Δ S) - max (Δ S) Δs := by
        have : (0 : ℝ) < ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) := lt_of_le_of_lt h0 hlate
        exact_mod_cast this
      have hiek : e < x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) := ((lt_stepBefore_iff M) x R E).2 hlate
      obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E h1t
      have hΔsR : (0 : ℝ) ≤ Δs := by positivity
      have hvk : v₁ ∈ A.active (x.stepBefore ((t_e + Δ S) - max (Δ S) Δs)) :=
        Activity.mem_activeThroughout.1 hv₁ _ (by linarith) hk2
      exact (pool_vote_at_tick_of_held M F U) S A x R GST s t_e b v₁ v₂ vote E hSkew hRedeliver Sy hb hhi
        hslot hcomm hrel h1 ((t_e + Δ S) - max (Δ S) Δs) (by omega) (by omega)
        (by linarith) _ hk1 hk2 hvk
        ((pool_mono M F) x R E v₁ (show e + 1 ≤ x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) by omega) s he1)
        (fun i h1 h2 => Activity.mem_activeThroughout.1 hv₁ i h2 (le_trans h1 (htime (Nat.le_succ i))))
        _ (min_le_left _ _) (min_le_right _ _) kR hkR hwin
  have hRk : kR ≤ k₂ := tick_step_le_of_le M F E hkR hk₂ h02
  rcases hres with h | ⟨u₁, h₁, u₂, h₂, hne', hi₁, hi₂⟩
  · exact Or.inl ((pool_mono M F) x R E v₂ hRk s h)
  · exact Or.inr ⟨u₁, (pool_mono M F) x R E v₂ hRk s h₁, u₂, (pool_mono M F) x R E v₂ hRk s h₂, hne', hi₁, hi₂⟩

/-- **A block the holder held at its tick to `t_e` reaches the receiver before its tick.** A block
`H` other than the genesis block, in `v₁`'s tree at its tick to `t_e`, with `v₁`'s finalized block at a
step whose real time is at least `t_e` an ancestor of `H` or `H`, is in `v₂`'s tree in the state
`v₂`'s tick to `c₂ ≥ t_e + Δ S` starts from, when `v₂`'s finalized block there is an ancestor of `H` or
`H`, `v₂` is active from a start more than both clock bounds before `t_e + Δ S − max (Δ S) Δs` up to its
tick to `t_e + Δ S`, `v₁` is active for the sync delay after that time, and roots name blocks until the
latest real time of `v₂`'s tick to `t_e + Δ S`. `v₁` relayed `H` when it entered its tree
(`tree_block_relayed_entry`), at a real time at most `t_e + ΔClockBehind`; from the read time on the
delivery promise, before it the sync fact (the holder serving `H`, compatible with its finalized
block), places a delivery before `v₂`'s tick to `t_e + Δ S` with the admission clause, and the block
enters `v₂`'s tree (`mem_tree_of_admitted_delivery`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- as `pool_vote_reaches_at_tick_core`'s; `H`: the block; `kF`: the step at which `v₁`'s finalized block
  is read.

Read aloud: a block the holder held at its tick to `t_e` is in the receiver's tree from its tick to
`t_e + Δ S` on, when both finalized blocks are on its chain. -/
theorem block_reaches_at_tick_core (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t_e c₂ k₂ b : ℕ) (v₁ v₂ : V)
    (H : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S) (hb : t_e + Δ S ≤ b) (h1 : 1 ≤ t_e)
    (tStart₂ : ℤ) (htStart₂ :
      (tStart₂ : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (hv₂ : v₂ ∈ A.activeThroughoutToTick x tStart₂ (t_e + Δ S))
    (h02 : t_e + Δ S ≤ c₂) (hk₂ : x.lbl k₂ = Event.tick v₂ c₂)
    (hv₁ : v₁ ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v₁ t_e) (hHk : H ∈ (x.st kₑ v₁).tree) (hg : H ≠ Block.genesis)
    (kF : ℕ) (hkFT : (t_e : ℝ) ≤ x.time kF) (hFv : (x.st kF v₁).finalized.AncestorEq H)
    (hF₂ : (x.st k₂ v₂).finalized.AncestorEq H) :
    H ∈ (x.st k₂ v₂).tree := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hvₑ : v₁ ∉ A.corrupted kₑ := E.not_mem_corrupted_of_tick hkₑ
  have hkₑT := (E.tick_active kₑ v₁ t_e hkₑ).2.2
  obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hHk hg
  have heT : x.time (ie + 1) ≤ (t_e : ℝ) + ΔClockBehind := le_trans (htime (show ie + 1 ≤ kₑ by omega)) hkₑT
  -- the start of `H`'s slot is at most `t_e`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hrel : M.slotStart S.C H.slot ≤ t_e := by
    have hHs := (slot_le_clockValue_of_mem_tree M F) R E hvₑ hHk
    rw [← hsl] at hHs
    exact le_trans (((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S
      H.slot _).2 hHs) (E.clockValue_le_of_set hvₑ (Or.inl hkₑ))
  -- `v₂`'s window and its tick `kR` to `t_e + Δ S`
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hcb : max (Δ S) Δs ≤ t_e + Δ S := by omega
  have ht₀e : (t_e + Δ S) - max (Δ S) Δs ≤ t_e := by omega
  have ht₀eR : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ t_e := by exact_mod_cast ht₀e
  obtain ⟨kR, hkR, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv₂
    (t₀ := min ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ((t_e : ℝ) - ΔClockAhead))
    (lt_min (by linarith) (by linarith))
  have hkRt := (E.tick_active kR v₂ _ hkR).2
  push_cast at hkRt
  have hRk : kR ≤ k₂ := tick_step_le_of_le M F E hkR hk₂ h02
  have hv₂kR : v₂ ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hcompatR : (x.st kR v₂).finalized.compatible H = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E v₂ hRk) hF₂))
  -- `v₂`'s tick to `t_e`, for the re-delivery premise
  obtain ⟨kt, hkt, -, -⟩ := E.tick_of_active t_e h1 v₂ fun j hj1 hj2 => by
    refine hwin j (le_trans (min_le_right _ _) hj1) ?_
    exact ((lt_of_time_lt M) x R (by linarith)).le
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C H.slot) hkt hkR
    (by push_cast; linarith) hrel
  have hTR : ∀ j, j < kR → x.time j ≤ (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind) := fun j hj => by
    have := htime hj.le
    push_cast
    linarith
  have hkₑT' : x.time kₑ ≤ (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind) := by
    push_cast
    have : (0 : ℝ) ≤ Δ S := by positivity
    linarith
  have hres : H ∈ (x.st kR v₂).tree := by
    by_cases hlate : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ x.time (ie + 1)
    · -- the relay from the read time on: the delivery promise
      have hiek : ie < kR := (lt_of_time_lt M) x R (by linarith [htime (Nat.le_succ ie)])
      have hGSTR : (GST : ℝ) ≤ t_e := by
        have : GST ≤ t_e := by omega
        exact_mod_cast this
      have hmax : max (x.time (ie + 1)) (GST : ℝ) ≤ (t_e : ℝ) + ΔClockBehind := max_le heT (by linarith)
      have hbR : ((t_e + Δ S : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      push_cast at hbR
      obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered ie kR v₂ ⟨v₁, NamedObject.block H⟩ (t_e + Δ S)
        (max (x.time (ie + 1)) GST + ΔNet) ⟨hsende, hhone⟩ trivial hkR hiek
        (fun j h1 h2 => hwin j (le_trans (min_le_left _ _) (le_trans hlate (htime h1))) h2)
        (deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
        (fun r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst => by
          have hr' : M.slotStart S.C H.slot = r := Option.some.inj hr
          subst hr'
          exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
      exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hvₑ hkₑT' hHk hlj (hTR j hjk)
        (hadm _ rfl (by omega)) hjk hv₂kR hcompatR
    · -- the relay before the read time: `v₁` holds `H` there, and the sync fact
      push_neg at hlate
      have h0 : (0 : ℝ) ≤ x.time (ie + 1) := (time_nonneg M) x R (ie + 1)
      have h1t : 1 ≤ (t_e + Δ S) - max (Δ S) Δs := by
        have : (0 : ℝ) < ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) := lt_of_le_of_lt h0 hlate
        exact_mod_cast this
      have hiek : ie < x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) := ((lt_stepBefore_iff M) x R E).2 hlate
      obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E h1t
      have hΔsR : (0 : ℝ) ≤ Δs := by positivity
      have hvk : v₁ ∈ A.active (x.stepBefore ((t_e + Δ S) - max (Δ S) Δs)) :=
        Activity.mem_activeThroughout.1 hv₁ _ (by linarith) hk2
      have hkF : x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) < kF := (lt_of_time_lt M) x R (by linarith)
      have hkk : x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) < kR := (lt_of_time_lt M) x R (by linarith)
      have hserve : servesMin M S.C (x.st (x.stepBefore ((t_e + Δ S) - max (Δ S) Δs)) v₁)
          (x.clockValue (x.stepBefore ((t_e + Δ S) - max (Δ S) Δs)) v₁) (NamedObject.block H) :=
        ⟨(mem_T_mono M F) x R E v₁ (show ie + 1 ≤ x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) by omega) hie1,
          (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E v₁ hkF.le) hFv)), hg⟩
      rcases (delivered_before_of_held_upTo_tick M) x R E Sy (by omega) hvk hk1 hk2 hserve trivial
          (fun i h1 h2 => Activity.mem_activeThroughout.1 hv₁ i h2 (le_trans h1 (htime (Nat.le_succ i))))
          (by omega) (by omega) hkR (fun i hi hik => hwin i (le_trans (min_le_left _ _) hi) hik)
          (fun r j₀ k₁ t₁ hr _ hnr hjk₁ _ hlk₁ _ hfirst => by
            have hr' : M.slotStart S.C H.slot = r := Option.some.inj hr
            subst hr'
            exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
        with hw | ⟨j, -, -, -, -, hlj, hjk, hadm, -⟩
      · exact (mem_T_mono M F) x R E v₂ hkk.le hw.1
      · exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hvₑ hkₑT' hHk hlj (hTR j hjk)
          (hadm _ rfl (by omega)) hjk hv₂kR hcompatR
  exact (mem_T_mono M F) x R E v₂ hRk hres

/-- **A vote included in a held block of the next slot is held, at a step** (read at a validator's
own tick, T-RC8-2). A Goldfish vote of slot `s`
included in a block of slot `s + 1` of `w`'s tree after `k` steps, of a member of the slot-`s` committee,
is in `w`'s pool of slot `s` after `k` steps, or that pool holds two distinct votes of the vote's validator,
when `w` is outside the adversary set after `k` steps and its clock value there is less than the start of
slot `s + 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's
  facts; `k`: the step; `w`: the validator; `s`: the slot of the vote; `B'`: the block; `vote`: the vote.

Read aloud: a vote a held block of the next slot includes is held, unless its validator equivocated. -/
theorem included_vote_held_or_two_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver
      acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (w : V) (s : ℕ) (B' : Block V) (vote : GoldfishVote V)
    (hB : B' ∈ (x.st k w).tree) (hBs : B'.slot = s + 1) (hvote : vote ∈ B'.votes)
    (hvs : vote.slot = s) (hcomm : vote.val_index ∈ S.P.committee s)
    (hw : w ∉ A.corrupted k) (hck : x.clockValue k w < M.slotStart S.C (s + 2)) :
    vote ∈ M.votesHeldSet (x.st k w) s ∨
      ∃ v₁ ∈ M.votesHeldSet (x.st k w) s, ∃ v₂ ∈ M.votesHeldSet (x.st k w) s,
        v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index := by
  classical
  have hne : B' ≠ Block.genesis := by
    rintro rfl
    exact Nat.succ_ne_zero s hBs.symm
  -- the step at which `B'` entered `w`'s tree
  have hex : ∃ m : ℕ, B' ∈ (x.st m w).tree := ⟨k, hB⟩
  have h0 : B' ∉ (x.st 0 w).tree := by
    rw [(getElem_zero_st M F) x R, F.init.initial_tree]
    intro h
    exact hne (Finset.mem_singleton.1 h)
  have hpos : Nat.find hex ≠ 0 := fun h => h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hB
  obtain ⟨i, hi⟩ : ∃ i : ℕ, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hni : B' ∉ (x.st i w).tree := Nat.find_min hex (by omega)
  have hi1 : B' ∈ (x.st (i + 1) w).tree := hi ▸ Nat.find_spec hex
  have hik : i + 1 ≤ k := by omega
  -- the model's slot of a natural-number time is the spec's (`U`)
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  -- from the entry step on, to `k`
  have hmono : ∀ v' : GoldfishVote V, v' ∈ M.votesHeldSet (x.st (i + 1) w) s →
      v' ∈ M.votesHeldSet (x.st k w) s :=
    fun v' h => (pool_mono M F) x R E w hik s h
  rcases (step_cases_per_step M F) x R E i w with h | ⟨t', n', sent, hl, hmem, hrun, h, -⟩ |
      ⟨sm, hl, hact, h⟩ | ⟨⟨tR, keep, hl⟩, -, -⟩
  · rw [h] at hi1
    exact absurd hi1 hni
  · -- `w` proposed `B'` at its tick, from the votes of its pool at the step `i`
    have hti : x.tickInput w t' = x.st i w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    have hBn := hi1
    rw [h] at hBn
    have hP := F.tk.tick_prov S.C S.P S.X _ (t' : Int) n' sent hrun
    obtain ⟨hBsent, -⟩ := hP.2 B' hBn (by rw [hti]; exact hni)
    have hInv : M.nodeInv S.C S.P S.X (x.tickInput w t') := by
      rw [hti]
      exact ((lem11_node_invariant M F S A x R E i w) (Activity.not_mem_corrupted_of_mem_active hmem)).1
    obtain ⟨-, -, -, -, H, votes, support, hvotes, -, -, hBdef⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n' _ sent B'
        hrun hInv hBsent
    have hvote' := hvote
    rw [hBdef] at hvote'
    have hvv : vote ∈ votes := hvote'
    rw [hvotes] at hvv
    change vote ∈ M.votesHeld (x.tickInput w t') _ at hvv
    rw [hti] at hvv
    have hs' : vote.slot = S.C.slot (t' : Int) - 1 :=
      ((F.nd.nodeInvCore_poolKeyed ((lem11_node_invariantCore_of_run M F) S x R i w).1)
        _ vote hvv).1
    have hpool : vote ∈ M.votesHeldSet (x.st i w) s := by
      rw [← hvs, hs']
      exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 hvv
    exact Or.inl ((pool_mono M F) x R E w (by omega) s hpool)
  · -- `w` received `B'`: its votes of the current or the previous slot are admitted
    have hi1' := hi1
    rw [h] at hi1'
    obtain ⟨hmsg, -⟩ := (F.rcv.receive_new S.C S.P S.X _ sm.msg).2 B' hi1' hni
    obtain ⟨-, -, hBslot⟩ := (step_tree_new M F) x R E hi1 hni
    -- a delivery moves no clock: `w`'s clock at the delivery is its clock value after `i` steps, at
    -- most its clock value after `k` steps (`clockValue_mono`, `w` honest at `k`)
    have hcv : x.clockValue (i + 1) w = x.clockValue i w :=
      x.clockValue_succ_of_not (fun t ht => by rw [hl] at ht; cases ht)
        (fun t keep ht => by rw [hl] at ht; cases ht)
    have hti : (x.st i w).t = ((x.clockValue i w : ℕ) : Int) := (clock_eq_clockValue M F) x R i w
    have hti1 : (x.st (i + 1) w).t = ((x.clockValue (i + 1) w : ℕ) : Int) :=
      (clock_eq_clockValue M F) x R (i + 1) w
    have hck' : x.clockValue i w < M.slotStart S.C (s + 2) :=
      lt_of_le_of_lt (E.clockValue_mono (show i ≤ k by omega) hw) hck
    have hup : S.C.slot ((x.clockValue i w : ℕ) : Int) ≤ s + 1 := by
      rw [← hsl]
      by_contra hlt
      have h3 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S
        (s + 2) (x.clockValue i w)).2 (Nat.lt_of_not_le hlt)
      omega
    have hlo : s + 1 ≤ S.C.slot ((x.clockValue i w : ℕ) : Int) := by
      have hb := hBslot
      rw [hti1, hcv, hBs] at hb
      exact hb
    have hmsg' : sm.msg = NamedObject.block B' := hmsg
    rw [hmsg'] at h
    have hin : B' ∈ (M.receive S.C S.P S.X (x.st i w) (NamedObject.block B')).tree := by
      rw [← h]; exact hi1
    rcases F.rcv.receive_block_votes S.C S.P S.X (x.st i w) B' hni hin vote hvote
        (by rw [hti, hvs]; exact hup)
        (by rw [hti, hvs]; exact le_trans (Nat.le_succ s) hlo)
        (by rw [hvs]; exact hcomm) with
      hv | heqv
    · rw [← h, hvs] at hv
      exact Or.inl (hmono vote hv)
    · rw [← h, hvs] at heqv
      obtain ⟨v₁, h₁, v₂, h₂, hne', hi₁, hi₂⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.two_votes_of_equivocates M F) heqv
      exact Or.inr ⟨v₁, hmono v₁ h₁, v₂, hmono v₂ h₂, hne', hi₁, hi₂⟩
  · -- `w`'s restart keeps its tree
    rw [(wake_case_tree M F) x R hl] at hi1
    exact absurd hi1 hni

end PoolVoteAtTick

/-- Lemma 62, a vote that resolved early at one validator reaches another within one delay of the
early cutoff. Its reading is on the statement page,
`Record/Restated/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery premises up to `b`, the latest deadline being `t_e + Δ S` (`v₁`'s
re-send reaching `v₂`). Read at the validators' own ticks (T-RC8-2: T-RC6-1's shape): `v₁`'s node state
at its tick to `c₁`, `v₂`'s at its tick to `c₂ ≥ t_e + Δ S`; the holder `v₁` active for the sync delay
after the sync fact's read time `t_e + Δ S − max (Δ S) Δs` and ticking to `t_e`.

Why: the vote is stamped strictly before `t_e`, so it entered `v₁`'s pool at a step with `v₁`'s clock
value less than `t_e` (`voteStamp_entry_clock`), before `v₁`'s tick to `t_e`, and `v₁` re-sent it there
(`step_pool_relayed`), at a real time at most `t_e + ΔClockBehind`. A re-send from the read time on is
delivered to `v₂` before its tick to `t_e + Δ S` (`pool_vote_at_tick_of_send`); a re-send before it
leaves the vote held by `v₁` at the read time, and the sync fact delivers it
(`pool_vote_at_tick_of_held`). The pool only grows up to `v₂`'s tick to `c₂`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a vote that resolved before `t_e` in the state `v₁`'s tick to `c₁` starts from is in `v₂`'s
pool in the state its tick to `c₂` starts from, or `v₂` then holds two votes of the vote's validator. -/
theorem lem62_early_vote_reaches_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e c₁ c₂ b : ℕ) (v₁ v₂ : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    (hhi : t_e + Δ S < M.slotStart S.C (s + 2))
    -- `v₂` ticks to `t_e + Δ S` at `kR`, and is active at every step up to that tick whose real time is at least
    -- one clock-ahead bound before the earlier of `t_e + Δ S − max (Δ S) Δs` and the start of slot `s`
    (kR : ℕ) (hkR : x.lbl kR = Event.tick v₂ (t_e + Δ S))
    (hwin₂ : ∀ i : ℕ, min ((t_e + Δ S : ℝ) - max (Δ S) Δs) (M.slotStart S.C s) - ΔClockAhead ≤ x.time i →
      i ≤ kR → v₂ ∈ A.active i)
    -- `v₂`'s node state is read at its tick `k₂` to `c₂ ≥ t_e + Δ S`
    (h02 : t_e + Δ S ≤ c₂) (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ c₂)
    -- `v₁` is active at every step whose real time is in the sync delay after the read time
    (hv₁ : v₁ ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v₁` ticks to `t_e` at `kₑ`, and its node state is read at its tick `k₁` to `c₁`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v₁ t_e) (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ c₁)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_e + Δ S ≤ b) :
    ∀ vote ∈ M.votesHeldSet (x.tickInput v₁ c₁) s,
      (∃ y : Stamp, ResolvesAt M (x.tickInput v₁ c₁) vote y ∧
        occurrenceBefore (some y) ((t_e : ℕ) : Int) = true) →
      vote ∈ M.votesHeldSet (x.tickInput v₂ c₂) s ∨
        ∃ u₁ ∈ M.votesHeldSet (x.tickInput v₂ c₂) s,
          ∃ u₂ ∈ M.votesHeldSet (x.tickInput v₂ c₂) s,
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  intro vote hvote ⟨y, hτ, hy⟩
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hti₁ : x.tickInput v₁ c₁ = x.st k₁ v₁ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₁]
  have hti₂ : x.tickInput v₂ c₂ = x.st k₂ v₂ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₂]
  rw [hti₁] at hvote hτ
  rw [hti₂]
  -- the vote's stamp is strictly before `t_e`
  obtain ⟨y', hyy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hy
  have hyy' : y = y' := Option.some_injective _ hyy
  obtain ⟨τ, τH, H', hts, -, -, -, -, hyτ⟩ := hτ
  have hτy : τ ≤ y' := by rw [← hyy', hyτ]; exact le_max_left _ _
  have hτlt := lt_of_le_of_lt hτy hlt
  -- it entered `v₁`'s pool at the step `e`, with `v₁`'s clock value then less than `t_e`, and was re-sent there
  obtain ⟨e, he, hne, he1, hτe⟩ := (voteStamp_entry_clock M F) R E hvote
  have hτeq : τ = (((x.st (e + 1) v₁).t : Int) : Stamp) := Option.some_injective _ (hts.symm.trans hτe)
  rw [hτeq, (clock_eq_clockValue M F) x R (e + 1) v₁] at hτlt
  have hcve : x.clockValue (e + 1) v₁ < t_e := by exact_mod_cast hτlt
  obtain ⟨hsent, hhon, hrel0⟩ := (step_pool_relayed M F U) S A x R E
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 he1)
    (fun h => hne (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))
  have hk₁c : v₁ ∉ A.corrupted k₁ := E.not_mem_corrupted_of_tick hk₁
  have hhon1 : v₁ ∉ A.corrupted (e + 1) := fun h => hk₁c (E.corrupted_mono (e + 1) k₁ he h)
  -- the re-send is before `v₁`'s tick to `t_e`, so at a real time at most `t_e + ΔClockBehind`
  have hek : e < kₑ := by
    by_contra hcon
    have := E.clockValue_mono (show kₑ + 1 ≤ e + 1 by omega) hhon1
    rw [x.clockValue_succ_of_tick hkₑ] at this
    omega
  have heT : x.time (e + 1) ≤ (t_e : ℝ) + ΔClockBehind :=
    le_trans (htime (show e + 1 ≤ kₑ by omega)) (E.tick_active kₑ v₁ t_e hkₑ).2.2
  have h1 : 1 ≤ t_e := by omega
  have hrel : M.slotStart S.C s ≤ t_e := by omega
  have hslot : vote.slot = s := (pool_slot_of_exec M F) S A x R E k₁ v₁ s vote hvote
  have hcomm : vote.val_index ∈ S.P.committee s := (pool_committee_of_exec M F) S A x R E k₁ v₁ s vote hvote
  -- the read time `t₀` and `v₂`'s window from the earlier of `t₀` and `t_e − ΔClockAhead`
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hcb : max (Δ S) Δs ≤ t_e + Δ S := by omega
  have ht₀e : (t_e + Δ S) - max (Δ S) Δs ≤ t_e := by omega
  have ht₀eR : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ t_e := by exact_mod_cast ht₀e
  have hwin : ∀ i : ℕ, min ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ((t_e : ℝ) - ΔClockAhead) ≤ x.time i →
      i ≤ kR → v₂ ∈ A.active i := by
    intro i hi hik
    refine hwin₂ i (le_trans ?_ hi) hik
    have hsub : ((t_e + Δ S : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ)) = ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) := by
      rw [Nat.cast_sub hcb]; push_cast; ring
    have hrelR : ((M.slotStart S.C s : ℕ) : ℝ) ≤ (t_e : ℝ) := by exact_mod_cast hrel
    have hm1 := min_le_left ((t_e + Δ S : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ)) (M.slotStart S.C s : ℝ)
    have hm2 := min_le_right ((t_e + Δ S : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ)) (M.slotStart S.C s : ℝ)
    exact le_min (by linarith) (by linarith)
  have hres : vote ∈ M.votesHeldSet (x.st kR v₂) s ∨
      ∃ u₁ ∈ M.votesHeldSet (x.st kR v₂) s, ∃ u₂ ∈ M.votesHeldSet (x.st kR v₂) s,
        u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
    by_cases hlate : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ x.time (e + 1)
    · -- the re-send from the read time on: the delivery promise
      exact (pool_vote_at_tick_of_send M F U) S A x R GST s t_e b v₁ v₂ vote E hNet hSkew hRedeliver
        (by omega) hb hhi hslot hcomm hrel h1 e hsent hhon heT _ (le_trans (min_le_left _ _) hlate)
        (min_le_right _ _) kR hkR hwin
    · -- the re-send before the read time: `v₁` holds the vote there, and the sync fact
      push_neg at hlate
      have h0 : (0 : ℝ) ≤ x.time (e + 1) := (time_nonneg M) x R (e + 1)
      have h1t : 1 ≤ (t_e + Δ S) - max (Δ S) Δs := by
        have : (0 : ℝ) < ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) := lt_of_le_of_lt h0 hlate
        exact_mod_cast this
      have hiek : e < x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) := ((lt_stepBefore_iff M) x R E).2 hlate
      obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E h1t
      have hΔsR : (0 : ℝ) ≤ Δs := by positivity
      have hvk : v₁ ∈ A.active (x.stepBefore ((t_e + Δ S) - max (Δ S) Δs)) :=
        Activity.mem_activeThroughout.1 hv₁ _ (by linarith) hk2
      have hΔ := one_le_Δ S
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      exact (pool_vote_at_tick_of_held M F U) S A x R GST s t_e b v₁ v₂ vote E hSkew hRedeliver Sy hb hhi
        hslot hcomm hrel h1 ((t_e + Δ S) - max (Δ S) Δs) (by omega) (by omega)
        (by linarith) _ hk1 hk2 hvk
        ((pool_mono M F) x R E v₁ (show e + 1 ≤ x.stepBefore ((t_e + Δ S) - max (Δ S) Δs) by omega) s he1)
        (fun i h1 h2 => Activity.mem_activeThroughout.1 hv₁ i h2 (le_trans h1 (htime (Nat.le_succ i))))
        _ (min_le_left _ _) (min_le_right _ _) kR hkR hwin
  -- the pool only grows up to `v₂`'s tick to `c₂`
  have hv₂kR : v₂ ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hRk : kR ≤ k₂ := by
    by_contra hcon
    have hle := E.clock_mono k₂ kR v₂ c₂ (t_e + Δ S) (by omega) hv₂kR (Or.inl hk₂) (Or.inl hkR)
    have hcc : c₂ = t_e + Δ S := le_antisymm hle h02
    rw [hcc] at hk₂
    exact absurd (E.tick_unique k₂ kR v₂ _ hk₂ hkR) (by omega)
  rcases hres with h | ⟨u₁, h₁, u₂, h₂, hne', hi₁, hi₂⟩
  · exact Or.inl ((pool_mono M F) x R E v₂ hRk s h)
  · exact Or.inr ⟨u₁, (pool_mono M F) x R E v₂ hRk s h₁, u₂, (pool_mono M F) x R E v₂ hRk s h₂, hne', hi₁, hi₂⟩

/-- Lemma 63's core: Lemma 63 with the transfer of `w`'s votes to `v` as a hypothesis `hToV` in
place of the holder window of `w`. `lem63_supporters_counted_at` supplies `hToV` by
`pool_transfer_of_holder`; for one validator, `v = w`, it is `pool_mono` (a node's pool only grows between two of
its steps), with no window after the validator's ticks.

The variables:
- `M`: the model; `F`: its facts; the others as `lem63_supporters_counted_at`'s.

Read aloud: each early supporter of `B`'s chain in the state `v`'s tick to `t_v` starts from has a vote
in `w`'s pool from its tick to `t_f` on, stamped before `t_f`, whose head block `w` holds stamped before
`t_f`, and it is the only vote of its validator `w` holds at its tick to `t_w`, when every slot-`s`
committee vote `w` holds then is in `v`'s pool at its tick to `t_v` or `v` holds two votes of its
validator. -/
theorem lem63_supporters_counted_at_core (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- the holder `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every slot-`s` committee vote `w` holds at its tick to `t_w` is in `v`'s pool at its tick to `t_v`,
    -- or `v` holds two votes of its validator (`pool_transfer_of_holder` for two validators,
    -- `pool_mono` for one)
    (hToV : ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
      vote' ∈ M.votesHeldSet (x.tickInput v t_v) s ∨
        ∃ v₁ ∈ M.votesHeldSet (x.tickInput v t_v) s, ∃ v₂ ∈ M.votesHeldSet (x.tickInput v t_v) s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index)
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup, ∃ vote_u ∈ M.votesHeldSet (x.tickInput w t_f) s, vote_u.val_index = u ∧
      (∃ τ : Stamp, (x.tickInput w t_w).voteStamp vote_u = some τ ∧
        τ < (((t_f : ℕ) : Int) : Stamp)) ∧
      (∃ H_u ∈ (x.tickInput w t_f).tree, H_u.root = vote_u.head ∧ B.AncestorEq H_u ∧
        H_u.slot ≤ s ∧
        ∃ st : Stamp, (x.tickInput w t_w).blockStamp H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
      ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index = u →
        vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
        vote' = vote_u) ∧
    (∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
      vote' ∈ M.votesHeldSet (x.tickInput v t_v) s ∨
        ∃ v₁ ∈ M.votesHeldSet (x.tickInput v t_v) s,
          ∃ v₂ ∈ M.votesHeldSet (x.tickInput v t_v) s,
            v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hti_f : x.tickInput w t_f = x.st k_f w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_f]
  have hti_w : x.tickInput w t_w = x.st k_w w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_w]
  have hti_v : x.tickInput v t_v = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  rw [hti_v] at hSup
  rw [hti_w, hti_v] at hToV
  rw [hti_w] at hF
  rw [hti_f, hti_w, hti_v]
  -- `w`'s tick `kW` to `t_e + Δ S`, and its clock value there
  have ht₀eR : ((((t_e + Δ S) - max (Δ S) Δs : ℕ)) : ℝ) ≤ ((t_e + Δ S : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  obtain ⟨kW, hkW, hwinW⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw
    (t₀ := ((t_e + Δ S : ℕ) : ℝ) - ΔClockAhead) (by linarith)
  have hcvW : x.clockValue kW w < t_e + Δ S :=
    clockValue_lt_of_tick_of_active M F E hkW (by omega) fun j hj hjk => hwinW j hj hjk
  have hWf : kW ≤ k_f := tick_step_le_of_le M F E hkW hk_f h01
  have hfw : k_f ≤ k_w := tick_step_le_of_le M F E hk_f hk_w h12
  have hWw : kW ≤ k_w := le_trans hWf hfw
  have hvₑ : v ∉ A.corrupted kₑ := E.not_mem_corrupted_of_tick hkₑ
  have hv_v : v ∉ A.corrupted k_v := E.not_mem_corrupted_of_tick hk_v
  have hwW : w ∉ A.corrupted kW := E.not_mem_corrupted_of_tick hkW
  refine ⟨fun u hu => ?_, hToV⟩
  obtain ⟨vote, hvote, hidx, ⟨H, hHΦ, hroot, hBH⟩, ⟨y, hres, hy⟩, huniqv⟩ := hSup u hu
  -- `u`'s votes `w` holds at its tick to `t_w` are `vote`: each reaches `v`, where `u` has one vote
  have huniqW : ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index = u →
      vote' ∈ M.votesHeldSet (x.st k_w w) s → vote' = vote := by
    intro vote' hs' hi' hvw
    have hc' := (pool_committee_of_exec M F) S A x R E k_w w s vote' hvw
    rcases hToV vote' hs' hc' hvw with h | ⟨y₁, h₁, y₂, h₂, hne, hi₁, hi₂⟩
    · exact huniqv vote' h hi'
    · exact absurd ((huniqv y₁ h₁ (hi₁.trans hi')).trans (huniqv y₂ h₂ (hi₂.trans hi')).symm) hne
  -- the resolution: the vote and its head block are stamped strictly before `t_e` at `v`
  obtain ⟨y', hyy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hy
  have hyy' : y = y' := Option.some_injective _ hyy
  obtain ⟨τ, τH, H', hts, hH'Φ, hroot', -, hτH, hyτ⟩ := hres
  have hHH : H' = H :=
    (rootsNameBlocksIn_frame_of_exec_node M F) S A x R E k_v v H' hH'Φ H hHΦ (hroot'.trans hroot.symm)
  rw [hHH] at hτH
  have hτlt := lt_of_le_of_lt (show τ ≤ y' by rw [← hyy', hyτ]; exact le_max_left _ _) hlt
  have hτHlt := lt_of_le_of_lt (show τH ≤ y' by rw [← hyy', hyτ]; exact le_max_right _ _) hlt
  -- the vote entered `v`'s pool before `v`'s tick to `t_e`
  obtain ⟨e, he, hne, he1, hτe⟩ := (voteStamp_entry_clock M F) R E hvote
  have hτeq : τ = (((x.st (e + 1) v).t : Int) : Stamp) := Option.some_injective _ (hts.symm.trans hτe)
  rw [hτeq, (clock_eq_clockValue M F) x R (e + 1) v] at hτlt
  have hcve : x.clockValue (e + 1) v < t_e := by exact_mod_cast hτlt
  have hv1 : v ∉ A.corrupted (e + 1) := fun h => hv_v (E.corrupted_mono (e + 1) k_v he h)
  have hek : e < kₑ := by
    by_contra hcon
    have := E.clockValue_mono (show kₑ + 1 ≤ e + 1 by omega) hv1
    rw [x.clockValue_succ_of_tick hkₑ] at this
    omega
  -- the vote reaches `w` by its tick to `t_e + Δ S`; `w` holding two votes of `u` would put two at `v`
  have hvW : vote ∈ M.votesHeldSet (x.st kW w) s := by
    rcases (pool_vote_reaches_at_tick_core M F U) S A x R GST s t_e (t_e + Δ S) kW b v w vote E hNet hSkew
        hRedeliver Sy hGST (by omega) (by omega) h1 tStartW htStartW hw le_rfl hkW hv₀ kₑ hkₑ e hek hne he1
      with h | ⟨u₁, h₁, u₂, h₂, hne', hi₁, hi₂⟩
    · exact h
    · exfalso
      have hs₁ := (pool_slot_of_exec M F) S A x R E kW w s u₁ h₁
      have hs₂ := (pool_slot_of_exec M F) S A x R E kW w s u₂ h₂
      exact hne' ((huniqW u₁ hs₁ (hi₁.trans hidx) ((pool_mono M F) x R E w hWw s h₁)).trans
        (huniqW u₂ hs₂ (hi₂.trans hidx) ((pool_mono M F) x R E w hWw s h₂)).symm)
  -- its stamp at `w`, kept to `w`'s tick to `t_w`
  obtain ⟨e', he', -, -, hτe'⟩ := (voteStamp_entry_clock M F) R E hvW
  have hτw : (x.st k_w w).voteStamp vote = some (((x.st (e' + 1) w).t : Int) : Stamp) := by
    rw [(voteStamp_kept M F) x R E w hWw hvW, hτe']
  have hcw : x.clockValue (e' + 1) w < t_f :=
    lt_of_le_of_lt (E.clockValue_mono (show e' + 1 ≤ kW by omega) hwW) (by omega)
  -- the head block `H`: in `v`'s tree at its tick to `t_e`, of slot at most `s`
  have hHTv : H ∈ (x.st k_v v).tree := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHΦ).1
  have hFvH : (x.st k_v v).finalized.AncestorEq H := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHΦ).2
  have hHk : H ∈ (x.st kₑ v).tree := by
    by_cases hg : H = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ v
    obtain ⟨e'', he'', -, he''1, hτe''⟩ := (blockStamp_entry_clock M F) R E hHTv hg
    have hτHeq : τH = (((x.st (e'' + 1) v).t : Int) : Stamp) := Option.some_injective _ (hτH.symm.trans hτe'')
    rw [hτHeq, (clock_eq_clockValue M F) x R (e'' + 1) v] at hτHlt
    have hcve'' : x.clockValue (e'' + 1) v < t_e := by exact_mod_cast hτHlt
    have hv1'' : v ∉ A.corrupted (e'' + 1) := fun h => hv_v (E.corrupted_mono (e'' + 1) k_v he'' h)
    have hek'' : e'' < kₑ := by
      by_contra hcon
      have := E.clockValue_mono (show kₑ + 1 ≤ e'' + 1 by omega) hv1''
      rw [x.clockValue_succ_of_tick hkₑ] at this
      omega
    exact (mem_T_mono M F) x R E v (show e'' + 1 ≤ kₑ by omega) he''1
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hHs : H.slot ≤ s := by
    have h₁ := (slot_le_clockValue_of_mem_tree M F) R E hvₑ hHk
    have h₂ : S.C.slot ((x.clockValue kₑ v : ℕ) : Int) ≤ S.C.slot ((t_e : ℕ) : Int) :=
      GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
        (by exact_mod_cast E.clockValue_le_of_set hvₑ (Or.inl hkₑ))
    have h₃ : M.slot S.C t_e ≤ s := by
      by_contra hc
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S (s + 1)
        t_e).2 (Nat.succ_le_of_lt (not_le.1 hc))
      exact absurd hslot (not_lt.2 this)
    rw [hsl] at h₃
    exact h₁.trans (h₂.trans h₃)
  -- `H` reaches `w` by its tick to `t_e + Δ S`, stamped there strictly before `t_e + Δ S`
  have hFw : (x.st kW w).finalized.AncestorEq H :=
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R E w hWw) (ancestorEq_trans hF hBH)
  have hkvT : (t_e : ℝ) ≤ x.time k_v := by
    have := (E.tick_active k_v v t_v hk_v).2.1
    have h23R : ((t_w + Δ S : ℕ) : ℝ) ≤ (t_v : ℝ) := by exact_mod_cast h23
    have h01R : ((t_e + Δ S : ℕ) : ℝ) ≤ (t_f : ℝ) := by exact_mod_cast h01
    have h12R : (t_f : ℝ) ≤ (t_w : ℝ) := by exact_mod_cast h12
    push_cast at h23R h01R
    linarith
  have hHW : H ∈ (x.st kW w).tree ∧ ∃ st : Stamp, (x.st k_w w).blockStamp H = some st ∧
      st < (((t_f : ℕ) : Int) : Stamp) := by
    by_cases hg : H = Block.genesis
    · rw [hg]
      exact ⟨(GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w,
        ⊥, (genesis_stamp M F) x R E k_w w, WithBot.bot_lt_coe _⟩
    have hHW' : H ∈ (x.st kW w).tree :=
      (block_reaches_at_tick_core M F U) S A x R GST t_e (t_e + Δ S) kW b v w H E hNet hSkew hRedeliver Sy
        hRoots hParent hGST (by omega) h1 tStartW htStartW hw le_rfl hkW hv₀ kₑ hkₑ hHk hg k_v hkvT hFvH hFw
    obtain ⟨e3, he3, -, -, hτe3⟩ := (blockStamp_entry_clock M F) R E hHW' hg
    refine ⟨hHW', _, by rw [(blockStamp_kept M F) x R E w hWw hHW', hτe3], ?_⟩
    rw [(clock_eq_clockValue M F) x R (e3 + 1) w]
    have : x.clockValue (e3 + 1) w < t_f :=
      lt_of_le_of_lt (E.clockValue_mono (show e3 + 1 ≤ kW by omega) hwW) (by omega)
    exact_mod_cast this
  obtain ⟨hHW', st, hst, hstlt⟩ := hHW
  refine ⟨vote, (pool_mono M F) x R E w hWf s hvW, hidx, ⟨_, hτw, ?_⟩,
    ⟨H, (mem_T_mono M F) x R E w hWf hHW', hroot, hBH, hHs, st, hst, hstlt⟩, huniqW⟩
  rw [(clock_eq_clockValue M F) x R (e' + 1) w]
  exact_mod_cast hcw

/-- **What a holder active after its tick holds reaches the receiver.** Every slot-`s` committee vote `w`
holds at its tick to `t_w` is in `v`'s pool at its tick to `t_v ≥ t_w + Δ S`, or `v`'s pool holds two
votes of its validator, when `w` is active for the sync delay after `t_w + Δ S − max (Δ S) Δs`
 and `v` from a start more than both clock bounds before that time up to its tick to
`t_w + Δ S`: `w` took the vote in at a step before its tick (`voteStamp_entry_clock`), and the delivery
or sync route carries it to `v` (`pool_vote_reaches_at_tick_core`). It is the hypothesis `hToV` of
`lem63_supporters_counted_at_core` for two validators.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; the others as
  `lem63_supporters_counted_at`'s.

Read aloud: what a validator active for the sync delay after the read time holds at its tick to `t_w`
is in the receiver's pool at its tick to `t_v`, or the receiver holds two votes of its validator. -/
theorem pool_transfer_of_holder (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_w t_v b : ℕ) (w v : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- the network is synchronous from the sync fact's read time `t_w + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_w + Δ S)
    -- the re-sends arrive while slot-`s` votes are still admitted, and by the bound
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2)) (hb : t_w + Δ S ≤ b)
    -- `t_w` is a clock value of a tick
    (h1 : 1 ≤ t_w)
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- `v` ticks to `t_v ≥ t_w + Δ S` at `k_v`
    (h23 : t_w + Δ S ≤ t_v) (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- the holder `w` active for the sync delay after `t_w + Δ S − max (Δ S) Δs`
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to `t_w` at `k_w`
    (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w) :
    ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
      vote' ∈ M.votesHeldSet (x.tickInput v t_v) s ∨
        ∃ v₁ ∈ M.votesHeldSet (x.tickInput v t_v) s, ∃ v₂ ∈ M.votesHeldSet (x.tickInput v t_v) s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index := by
  have hti_w : x.tickInput w t_w = x.st k_w w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_w]
  have hti_v : x.tickInput v t_v = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  rw [hti_w, hti_v]
  intro vote' _ _ hvw
  obtain ⟨e, he, hne, he1, -⟩ := (voteStamp_entry_clock M F) R E hvw
  exact (pool_vote_reaches_at_tick_core M F U) S A x R GST s t_w t_v k_v b w v vote' E hNet hSkew
    hRedeliver Sy hGST hhi hb h1 tStart htStart hv h23 hk_v hw₀ k_w hk_w e he hne he1

/-- Lemma 63, the early supporters' votes and heads reach the next slot's voter, and are its only
votes of their validators. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery premises up to `b`, the latest deadline being `t_w + Δ S`
(`w`'s re-sends reaching `v`; the re-sends from `v` reach `w` by `t_e + Δ S ≤ t_w + Δ S`). Read at the
validators' own ticks (T-RC8-2, T-RC6-1's shape): `w`'s node states at its ticks to `t_f` and `t_w`,
`v`'s at its tick to `t_v`; the receivers' windows end at their ticks to `t_e + Δ S` (`w`) and
`t_w + Δ S` (`v`); the holders active for the sync delay after the read times; roots name
blocks until the latest real time of `w`'s tick to `t_e + Δ S`.

Why: each supporter's vote and head block are stamped strictly before `t_e` at `v`, so `v` held them at
its tick to `t_e`; they reach `w` before its tick to `t_e + Δ S` (`pool_vote_reaches_at_tick_core`,
`block_reaches_at_tick_core`), stamped there strictly before `t_e + Δ S ≤ t_f`. A slot-`s` vote `w` holds
at its tick to `t_w` reaches `v` before its tick to `t_w + Δ S` (the same route, `w` the holder), where
the supporter has one vote; so `w` holds no other vote of it.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: each early supporter of `B`'s chain in the state `v`'s tick to `t_v` starts from has a vote
in `w`'s pool from its tick to `t_f` on, stamped before `t_f`, whose head block `w` holds stamped before
`t_f`, and it is the only vote of its validator `w` holds at its tick to `t_w`; every slot-`s` vote `w`
holds then is in `v`'s pool at its tick to `t_v`, or `v` holds two votes of its validator. -/
theorem lem63_supporters_counted_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup, ∃ vote_u ∈ M.votesHeldSet (x.tickInput w t_f) s, vote_u.val_index = u ∧
      (∃ τ : Stamp, (x.tickInput w t_w).voteStamp vote_u = some τ ∧
        τ < (((t_f : ℕ) : Int) : Stamp)) ∧
      (∃ H_u ∈ (x.tickInput w t_f).tree, H_u.root = vote_u.head ∧ B.AncestorEq H_u ∧
        H_u.slot ≤ s ∧
        ∃ st : Stamp, (x.tickInput w t_w).blockStamp H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
      ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index = u →
        vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
        vote' = vote_u) ∧
    (∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
      vote' ∈ M.votesHeldSet (x.tickInput v t_v) s ∨
        ∃ v₁ ∈ M.votesHeldSet (x.tickInput v t_v) s,
          ∃ v₂ ∈ M.votesHeldSet (x.tickInput v t_v) s,
            v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index) := by
  exact (lem63_supporters_counted_at_core M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w E hNet hSkew
    hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw hv₀
    ((pool_transfer_of_holder M F U) S A x R GST s t_w t_v b w v E hNet hSkew hRedeliver Sy (by omega) hhi
      hb (by omega) tStart htStart hv h23 k_v hk_v hw₀ k_w hk_w)
    kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hF hb

/-- Lemma 63 read on the sets the voter counts: each early supporter votes once for `B`'s chain
among them, the voters are fewer than twice the supporters, and every support vote is counted. Its
reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: each early supporter of `B`'s chain votes once for it among the votes `w` counts with
the cutoff `t_f`, the voters `w` counts are fewer than twice the supporters, and every support vote
is counted. -/
theorem supporters_vote_once_counted_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (votes support_votes : Finset (GoldfishVote V))
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    (hEligible : M.voters_count (M.votesHeldSet (x.tickInput v t_v) s) < 2 * Sup.card)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    (hCounted : CountedVotesAt M (x.tickInput w t_w)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    (∀ u ∈ Sup,
      VotesOnceFor (M.fg_to_ac (x.tickInput w t_w)) votes support_votes s B u ∧
      ∃ H_u ∈ (x.tickInput w t_w).tree, B.AncestorEq H_u ∧
        ∃ st : Stamp, (x.tickInput w t_w).blockStamp H_u = some st ∧
          st < (((t_f : ℕ) : Int) : Stamp)) ∧
    M.voters_count votes < 2 * Sup.card ∧ support_votes ⊆ votes := by
  obtain ⟨hPer, hToV⟩ := (lem63_supporters_counted_at M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w E hNet hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw tStart htStart htStartSlot hv hv₀ hw₀ kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hF hb
  have hti_f : x.tickInput w t_f = x.st k_f w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_f]
  have hti_w : x.tickInput w t_w = x.st k_w w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_w]
  have hti_v : x.tickInput v t_v = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  simp only [hti_f, hti_w, hti_v] at hPer hToV
  rw [hti_v] at hEligible
  rw [hti_w] at hF hCounted ⊢
  have hRootsΦ : RootsNameBlocksIn (M.fg_to_ac (x.st k_w w)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ w
  have hle12 : k_f ≤ k_w := tick_step_le_of_le M F E hk_f hk_w h12
  obtain ⟨hCv, hCs⟩ := hCounted
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- the blocks whose included votes `w` counts
  have hBne : ∀ B' : Block V, B'.slot = s + 1 → B' ≠ Block.genesis := by
    rintro B' hBs rfl
    exact Nat.succ_ne_zero s hBs.symm
  have hPayload : ∀ B' ∈ (M.fg_to_ac (x.st k_w w)).tree,
      B'.slot = s + 1 → M.ac_valid_payload S.P B' = true := by
    intro B' hB' hBs
    have hBT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB').1
    have hwf := (((F.nd.nodeInvCore_treeClosed ((lem11_node_invariantCore_of_run M F) S x R k_w w).1)).2
      B' hBT (hBne B' hBs)).2.1
    exact ((F.rd.block_well_formed_iff S.P S.X B').1 hwf).1.2
  have hIncl : ∀ vote' ∈ M.included_votes (M.fg_to_ac (x.st k_w w)) (s + 1),
      ∃ B' ∈ (M.fg_to_ac (x.st k_w w)).tree,
        B'.slot = s + 1 ∧ vote' ∈ B'.votes ∧ vote'.slot = s := by
    intro vote' hv
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F),
      Nat.add_sub_cancel] at hv
    obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hv
    exact ⟨B', hB', hBs, hvB, hvs⟩
  have hSupport : support_votes ⊆ votes := by
    intro vote' hv
    rcases (hCs vote').1 hv with ⟨hp', hτ, -⟩ | ⟨hinc, -⟩
    · exact (hCv vote').2 (Or.inl ⟨hp', hτ⟩)
    · simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_support_votes_iff M F),
        Nat.add_sub_cancel] at hinc
      obtain ⟨B', ⟨hB', hBs⟩, hvB, hvs⟩ := hinc
      have hvB' : vote' ∈ B'.votes :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B' (hPayload B' hB' hBs)).2.1 vote' hvB
      refine (hCv vote').2 (Or.inr ?_)
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F),
        Nat.add_sub_cancel]
      exact ⟨B', ⟨hB', hBs⟩, hvB', hvs⟩
  -- every vote `w` counts is of slot `s`, from the slot-`s` committee, and was re-sent by `w`
  -- before `t_w`, as a pool vote or as a vote included in a block of `w`'s tree
  have hRelW : ∀ vote' ∈ votes, vote'.slot = s ∧ vote'.val_index ∈ S.P.committee s ∧
      (vote' ∈ M.votesHeldSet (x.st k_w w) s ∨
        ∃ y₁ ∈ M.votesHeldSet (x.st k_w w) s, ∃ y₂ ∈ M.votesHeldSet (x.st k_w w) s,
          y₁ ≠ y₂ ∧ y₁.val_index = vote'.val_index ∧ y₂.val_index = vote'.val_index) := by
    intro vote' hv
    rcases (hCv vote').1 hv with ⟨hp', -⟩ | hinc
    · have hs' := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k_w w s vote' hp'
      exact ⟨hs', (GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E k_w w s vote' hp',
        Or.inl hp'⟩
    · obtain ⟨B', hB', hBs, hvB, hvs⟩ := hIncl vote' hinc
      have hc' := ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B' (hPayload B' hB' hBs)).2.2 vote' hvB
      rw [hBs, Nat.add_sub_cancel] at hc'
      exact ⟨hvs, hc', (included_vote_held_or_two_at M F U) S A x R E k_w w s B' vote'
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB').1 hBs hvB hvs hc'
        (E.not_mem_corrupted_of_tick hk_w)
        (lt_of_le_of_lt (E.clockValue_le_of_set (E.not_mem_corrupted_of_tick hk_w) (Or.inl hk_w)) (by omega))⟩
  -- every validator with a vote `w` counts has a vote in `v`'s pool of slot `s`
  have hVoters : M.voters_count votes < 2 * Sup.card := by
    have hsub : M.participants votes ⊆ M.participants (M.votesHeldSet (x.st k_v v) s) := by
      intro u' hu'
      obtain ⟨vote', hv', hi'⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_participants_iff M F) _ _).1 hu'
      obtain ⟨hs', hcomm', hrel⟩ := hRelW vote' hv'
      refine ((GoldilocksCorrectness.Record.Proofs.Routines.mem_participants_iff M F) _ _).2 ?_
      rcases hrel with hrel | ⟨y₁, hy₁, -, -, -, hj₁, -⟩
      · rcases hToV vote' hs' hcomm' hrel with h | ⟨v₁, h₁, -, -, -, hi₁, -⟩
        · exact ⟨vote', h, hi'⟩
        · exact ⟨v₁, h₁, hi₁.trans hi'⟩
      · have hys := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k_w w s y₁ hy₁
        rcases hToV y₁ hys (by rw [hj₁]; exact hcomm') hy₁ with h | ⟨v₁, h₁, -, -, -, hi₁, -⟩
        · exact ⟨y₁, h, hj₁.trans hi'⟩
        · exact ⟨v₁, h₁, hi₁.trans (hj₁.trans hi')⟩
    exact lt_of_le_of_lt (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq M F), (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq M F)]; exact Finset.card_le_card hsub)
      hEligible
  refine ⟨?_, hVoters, hSupport⟩
  -- each member of `Sup` votes once for `B`'s chain among the votes `w` counts
  intro u hu
  obtain ⟨vote_u, hpw1, hidx, ⟨τv, hτv, hτvlt⟩, ⟨H_u, hHT1, hroot, hBH, hHs, τH, hτH, hτHlt⟩,
    huniq⟩ := hPer u hu
  have hpw2 : vote_u ∈ M.votesHeldSet (x.st k_w w) s := (pool_mono M F) x R E w hle12 s hpw1
  have hsu : vote_u.slot = s := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k_f w s vote_u hpw1
  have hHT2 : H_u ∈ (x.st k_w w).tree := (mem_T_mono M F) x R E w hle12 hHT1
  have hHΦw : H_u ∈ (M.fg_to_ac (x.st k_w w)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hHT2, ancestorEq_trans hF hBH⟩
  -- the vote resolves at the later of its stamp and its head block's
  have htau : ResolvesAt M (x.st k_w w) vote_u (max τv τH) :=
    ⟨τv, τH, H_u, hτv, hHΦw, hroot, by rw [hsu]; exact hHs, hτH, rfl⟩
  refine ⟨⟨vote_u, (hCs vote_u).2 (Or.inl ⟨hpw2, ⟨τv, hτv, hτvlt⟩,
    ⟨max τv τH, htau, max_lt hτvlt hτHlt⟩⟩), hidx, hsu, ⟨H_u, hHΦw, hroot, hBH⟩, ?_⟩,
    H_u, hHT2, hBH, τH, hτH, hτHlt⟩
  intro vote' hv' hi'
  obtain ⟨hs', -, hrel⟩ := hRelW vote' hv'
  rcases hrel with hrel | ⟨y₁, hy₁, y₂, hy₂, hne, hj₁, hj₂⟩
  · exact huniq vote' hs' hi' hrel
  · exfalso
    have hs₁ := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k_w w s y₁ hy₁
    have hs₂ := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k_w w s y₂ hy₂
    exact hne ((huniq y₁ hs₁ (hj₁.trans hi') hy₁).trans (huniq y₂ hs₂ (hj₂.trans hi') hy₂).symm)

/-- Lemma 63 read on the voter's pool, its core: the pool form with the transfer of `w`'s votes to `v`
as a hypothesis `hToV` in place of the holder window of `w`; as
`lem63_supporters_counted_at_core`, which it calls.

The variables:
- `M`: the model; `F`: its facts; the others as `supporters_vote_once_in_pool_at`'s.

Read aloud: each early supporter of `B`'s chain in `v`'s node state votes once for it in `w`'s pool
before `t_w`, when every slot-`s` committee vote `w` holds at its tick to `t_w` is in `v`'s pool at its
tick to `t_v` or `v` holds two votes of its validator. -/
theorem supporters_vote_once_in_pool_at_core (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- the holder `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every slot-`s` committee vote `w` holds at its tick to `t_w` is in `v`'s pool at its tick to `t_v`,
    -- or `v` holds two votes of its validator (`pool_transfer_of_holder` for two validators,
    -- `pool_mono` for one)
    (hToV : ∀ vote' : GoldfishVote V, vote'.slot = s → vote'.val_index ∈ S.P.committee s →
      vote' ∈ M.votesHeldSet (x.tickInput w t_w) s →
      vote' ∈ M.votesHeldSet (x.tickInput v t_v) s ∨
        ∃ v₁ ∈ M.votesHeldSet (x.tickInput v t_v) s, ∃ v₂ ∈ M.votesHeldSet (x.tickInput v t_v) s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote'.val_index ∧ v₂.val_index = vote'.val_index)
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    ∀ u ∈ Sup,
      VotesOnceInPoolFor M (x.tickInput w t_w) s B u := by
  obtain ⟨hPer, -⟩ := (lem63_supporters_counted_at_core M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w E hNet hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw hv₀ hToV kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hF hb
  have hti_f : x.tickInput w t_f = x.st k_f w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_f]
  have hti_w : x.tickInput w t_w = x.st k_w w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_w]
  have hti_v : x.tickInput v t_v = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  simp only [hti_f, hti_w] at hPer
  rw [hti_w] at hF ⊢
  have hle12 : k_f ≤ k_w := tick_step_le_of_le M F E hk_f hk_w h12
  intro u hu
  obtain ⟨vote_u, hpw1, hidx, ⟨τv, hτv, -⟩, ⟨H_u, hHT1, hroot, hBH, hHs, τH, hτH, -⟩,
    huniq⟩ := hPer u hu
  have hpw2 : vote_u ∈ M.votesHeldSet (x.st k_w w) s := (pool_mono M F) x R E w hle12 s hpw1
  have hsu : vote_u.slot = s := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k_f w s vote_u hpw1
  have hHT2 : H_u ∈ (x.st k_w w).tree := (mem_T_mono M F) x R E w hle12 hHT1
  have hHΦw : H_u ∈ (M.fg_to_ac (x.st k_w w)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hHT2, ancestorEq_trans hF hBH⟩
  refine ⟨vote_u, hpw2, hidx,
    ⟨max τv τH, τv, τH, H_u, hτv, hHΦw, hroot, by rw [hsu]; exact hHs, hτH, rfl⟩,
    ⟨H_u, hHΦw, hroot, hBH⟩, ?_⟩
  intro vote' hv' hi'
  have hsj := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k_w w s vote' hv'
  exact huniq vote' hsj hi' hv'

/-- Lemma 63 read on the voter's pool: each early supporter votes once for `B`'s chain in it. Its
reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, which it calls).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: each early supporter of `B`'s chain in `v`'s node state votes once for it in `w`'s pool
before `t_w`. -/
theorem supporters_vote_once_in_pool_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    -- `w`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput w t_w).finalized.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    ∀ u ∈ Sup,
      VotesOnceInPoolFor M (x.tickInput w t_w) s B u := by
  exact (supporters_vote_once_in_pool_at_core M F U) S A x R GST s t_e t_f t_w t_v b Sup B v w E hNet
    hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw hv₀
    ((pool_transfer_of_holder M F U) S A x R GST s t_w t_v b w v E hNet hSkew hRedeliver Sy (by omega) hhi
      hb (by omega) tStart htStart hv h23 k_v hk_v hw₀ k_w hk_w)
    kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hF hb

/-- Lemma 63 read on one validator's own pool: each early supporter of `B`'s chain in the
state `u`'s tick to `t_v` starts from votes once for it in `u`'s own pool at its earlier tick to `t_w`.
It is `supporters_vote_once_in_pool_at_core` at `v := u`, `w := u`, with the transfer `hToV` by
`pool_mono`: what `u` holds at its tick to `t_w` it holds at its later tick to `t_v`. No window after
`u`'s tick to `t_w` is asked: a node reading its own pool serves no other node.

The variables:
- `M`: the model; `F`: its facts; `u`: the validator; the others as `supporters_vote_once_in_pool_at`'s.

Read aloud: each early supporter of `B`'s chain in `u`'s node state at its tick to `t_v` votes once
for it in `u`'s pool before `t_w`. -/
theorem supporters_vote_once_in_own_pool_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (u : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `u`'s tick to `t_e + Δ S`
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of `u`'s ticks read: to `t_f`, to `t_w` and to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `u` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `u`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `u` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : u ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `u` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, a time before its
    -- tick to `t_e + Δ S`
    (hv₀ : u ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `u`'s ticks to `t_e`, `t_f`, `t_w` and `t_v`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick u t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick u t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick u t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick u t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `u`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u' ∈ Sup, EarlySupporterAt M (x.tickInput u t_v)
      ((t_e : ℕ) : Int) s B u')
    -- `u`'s finalized block at its tick to `t_w` is `B` or an ancestor of `B`
    (hF : (x.tickInput u t_w).finalized.AncestorEq B)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    ∀ u' ∈ Sup,
      VotesOnceInPoolFor M (x.tickInput u t_w) s B u' := by
  have hti_w : x.tickInput u t_w = x.st k_w u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_w]
  have hti_v : x.tickInput u t_v = x.st k_v u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hle : k_w ≤ k_v := tick_step_le_of_le M F E hk_w hk_v (by omega)
  exact (supporters_vote_once_in_pool_at_core M F U) S A x R GST s t_e t_f t_w t_v b Sup B u u E hNet
    hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot hhi tStartW htStartW htStartSlotW hw hv₀
    (fun vote' _ _ h => Or.inl (by
      rw [hti_w] at h; rw [hti_v]; exact (pool_mono M F) x R E u hle s h))
    kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v hSup hF hb

/-- Lemma 64, the next slot's Goldfish fork choice extends a block an honest validator finds
eligible, over reading points. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t_w + Δ S`
(Lemma 63's, through `supporters_vote_once_counted_at`, which it calls).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the end `H_w` of `w`'s Goldfish walk at `t_w` is `B` or a descendant of `B`, when the
early supporters of `B`'s chain are more than half of the voters in `v`'s pool. -/
theorem lem64_goldfish_vote_extends_eligible_block_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e t_f t_w t_v b : ℕ) (Sup : Finset V)
    (B : Block V) (v w : V) (E : Finset M.LE) (votes support_votes : Finset (GoldfishVote V))
    (vbt : Finset (Block V)) (H_w : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (Env : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks until the latest real time of `w`'s tick to `t_e + Δ S`, the one receiver of a
    -- block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x (((t_e + Δ S : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the sync fact's read time `t_e + Δ S − max (Δ S) Δs` on
    (hGST : GST + max (Δ S) Δs ≤ t_e + Δ S)
    -- `t_e` is a clock value of a tick
    (h1 : 1 ≤ t_e)
    -- the clock values of the ticks read: `w`'s to `t_f` and to `t_w`, `v`'s to `t_v`
    (h01 : t_e + Δ S ≤ t_f)
    (h12 : t_f ≤ t_w)
    (h23 : t_w + Δ S ≤ t_v)
    -- a block `v` holds at its tick to `t_e` has slot at most `s`
    (hslot : t_e < M.slotStart S.C (s + 1))
    -- the re-sends arrive while slot-`s` votes are still admitted
    (hhi : t_w + Δ S < M.slotStart S.C (s + 2))
    -- `w`'s window starts at `tStartW`, more than both clock bounds before `t_e + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlotW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `w` is active from `tStartW` up to its tick to `t_e + Δ S`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (t_e + Δ S))
    -- `v`'s window starts at `tStart`, more than both clock bounds before `t_w + Δ S − max (Δ S) Δs`
    -- and the start of slot `s`
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ))
    (htStartSlot : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    -- `v` is active from `tStart` up to its tick to `t_w + Δ S`
    (hv : v ∈ A.activeThroughoutToTick x tStart (t_w + Δ S))
    -- the holders: `v` active for the sync delay after `t_e + Δ S − max (Δ S) Δs`, `w` for the sync
    -- delay after `t_w + Δ S − max (Δ S) Δs`
    (hv₀ : v ∈ A.activeThroughout x (((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_e + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x (((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t_w + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the ticks: `v`'s to `t_e` and to `t_v`, `w`'s to `t_f` and to `t_w`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v t_e)
    (k_f : ℕ) (hk_f : x.lbl k_f = Event.tick w t_f) (k_w : ℕ) (hk_w : x.lbl k_w = Event.tick w t_w)
    (k_v : ℕ) (hk_v : x.lbl k_v = Event.tick v t_v)
    -- each member of `Sup` is an early supporter of `B`'s chain at `v`'s tick to `t_v`, with the cutoff `t_e`
    (hSup : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v t_v)
      ((t_e : ℕ) : Int) s B u)
    (hEligible : M.voters_count (M.votesHeldSet (x.tickInput v t_v) s) < 2 * Sup.card)
    (hCounted : CountedVotesAt M (x.tickInput w t_w)
      ((t_f : ℕ) : Int) (s + 1) votes support_votes)
    (hvbt : ∀ B' : Block V, B' ∈ vbt ↔
      VoterTreeAt M (x.tickInput w t_w) ((t_f : ℕ) : Int) (s + 1) B')
    (hWalk : @WalkEnd V M.tieBreak (M.viable_tree (M.fg_to_ac (x.tickInput w t_w)) vbt)
      (goldfish_score (M.fg_to_ac (x.tickInput w t_w)) votes support_votes s)
      (goldfish_eligible S.C (M.fg_to_ac (x.tickInput w t_w)) ((t_w : ℕ) : Int) votes
        support_votes s)
      (AnchorAt M (M.fg_to_ac (x.tickInput w t_w)) E ((t_w : ℕ) : Int)) H_w)
    (hF2 : (M.fg_to_ac (x.tickInput w t_w)).fc_root.compatible B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w t_w)).fc_root.AncestorEq B →
      ∃ W ∈ vbt, W ∈ (M.fg_to_ac (x.tickInput w t_w)).viable_heads ∧ B.AncestorEq W)
    (hLocks : ∀ e ∈ E,
      M.is_live (x.tickInput w t_w) ((t_w : ℕ) : Int) e = true →
        e.B.compatible B = true)
    -- the latest deadline the proof reads is at most the bound
    (hb : t_w + Δ S ≤ b) :
    B.AncestorEq H_w := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hti_f : x.tickInput w t_f = x.st k_f w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x Env hk_f]
  have hti_w : x.tickInput w t_w = x.st k_w w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x Env hk_w]
  have hti_v : x.tickInput v t_v = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x Env hk_v]
  rw [hti_w] at hvbt hWalk hF2 hF3 hLocks
  have hFroot : (x.st k_w w).finalized.AncestorEq (M.fg_to_ac (x.st k_w w)).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R Env k_w w
  -- the anchor is a descendant of the fgroot (or the fgroot)
  have hRAw : (M.fg_to_ac (x.st k_w w)).fc_root.AncestorEq (AnchorAt M (M.fg_to_ac (x.st k_w w)) E ((t_w : ℕ) : Int)) := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M (M.fg_to_ac (x.st k_w w)) E ((t_w : ℕ) : Int) with h | h
    · rw [h]
      exact ancestorEq_refl _
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1
  -- the case `B` an ancestor of `w`'s finalized block: the walk's end is the anchor or a
  -- descendant of it, the anchor is the fgroot or a descendant of it, and the fgroot is `w`'s
  -- finalized block or a descendant of it
  have hF1 := compatible_of_ancestorEq_compatible hFroot hF2
  rcases (compatible_iff _ _).1 hF1 with hF1 | hBF
  swap
  · have hAH : (AnchorAt M (M.fg_to_ac (x.st k_w w)) E ((t_w : ℕ) : Int)).AncestorEq H_w := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1
    exact ancestorEq_trans hBF (ancestorEq_trans hFroot (ancestorEq_trans hRAw hAH))
  -- the supporters' votes are counted at `w`
  obtain ⟨hPer, hVoters, hSupport⟩ := (supporters_vote_once_counted_at M F U) S A x R GST s t_e t_f t_w
    t_v b Sup B v w votes support_votes Env hNet hSkew hRedeliver Sy hRoots hParent hGST h1 h01 h12 h23 hslot
    hhi tStartW htStartW htStartSlotW hw tStart htStart htStartSlot hv hv₀ hw₀ kₑ hkₑ k_f hk_f k_w hk_w k_v hk_v
    hSup hEligible (by rw [hti_w]; exact hF1) hCounted hb
  rw [hti_w] at hPer
  have hRootsΦ : RootsNameBlocksIn (M.fg_to_ac (x.st k_w w)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R Env _ w
  obtain ⟨u₀, hu₀⟩ : Sup.Nonempty := Finset.card_pos.1 (by omega)
  -- the anchor is compatible with `B` (Lemma 6, read off the anchor's cases): it is the fgroot,
  -- compatible with `B` by F2, or an ancestor of the block of a lock entry of `E` live at `t_w`
  have hAnchor : (AnchorAt M (M.fg_to_ac (x.st k_w w)) E ((t_w : ℕ) : Int)).compatible B = true := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases_locked M (M.fg_to_ac (x.st k_w w)) E ((t_w : ℕ) : Int) with h | ⟨-, e, he, hd, heT, hAe⟩
    · rw [h]
      exact hF2
    · have hlive : M.is_live (x.st k_w w) ((t_w : ℕ) : Int) e = true := by
        simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
        exact ⟨hd, heT⟩
      exact compatible_of_ancestorEq_compatible hAe (hLocks e he hlive)
  -- the start
  obtain ⟨-, H₀, hH₀T, hBH₀, τ₀, hτ₀, hτ₀lt⟩ := hPer u₀ hu₀
  have hStart : StartsTowards (AnchorAt M (M.fg_to_ac (x.st k_w w)) E ((t_w : ℕ) : Int)) B (M.viable_tree (M.fg_to_ac (x.st k_w w)) vbt) := by
    rcases (compatible_iff _ _).1 hF2 with hRoot | hRoot
    · obtain ⟨W, hW, hWv, hRW⟩ := hF3 hRoot
      refine (GoldilocksCorrectness.Record.Statements.Routines.lem7_startsTowards_of_compatible M F) _ vbt _ B W hAnchor hRAw ?_ ⟨hW, hWv⟩ hRW
      intro P hXP _ hPB
      have hPH : P.AncestorEq H₀ := ancestorEq_trans hPB hBH₀
      have hPT : P ∈ (x.st k_w w).tree := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R Env _ w _ P hH₀T hPH
      have hFP : (x.st k_w w).finalized.AncestorEq P := ancestorEq_trans hFroot (ancestorEq_trans hRAw hXP)
      have hPΦ : P ∈ (M.fg_to_ac (x.st k_w w)).tree := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hPT, hFP⟩
      obtain ⟨τP, τH, hτP, hτH, hle⟩ := (ancestor_blockStamp_le M F) S A x R Env _ w H₀ P hH₀T hPH
      have hτHH : τH = τ₀ := Option.some_injective _ (hτH.symm.trans hτ₀)
      exact (hvbt P).2 ⟨hPΦ, τP, hτP, Or.inl (lt_of_le_of_lt hle (hτHH ▸ hτ₀lt))⟩
    · exact Or.inl (ancestorEq_trans hRoot hRAw)
  -- the walk: Lemma 2 over the walk predicate
  exact GoldilocksCorrectness.Statements.Routines.lem2_goldfish_walkEnd_extends_majority_block
    S.C _ _ votes support_votes s _ B H_w _ Sup hStart hRootsΦ hSupport
    (fun u hu => (hPer u hu).1) (by rw [← GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F]; exact hVoters) hWalk


/-- Lemma 62 for a slot that starts after `GST`: a slot-`s` vote that resolved before `t_e` at
`v₁` is in `v₂`'s pool before `t_w ≥ t_e + Δ S`, or `v₂` then holds two votes of its validator,
when the network is synchronous from the start of slot `s`, `v₂` is active from a start more than both
clock bounds before that start up to its tick to `t_e + Δ S`, `t_e + Δ S` is before the start of slot
`s + 2`, and `v₁` ticks to `t_e`. No sync fact and no sync delay is taken. Read at the validators' own
ticks (T-RC8-2): `v₁`'s node state at its tick to `c₁`, `v₂`'s at its tick to `c₂ ≥ t_e + Δ S`. The
tick of `v₁` to `t_e` is what places the re-send of the vote, stamped strictly before `t_e`, at a real
time at most `t_e + ΔClockBehind`; its clock value then is at least the start of slot `s`, so the
re-send is at a real time at least that start minus `ΔClockAhead`, where `v₂` is up
(`pool_vote_at_tick_of_send`).

Read aloud: a vote that resolved before `t_e` in the state `v₁`'s tick to `c₁` starts from is in `v₂`'s
pool in the state its tick to `c₂` starts from, or `v₂` then holds two votes of the vote's validator.
 -/
theorem lem62_early_vote_reaches_of_slotStart_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s t_e c₁ c₂ b : ℕ) (v₁ v₂ : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hGST : GST ≤ M.slotStart S.C s)
    (hhi : t_e + Δ S < M.slotStart S.C (s + 2))
    -- `v₂` is active from `tStart₂`, more than both clock bounds before the start of slot `s`, up to its
    -- tick to `t_e + Δ S`
    (tStart₂ : ℤ) (htStart₂ : (tStart₂ : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    (hv₂ : v₂ ∈ A.activeThroughoutToTick x tStart₂ (t_e + Δ S))
    -- `v₂`'s node state is read at its tick `k₂` to `c₂ ≥ t_e + Δ S` (T-RC8-2)
    (h02 : t_e + Δ S ≤ c₂) (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ c₂)
    -- `v₁` ticks to `t_e` at `kₑ`, and its node state is read at its tick `k₁` to `c₁`
    (kₑ : ℕ) (hkₑ : x.lbl kₑ = Event.tick v₁ t_e) (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ c₁)
    (hb : t_e + Δ S ≤ b) :
    ∀ vote ∈ M.votesHeldSet (x.tickInput v₁ c₁) s,
      (∃ y : Stamp, ResolvesAt M (x.tickInput v₁ c₁) vote y ∧
        occurrenceBefore (some y) ((t_e : ℕ) : Int) = true) →
      vote ∈ M.votesHeldSet (x.tickInput v₂ c₂) s ∨
        ∃ u₁ ∈ M.votesHeldSet (x.tickInput v₂ c₂) s,
          ∃ u₂ ∈ M.votesHeldSet (x.tickInput v₂ c₂) s,
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index := by
  intro vote hvote ⟨y, hτ, hy⟩
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hti₁ : x.tickInput v₁ c₁ = x.st k₁ v₁ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₁]
  have hti₂ : x.tickInput v₂ c₂ = x.st k₂ v₂ := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₂]
  rw [hti₁] at hvote hτ
  rw [hti₂]
  obtain ⟨y', hyy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hy
  have hyy' : y = y' := Option.some_injective _ hyy
  obtain ⟨τ, τH, H', hts, -, -, -, -, hyτ⟩ := hτ
  have hτy : τ ≤ y' := by rw [← hyy', hyτ]; exact le_max_left _ _
  have hτlt := lt_of_le_of_lt hτy hlt
  obtain ⟨e, he, hne, he1, hτe⟩ := (voteStamp_entry_clock M F) R E hvote
  have hτeq : τ = (((x.st (e + 1) v₁).t : Int) : Stamp) := Option.some_injective _ (hts.symm.trans hτe)
  rw [hτeq, (clock_eq_clockValue M F) x R (e + 1) v₁] at hτlt
  have hcve : x.clockValue (e + 1) v₁ < t_e := by exact_mod_cast hτlt
  obtain ⟨hsent, hhon, hrel0⟩ := (step_pool_relayed M F U) S A x R E
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 he1)
    (fun h => hne (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))
  have hk₁c : v₁ ∉ A.corrupted k₁ := E.not_mem_corrupted_of_tick hk₁
  have hhon1 : v₁ ∉ A.corrupted (e + 1) := fun h => hk₁c (E.corrupted_mono (e + 1) k₁ he h)
  have hek : e < kₑ := by
    by_contra hcon
    have := E.clockValue_mono (show kₑ + 1 ≤ e + 1 by omega) hhon1
    rw [x.clockValue_succ_of_tick hkₑ] at this
    omega
  have heT : x.time (e + 1) ≤ (t_e : ℝ) + ΔClockBehind :=
    le_trans (htime (show e + 1 ≤ kₑ by omega)) (E.tick_active kₑ v₁ t_e hkₑ).2.2
  have h1 : 1 ≤ t_e := by omega
  have hrel : M.slotStart S.C s ≤ t_e := by omega
  have hslot : vote.slot = s := (pool_slot_of_exec M F) S A x R E k₁ v₁ s vote hvote
  have hcomm : vote.val_index ∈ S.P.committee s := (pool_committee_of_exec M F) S A x R E k₁ v₁ s vote hvote
  -- the re-send is at a real time at least the start of slot `s` minus `ΔClockAhead`
  have hrelR : ((M.slotStart S.C s : ℕ) : ℝ) ≤ (x.clockValue (e + 1) v₁ : ℝ) := by exact_mod_cast hrel0
  have hcvT := (clockValue_le_time_add_ahead M F) x R E (e + 1) v₁
  have h0 : (0 : ℝ) ≤ x.time (e + 1) := (time_nonneg M) x R (e + 1)
  have hTe : (M.slotStart S.C s : ℝ) - ΔClockAhead ≤ x.time (e + 1) := by
    rcases le_max_iff.1 (le_trans hrelR hcvT) with h | h
    · linarith
    · linarith
  have hrelR' : ((M.slotStart S.C s : ℕ) : ℝ) ≤ t_e := by exact_mod_cast hrel
  obtain ⟨kR, hkR, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv₂
    (t₀ := (M.slotStart S.C s : ℝ) - ΔClockAhead) (by linarith)
  have hres := (pool_vote_at_tick_of_send M F U) S A x R GST s t_e b v₁ v₂ vote E hNet hSkew hRedeliver
    (le_trans hGST hrel) hb hhi hslot hcomm hrel h1 e hsent hhon heT _ hTe (by linarith) kR hkR hwin
  have hv₂kR : v₂ ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hRk : kR ≤ k₂ := by
    by_contra hcon
    have hle := E.clock_mono k₂ kR v₂ c₂ (t_e + Δ S) (by omega) hv₂kR (Or.inl hk₂) (Or.inl hkR)
    have hcc : c₂ = t_e + Δ S := le_antisymm hle h02
    rw [hcc] at hk₂
    exact absurd (E.tick_unique k₂ kR v₂ _ hk₂ hkR) (by omega)
  rcases hres with h | ⟨u₁, h₁, u₂, h₂, hne', hi₁, hi₂⟩
  · exact Or.inl ((pool_mono M F) x R E v₂ hRk s h)
  · exact Or.inr ⟨u₁, (pool_mono M F) x R E v₂ hRk s h₁, u₂, (pool_mono M F) x R E v₂ hRk s h₂, hne', hi₁, hi₂⟩

open GoldilocksCorrectness.Statements.AbstractTrace (deadlineUpTo_eq_some)

/-- **A block an honest validator holds at its tick to `cu` is in a receiver's tree at its tick to `c`.**
The holder-at-tick twin of `block_at_tick_of_held_before`: a block `D` other than the genesis block, in
`u`'s tree at its tick step `kU` to the clock value `cu`, `u` active from `a` through the sync delay after
it and its finalized block at its last step before `a` compatible with `D`, is in `w`'s tree at its tick
`kR` to `c`, when `w`'s finalized block there is compatible with `D`, `w` is active at every step from the
real time `a` up to `kR`, and `w` ticked to a clock value `c₂`, at least the start of `D`'s slot and at
least one delay before `c`. Here `GST ≤ a`, `a + max (Δ S) Δs ≤ c` and `cu + Δ S ≤ c`.

Why: `u` relayed `D` when it entered its tree (`tree_block_relayed_entry`), before `kU`, honest there.
When the relay is at a real time at least `a`, the delivery promise `delivered` places a delivery
before `kR` (its deadline `max _ GST + ΔNet` is at most `cu + ΔClockBehind + ΔNet ≤ c − ΔClockAhead`,
`hNet`); otherwise `u` serves `D` at its last step before `a`, and the sync fact at `a` does
(`delivered_before_of_held_upTo_tick`). The re-delivery premise comes from `w`'s tick to `c₂`
(`redeliver_before_of_tick`); the delivered block enters `w`'s tree (`mem_tree_of_admitted_delivery`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `b`: the bound of the delivery premises; `cu`, `kU`: the clock
  value and the step of `u`'s tick; `a`: the start of the windows; `c`, `kR`: the clock value and the
  step of `w`'s tick; `c₂`, `k₂`: those of `w`'s earlier tick; `u`: the holder; `w`: the receiver;
  `D`: the block.

Read aloud: a block an honest holder has at its tick to `cu` is in every receiver's tree at its tick
to a clock value at least one delay after `cu`, when the receiver is up from `a`, the holder is up for
one sync delay after `a`, and the receiver's finalized block is compatible with the block. -/
theorem block_at_tick_of_held_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST b cu kU a c c₂ kR k₂ : ℕ) (u w : V)
    (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ c) (hcu : cu + Δ S ≤ c)
    (hcb : c ≤ b)
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hkU : x.lbl kU = Event.tick u cu)
    (hD : D ∈ (x.st kU u).tree)
    (hFa : (x.st (x.stepBefore a) u).finalized.compatible D = true)
    (hg : D ≠ Block.genesis)
    (hkR : x.lbl kR = Event.tick w c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂)
    (hFw : (x.st kR w).finalized.compatible D = true) :
    D ∈ (x.st kR w).tree := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
  have hN0 : (0 : ℝ) ≤ ΔNet := by positivity
  have hu : u ∉ A.corrupted kU := E.not_mem_corrupted_of_tick hkU
  have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  have hkUt := (E.tick_active kU u cu hkU).2.2
  obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hD hg
  have hcR : (cu : ℝ) + Δ S ≤ c := by exact_mod_cast hcu
  have hc₂R : (c₂ : ℝ) + Δ S ≤ c := by exact_mod_cast hc₂
  have hmaxR : ((a : ℕ) : ℝ) + Δ S ≤ c := by
    have h1 : a + Δ S ≤ c := le_trans (Nat.add_le_add_left (le_max_left _ _) a) ha
    exact_mod_cast h1
  have hsk : kU < kR := (lt_of_time_lt M) x R (by linarith)
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C D.slot) hk₂ hkR
    (by linarith) hDc₂
  by_cases hlate : (a : ℝ) ≤ x.time (ie + 1)
  · -- the relay from `a` on: the delivery promise
    have hiek : ie < kR := by omega
    have hieT : x.time (ie + 1) ≤ x.time kU := htime (show ie + 1 ≤ kU by omega)
    have hGSTR : (GST : ℝ) ≤ a := by exact_mod_cast hGSTa
    have hmax : max (x.time (ie + 1)) (GST : ℝ) ≤ cu + ΔClockBehind :=
      max_le (by linarith) (by linarith)
    have hbR : (c : ℝ) ≤ b := by exact_mod_cast hcb
    obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered ie kR w ⟨u, NamedObject.block D⟩ c
      (max (x.time (ie + 1)) GST + ΔNet) ⟨hsende, hhone⟩ trivial hkR hiek
      (fun j h1 h2 => hwin j (le_trans hlate (htime h1)) h2)
      (deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
      (fun r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst => by
        have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
        subst hr'
        exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
    exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD hlj
      (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw
  · -- the relay before `a`: `u` serves `D` at its last step before `a`, and the sync fact
    push_neg at hlate
    have h0 : (0 : ℝ) ≤ x.time (ie + 1) := (time_nonneg M) x R (ie + 1)
    have ha1 : 1 ≤ a := by
      have : (0 : ℝ) < (a : ℝ) := lt_of_le_of_lt h0 hlate
      exact_mod_cast this
    have hiek : ie < x.stepBefore a := ((lt_stepBefore_iff M) x R E).2 hlate
    obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E ha1
    have hΔsR : (0 : ℝ) ≤ Δs := by positivity
    have hvk : u ∈ A.active (x.stepBefore a) :=
      Activity.mem_activeThroughout.1 hu₀ _ (by linarith) hk2
    have hkk : x.stepBefore a < kR := (lt_of_time_lt M) x R (by linarith)
    have hserve : servesMin M S.C (x.st (x.stepBefore a) u) (x.clockValue (x.stepBefore a) u)
        (NamedObject.block D) :=
      ⟨(mem_T_mono M F) x R E u (show ie + 1 ≤ x.stepBefore a by omega) hie1, hFa, hg⟩
    have hamax : a + Δs ≤ c := by
      have := le_max_right (Δ S) Δs
      omega
    rcases (delivered_before_of_held_upTo_tick M) x R E Sy (by omega) hvk hk1 hk2 hserve trivial
        (fun i h1 h2 => Activity.mem_activeThroughout.1 hu₀ i h2 (le_trans h1 (htime (Nat.le_succ i))))
        hGSTa hamax hkR (fun i hi hik => hwin i hi hik)
        (fun r j₀ k₁ t₁ hr _ hnr hjk₁ _ hlk₁ _ hfirst => by
          have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
          subst hr'
          exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
      with hw | ⟨j, -, -, -, -, hlj, hjk, hadm, -⟩
    · exact (mem_T_mono M F) x R E w hkk.le hw.1
    · exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD hlj
        (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw

/-- **A block an honest validator holds at a step is in a receiver's tree at its tick to `c`.**
The holder-at-a-step twin of `block_at_tick_of_held_tick`: a block `D` other than the genesis block, in
`u`'s tree at a step `kU` whose real time is at most the natural number `tu`, `u` outside the adversary set
at `kU`, active from `a` through the sync delay after it and its finalized block at its last step before
`a` compatible with `D`, is in `w`'s tree at its tick `kR` to `c`, when `w`'s finalized block there is
compatible with `D`, `w` is active at every step from the real time `a` up to `kR`, and `w` ticked to a
clock value `c₂`, at least the start of `D`'s slot and at least one delay before `c`. Here `GST ≤ a`,
`a + max (Δ S) Δs ≤ c` and `tu + Δ S ≤ c`.

Why: as `block_at_tick_of_held_tick`, with the relay's real time at most `tu` (the relay is at or before
`kU`): the delivery promise's deadline `max _ GST + ΔNet` is at most `tu + ΔNet ≤ c − ΔClockAhead`
(`hNet`), and `kU` comes before `kR` (its real time is at most `tu`, less than `c − ΔClockAhead`,
`hSkew`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `b`: the bound of the delivery premises; `tu`: a natural number
  at least the real time of `kU`, the holder's step; `a`: the start of the windows; `c`, `kR`: the
  clock value and the step of `w`'s tick; `c₂`, `k₂`: those of `w`'s earlier tick; `u`: the holder;
  `w`: the receiver; `D`: the block.

Read aloud: a block an honest holder has at a step by the real time `tu` is in every receiver's tree at
its tick to a clock value at least one delay after `tu`, when the receiver is up from `a`, the holder is
up for one sync delay after `a`, and the receiver's finalized block is compatible with the block. -/
theorem block_at_tick_of_held_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST b tu kU a c c₂ kR k₂ : ℕ) (u w : V)
    (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ c) (hcu : tu + Δ S ≤ c)
    (hcb : c ≤ b)
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (htu : x.time kU ≤ tu) (hu : u ∉ A.corrupted kU)
    (hD : D ∈ (x.st kU u).tree)
    (hFa : (x.st (x.stepBefore a) u).finalized.compatible D = true)
    (hg : D ≠ Block.genesis)
    (hkR : x.lbl kR = Event.tick w c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂)
    (hFw : (x.st kR w).finalized.compatible D = true) :
    D ∈ (x.st kR w).tree := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
  have hN0 : (0 : ℝ) ≤ ΔNet := by positivity
  have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  have hkUt : x.time kU ≤ tu := htu
  obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hD hg
  have hcR : (tu : ℝ) + Δ S ≤ c := by exact_mod_cast hcu
  have hc₂R : (c₂ : ℝ) + Δ S ≤ c := by exact_mod_cast hc₂
  have hmaxR : ((a : ℕ) : ℝ) + Δ S ≤ c := by
    have h1 : a + Δ S ≤ c := le_trans (Nat.add_le_add_left (le_max_left _ _) a) ha
    exact_mod_cast h1
  have hsk : kU < kR := (lt_of_time_lt M) x R (by linarith)
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C D.slot) hk₂ hkR
    (by linarith) hDc₂
  by_cases hlate : (a : ℝ) ≤ x.time (ie + 1)
  · -- the relay from `a` on: the delivery promise
    have hiek : ie < kR := by omega
    have hieT : x.time (ie + 1) ≤ x.time kU := htime (show ie + 1 ≤ kU by omega)
    have hGSTR : (GST : ℝ) ≤ a := by exact_mod_cast hGSTa
    have hmax : max (x.time (ie + 1)) (GST : ℝ) ≤ tu :=
      max_le (by linarith) (by linarith)
    have hbR : (c : ℝ) ≤ b := by exact_mod_cast hcb
    obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered ie kR w ⟨u, NamedObject.block D⟩ c
      (max (x.time (ie + 1)) GST + ΔNet) ⟨hsende, hhone⟩ trivial hkR hiek
      (fun j h1 h2 => hwin j (le_trans hlate (htime h1)) h2)
      (deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
      (fun r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst => by
        have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
        subst hr'
        exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
    exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD hlj
      (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw
  · -- the relay before `a`: `u` serves `D` at its last step before `a`, and the sync fact
    push_neg at hlate
    have h0 : (0 : ℝ) ≤ x.time (ie + 1) := (time_nonneg M) x R (ie + 1)
    have ha1 : 1 ≤ a := by
      have : (0 : ℝ) < (a : ℝ) := lt_of_le_of_lt h0 hlate
      exact_mod_cast this
    have hiek : ie < x.stepBefore a := ((lt_stepBefore_iff M) x R E).2 hlate
    obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E ha1
    have hΔsR : (0 : ℝ) ≤ Δs := by positivity
    have hvk : u ∈ A.active (x.stepBefore a) :=
      Activity.mem_activeThroughout.1 hu₀ _ (by linarith) hk2
    have hkk : x.stepBefore a < kR := (lt_of_time_lt M) x R (by linarith)
    have hserve : servesMin M S.C (x.st (x.stepBefore a) u) (x.clockValue (x.stepBefore a) u)
        (NamedObject.block D) :=
      ⟨(mem_T_mono M F) x R E u (show ie + 1 ≤ x.stepBefore a by omega) hie1, hFa, hg⟩
    have hamax : a + Δs ≤ c := by
      have := le_max_right (Δ S) Δs
      omega
    rcases (delivered_before_of_held_upTo_tick M) x R E Sy (by omega) hvk hk1 hk2 hserve trivial
        (fun i h1 h2 => Activity.mem_activeThroughout.1 hu₀ i h2 (le_trans h1 (htime (Nat.le_succ i))))
        hGSTa hamax hkR (fun i hi hik => hwin i hi hik)
        (fun r j₀ k₁ t₁ hr _ hnr hjk₁ _ hlk₁ _ hfirst => by
          have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
          subst hr'
          exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
      with hw | ⟨j, -, -, -, -, hlj, hjk, hadm, -⟩
    · exact (mem_T_mono M F) x R E w hkk.le hw.1
    · exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD hlj
        (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw


end GoldilocksCorrectness.Record.Proofs.Executions

